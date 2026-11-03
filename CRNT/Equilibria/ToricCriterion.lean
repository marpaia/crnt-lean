import CRNT.Equilibria.ToricSteadyStates
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A sufficient criterion for toric steady states (Pérez Millán–Dickenstein–Shiu–Conradi)

Write the mass-action steady-state equations as `Σ (Ψ x) = 0`, where `Ψ x = (x ^ y_j)_{j ∈ J}`
collects monomials and `Σ : ℝ^J → ℝ^S` is linear. Suppose `ker Σ` is spanned by vectors
`b_1, …, b_d` with pairwise disjoint supports, each positive on its support (Pérez Millán,
Dickenstein, Shiu, Conradi, *Chemical reaction systems with toric steady states*, Bull. Math.
Biol. 74 (2012), Theorem 3.8 / Condition 3.4). Then a positive `x` is a steady state iff
`b_{c j'} · x ^ y_j = b_{c j} · x ^ y_{j'}` whenever `j, j'` lie in the same support class `c`.
These are binomials with positive coefficients, so the system has toric steady states, and the
log-affine parametrization of `CRNT.Equilibria.ToricSteadyStates` applies.

Main results:
* `CRNT.ToricCriterion.mem_ker_iff`: the kernel membership of `Ψ x`, binomially.
* `CRNT.Network.hasToricSteadyStates_of_disjointKernelBasis`.
-/

namespace CRNT

namespace ToricCriterion

open scoped BigOperators

variable {J : Type} {d : ℕ}

/-- A kernel basis with disjoint positive supports: `b i j > 0` iff `cls j = i`, else `0`. -/
structure DisjointPositiveBasis (J : Type) (d : ℕ) where
  cls : J → Fin d
  b : Fin d → J → ℝ
  pos : ∀ j, 0 < b (cls j) j
  zero : ∀ i j, cls j ≠ i → b i j = 0

variable (B : DisjointPositiveBasis J d)

/-- A vector lies in the span of the basis iff it is proportional to `b c` on each class `c`
(all classes nonempty since each `b c` is supported on its class). -/
theorem mem_span_of_proportional [Fintype J] {w : J → ℝ}
    (hw : ∀ j j', B.cls j = B.cls j' → B.b (B.cls j) j' * w j = B.b (B.cls j) j * w j') :
    w ∈ Submodule.span ℝ (Set.range B.b) := by
  classical
  -- coefficient of class `i`: `w j / b i j` for any `j` in class `i` (0 if empty)
  let coef : Fin d → ℝ := fun i =>
    if h : ∃ j, B.cls j = i then w h.choose / B.b i h.choose else 0
  have hw' : w = ∑ i, coef i • B.b i := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single (B.cls j)]
    · have hex : ∃ j', B.cls j' = B.cls j := ⟨j, rfl⟩
      simp only [Pi.smul_apply, smul_eq_mul, coef, hex, dite_true]
      set j' := hex.choose
      have hj' : B.cls j' = B.cls j := hex.choose_spec
      have hp := B.pos j'
      rw [hj'] at hp
      have := hw j j' hj'.symm
      rw [div_mul_eq_mul_div, eq_div_iff hp.ne']
      linarith
    · intro i _ hi
      simp [B.zero i j (Ne.symm hi ∘ Eq.symm ∘ Eq.symm) ]
    · simp
  rw [hw']
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Conversely every vector in the span is proportional on classes. -/
theorem proportional_of_mem_span {w : J → ℝ} (hw : w ∈ Submodule.span ℝ (Set.range B.b)) :
    ∀ j j', B.cls j = B.cls j' → B.b (B.cls j) j' * w j = B.b (B.cls j) j * w j' := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  intro j j' hjj'
  have hval : ∀ k, (∑ i, c i • B.b i) k = c (B.cls k) * B.b (B.cls k) k := by
    intro k
    rw [Finset.sum_apply, Finset.sum_eq_single (B.cls k)]
    · simp
    · intro i _ hi
      simp [B.zero i k (fun h => hi h.symm)]
    · simp
  rw [hval, hval, ← hjj']
  ring

/-- **Binomial description of the kernel.** -/
theorem mem_ker_iff {S : Type} [Fintype J] (Sig : (J → ℝ) →ₗ[ℝ] (S → ℝ)) (hker : LinearMap.ker Sig = Submodule.span ℝ (Set.range B.b))
    (w : J → ℝ) :
    Sig w = 0 ↔ ∀ j j', B.cls j = B.cls j' → B.b (B.cls j) j' * w j = B.b (B.cls j) j * w j' := by
  rw [← LinearMap.mem_ker, hker]
  exact ⟨proportional_of_mem_span B, mem_span_of_proportional B⟩

end ToricCriterion

namespace Network

open ToricCriterion

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Toric steady states from a disjoint kernel basis** (Pérez Millán et al. 2012,
Theorem 3.8). If the mass-action field factors as `f(x) = Σ (x ^ y_j)_j` and `ker Σ` has a basis
with pairwise disjoint positive supports, the system has toric steady states. -/
theorem hasToricSteadyStates_of_disjointKernelBasis (N : Network S) (κ : RateConstants N)
    {J : Type} [Fintype J] [DecidableEq J] {d : ℕ} (y : J → Complex S)
    (Sig : (J → ℝ) →ₗ[ℝ] (S → ℝ))
    (hfac : ∀ x, N.massActionVectorField κ x = Sig (fun j => (y j).massActionMonomial x))
    (B : DisjointPositiveBasis J d)
    (hker : LinearMap.ker Sig = Submodule.span ℝ (Set.range B.b)) :
    N.HasToricSteadyStates κ := by
  classical
  -- index the binomials by pairs in the same class
  let P := {p : J × J // B.cls p.1 = B.cls p.2}
  let e := Fintype.equivFin P
  refine ⟨Fintype.card P, fun k => y (e.symm k).1.1, fun k => y (e.symm k).1.2,
    fun k => B.b (B.cls (e.symm k).1.1) (e.symm k).1.1 / B.b (B.cls (e.symm k).1.1) (e.symm k).1.2,
    fun k => ?_, fun x hx => ?_⟩
  · have h1 := B.pos (e.symm k).1.1
    have h2 := B.pos (e.symm k).1.2
    rw [← (e.symm k).2] at h2
    exact div_pos h1 h2
  · have hss : N.IsMassActionSteadyState κ x ↔
        Sig (fun j => (y j).massActionMonomial x) = 0 := by
      rw [← hfac]
      exact ⟨fun h => funext h, fun h s => congrFun h s⟩
    rw [hss, mem_ker_iff B Sig hker]
    constructor
    · intro h k
      set p := e.symm k
      have hp2 := B.pos p.1.2
      rw [← p.2] at hp2
      have := h p.1.1 p.1.2 p.2
      show (y p.1.1).massActionMonomial x =
        B.b (B.cls p.1.1) p.1.1 / B.b (B.cls p.1.1) p.1.2 * (y p.1.2).massActionMonomial x
      rw [div_mul_eq_mul_div, eq_div_iff hp2.ne']
      linarith
    · intro h j j' hjj'
      have := h (e ⟨(j, j'), hjj'⟩)
      simp only [Equiv.symm_apply_apply] at this
      have hp2 := B.pos j'
      rw [← hjj'] at hp2
      rw [this]
      field_simp
end Network

end CRNT
