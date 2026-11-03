import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear elimination of intermediates (Feliu–Wiuf)

At steady state the concentrations `u` of intermediate species `Y_i` solve a linear system
`L u = b`, where `a i j ≥ 0` is the rate constant of the conversion `Y_j → Y_i`, `e j ≥ 0` the
total rate constant of reactions `Y_j → (non-intermediate complex)`, and `b i ≥ 0` the inflow
into `Y_i` from non-intermediate complexes (a nonnegative combination of monomials in the
non-intermediate concentrations):

`(L u)_i = (∑_k a k i + e i) u_i - ∑_j a i j u_j`.

If every intermediate can eventually leave the set of intermediates (no nonempty set of
intermediates is closed), then (Feliu–Wiuf, *Simplifying biochemical models with intermediate
species*, J. R. Soc. Interface 10 (2013), Theorem 1) the system has a unique solution, which is a
nonnegative linear combination of the inflows; in particular, the steady-state intermediate
concentrations are polynomials with nonnegative coefficients in the remaining concentrations,
positive when every inflow is positive.

Main results:
* `CRNT.Elimination.nonneg_of_nonneg`: a discrete maximum principle.
* `CRNT.Elimination.existsUnique_solution`.
* `CRNT.Elimination.pos_of_pos`.
* `CRNT.Elimination.solution_eq_nonneg_combination`: `u = M b` with `M ≥ 0` entrywise.
* `CRNT.Elimination.eliminated_eq_monomial_combination`: inflows that are nonnegative
  combinations of monomials give intermediates that are nonnegative combinations of the same
  monomials.
-/

namespace CRNT

namespace Elimination

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The intermediate operator `(L u)_i = (∑_k a k i + e i) u_i - ∑_j a i j u_j`. -/
def op (a : ι → ι → ℝ) (e : ι → ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i => (∑ k, a k i + e i) * u i - ∑ j, a i j * u j

/-- **Drainage**: no nonempty set of intermediates is closed under the dynamics; some member
either exits directly or converts to an intermediate outside the set. -/
def Drained (a : ι → ι → ℝ) (e : ι → ℝ) : Prop :=
  ∀ N : Finset ι, N.Nonempty → ∃ j ∈ N, 0 < e j ∨ ∃ i, i ∉ N ∧ 0 < a i j

/-- The intermediate operator as a linear map. -/
def opLinear (a : ι → ι → ℝ) (e : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := op a e
  map_add' u v := by
    funext i; simp only [op, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c u := by
    funext i; simp only [op, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring

/-- **Discrete maximum principle.** Under drainage, `L u ≥ 0` forces `u ≥ 0`. -/
theorem nonneg_of_nonneg {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) {u : ι → ℝ} (hb : ∀ i, 0 ≤ op a e u i) :
    ∀ i, 0 ≤ u i := by
  classical
  by_contra hcon
  push Not at hcon
  set N := Finset.univ.filter (fun i => u i < 0)
  have hN : N.Nonempty := by
    obtain ⟨i, hi⟩ := hcon
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  -- sum the equations over `N`
  have hsum : 0 ≤ ∑ i ∈ N, op a e u i := Finset.sum_nonneg fun i _ => hb i
  -- upper bound: drop the (nonpositive) contributions from outside `N`
  have hout : ∀ i, -∑ j, a i j * u j ≤ -∑ j ∈ N, a i j * u j := by
    intro i
    rw [neg_le_neg_iff, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => u j < 0)]
    have : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ u j < 0), a i j * u j :=
      Finset.sum_nonneg fun j hj =>
        mul_nonneg (ha i j) (not_lt.mp (Finset.mem_filter.mp hj).2)
    simp only [N]; linarith
  have hupper : ∑ i ∈ N, op a e u i ≤
      ∑ j ∈ N, u j * (∑ k, a k j + e j - ∑ i ∈ N, a i j) := by
    calc ∑ i ∈ N, op a e u i ≤ ∑ i ∈ N, ((∑ k, a k i + e i) * u i - ∑ j ∈ N, a i j * u j) :=
          Finset.sum_le_sum fun i _ => by unfold op; linarith [hout i]
      _ = ∑ j ∈ N, u j * (∑ k, a k j + e j - ∑ i ∈ N, a i j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_comm (s := N) (t := N)]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_sub, Finset.mul_sum]
          congr 1
          · ring
          · exact Finset.sum_congr rfl fun i _ => by ring
  -- each coefficient `c j = e j + ∑_{i ∉ N} a i j` is nonnegative
  have hcoef : ∀ j, ∑ k, a k j + e j - ∑ i ∈ N, a i j =
      e j + ∑ i ∈ Finset.univ.filter (fun i => ¬ u i < 0), a i j := by
    intro j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => u i < 0)]
    simp only [N]; ring
  have hterm : ∀ j ∈ N, u j * (∑ k, a k j + e j - ∑ i ∈ N, a i j) ≤ 0 := by
    intro j hj
    rw [hcoef]
    have hu := (Finset.mem_filter.mp hj).2
    have : 0 ≤ e j + ∑ i ∈ Finset.univ.filter (fun i => ¬ u i < 0), a i j :=
      add_nonneg (he j) (Finset.sum_nonneg fun i _ => ha i j)
    nlinarith
  -- so every term vanishes, which contradicts drainage
  have hzero : ∑ j ∈ N, u j * (∑ k, a k j + e j - ∑ i ∈ N, a i j) = 0 :=
    le_antisymm (Finset.sum_nonpos hterm) (hsum.trans hupper)
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hzero
  obtain ⟨j, hjN, hj⟩ := hdr N hN
  have hu := (Finset.mem_filter.mp hjN).2
  have h0 := hall j hjN
  rw [hcoef] at h0
  have hc : e j + ∑ i ∈ Finset.univ.filter (fun i => ¬ u i < 0), a i j = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hu.ne
    · exact h
  have hsum0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ u i < 0), a i j = 0 := by
    have := Finset.sum_nonneg (s := Finset.univ.filter (fun i => ¬ u i < 0))
      fun i (_ : i ∈ _) => ha i j
    linarith [he j]
  rcases hj with hej | ⟨i, hiN, hai⟩
  · linarith [Finset.sum_nonneg (s := Finset.univ.filter (fun i => ¬ u i < 0))
      fun i (_ : i ∈ _) => ha i j]
  · have hi : i ∈ Finset.univ.filter (fun i => ¬ u i < 0) := by
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hiN ⊢
      exact hiN
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ _) => ha i j).mp hsum0 i hi
    linarith

/-- Under drainage the intermediate operator is injective. -/
theorem op_injective {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) : Function.Injective (opLinear a e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h1 := nonneg_of_nonneg ha he hdr (u := u) (fun i => by
    have := congrFun hu i; simp [opLinear] at this; rw [this])
  have h2 := nonneg_of_nonneg ha he hdr (u := -u) (fun i => by
    have := congrFun ((opLinear a e).map_neg u) i
    rw [hu, neg_zero] at this
    have h' : op a e (-u) i = 0 := by simpa [opLinear] using this
    rw [h'])
  funext i
  have := h2 i
  simp only [Pi.neg_apply, neg_nonneg] at this
  exact le_antisymm this (h1 i)

/-- **Existence and uniqueness of the intermediate steady state.** -/
theorem existsUnique_solution {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) (b : ι → ℝ) :
    ∃! u : ι → ℝ, op a e u = b := by
  have hinj := op_injective ha he hdr
  have hsurj : Function.Surjective (opLinear a e) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsurj b
  exact ⟨u, hu, fun v hv => hinj (hv.trans hu.symm)⟩

/-- **Positivity.** With positive inflows every intermediate has positive steady-state
concentration. -/
theorem pos_of_pos {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) {u b : ι → ℝ} (hu : op a e u = b)
    (hb : ∀ i, 0 < b i) : ∀ i, 0 < u i := by
  have hnn := nonneg_of_nonneg ha he hdr (u := u) (fun i => by rw [hu]; exact (hb i).le)
  intro i
  have hi := congrFun hu i
  unfold op at hi
  have : 0 ≤ ∑ j, a i j * u j := Finset.sum_nonneg fun j _ => mul_nonneg (ha i j) (hnn j)
  have hd : 0 ≤ ∑ k, a k i + e i :=
    add_nonneg (Finset.sum_nonneg fun k _ => ha k i) (he i)
  rcases (hnn i).lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at hi; linarith [hb i]

/-- The solution operator `b ↦ u`. -/
noncomputable def solve {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) (b : ι → ℝ) : ι → ℝ :=
  (existsUnique_solution ha he hdr b).exists.choose

theorem op_solve {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) (b : ι → ℝ) : op a e (solve ha he hdr b) = b :=
  (existsUnique_solution ha he hdr b).exists.choose_spec

theorem solve_nonneg {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) :
    ∀ i, 0 ≤ solve ha he hdr b i :=
  nonneg_of_nonneg ha he hdr (fun k => by rw [op_solve]; exact hb k)

/-- **Linear elimination formula.** The solution is `u = M b` for the matrix
`M i j = (solve (eⱼ)) i ≥ 0`. -/
theorem solution_eq_nonneg_combination [DecidableEq ι] {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) :
    ∃ M : ι → ι → ℝ, (∀ i j, 0 ≤ M i j) ∧
      ∀ b u : ι → ℝ, op a e u = b → ∀ i, u i = ∑ j, M i j * b j := by
  classical
  let M : ι → ι → ℝ := fun i j => solve ha he hdr (Pi.single j 1) i
  refine ⟨M, fun i j => solve_nonneg ha he hdr (fun k => by
    by_cases h : k = j <;> simp [h]) i, ?_⟩
  intro b u hu i
  have hinj := op_injective ha he hdr
  have hlin : opLinear a e (fun i => ∑ j, M i j * b j) = b := by
    have : (fun i => ∑ j, M i j * b j) = ∑ j, b j • solve ha he hdr (Pi.single j 1) := by
      funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, map_sum]
    simp_rw [map_smul]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [opLinear, LinearMap.coe_mk, AddHom.coe_mk, op_solve]
    simp [Pi.single_apply]
  have : u = fun i => ∑ j, M i j * b j := hinj (by
    show op a e u = op a e _
    rw [hu]; exact hlin.symm)
  exact congrFun this i

/-- **Eliminated intermediates are nonnegative combinations of monomials.** If the inflow into
each intermediate is `b j(x) = ∑_c β j c · m c(x)` with `β ≥ 0` (here `m c` are arbitrary
functions, e.g. mass-action monomials in the non-intermediate species), the eliminated
intermediate concentrations are `u i(x) = ∑_c γ i c · m c(x)` with `γ ≥ 0`, independent of `x`. -/
theorem eliminated_eq_monomial_combination [DecidableEq ι] {a : ι → ι → ℝ} {e : ι → ℝ}
    (ha : ∀ i j, 0 ≤ a i j) (he : ∀ i, 0 ≤ e i) (hdr : Drained a e)
    {κ X : Type*} [Fintype κ] (β : ι → κ → ℝ) (hβ : ∀ j c, 0 ≤ β j c) (m : κ → X → ℝ) :
    ∃ γ : ι → κ → ℝ, (∀ i c, 0 ≤ γ i c) ∧ ∀ (x : X) (u : ι → ℝ),
      op a e u = (fun j => ∑ c, β j c * m c x) → ∀ i, u i = ∑ c, γ i c * m c x := by
  obtain ⟨M, hM, hsol⟩ := solution_eq_nonneg_combination ha he hdr
  refine ⟨fun i c => ∑ j, M i j * β j c, fun i c =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hβ j c), ?_⟩
  intro x u hu i
  rw [hsol _ u hu i]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

end Elimination

end CRNT
