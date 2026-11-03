import CRNT.Multistationarity.RankOneLowerBound
import CRNT.Multistationarity.TwoReactionNondegenerate
import CRNT.Multistationarity.InheritanceAddReactions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Positively decorated simplices give steady states (Bihan–Dickenstein–Giaroli)

Bihan, Dickenstein and Giaroli (2020) bound the number of positive steady states from below by
the number of *positively decorated simplices* in a regular subdivision of the set of reactant
complexes. This module proves the full-rank version by a toric (patchworking) deformation.

**Data.** Fix positive rate constants `κ̄` and integer heights `h` on complexes. A *decorated
cell* is a set `Δ` of `n + 1` affinely independent complexes (`n = #species`) together with
`w ∈ ℤ^S`, `c ∈ ℤ` such that `⟨w, a⟩ + h(a) = c` on `Δ` and `> c` at every other reactant
complex (a lower facet of the lifted configuration), whose combined reaction vectors
`W_a = ∑_{source r = a} κ̄_r (y'_r − y_r)` span `ℝ^S` and admit a positive linear relation
`∑_a λ_a W_a = 0` (positive decoration).

**Argument.** With rates `κ̄_r t^{h(y_r)}` and the substitution `x = t^w y`, the mass-action field
is `t^c G(t, y)` with `G` polynomial in `(t, y)` and `G(0, ·)` the field of the subnetwork of
reactions with reactant in `Δ`. That subsystem has a positive steady state (`y^a = ρ λ_a`, solvable
by affine independence) with injective Jacobian (the kernel of `β ↦ ∑ β_a W_a` is the line
`ℝ λ`). The implicit function theorem continues it to `t > 0`; cells with different `w` give
different steady states for small `t`.

* `rowsMatrix_solve`: square-rank linear algebra.
* `DecoratedCell`, `DecoratedCell.exists_simplex_solution`, `DecoratedCell.jacobian_injective`.
* `DecoratedCell.G`, `DecoratedCell.field_scalePoint`, `DecoratedCell.exists_branch`.
* `multistationary_of_two_decoratedCells`, `steadyStates_of_decoratedCells` (`d` cells with
  distinct normals give `d` distinct positive steady states).
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Rows linearly independent and as many rows as columns: the system `A ξ = b` is uniquely
solvable. -/
theorem rowsMatrix_solve {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (hcard : Fintype.card ι = Fintype.card κ)
    (hli : LinearIndependent ℝ A.row) :
    (∀ b : ι → ℝ, ∃ ξ : κ → ℝ, A.mulVec ξ = b) ∧ (∀ ξ : κ → ℝ, A.mulVec ξ = 0 → ξ = 0) := by
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli]
  have hrange : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card, hcard] at h
    exact Submodule.finrank_eq_zero.mp (by omega)
  constructor
  · intro b
    have : b ∈ LinearMap.range A.mulVecLin := by rw [hrange]; trivial
    obtain ⟨ξ, hξ⟩ := this
    exact ⟨ξ, hξ⟩
  · intro ξ hξ
    have : ξ ∈ LinearMap.ker A.mulVecLin := hξ
    rw [hker] at this
    exact this

/-- The combined reaction vector of a complex: `W_a = ∑_{source r = a} κ̄_r (y'_r − y_r)`. -/
noncomputable def combinedVector (N : Network S) (κ : RateConstants N) (a : Complex S) :
    S → ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => (N.reaction r).source = a), κ.k r • N.reactionVector r

/-- The affine row `(1, a)` of a complex, indexed by `Option S`. -/
def affineRow (a : Complex S) : Option S → ℝ := fun j => Option.elim j 1 (fun s => (a s : ℝ))

/-- `⟨w, a⟩` for an integer weight. -/
def pairing (w : S → ℤ) (a : Complex S) : ℤ := ∑ s, w s * (a s : ℤ)

/-- A **positively decorated lower cell** for rates `κ̄` and heights `h`. -/
structure DecoratedCell (N : Network S) (κ : RateConstants N) (h : Complex S → ℕ) where
  Δ : Finset (Complex S)
  w : S → ℤ
  c : ℤ
  card : Fintype.card Δ = Fintype.card (Option S)
  affInd : LinearIndependent ℝ (fun a : Δ => affineRow a.1)
  onCell : ∀ a ∈ Δ, pairing w a + h a = c
  offCell : ∀ r : N.R, (N.reaction r).source ∉ Δ → c < pairing w (N.reaction r).source +
    h (N.reaction r).source
  span : Submodule.span ℝ (Set.range fun a : Δ => combinedVector N κ a.1) = ⊤
  lam : Δ → ℝ
  lam_pos : ∀ a, 0 < lam a
  lam_ker : ∑ a, lam a • combinedVector N κ a.1 = 0

namespace DecoratedCell

variable {N : Network S} {κ : RateConstants N} {h : Complex S → ℕ}

/-- The affine matrix with rows `(1, a)`, `a ∈ Δ`. -/
def rows (C : DecoratedCell N κ h) : Matrix C.Δ (Option S) ℝ := fun a => affineRow a.1

theorem rows_row (C : DecoratedCell N κ h) : C.rows.row = fun a : C.Δ => affineRow a.1 := rfl

theorem rows_mulVec (C : DecoratedCell N κ h) (ξ : Option S → ℝ) (a : C.Δ) :
    C.rows.mulVec ξ a = ξ none + ∑ s, (a.1 s : ℝ) * ξ (some s) := by
  simp only [rows, Matrix.mulVec, dotProduct, Fintype.sum_option, affineRow, Option.elim]
  ring

/-- **The simplex system is solvable**: there are `y > 0`, `ρ > 0` with `y^a = ρ λ_a` on `Δ`. -/
theorem exists_simplex_solution (C : DecoratedCell N κ h) :
    ∃ y : Concentration S, y.Positive ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a : C.Δ, a.1.massActionMonomial y = ρ * C.lam a := by
  obtain ⟨ξ, hξ⟩ := (rowsMatrix_solve C.rows C.card (by rw [rows_row]; exact C.affInd)).1
    (fun a => Real.log (C.lam a))
  refine ⟨fun s => Real.exp (ξ (some s)), fun s => Real.exp_pos _, Real.exp (-ξ none),
    Real.exp_pos _, fun a => ?_⟩
  have h1 := congrFun hξ a
  rw [rows_mulVec] at h1
  rw [monomial_eq_exp_sum_log _ (fun s => Real.exp_pos _)]
  simp only [Real.log_exp]
  have : ∑ s, (a.1 s : ℝ) * ξ (some s) = Real.log (C.lam a) + (-ξ none) := by linarith
  rw [this, Real.exp_add, Real.exp_log (C.lam_pos a)]
  ring

/-- **The kernel of `β ↦ ∑ β_a W_a` is the line `ℝ λ`.** -/
theorem ker_eq_smul_lam (C : DecoratedCell N κ h) (β : C.Δ → ℝ)
    (hβ : ∑ a, β a • combinedVector N κ a.1 = 0) : ∃ θ : ℝ, ∀ a, β a = θ * C.lam a := by
  classical
  set L := Fintype.linearCombination ℝ (fun a : C.Δ => combinedVector N κ a.1) with hL
  have hrange : LinearMap.range L = ⊤ := by rw [hL, Fintype.range_linearCombination, C.span]
  have hfin : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      C.card, Fintype.card_option] at h1
    omega
  have hlam : C.lam ∈ LinearMap.ker L := by
    show L C.lam = 0
    rw [hL, Fintype.linearCombination_apply]; exact C.lam_ker
  have hβk : β ∈ LinearMap.ker L := by
    show L β = 0
    rw [hL, Fintype.linearCombination_apply]; exact hβ
  have hne : (⟨C.lam, hlam⟩ : LinearMap.ker L) ≠ 0 := by
    intro h0
    have hc : Fintype.card C.Δ ≠ 0 := by rw [C.card]; simp
    obtain ⟨a⟩ : Nonempty C.Δ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hc)
    have := congrArg (fun v : LinearMap.ker L => (v : C.Δ → ℝ) a) h0
    simp at this
    exact (C.lam_pos a).ne' this
  obtain ⟨θ, hθ⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin ⟨β, hβk⟩
  refine ⟨θ, fun a => ?_⟩
  have := congrArg (fun v : LinearMap.ker L => (v : C.Δ → ℝ) a) hθ
  simpa using this.symm

end DecoratedCell

/-- The subnetwork of reactions whose reactant lies in `Δ`. -/
def cellNet (N : Network S) (Δ : Finset (Complex S)) : Network S :=
  ⟨{r : N.R // (N.reaction r).source ∈ Δ}, inferInstance, inferInstance, fun r => N.reaction r.1⟩

/-- Restricted rate constants. -/
def cellRates (N : Network S) (κ : RateConstants N) (Δ : Finset (Complex S)) :
    RateConstants (cellNet N Δ) :=
  ⟨fun r => κ.k r.1, fun r => κ.positive r.1⟩

namespace DecoratedCell

variable {N : Network S} {κ : RateConstants N} {h : Complex S → ℕ}

/-- Grouping a sum over the reactions of the cell network by reactant complex. -/
theorem cellNet_sum_group (C : DecoratedCell N κ h) (f : Complex S → ℝ) :
    ∑ r : (cellNet N C.Δ).R, (κ.k r.1 * f (N.reaction r.1).source) • N.reactionVector r.1 =
      ∑ a : C.Δ, f a.1 • combinedVector N κ a.1 := by
  classical
  have h1 : ∑ r : (cellNet N C.Δ).R, (κ.k r.1 * f (N.reaction r.1).source) • N.reactionVector r.1
      = ∑ r ∈ Finset.univ.filter (fun r : N.R => (N.reaction r).source ∈ C.Δ),
          (κ.k r * f (N.reaction r).source) • N.reactionVector r := by
    show ∑ r : {r : N.R // (N.reaction r).source ∈ C.Δ}, _ = _
    exact (Finset.sum_subtype (p := fun r : N.R => (N.reaction r).source ∈ C.Δ)
      (Finset.univ.filter (fun r : N.R => (N.reaction r).source ∈ C.Δ)) (fun r => by simp)
      (fun r => (κ.k r * f (N.reaction r).source) • N.reactionVector r)).symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
    (fun r : N.R => (N.reaction r).source ∈ C.Δ)) (t := C.Δ) (g := fun r => (N.reaction r).source)
    (fun r hr => (Finset.mem_filter.mp hr).2)]
  rw [← Finset.sum_coe_sort C.Δ]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [combinedVector, Finset.smul_sum, smul_smul]
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun r hr => ?_
  · ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h ▸ a.2, h⟩
  · rw [(Finset.mem_filter.mp hr).2]; ring_nf

/-- **The Jacobian of the cell subsystem is injective at its simplex solution.** -/
theorem jacobian_injective (C : DecoratedCell N κ h) {y : Concentration S} (hy : y.Positive)
    {ρ : ℝ} (hρ : 0 < ρ) (hsol : ∀ a : C.Δ, a.1.massActionMonomial y = ρ * C.lam a)
    (u : S → ℝ) (hu : (cellNet N C.Δ).massActionJacobianCLM (cellRates N κ C.Δ) y u = 0) :
    u = 0 := by
  classical
  rw [massActionJacobianCLM_apply_sum] at hu
  have hform : ∀ r : (cellNet N C.Δ).R,
      ((cellRates N κ C.Δ).k r * ∑ j, massActionMonomialGrad ((cellNet N C.Δ).reaction r).source y j
        * u j) • (cellNet N C.Δ).reactionVector r =
      (κ.k r.1 * ((N.reaction r.1).source.massActionMonomial y *
        ∑ j, ((N.reaction r.1).source j : ℝ) * (u j / y j))) • N.reactionVector r.1 := by
    intro r
    congr 1
    show κ.k r.1 * ∑ j, massActionMonomialGrad (N.reaction r.1).source y j * u j = _
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [massActionMonomialGrad_eq_of_pos _ hy]
    have := (hy j).ne'
    field_simp
  simp_rw [hform] at hu
  rw [cellNet_sum_group C (fun a => a.massActionMonomial y * ∑ j, (a j : ℝ) * (u j / y j))] at hu
  -- the coefficient vector is in the kernel
  set z : S → ℝ := fun j => u j / y j with hz
  obtain ⟨θ, hθ⟩ := C.ker_eq_smul_lam
    (fun a => a.1.massActionMonomial y * ∑ j, (a.1 j : ℝ) * z j) hu
  have hlin : ∀ a : C.Δ, ∑ j, (a.1 j : ℝ) * z j = θ / ρ := by
    intro a
    have h1 := hθ a
    rw [hsol a] at h1
    have hl := C.lam_pos a
    field_simp
    nlinarith [h1]
  -- affine independence forces `z = 0`
  have hξ := (rowsMatrix_solve C.rows C.card (by rw [rows_row]; exact C.affInd)).2
    (fun j => Option.elim j (-(θ / ρ)) z) (by
      funext a
      rw [rows_mulVec]
      simp only [Option.elim, Pi.zero_apply]
      rw [hlin a]; ring)
  funext j
  have := congrFun hξ (some j)
  simp only [Option.elim, Pi.zero_apply] at this
  have hyj := (hy j).ne'
  simp only [hz] at this
  rw [Pi.zero_apply]
  rcases div_eq_zero_iff.mp this with h0 | h0
  · exact h0
  · exact absurd h0 hyj

/-- The height-plus-pairing excess `⟨w, y_r⟩ + h(y_r) − c ≥ 0`. -/
noncomputable def expo (C : DecoratedCell N κ h) (r : N.R) : ℕ :=
  (pairing C.w (N.reaction r).source + h (N.reaction r).source - C.c).toNat

theorem expo_spec (C : DecoratedCell N κ h) (r : N.R) :
    ((C.expo r : ℕ) : ℤ) = pairing C.w (N.reaction r).source + h (N.reaction r).source - C.c := by
  unfold expo
  apply Int.toNat_of_nonneg
  by_cases hr : (N.reaction r).source ∈ C.Δ
  · rw [C.onCell _ hr]; simp
  · have := C.offCell r hr; omega

theorem expo_eq_zero_iff (C : DecoratedCell N κ h) (r : N.R) :
    C.expo r = 0 ↔ (N.reaction r).source ∈ C.Δ := by
  constructor
  · intro h0
    by_contra hr
    have h1 := C.expo_spec r
    rw [h0] at h1
    have := C.offCell r hr
    omega
  · intro hr
    have h1 := C.expo_spec r
    rw [C.onCell _ hr, sub_self] at h1
    exact_mod_cast h1

/-- The deformed field `G(t, y) = ∑_r κ̄_r t^{e_r} y^{y_r} (y'_r − y_r)`. -/
noncomputable def G (C : DecoratedCell N κ h) (p : ℝ × (S → ℝ)) : S → ℝ :=
  ∑ r, (κ.k r * p.1 ^ C.expo r * (N.reaction r).source.massActionMonomial p.2) •
    N.reactionVector r

theorem G_contDiff (C : DecoratedCell N κ h) : ContDiff ℝ ⊤ C.G := by
  rw [contDiff_pi]
  intro s
  simp only [G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.massActionMonomial]
  fun_prop

/-- At `t = 0` only the reactions with reactant in the cell survive. -/
theorem G_zero (C : DecoratedCell N κ h) (y : S → ℝ) :
    C.G (0, y) = (cellNet N C.Δ).massActionVectorField (cellRates N κ C.Δ) y := by
  classical
  funext s
  rw [massActionVectorField_apply]
  simp only [G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun r : N.R => (N.reaction r).source ∈ C.Δ)]
  have hoff : ∑ r ∈ Finset.univ.filter (fun r : N.R => ¬ (N.reaction r).source ∈ C.Δ),
      κ.k r * (0 : ℝ) ^ C.expo r * (N.reaction r).source.massActionMonomial y *
        N.reactionVector r s = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hne : C.expo r ≠ 0 := fun h0 =>
      (Finset.mem_filter.mp hr).2 ((C.expo_eq_zero_iff r).mp h0)
    rw [zero_pow hne]; ring
  rw [hoff, add_zero]
  have hon : ∀ r ∈ Finset.univ.filter (fun r : N.R => (N.reaction r).source ∈ C.Δ),
      κ.k r * (0 : ℝ) ^ C.expo r * (N.reaction r).source.massActionMonomial y *
        N.reactionVector r s =
      κ.k r * (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by
    intro r hr
    rw [(C.expo_eq_zero_iff r).mpr (Finset.mem_filter.mp hr).2, pow_zero, mul_one]
  rw [Finset.sum_congr rfl hon]
  exact Finset.sum_subtype (p := fun r : N.R => (N.reaction r).source ∈ C.Δ)
    (Finset.univ.filter (fun r : N.R => (N.reaction r).source ∈ C.Δ)) (fun r => by simp)
    (fun r => κ.k r * (N.reaction r).source.massActionMonomial y * N.reactionVector r s)

/-- The toric substitution `x_s = t^{w_s} y_s`, written with `exp (w_s log t)`. -/
noncomputable def scalePoint (w : S → ℤ) (t : ℝ) (y : Concentration S) : Concentration S :=
  fun s => Real.exp ((w s : ℝ) * Real.log t) * y s

/-- The deformed rates `κ̄_r t^{h(y_r)}`. -/
noncomputable def deformedRates (κ : RateConstants N) (h : Complex S → ℕ) (t : ℝ) :
    RateConstants N :=
  ⟨fun r => κ.k r * Real.exp ((h (N.reaction r).source : ℝ) * Real.log t),
    fun r => mul_pos (κ.positive r) (Real.exp_pos _)⟩

omit [DecidableEq S] in
theorem monomial_scalePoint (w : S → ℤ) (t : ℝ) (y : Concentration S) (a : Complex S) :
    a.massActionMonomial (scalePoint w t y) =
      Real.exp ((pairing w a : ℝ) * Real.log t) * a.massActionMonomial y := by
  simp only [Complex.massActionMonomial, scalePoint, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp only [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1
  simp only [pairing]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The toric deformation.** For `t > 0`, the field with rates `κ̄_r t^{h(y_r)}` at
`x = t^w y` equals `t^c G(t, y)`. -/
theorem field_scalePoint (C : DecoratedCell N κ h) {t : ℝ} (ht : 0 < t) (y : Concentration S) :
    N.massActionVectorField (deformedRates κ h t) (scalePoint C.w t y) =
      Real.exp ((C.c : ℝ) * Real.log t) • C.G (t, y) := by
  funext s
  rw [massActionVectorField_apply]
  simp only [G, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [massActionRate, deformedRates, monomial_scalePoint]
  have hexp : Real.exp ((h (N.reaction r).source : ℝ) * Real.log t) *
      Real.exp ((pairing C.w (N.reaction r).source : ℝ) * Real.log t) =
      Real.exp ((C.c : ℝ) * Real.log t) * t ^ C.expo r := by
    rw [← Real.exp_add, ← Real.exp_log ht, ← Real.exp_nat_mul, Real.exp_log ht, ← Real.exp_add]
    congr 1
    have := C.expo_spec r
    have h' : ((C.expo r : ℕ) : ℝ) = (pairing C.w (N.reaction r).source : ℝ) +
        (h (N.reaction r).source : ℝ) - (C.c : ℝ) := by exact_mod_cast this
    rw [h']; ring
  calc κ.k r * Real.exp ((h (N.reaction r).source : ℝ) * Real.log t) *
        (Real.exp ((pairing C.w (N.reaction r).source : ℝ) * Real.log t) *
          (N.reaction r).source.massActionMonomial y) * N.reactionVector r s
      = κ.k r * (Real.exp ((h (N.reaction r).source : ℝ) * Real.log t) *
          Real.exp ((pairing C.w (N.reaction r).source : ℝ) * Real.log t)) *
          (N.reaction r).source.massActionMonomial y * N.reactionVector r s := by ring
    _ = _ := by rw [hexp]; ring

/-- **A branch of steady states from a decorated cell.** There is a positive simplex solution `y*`
and a branch `ψ`, continuous at `0` with `ψ 0 = y*`, with `G(t, ψ t) = 0` for `t` near `0`. -/
theorem exists_branch (C : DecoratedCell N κ h) :
    ∃ y : Concentration S, y.Positive ∧ ∃ ψ : ℝ → (S → ℝ), ψ 0 = y ∧ ContinuousAt ψ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), C.G (t, ψ t) = 0 := by
  classical
  obtain ⟨y, hy, ρ, hρ, hsol⟩ := C.exists_simplex_solution
  -- the simplex solution is a zero of `G(0, ·)`
  have hG0 : C.G (0, y) = 0 := by
    rw [G_zero]
    have hfield : (cellNet N C.Δ).massActionVectorField (cellRates N κ C.Δ) y =
        ∑ r : (cellNet N C.Δ).R, (κ.k r.1 * (N.reaction r.1).source.massActionMonomial y) •
          N.reactionVector r.1 := by
      funext s
      rw [massActionVectorField_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hfield, cellNet_sum_group C (fun a => a.massActionMonomial y)]
    simp only [hsol, mul_smul, ← Finset.smul_sum, C.lam_ker, smul_zero]
  have hcd : ContDiffAt ℝ 1 C.G (0, y) := (C.G_contDiff.of_le (by simp)).contDiffAt
  -- the partial derivative in `y` is the Jacobian of the cell subsystem
  set J := (cellNet N C.Δ).massActionJacobianCLM (cellRates N κ C.Δ) y with hJ
  have hpart : fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) = J := by
    have hdiff : DifferentiableAt ℝ C.G (0, y) := (C.G_contDiff.differentiable (by simp)) _
    have hcomp : HasFDerivAt (fun x => C.G (0, x))
        (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) y :=
      hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have heq : (fun x => C.G (0, x)) =
        (cellNet N C.Δ).massActionVectorField (cellRates N κ C.Δ) := by
      funext x; exact C.G_zero x
    rw [heq] at hcomp
    exact hcomp.unique ((cellNet N C.Δ).massActionVectorField_hasFDerivAt _ y)
  have hinj : Function.Injective (J : (S → ℝ) →ₗ[ℝ] (S → ℝ)) := by
    intro u v huv
    have h1 : J (u - v) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (C.jacobian_injective hy hρ hsol (u - v) h1)
  have hinv : (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    rw [hpart]
    let e : (S → ℝ) ≃ₗ[ℝ] (S → ℝ) := LinearEquiv.ofInjectiveEndo (J : (S → ℝ) →ₗ[ℝ] (S → ℝ)) hinj
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext v; rfl
  refine ⟨y, hy, hcd.implicitFunction one_ne_zero hinv,
    hcd.implicitFunction_apply_self one_ne_zero hinv,
    (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt, ?_⟩
  filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with t ht
  rw [ht, hG0]

end DecoratedCell

/-- **Bihan–Dickenstein–Giaroli lower bound, two cells (full-rank version).** If two positively
decorated lower cells of the same height function `h` (for rates `κ̄`) have different normals
`w`, the network is multistationary: for small `t > 0` the rates `κ̄_r t^{h(y_r)}` have two
distinct positive steady states, and the stoichiometric subspace is all of `ℝ^S`. -/
theorem multistationary_of_two_decoratedCells {N : Network S} {κ : RateConstants N}
    {h : Complex S → ℕ} (C₁ C₂ : DecoratedCell N κ h) (hw : C₁.w ≠ C₂.w) :
    N.HasMultistationarityCapacity := by
  classical
  obtain ⟨y₁, hy₁, ψ₁, hψ₁0, hψ₁c, hψ₁⟩ := C₁.exists_branch
  obtain ⟨y₂, hy₂, ψ₂, hψ₂0, hψ₂c, hψ₂⟩ := C₂.exists_branch
  -- the stoichiometric subspace is everything
  have hStop : N.stoichSubspace = ⊤ := by
    rw [eq_top_iff, ← C₁.span, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  -- positivity of the branches near `0`
  have hposev : ∀ (ψ : ℝ → (S → ℝ)) (y : Concentration S), y.Positive → ψ 0 = y →
      ContinuousAt ψ 0 → ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < ψ t s := by
    intro ψ y hy h0 hc
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ψ t s) 0 := (continuous_apply s).continuousAt.comp hc
    have : 0 < ψ 0 s := by rw [h0]; exact hy s
    exact hcs.eventually (lt_mem_nhds this)
  -- a coordinate where the normals differ
  obtain ⟨s, hs⟩ : ∃ s, C₁.w s ≠ C₂.w s := by
    by_contra hno; push Not at hno; exact hw (funext hno)
  set d : ℝ := (C₁.w s : ℝ) - C₂.w s with hd
  have hd0 : d ≠ 0 := by
    rw [hd, sub_ne_zero]; exact_mod_cast hs
  -- the log-ratio of the branches stays bounded near `0`
  set B : ℝ := |Real.log (y₂ s / y₁ s)| + 1 with hB
  have hratio : ∀ᶠ t in 𝓝 (0 : ℝ), |Real.log (ψ₂ t s / ψ₁ t s)| < B := by
    have hc : ContinuousAt (fun t => Real.log (ψ₂ t s / ψ₁ t s)) 0 := by
      have h1 : ContinuousAt (fun t => ψ₁ t s) 0 := (continuous_apply s).continuousAt.comp hψ₁c
      have h2 : ContinuousAt (fun t => ψ₂ t s) 0 := (continuous_apply s).continuousAt.comp hψ₂c
      have hp1 : ψ₁ 0 s ≠ 0 := by rw [hψ₁0]; exact (hy₁ s).ne'
      have hp2 : ψ₂ 0 s / ψ₁ 0 s ≠ 0 := by
        rw [hψ₁0, hψ₂0]; exact div_ne_zero (hy₂ s).ne' (hy₁ s).ne'
      exact (h2.div h1 hp1).log hp2
    have := hc.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with t ht
    rw [Real.dist_eq, hψ₁0, hψ₂0] at ht
    rw [hB]
    have := abs_sub_abs_le_abs_sub (Real.log (ψ₂ t s / ψ₁ t s)) (Real.log (y₂ s / y₁ s))
    linarith
  have hlog : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.log t < -(B / |d|) := by
    exact Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  -- choose `t`
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), C₁.G (t, ψ₁ t) = 0 ∧ C₂.G (t, ψ₂ t) = 0 ∧
      (∀ s, 0 < ψ₁ t s) ∧ (∀ s, 0 < ψ₂ t s) ∧ |Real.log (ψ₂ t s / ψ₁ t s)| < B ∧
      Real.log t < -(B / |d|) ∧ 0 < t := by
    have hn := fun {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℝ), p t) =>
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) h)
    filter_upwards [hn hψ₁, hn hψ₂, hn (hposev ψ₁ y₁ hy₁ hψ₁0 hψ₁c),
      hn (hposev ψ₂ y₂ hy₂ hψ₂0 hψ₂c), hn hratio, hlog, self_mem_nhdsWithin] with t a1 a2 a3 a4 a5 a6 a7
    exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
  obtain ⟨t, hG₁, hG₂, hp₁, hp₂, hrt, hlt, ht⟩ := hev.exists
  set x₁ := DecoratedCell.scalePoint C₁.w t (ψ₁ t)
  set x₂ := DecoratedCell.scalePoint C₂.w t (ψ₂ t)
  have hx₁ : x₁.Positive := fun s' => mul_pos (Real.exp_pos _) (hp₁ s')
  have hx₂ : x₂.Positive := fun s' => mul_pos (Real.exp_pos _) (hp₂ s')
  have hss₁ : N.IsMassActionSteadyState (DecoratedCell.deformedRates κ h t) x₁ := by
    intro s'
    show N.massActionVectorField _ x₁ s' = 0
    rw [C₁.field_scalePoint ht, hG₁, smul_zero]; rfl
  have hss₂ : N.IsMassActionSteadyState (DecoratedCell.deformedRates κ h t) x₂ := by
    intro s'
    show N.massActionVectorField _ x₂ s' = 0
    rw [C₂.field_scalePoint ht, hG₂, smul_zero]; rfl
  have hcomp : ∀ a b : Concentration S, N.StoichCompatible a b := fun a b => by
    show b - a ∈ N.stoichSubspace
    rw [hStop]; trivial
  refine ⟨DecoratedCell.deformedRates κ h t, x₁, x₁, x₂, ⟨hcomp _ _, hx₁⟩, ⟨hcomp _ _, hx₂⟩,
    hss₁, hss₂, ?_⟩
  -- distinctness at the coordinate `s`
  intro heq
  have h1 := congrFun heq s
  simp only [x₁, x₂, DecoratedCell.scalePoint] at h1
  have hq : Real.exp (d * Real.log t) = ψ₂ t s / ψ₁ t s := by
    rw [hd, sub_mul, Real.exp_sub, div_eq_div_iff (Real.exp_pos _).ne' (hp₁ s).ne']
    linear_combination h1
  have hlq : d * Real.log t = Real.log (ψ₂ t s / ψ₁ t s) := by
    rw [← hq, Real.log_exp]
  have hdpos : 0 < |d| := abs_pos.mpr hd0
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBd : 0 < B / |d| := div_pos hB0 hdpos
  have h2 : B < |d * Real.log t| := by
    rw [abs_mul]
    have hl : B / |d| < |Real.log t| := by
      rw [abs_of_neg (show Real.log t < 0 by linarith)]
      linarith
    calc B = |d| * (B / |d|) := by field_simp
      _ < |d| * |Real.log t| := mul_lt_mul_of_pos_left hl hdpos
  rw [hlq] at h2
  linarith



omit [DecidableEq S] in
/-- Branches with different normals separate for small `t > 0`. -/
theorem eventually_scalePoint_ne {w₁ w₂ : S → ℤ} (hw : w₁ ≠ w₂) {ψ₁ ψ₂ : ℝ → (S → ℝ)}
    {y₁ y₂ : Concentration S} (hy₁ : y₁.Positive) (hy₂ : y₂.Positive) (hψ₁0 : ψ₁ 0 = y₁)
    (hψ₂0 : ψ₂ 0 = y₂) (hψ₁c : ContinuousAt ψ₁ 0) (hψ₂c : ContinuousAt ψ₂ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), DecoratedCell.scalePoint w₁ t (ψ₁ t) ≠
      DecoratedCell.scalePoint w₂ t (ψ₂ t) := by
  obtain ⟨s, hs⟩ : ∃ s, w₁ s ≠ w₂ s := by
    by_contra hno; push Not at hno; exact hw (funext hno)
  set d : ℝ := (w₁ s : ℝ) - w₂ s with hd
  have hd0 : d ≠ 0 := by rw [hd, sub_ne_zero]; exact_mod_cast hs
  set B : ℝ := |Real.log (y₂ s / y₁ s)| + 1 with hB
  have h1 : ContinuousAt (fun t => ψ₁ t s) 0 := (continuous_apply s).continuousAt.comp hψ₁c
  have h2 : ContinuousAt (fun t => ψ₂ t s) 0 := (continuous_apply s).continuousAt.comp hψ₂c
  have hp1 : ψ₁ 0 s ≠ 0 := by rw [hψ₁0]; exact (hy₁ s).ne'
  have hratio : ∀ᶠ t in 𝓝 (0 : ℝ), |Real.log (ψ₂ t s / ψ₁ t s)| < B := by
    have hp2 : ψ₂ 0 s / ψ₁ 0 s ≠ 0 := by
      rw [hψ₁0, hψ₂0]; exact div_ne_zero (hy₂ s).ne' (hy₁ s).ne'
    have hc : ContinuousAt (fun t => Real.log (ψ₂ t s / ψ₁ t s)) 0 := (h2.div h1 hp1).log hp2
    have := hc.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with t ht
    rw [Real.dist_eq, hψ₁0, hψ₂0] at ht
    rw [hB]
    have := abs_sub_abs_le_abs_sub (Real.log (ψ₂ t s / ψ₁ t s)) (Real.log (y₂ s / y₁ s))
    linarith
  have hpos₁ : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < ψ₁ t s := by
    have : 0 < ψ₁ 0 s := by rw [hψ₁0]; exact hy₁ s
    exact h1.eventually (lt_mem_nhds this)
  have hdpos : 0 < |d| := abs_pos.mpr hd0
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBd : 0 < B / |d| := div_pos hB0 hdpos
  have hlog : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.log t < -(B / |d|) :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  filter_upwards [nhdsWithin_le_nhds hratio, nhdsWithin_le_nhds hpos₁, hlog] with t hrt hp hlt
  intro heq
  have hc := congrFun heq s
  simp only [DecoratedCell.scalePoint] at hc
  have hq : Real.exp (d * Real.log t) = ψ₂ t s / ψ₁ t s := by
    rw [hd, sub_mul, Real.exp_sub, div_eq_div_iff (Real.exp_pos _).ne' hp.ne']
    linear_combination hc
  have hlq : d * Real.log t = Real.log (ψ₂ t s / ψ₁ t s) := by rw [← hq, Real.log_exp]
  have hgt : B < |d * Real.log t| := by
    rw [abs_mul]
    have hl : B / |d| < |Real.log t| := by
      rw [abs_of_neg (show Real.log t < 0 by linarith)]; linarith
    calc B = |d| * (B / |d|) := by field_simp
      _ < |d| * |Real.log t| := mul_lt_mul_of_pos_left hl hdpos
  rw [hlq] at hgt
  linarith

/-- **Bihan–Dickenstein–Giaroli lower bound (full-rank version).** If `d` positively decorated
lower cells of the same height function `h` have pairwise different normals, then for small
`t > 0` the rates `κ̄_r t^{h(y_r)}` give `d` distinct positive steady states (all in the single
compatibility class `ℝ^S_{>0}`). -/
theorem steadyStates_of_decoratedCells {N : Network S} {κ : RateConstants N}
    {h : Complex S → ℕ} {d : ℕ} (C : Fin d → DecoratedCell N κ h)
    (hw : Function.Injective fun j => (C j).w) (hd : 0 < d) :
    ∃ (κ' : RateConstants N) (X : Fin d → Concentration S),
      (∀ j, (X j).Positive ∧ N.IsMassActionSteadyState κ' (X j)) ∧ Function.Injective X ∧
        N.stoichSubspace = ⊤ := by
  classical
  choose y hy ψ hψ0 hψc hψ using fun j => (C j).exists_branch
  have hStop : N.stoichSubspace = ⊤ := by
    rw [eq_top_iff, ← (C ⟨0, hd⟩).span, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  have hposev : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < ψ j t s := by
    intro j
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ψ j t s) 0 :=
      (continuous_apply s).continuousAt.comp (hψc j)
    have : 0 < ψ j 0 s := by rw [hψ0 j]; exact hy j s
    exact hcs.eventually (lt_mem_nhds this)
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p : Fin d × Fin d, p.1 ≠ p.2 →
      DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
        DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t) := by
    rw [eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · exact (eventually_scalePoint_ne (fun e => hp (hw e)) (hy p.1) (hy p.2) (hψ0 p.1)
        (hψ0 p.2) (hψc p.1) (hψc p.2)).mono fun t ht _ => ht
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ j, (C j).G (t, ψ j t) = 0) ∧
      (∀ j, ∀ s, 0 < ψ j t s) ∧ (∀ p : Fin d × Fin d, p.1 ≠ p.2 →
        DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
          DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t)) ∧ 0 < t := by
    filter_upwards [nhdsWithin_le_nhds (eventually_all.mpr hψ),
      nhdsWithin_le_nhds (eventually_all.mpr hposev), hne, self_mem_nhdsWithin]
      with t a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  obtain ⟨t, hG, hp, hX, ht⟩ := hall.exists
  refine ⟨DecoratedCell.deformedRates κ h t,
    fun j => DecoratedCell.scalePoint (C j).w t (ψ j t), fun j => ⟨fun s =>
      mul_pos (Real.exp_pos _) (hp j s), fun s => ?_⟩, fun j j' heq => ?_, hStop⟩
  · show N.massActionVectorField _ _ s = 0
    rw [(C j).field_scalePoint ht, hG j, smul_zero]; rfl
  · by_contra hjj
    exact hX (j, j') hjj heq

namespace DecoratedCell

variable {N : Network S} {κ : RateConstants N} {h : Complex S → ℕ}

/-- The diagonal scaling `y ↦ t^w y` as a continuous linear map. -/
noncomputable def scaleCLM (w : S → ℤ) (t : ℝ) : (S → ℝ) →L[ℝ] (S → ℝ) :=
  ContinuousLinearMap.pi fun s => Real.exp ((w s : ℝ) * Real.log t) • ContinuousLinearMap.proj s

omit [DecidableEq S] [Fintype S] in
theorem scaleCLM_apply (w : S → ℤ) (t : ℝ) (y : S → ℝ) :
    scaleCLM w t y = scalePoint w t y := by
  funext s; simp [scaleCLM, scalePoint]

/-- **The Jacobian along the deformation.** For `t > 0`,
`DF(t^w y) ∘ diag(t^w) = t^c D_y G(t, y)`. -/
theorem jacobian_scale (C : DecoratedCell N κ h) {t : ℝ} (ht : 0 < t) (y : S → ℝ) :
    N.massActionJacobianCLM (deformedRates κ h t) (scalePoint C.w t y) ∘L scaleCLM C.w t =
      Real.exp ((C.c : ℝ) * Real.log t) •
        (fderiv ℝ C.G (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) := by
  have hsc : (fun y : S → ℝ => scalePoint C.w t y) = scaleCLM C.w t := by
    funext y; exact (scaleCLM_apply _ _ _).symm
  have h1 : HasFDerivAt (fun y : S → ℝ =>
      N.massActionVectorField (deformedRates κ h t) (scalePoint C.w t y))
      (N.massActionJacobianCLM (deformedRates κ h t) (scalePoint C.w t y) ∘L scaleCLM C.w t) y := by
    have hJ := N.massActionVectorField_hasFDerivAt (deformedRates κ h t) (scalePoint C.w t y)
    have hL : HasFDerivAt (fun y : S → ℝ => scalePoint C.w t y) (scaleCLM C.w t) y := by
      rw [hsc]; exact (scaleCLM C.w t).hasFDerivAt
    exact hJ.comp y hL
  have hdiff : DifferentiableAt ℝ C.G (t, y) := (C.G_contDiff.differentiable (by simp)) _
  have h2 : HasFDerivAt (fun y : S → ℝ => Real.exp ((C.c : ℝ) * Real.log t) • C.G (t, y))
      (Real.exp ((C.c : ℝ) * Real.log t) •
        (fderiv ℝ C.G (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) y :=
    (hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).const_smul
      (Real.exp ((C.c : ℝ) * Real.log t))
  have heq : (fun y : S → ℝ =>
      N.massActionVectorField (deformedRates κ h t) (scalePoint C.w t y)) =
      fun y => Real.exp ((C.c : ℝ) * Real.log t) • C.G (t, y) := by
    funext y; exact C.field_scalePoint ht y
  rw [heq] at h1
  exact h1.unique h2

/-- **A nondegenerate branch.** As `exists_branch`, and moreover `D_y G(t, ψ t)` is invertible for
`t` near `0`. -/
theorem exists_branch_nondeg (C : DecoratedCell N κ h) :
    ∃ y : Concentration S, y.Positive ∧ ∃ ψ : ℝ → (S → ℝ), ψ 0 = y ∧ ContinuousAt ψ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), C.G (t, ψ t) = 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (fderiv ℝ C.G (t, ψ t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
  classical
  obtain ⟨y, hy, ρ, hρ, hsol⟩ := C.exists_simplex_solution
  have hG0 : C.G (0, y) = 0 := by
    rw [G_zero]
    have hfield : (cellNet N C.Δ).massActionVectorField (cellRates N κ C.Δ) y =
        ∑ r : (cellNet N C.Δ).R, (κ.k r.1 * (N.reaction r.1).source.massActionMonomial y) •
          N.reactionVector r.1 := by
      funext s
      rw [massActionVectorField_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hfield, cellNet_sum_group C (fun a => a.massActionMonomial y)]
    simp only [hsol, mul_smul, ← Finset.smul_sum, C.lam_ker, smul_zero]
  have hcd : ContDiffAt ℝ 1 C.G (0, y) := (C.G_contDiff.of_le (by simp)).contDiffAt
  set J := (cellNet N C.Δ).massActionJacobianCLM (cellRates N κ C.Δ) y with hJ
  have hpart : fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) = J := by
    have hdiff : DifferentiableAt ℝ C.G (0, y) := (C.G_contDiff.differentiable (by simp)) _
    have hcomp : HasFDerivAt (fun x => C.G (0, x))
        (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) y :=
      hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have heq : (fun x => C.G (0, x)) =
        (cellNet N C.Δ).massActionVectorField (cellRates N κ C.Δ) := by
      funext x; exact C.G_zero x
    rw [heq] at hcomp
    exact hcomp.unique ((cellNet N C.Δ).massActionVectorField_hasFDerivAt _ y)
  have hinj : Function.Injective (J : (S → ℝ) →ₗ[ℝ] (S → ℝ)) := by
    intro u v huv
    have h1 : J (u - v) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (C.jacobian_injective hy hρ hsol (u - v) h1)
  have hinv : (fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    rw [hpart]
    let e : (S → ℝ) ≃ₗ[ℝ] (S → ℝ) := LinearEquiv.ofInjectiveEndo (J : (S → ℝ) →ₗ[ℝ] (S → ℝ)) hinj
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext v; rfl
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψ0 : ψ 0 = y := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψc : ContinuousAt ψ 0 := (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt
  refine ⟨y, hy, ψ, hψ0, hψc, ?_, ?_⟩
  · filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with t ht
    rw [← hψdef] at ht
    rw [ht, hG0]
  · -- continuity of `t ↦ D_y G(t, ψ t)`
    have hfc : Continuous (fderiv ℝ C.G) := C.G_contDiff.continuous_fderiv (by simp)
    have hpath : ContinuousAt (fun t => ((t, ψ t) : ℝ × (S → ℝ))) 0 :=
      continuousAt_id.prodMk hψc
    set R := (ContinuousLinearMap.compL ℝ (S → ℝ) (ℝ × (S → ℝ)) (S → ℝ)).flip
      (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) with hR
    have hD : ContinuousAt (fun t => R (fderiv ℝ C.G (t, ψ t))) 0 :=
      R.continuous.continuousAt.comp (hfc.continuousAt.comp hpath)
    have hD0 : R (fderiv ℝ C.G (0, ψ 0)) =
        fderiv ℝ C.G (0, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) := by
      rw [hψ0]; rfl
    have hev := hD.eventually (hD0 ▸ hinv.eventually_nhds)
    filter_upwards [hev] with t ht
    exact ht

end DecoratedCell

/-- **Bihan–Dickenstein–Giaroli lower bound, nondegenerate (full-rank version).** Under the
hypotheses of `steadyStates_of_decoratedCells`, the `d` steady states can be taken nondegenerate
(injective Jacobian). -/
theorem nondegenerate_steadyStates_of_decoratedCells {N : Network S} {κ : RateConstants N}
    {h : Complex S → ℕ} {d : ℕ} (C : Fin d → DecoratedCell N κ h)
    (hw : Function.Injective fun j => (C j).w) (hd : 0 < d) :
    ∃ (κ' : RateConstants N) (X : Fin d → Concentration S),
      (∀ j, (X j).Positive ∧ N.IsMassActionSteadyState κ' (X j) ∧
        N.IsNondegenerateSteadyState κ' (X j)) ∧ Function.Injective X ∧
        N.stoichSubspace = ⊤ := by
  classical
  choose y hy ψ hψ0 hψc hψ hinvev using fun j => (C j).exists_branch_nondeg
  have hStop : N.stoichSubspace = ⊤ := by
    rw [eq_top_iff, ← (C ⟨0, hd⟩).span, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  have hposev : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < ψ j t s := by
    intro j
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ψ j t s) 0 :=
      (continuous_apply s).continuousAt.comp (hψc j)
    have : 0 < ψ j 0 s := by rw [hψ0 j]; exact hy j s
    exact hcs.eventually (lt_mem_nhds this)
  have hne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p : Fin d × Fin d, p.1 ≠ p.2 →
      DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
        DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t) := by
    rw [eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · exact (eventually_scalePoint_ne (fun e => hp (hw e)) (hy p.1) (hy p.2) (hψ0 p.1)
        (hψ0 p.2) (hψc p.1) (hψc p.2)).mono fun t ht _ => ht
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ j, (C j).G (t, ψ j t) = 0) ∧
      (∀ j, ∀ s, 0 < ψ j t s) ∧ (∀ p : Fin d × Fin d, p.1 ≠ p.2 →
        DecoratedCell.scalePoint (C p.1).w t (ψ p.1 t) ≠
          DecoratedCell.scalePoint (C p.2).w t (ψ p.2 t)) ∧
      (∀ j, (fderiv ℝ (C j).G (t, ψ j t) ∘L
        ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible) ∧ 0 < t := by
    filter_upwards [nhdsWithin_le_nhds (eventually_all.mpr hψ),
      nhdsWithin_le_nhds (eventually_all.mpr hposev), hne,
      nhdsWithin_le_nhds (eventually_all.mpr hinvev), self_mem_nhdsWithin]
      with t a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  obtain ⟨t, hG, hp, hX, hinv, ht⟩ := hall.exists
  refine ⟨DecoratedCell.deformedRates κ h t,
    fun j => DecoratedCell.scalePoint (C j).w t (ψ j t), fun j => ⟨fun s =>
      mul_pos (Real.exp_pos _) (hp j s), fun s => ?_, ?_⟩, fun j j' heq => ?_, hStop⟩
  · show N.massActionVectorField _ _ s = 0
    rw [(C j).field_scalePoint ht, hG j, smul_zero]; rfl
  · -- nondegeneracy
    intro u _ hu
    obtain ⟨e, he⟩ := hinv j
    have hscale := (C j).jacobian_scale ht (ψ j t)
    -- write `u = t^w v`
    set v : S → ℝ := fun s => Real.exp (-((C j).w s : ℝ) * Real.log t) * u s with hv
    have huv : DecoratedCell.scaleCLM (C j).w t v = u := by
      funext s
      simp only [DecoratedCell.scaleCLM_apply, DecoratedCell.scalePoint, hv, ← mul_assoc,
        ← Real.exp_add]
      rw [show ((C j).w s : ℝ) * Real.log t + -((C j).w s : ℝ) * Real.log t = 0 by ring,
        Real.exp_zero, one_mul]
    have h1 : (Real.exp (((C j).c : ℝ) * Real.log t) •
        (fderiv ℝ (C j).G (t, ψ j t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) v = 0 := by
      rw [← hscale, ContinuousLinearMap.comp_apply, huv]; exact hu
    rw [smul_apply, ← he] at h1
    have h2 : (e : (S → ℝ) →L[ℝ] (S → ℝ)) v = 0 :=
      (smul_eq_zero.mp h1).resolve_left (Real.exp_pos _).ne'
    have hv0 : v = 0 := by
      have := congrArg e.symm h2
      simpa using this
    rw [← huv, hv0, map_zero]
  · by_contra hjj
    exact hX (j, j') hjj heq

end Network

end CRNT
