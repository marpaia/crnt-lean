import CRNT.Kinetics.MassAction
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Interval.Set.Infinite

/-!
# Identifiability of rate constants (Craciun–Pantea 2008)

The mass-action vector field of a network is
`f_κ(x) = ∑_r κ_r x^{y_r} (y'_r - y_r)`, a polynomial in `x` whose monomials are indexed by
the source complexes. Distinct monomials are linearly independent as functions on the
positive orthant, so `f_κ = f_κ'` on the positive orthant if and only if, for every source
complex `y`, `∑_{r : source r = y} (κ_r - κ'_r) (y'_r - y) = 0`.

Hence (Craciun–Pantea, *Identifiability of chemical reaction networks*, J. Math. Chem. 44
(2008), Theorem 3.2) the rate constants are determined by the vector field if and only if,
for every complex `y`, the reaction vectors of the reactions with source `y` are linearly
independent. Reactions are indexed (parallel reactions allowed); a parallel pair or a
self-loop makes the family dependent and indeed destroys identifiability.

Main results:
* `CRNT.Complex.sum_massActionMonomial_eq_zero`: linear independence of distinct
  monomials on the positive orthant.
* `CRNT.Network.massActionVectorField_eqOn_positive_iff`: the vector fields agree on the
  positive orthant iff the source-wise weighted sums of reaction vectors agree.
* `CRNT.Network.rateConstants_identifiable_iff`: the Craciun–Pantea identifiability
  criterion.
-/

namespace CRNT

open scoped BigOperators

namespace Complex

variable {S : Type} [Fintype S]

/-- A complex as a finitely supported exponent vector. -/
noncomputable def toFinsupp (y : Complex S) : S →₀ ℕ := Finsupp.equivFunOnFinite.symm y

theorem toFinsupp_injective : Function.Injective (toFinsupp (S := S)) :=
  Finsupp.equivFunOnFinite.symm.injective

theorem eval_monomial_toFinsupp (y : Complex S) (x : Concentration S) (a : ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial (toFinsupp y) a) = a * y.massActionMonomial x := by
  rw [MvPolynomial.eval_monomial, massActionMonomial, Finsupp.prod_fintype]
  · rfl
  · intro i; simp

/-- **Linear independence of monomials on the positive orthant.** If a finite linear
combination `∑ i, a i * x ^ (src i)` vanishes at every positive concentration, then for every
complex `y` the coefficients attached to the occurrences of `y` sum to zero. -/
theorem sum_massActionMonomial_eq_zero {ι : Type*} [Fintype ι] (src : ι → Complex S)
    (a : ι → ℝ)
    (h : ∀ x : Concentration S, x.Positive → ∑ i, a i * (src i).massActionMonomial x = 0)
    (y : Complex S) :
    ∑ i ∈ Finset.univ.filter (fun i => src i = y), a i = 0 := by
  classical
  set P : MvPolynomial S ℝ := ∑ i, MvPolynomial.monomial (toFinsupp (src i)) (a i) with hP
  have hP0 : P = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0) ?_
    intro x hx
    have hpos : Concentration.Positive x := fun s => hx s (Set.mem_univ s)
    simp only [hP, map_sum, eval_monomial_toFinsupp, map_zero]
    exact h x hpos
  have hcoeff := congrArg (fun p : MvPolynomial S ℝ => p.coeff (toFinsupp y)) hP0
  simp only [hP, MvPolynomial.coeff_sum] at hcoeff
  rw [show (0 : MvPolynomial S ℝ).coeff (toFinsupp y) = 0 by simp] at hcoeff
  simp only [MvPolynomial.coeff_monomial] at hcoeff
  rw [Finset.sum_filter]
  refine Eq.trans ?_ hcoeff
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : src i = y
  · simp [hi]
  · have : toFinsupp (src i) ≠ toFinsupp y := fun e => hi (toFinsupp_injective e)
    simp [hi, this]

end Complex

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The source-wise weighted reaction-vector sum `∑_{r : source r = y} c_r (y'_r - y)`. -/
noncomputable def sourceWeightedSum (N : Network S) (c : N.R → ℝ) (y : Complex S) : S → ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => (N.reaction r).source = y), c r • N.reactionVector r

theorem massActionVectorField_apply_eq_sum_monomial (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (s : S) :
    N.massActionVectorField κ x s =
      ∑ r, (κ.k r * N.reactionVector r s) * (N.reaction r).source.massActionMonomial x := by
  rw [massActionVectorField_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [massActionRate]; ring

/-- **Vector fields agree iff source-wise sums agree.** Two rate-constant vectors induce the
same mass-action vector field on the positive orthant if and only if, for every complex `y`,
the rate-weighted sums of the reaction vectors out of `y` coincide. -/
theorem massActionVectorField_eqOn_positive_iff (N : Network S) (κ κ' : RateConstants N) :
    (∀ x : Concentration S, x.Positive →
        N.massActionVectorField κ x = N.massActionVectorField κ' x) ↔
      ∀ y : Complex S, N.sourceWeightedSum κ.k y = N.sourceWeightedSum κ'.k y := by
  constructor
  · intro h y
    funext s
    have hz := Complex.sum_massActionMonomial_eq_zero (fun r => (N.reaction r).source)
      (fun r => (κ.k r - κ'.k r) * N.reactionVector r s) (fun x hx => by
        have := congrFun (h x hx) s
        rw [massActionVectorField_apply_eq_sum_monomial, massActionVectorField_apply_eq_sum_monomial] at this
        rw [← sub_eq_zero.mpr this, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring) y
    simp only [sourceWeightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← hz]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  · intro h x _
    funext s
    rw [massActionVectorField_apply_eq_sum_monomial, massActionVectorField_apply_eq_sum_monomial]
    -- regroup both sums by source complex
    have key : ∀ c : N.R → ℝ,
        ∑ r, (c r * N.reactionVector r s) * (N.reaction r).source.massActionMonomial x =
          ∑ y ∈ Finset.univ.image (fun r => (N.reaction r).source),
            N.sourceWeightedSum c y s * y.massActionMonomial x := by
      intro c
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun r => (N.reaction r).source)
        (t := Finset.univ.image (fun r => (N.reaction r).source))
        (fun r _ => Finset.mem_image_of_mem _ (Finset.mem_univ r))]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [sourceWeightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [(Finset.mem_filter.mp hr).2]
    rw [key κ.k, key κ'.k]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [h y]

theorem sourceWeightedSum_eq_subtype (N : Network S) (c : N.R → ℝ) (y : Complex S) :
    N.sourceWeightedSum c y =
      ∑ r : {r : N.R // (N.reaction r).source = y}, c r • N.reactionVector r := by
  simp only [sourceWeightedSum]
  exact Finset.sum_subtype _ (fun r => by simp) (fun r => c r • N.reactionVector r)

/-- **Identifiability of rate constants (Craciun–Pantea 2008).** The positive rate constants
of a mass-action network are uniquely determined by its vector field on the positive orthant
if and only if, for every complex `y`, the reaction vectors of the reactions with source `y`
are linearly independent. -/
theorem rateConstants_identifiable_iff (N : Network S) :
    (∀ κ κ' : RateConstants N,
        (∀ x : Concentration S, x.Positive →
          N.massActionVectorField κ x = N.massActionVectorField κ' x) → κ.k = κ'.k) ↔
      ∀ y : Complex S,
        LinearIndependent ℝ
          (fun r : {r : N.R // (N.reaction r).source = y} => N.reactionVector r) := by
  classical
  constructor
  · intro hid y
    rw [Fintype.linearIndependent_iff]
    intro g hg r
    -- perturb the constant rate vector `2` in the direction `g / M`
    set M : ℝ := ∑ r, |g r| + 1 with hM
    have hMpos : 0 < M := by
      have : 0 ≤ ∑ r, |g r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have hgle : ∀ r, |g r| ≤ M - 1 := fun r => by
      have := Finset.single_le_sum (f := fun r => |g r|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ r)
      simp only [hM]; linarith
    let c : N.R → ℝ := fun r' =>
      if h : (N.reaction r').source = y then g ⟨r', h⟩ / M else 0
    have hc : ∀ r', |c r'| < 1 := by
      intro r'
      simp only [c]
      split_ifs with h
      · rw [abs_div, abs_of_pos hMpos, div_lt_one hMpos]
        linarith [hgle ⟨r', h⟩]
      · simp
    have hcy : ∀ r' : {r' : N.R // (N.reaction r').source = y}, c r' = g r' / M := by
      intro r'
      simp only [c, r'.2, dite_true]
    let κ : RateConstants N := ⟨fun _ => 2, fun _ => by norm_num⟩
    let κ' : RateConstants N := ⟨fun r' => 2 + c r', fun r' => by
      have := (abs_lt.mp (hc r')).1; linarith⟩
    have heq := hid κ κ' ((massActionVectorField_eqOn_positive_iff N κ κ').mpr (by
      intro z
      by_cases hz : z = y
      · subst hz
        rw [sourceWeightedSum_eq_subtype, sourceWeightedSum_eq_subtype]
        have : ∀ r' : {r' : N.R // (N.reaction r').source = z},
            κ'.k r' • N.reactionVector r' =
              κ.k r' • N.reactionVector r' + (1 / M) • (g r' • N.reactionVector r') := by
          intro r'
          show (2 + c r') • N.reactionVector r' = (2 : ℝ) • N.reactionVector r' + _
          rw [hcy, add_smul, smul_smul]
          congr 2
          ring
        simp_rw [this]
        rw [Finset.sum_add_distrib]
        have h0 : ∑ x : {r' : N.R // (N.reaction r').source = z},
            (1 / M) • (g x • N.reactionVector x) = 0 := by
          rw [← Finset.smul_sum, hg, smul_zero]
        rw [h0, add_zero]
      · simp only [sourceWeightedSum]
        refine Finset.sum_congr rfl fun r' hr' => ?_
        have hr'' := (Finset.mem_filter.mp hr').2
        have hne : ¬ (N.reaction r').source = y := fun e => hz (hr''.symm.trans e)
        show (2 : ℝ) • N.reactionVector r' = (2 + c r') • N.reactionVector r'
        simp [c, hne]))
    have := congrFun heq r.1
    change (2 : ℝ) = 2 + c r.1 at this
    have hgr : g r / M = 0 := by rw [← hcy r]; linarith
    rcases div_eq_zero_iff.mp hgr with h0 | h0
    · exact h0
    · exact absurd h0 hMpos.ne'
  · intro hli κ κ' hf
    have hsum := (massActionVectorField_eqOn_positive_iff N κ κ').mp hf
    funext r
    have hy := hsum (N.reaction r).source
    rw [sourceWeightedSum_eq_subtype, sourceWeightedSum_eq_subtype, ← sub_eq_zero,
      ← Finset.sum_sub_distrib] at hy
    simp_rw [← sub_smul] at hy
    have := (Fintype.linearIndependent_iff.mp (hli _)) _ hy ⟨r, rfl⟩
    simp only at this
    linarith

end Network

end CRNT
