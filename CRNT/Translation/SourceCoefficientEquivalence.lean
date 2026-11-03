import CRNT.Translation.DynamicalEquivalence
import CRNT.Basic.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Source-coefficient certificates for dynamical equivalence

A mass-action vector field can be grouped by source complex:

`f(x) = Σ_y x^y b_y`,  where
`b_y = Σ_{r : source(r)=y} κ_r (y'_r-y_r)`.

Therefore equality of the coefficient vector `b_y` at every source complex is a finite,
structural certificate for dynamical equivalence between completely different CRN
realizations.  No realization-search algorithm is included here.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Coefficient of the source monomial associated with complex `y`. -/
def sourceCoefficient (N : Network S) (κ : N.RateConstants) (y : Complex S) : S → ℝ :=
  fun s => ∑ r : N.R, if (N.reaction r).source = y then
    κ.k r * N.reactionVector r s else 0

/-- Source complexes actually used by the network. -/
def sourceComplexes (N : Network S) : Finset (Complex S) :=
  Finset.univ.image fun r : N.R => (N.reaction r).source

/-- A source coefficient vanishes away from the finite source-complex set. -/
theorem sourceCoefficient_eq_zero_of_not_mem (N : Network S) (κ : N.RateConstants)
    {y : Complex S} (hy : y ∉ N.sourceComplexes) : N.sourceCoefficient κ y = 0 := by
  funext s
  simp only [sourceCoefficient]
  apply Finset.sum_eq_zero
  intro r _
  have hne : (N.reaction r).source ≠ y := by
    intro h
    apply hy
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, h⟩
  simp [hne]

/-- Regroup the mass-action vector field by source complex. -/
theorem massActionVectorField_eq_sum_sourceCoefficient (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) :
    N.massActionVectorField κ x =
      ∑ y ∈ N.sourceComplexes, y.massActionMonomial x • N.sourceCoefficient κ y := by
  classical
  funext s
  rw [N.massActionVectorField_apply]
  simp only [massActionRate]
  have hsum_apply (t : Finset (Complex S)) (f : Complex S → S → ℝ) :
      (∑ y ∈ t, f y) s = ∑ y ∈ t, f y s := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih => simp [ha, ih]
  rw [hsum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, sourceCoefficient]
  have hcoeff : ∀ y : Complex S,
      (∑ r : N.R, if (N.reaction r).source = y then
          κ.k r * N.reactionVector r s else 0) =
        ∑ r ∈ Finset.univ with (N.reaction r).source = y,
          κ.k r * N.reactionVector r s := by
    intro y
    simpa using (Finset.sum_filter
      (s := Finset.univ) (fun r : N.R => (N.reaction r).source = y)
      (fun r => κ.k r * N.reactionVector r s)).symm
  have hfiber : ∀ y ∈ N.sourceComplexes,
      y.massActionMonomial x *
        (∑ r : N.R, if (N.reaction r).source = y then
          κ.k r * N.reactionVector r s else 0) =
      ∑ r ∈ Finset.univ with (N.reaction r).source = y,
        κ.k r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s := by
    intro y hy
    rw [hcoeff y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrsrc : (N.reaction r).source = y := (Finset.mem_filter.mp hr).2
    rw [hrsrc]
    ring
  symm
  calc
    (∑ y ∈ N.sourceComplexes, y.massActionMonomial x *
      (∑ r : N.R, if (N.reaction r).source = y then
        κ.k r * N.reactionVector r s else 0)) =
      ∑ y ∈ N.sourceComplexes,
        ∑ r ∈ Finset.univ with (N.reaction r).source = y,
          κ.k r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hfiber y hy
    _ = ∑ r : N.R,
        κ.k r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := N.sourceComplexes)
        (g := fun r : N.R => (N.reaction r).source)
        (fun r _ => Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
        (fun r => κ.k r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s)

/-- Equality of all source-monomial coefficient vectors. -/
def SourceCoefficientEquivalent (N M : Network S)
    (κN : N.RateConstants) (κM : M.RateConstants) : Prop :=
  ∀ y : Complex S, N.sourceCoefficient κN y = M.sourceCoefficient κM y

@[refl] theorem sourceCoefficientEquivalent_refl (N : Network S) (κ : N.RateConstants) :
    N.SourceCoefficientEquivalent N κ κ := fun _ => rfl

@[symm] theorem SourceCoefficientEquivalent.symm {N M : Network S}
    {κN : N.RateConstants} {κM : M.RateConstants}
    (h : N.SourceCoefficientEquivalent M κN κM) :
    M.SourceCoefficientEquivalent N κM κN :=
  fun y => (h y).symm

@[trans] theorem SourceCoefficientEquivalent.trans {N M L : Network S}
    {κN : N.RateConstants} {κM : M.RateConstants} {κL : L.RateConstants}
    (hNM : N.SourceCoefficientEquivalent M κN κM)
    (hML : M.SourceCoefficientEquivalent L κM κL) :
    N.SourceCoefficientEquivalent L κN κL :=
  fun y => (hNM y).trans (hML y)

/-- **Source-coefficient equality implies dynamical equivalence.** -/
theorem massActionDynamicallyEquivalent_of_sourceCoefficientEquivalent
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    (h : N.SourceCoefficientEquivalent M κN κM) :
    N.MassActionDynamicallyEquivalent M κN κM := by
  intro x
  rw [N.massActionVectorField_eq_sum_sourceCoefficient,
    M.massActionVectorField_eq_sum_sourceCoefficient]
  have hN :
      (∑ y ∈ N.sourceComplexes, y.massActionMonomial x • N.sourceCoefficient κN y) =
      ∑ y ∈ N.sourceComplexes ∪ M.sourceComplexes,
        y.massActionMonomial x • N.sourceCoefficient κN y := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro y hyu hyn
    have hz := N.sourceCoefficient_eq_zero_of_not_mem κN hyn
    rw [hz]
    funext s
    simp
  have hM :
      (∑ y ∈ M.sourceComplexes, y.massActionMonomial x • M.sourceCoefficient κM y) =
      ∑ y ∈ N.sourceComplexes ∪ M.sourceComplexes,
        y.massActionMonomial x • M.sourceCoefficient κM y := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro y hyu hym
    have hz := M.sourceCoefficient_eq_zero_of_not_mem κM hym
    rw [hz]
    funext s
    simp
  rw [hN, hM]
  apply Finset.sum_congr rfl
  intro y hy
  rw [h y]

/-- Source-coefficient equivalence therefore preserves the steady-state set. -/
theorem steadyState_iff_of_sourceCoefficientEquivalent
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    (h : N.SourceCoefficientEquivalent M κN κM) (x : Concentration S) :
    N.IsMassActionSteadyState κN x ↔ M.IsMassActionSteadyState κM x :=
  (massActionDynamicallyEquivalent_of_sourceCoefficientEquivalent h).steadyState_iff x

/-- A finite certificate only needs to check the union of the two source-complex sets. -/
theorem sourceCoefficientEquivalent_iff_on_union (N M : Network S)
    (κN : N.RateConstants) (κM : M.RateConstants) :
    N.SourceCoefficientEquivalent M κN κM ↔
      ∀ y ∈ N.sourceComplexes ∪ M.sourceComplexes,
        N.sourceCoefficient κN y = M.sourceCoefficient κM y := by
  constructor
  · intro h y _; exact h y
  · intro h y
    by_cases hy : y ∈ N.sourceComplexes ∪ M.sourceComplexes
    · exact h y hy
    · have hyN : y ∉ N.sourceComplexes := fun hN => hy (Finset.mem_union_left _ hN)
      have hyM : y ∉ M.sourceComplexes := fun hM => hy (Finset.mem_union_right _ hM)
      rw [N.sourceCoefficient_eq_zero_of_not_mem κN hyN,
        M.sourceCoefficient_eq_zero_of_not_mem κM hyM]

end Network

end CRNT
