import CRNT.Theorems.DeficiencyZero.Characterization
import CRNT.Multistationarity.Capacity

/-!
# Positive multistationarity forces positive deficiency

The deficiency-zero theorem has an immediate global consequence that is useful as a
structural screening rule: a mass-action CRN of deficiency zero can never possess two
distinct positive steady states in one stoichiometric compatibility class.  If it is
weakly reversible there is exactly one; if it is not weakly reversible there is none.
Thus positive multistationarity implies strictly positive deficiency without any separate
weak-reversibility assumption.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Deficiency-zero networks have no positive multistationarity for fixed rates. -/
theorem no_positive_multistationarity_of_deficiencyZero
    (N : Network S) (hδ : N.DeficiencyZero) (κ : N.RateConstants) :
    ¬ ∃ x y : Concentration S,
      x.Positive ∧ y.Positive ∧ x ≠ y ∧
      N.StoichCompatible x y ∧
      N.IsMassActionSteadyState κ x ∧
      N.IsMassActionSteadyState κ y := by
  rintro ⟨x, y, hx, hy, hxy, hcomp, hssx, hssy⟩
  have hcbx := N.complexBalanced_of_massActionSteadyState_deficiencyZero κ hδ hssx
  have hcby := N.complexBalanced_of_massActionSteadyState_deficiencyZero κ hδ hssy
  -- complex-balanced equilibrium is unique in each positive class
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_deficiencyZero_of_positiveSteadyState hδ
      ⟨κ, x, hx, hssx⟩
  have hxclass : x ∈ N.positiveCompatibilityClass x :=
    ⟨StoichCompatible.refl N x, hx⟩
  have hyclass : y ∈ N.positiveCompatibilityClass x := ⟨hcomp, hy⟩
  have hEq : x = y :=
    N.isComplexBalanced_unique_in_positiveClass hwr κ hxclass hyclass hcbx hcby
  exact hxy hEq

/-- Any positive multistationary realization has positive structural deficiency. -/
theorem deficiency_pos_of_positive_multistationarity
    (N : Network S) (κ : N.RateConstants)
    (hms : ∃ x y : Concentration S,
      x.Positive ∧ y.Positive ∧ x ≠ y ∧
      N.StoichCompatible x y ∧
      N.IsMassActionSteadyState κ x ∧
      N.IsMassActionSteadyState κ y) :
    0 < N.deficiency := by
  by_contra hnot
  have hz : N.deficiency = 0 := Nat.eq_zero_of_not_pos hnot
  have hδ : N.DeficiencyZero := (N.deficiencyZero_iff_deficiency_eq_zero).2 hz
  exact N.no_positive_multistationarity_of_deficiencyZero hδ κ hms

/-- Structural capacity for positive multistationarity requires nonzero deficiency. -/
theorem deficiency_ne_zero_of_multistationarityCapacity
    (N : Network S)
    (hcap : HasMultistationarityCapacity N) : N.deficiency ≠ 0 := by
  intro hz
  rcases hcap with ⟨κ, x₀, x, y, hx, hy, hssx, hssy, hxy⟩
  have hcomp : N.StoichCompatible x y := hx.1.symm.trans hy.1
  have hpos : 0 < N.deficiency :=
    N.deficiency_pos_of_positive_multistationarity κ
      ⟨x, y, hx.2, hy.2, hxy, hcomp, hssx, hssy⟩
  exact (Nat.ne_of_gt hpos) hz

end Network
end CRNT
