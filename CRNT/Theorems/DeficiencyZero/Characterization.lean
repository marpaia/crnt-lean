import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Deficiency.DeficiencyZeroConsistency
import CRNT.Equilibria.SteadyStateFlux
import CRNT.Algebra.DeficiencyIdeal

/-!
# Structural characterizations of deficiency-zero CRNs

For a deficiency-zero network, the following conditions coincide:

* weak reversibility;
* consistency;
* existence of a positive mass-action steady state for some positive rate vector;
* existence of a positive mass-action steady state for every positive rate vector;
* existence of a positive complex-balanced state for every positive rate vector.

Moreover every mass-action steady state is automatically complex balanced at deficiency
zero.  Thus non-weakly-reversible deficiency-zero networks cannot possess positive
steady states for any choice of positive rate constants.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A complex-balanced state is a mass-action steady state. -/
theorem isMassActionSteadyState_of_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hcb : N.IsComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x := by
  have hk : N.kineticMap κ (N.complexMonomialVector x) = 0 := by
    funext c
    rw [N.kineticMap_complexMonomial_apply κ x c]
    exact sub_eq_zero.mpr (hcb c.1 c.2)
  unfold IsMassActionSteadyState IsSteadyState
  intro s
  rw [N.massActionVectorField_eq κ x, hk, map_zero]
  rfl

/-- At deficiency zero, every steady state is complex balanced. -/
theorem complexBalanced_of_massActionSteadyState_deficiencyZero
    (N : Network S) (κ : N.RateConstants) (hδ : N.DeficiencyZero)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x := by
  apply N.complexBalanced_of_steadyState_deficiencyZero_polynomial κ hδ
  funext s
  exact hss s

/-- Positive steady state existence at deficiency zero forces weak reversibility. -/
theorem weaklyReversible_of_deficiencyZero_of_positiveSteadyState
    (N : Network S) (hδ : N.DeficiencyZero)
    (h : ∃ κ : N.RateConstants, ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.WeaklyReversible := by
  exact N.weaklyReversible_of_deficiencyZero_of_consistent hδ
    (N.isConsistent_of_exists_positive_massActionSteadyState h)

/-- Under deficiency zero, weak reversibility is equivalent to positive steady-state
existence for at least one positive rate vector. -/
theorem deficiencyZero_weaklyReversible_iff_exists_positiveSteadyState
    (N : Network S) (hδ : N.DeficiencyZero) :
    N.WeaklyReversible ↔
      ∃ κ : N.RateConstants, ∃ x : Concentration S,
        x.Positive ∧ N.IsMassActionSteadyState κ x := by
  constructor
  · intro hwr
    let κ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
    obtain ⟨x, hx, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
    exact ⟨κ, x, hx, N.isMassActionSteadyState_of_complexBalanced κ hcb⟩
  · exact N.weaklyReversible_of_deficiencyZero_of_positiveSteadyState hδ

/-- Under deficiency zero, one positive steady-state realization is equivalent to positive
steady-state existence for every positive rate vector. -/
theorem deficiencyZero_exists_some_iff_every_positiveSteadyState
    (N : Network S) (hδ : N.DeficiencyZero) :
    (∃ κ : N.RateConstants, ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x) ↔
    (∀ κ : N.RateConstants, ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x) := by
  constructor
  · intro hsome κ
    have hwr := N.weaklyReversible_of_deficiencyZero_of_positiveSteadyState hδ hsome
    obtain ⟨x, hx, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
    exact ⟨x, hx, N.isMassActionSteadyState_of_complexBalanced κ hcb⟩
  · intro hall
    let κ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
    exact ⟨κ, hall κ⟩

/-- Full deficiency-zero equivalence: consistency iff positive steady states exist for
all positive rate constants. -/
theorem deficiencyZero_consistent_iff_every_rate_has_positiveSteadyState
    (N : Network S) (hδ : N.DeficiencyZero) :
    N.IsConsistent ↔
      ∀ κ : N.RateConstants, ∃ x : Concentration S,
        x.Positive ∧ N.IsMassActionSteadyState κ x := by
  rw [N.deficiencyZero_consistent_iff_weaklyReversible hδ]
  constructor
  · intro hwr κ
    obtain ⟨x, hx, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
    exact ⟨x, hx, N.isMassActionSteadyState_of_complexBalanced κ hcb⟩
  · intro hall
    have hsome : ∃ κ : N.RateConstants, ∃ x : Concentration S,
        x.Positive ∧ N.IsMassActionSteadyState κ x := by
      let κ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
      exact ⟨κ, hall κ⟩
    exact N.weaklyReversible_of_deficiencyZero_of_positiveSteadyState hδ hsome

/-- Non-weakly-reversible deficiency-zero networks have no positive mass-action steady
state for any positive rates. -/
theorem no_positiveSteadyState_of_deficiencyZero_not_weaklyReversible
    (N : Network S) (hδ : N.DeficiencyZero) (hnwr : ¬ N.WeaklyReversible) :
    ∀ κ : N.RateConstants, ¬ ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x := by
  intro κ h
  apply hnwr
  exact N.weaklyReversible_of_deficiencyZero_of_positiveSteadyState hδ ⟨κ, h⟩

end Network
end CRNT
