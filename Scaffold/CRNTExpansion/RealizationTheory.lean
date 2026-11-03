import CRNT.Translation.SourceCoefficientEquivalence
import CRNT.Translation.LinearConjugacy
import CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete

/-!
# Realization theory scaffold

The translation layer already has exact dynamical equivalence, source-coefficient certificates,
and positive diagonal linear conjugacy.  This file packages those relations in the form needed by
realization theory.

The key extra distinction is **stoichiometric realization**.  Equality of vector fields preserves
the steady-state set but need not, by itself, identify the two networks' stoichiometric
compatibility classes.  A realization intended to transfer deficiency-theory uniqueness therefore
carries equality of stoichiometric subspaces explicitly.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Existence of a dynamically equivalent realization satisfying a structural property `P`. -/
def HasDynamicallyEquivalentRealizationWith (N : Network S) (κ : N.RateConstants)
    (P : Network S -> Prop) : Prop :=
  ∃ R : MassActionRealization N κ, P R.network

/-- A dynamically equivalent weakly-reversible realization exists. -/
def HasWeaklyReversibleRealization (N : Network S) (κ : N.RateConstants) : Prop :=
  N.HasDynamicallyEquivalentRealizationWith κ (fun M => M.WeaklyReversible)

/-- A dynamically equivalent realization possessing a positive complex-balanced state exists. -/
def HasComplexBalancedRealization (N : Network S) (κ : N.RateConstants) : Prop :=
  ∃ R : MassActionRealization N κ, ∃ x : Concentration S,
    x.Positive ∧ R.network.IsComplexBalanced R.rates x

/-- Dynamical equivalence together with equality of stoichiometric subspaces.  This is the natural
package for transferring statements that are relative to compatibility classes. -/
structure StoichiometricMassActionRealization (N : Network S) (κN : N.RateConstants) where
  network : Network S
  rates : network.RateConstants
  equivalent : N.MassActionDynamicallyEquivalent network κN rates
  stoich_eq : N.stoichSubspace = network.stoichSubspace

/-- Existence of a stoichiometrically equivalent weakly-reversible deficiency-zero realization.
This is the realization-theoretic hypothesis strong enough to transfer deficiency-zero classwise
uniqueness back to the original vector field. -/
def HasStoichiometricWR0Realization (N : Network S) (κN : N.RateConstants) : Prop :=
  ∃ R : StoichiometricMassActionRealization N κN,
    R.network.WeaklyReversible ∧ R.network.DeficiencyZero

namespace StoichiometricMassActionRealization

variable {N : Network S} {κN : N.RateConstants}

/-- The original system is its own stoichiometric realization. -/
def self (N : Network S) (κN : N.RateConstants) :
    StoichiometricMassActionRealization N κN where
  network := N
  rates := κN
  equivalent := N.massActionDynamicallyEquivalent_refl κN
  stoich_eq := rfl

/-- A weakly-reversible deficiency-zero system trivially has a stoichiometric WR0
realization, namely itself.  This gives the realization certificate API a reflexive base case. -/
theorem hasStoichiometricWR0Realization_self
    (N : Network S) (κN : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) :
    N.HasStoichiometricWR0Realization κN := by
  exact ⟨StoichiometricMassActionRealization.self N κN, hwr, hδ⟩

/-- Forgetting the stoichiometric-subspace equality gives an ordinary dynamically equivalent
realization. -/
def toMassActionRealization (R : StoichiometricMassActionRealization N κN) :
    MassActionRealization N κN where
  network := R.network
  rates := R.rates
  equivalent := R.equivalent

/-- A stoichiometric realization satisfying a structural property is, in particular, a dynamically
equivalent realization satisfying that property. -/
theorem hasDynamicallyEquivalentRealizationWith
    (R : StoichiometricMassActionRealization N κN)
    {P : Network S -> Prop} (hP : P R.network) :
    N.HasDynamicallyEquivalentRealizationWith κN P := by
  exact ⟨R.toMassActionRealization, hP⟩

/-- A weakly-reversible stoichiometric realization witnesses the corresponding realization
predicate. -/
theorem hasWeaklyReversibleRealization
    (R : StoichiometricMassActionRealization N κN)
    (hwr : R.network.WeaklyReversible) : N.HasWeaklyReversibleRealization κN := by
  exact R.hasDynamicallyEquivalentRealizationWith hwr

/-- Stoichiometric realizations have the same steady states. -/
theorem steadyState_iff (R : StoichiometricMassActionRealization N κN)
    (x : Concentration S) :
    N.IsMassActionSteadyState κN x <->
      R.network.IsMassActionSteadyState R.rates x :=
  R.equivalent.steadyState_iff x

/-- Equality of stoichiometric subspaces identifies compatibility. -/
theorem stoichCompatible_iff (R : StoichiometricMassActionRealization N κN)
    (x y : Concentration S) :
    N.StoichCompatible x y <-> R.network.StoichCompatible x y := by
  unfold StoichCompatible
  rw [R.stoich_eq]

/-- Hence positive compatibility classes agree pointwise. -/
theorem positiveCompatibilityClass_iff
    (R : StoichiometricMassActionRealization N κN) (x0 x : Concentration S) :
    x ∈ N.positiveCompatibilityClass x0 <->
      x ∈ R.network.positiveCompatibilityClass x0 := by
  constructor
  · rintro ⟨hcomp, hpos⟩
    exact ⟨(R.stoichCompatible_iff x0 x).mp hcomp, hpos⟩
  · rintro ⟨hcomp, hpos⟩
    exact ⟨(R.stoichCompatible_iff x0 x).mpr hcomp, hpos⟩

/-- A weakly-reversible deficiency-zero stoichiometric realization turns every positive steady
state of the original system into a complex-balanced state of the realization. -/
theorem complexBalanced_of_wr0_of_positiveSteadyState
    (R : StoichiometricMassActionRealization N κN)
    (hwr : R.network.WeaklyReversible) (hδ : R.network.DeficiencyZero)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κN x) :
    R.network.IsComplexBalanced R.rates x := by
  have hssR : R.network.IsMassActionSteadyState R.rates x :=
    (R.steadyState_iff x).mp hss
  exact R.network.deficiencyZero_positiveSteadyState_isComplexBalanced_complete
    R.rates hwr hδ hx hssR

/-- If the original vector field has a positive steady state and admits a stoichiometrically
equivalent WR0 realization, that realization is a complex-balanced realization of the original
system. -/
theorem hasComplexBalancedRealization_of_wr0_of_exists_positiveSteadyState
    (R : StoichiometricMassActionRealization N κN)
    (hwr : R.network.WeaklyReversible) (hδ : R.network.DeficiencyZero)
    (hex : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κN x) :
    N.HasComplexBalancedRealization κN := by
  rcases hex with ⟨x, hx, hss⟩
  refine ⟨R.toMassActionRealization, x, hx, ?_⟩
  exact R.complexBalanced_of_wr0_of_positiveSteadyState hwr hδ hx hss

/-- A stoichiometrically equivalent WR0 realization transfers the full classwise uniqueness
conclusion back to the original mass-action system. -/
theorem existsUnique_steadyState_in_positiveClass_of_wr0
    (R : StoichiometricMassActionRealization N κN)
    (hwr : R.network.WeaklyReversible) (hδ : R.network.DeficiencyZero)
    {x0 : Concentration S} (hx0 : x0.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x0 ∧ N.IsMassActionSteadyState κN x := by
  obtain ⟨x, hx, huniq⟩ :=
    R.network.deficiencyZero_existsUnique_complexBalanced_in_positiveClass_complete
      R.rates hwr hδ hx0
  refine ⟨x, ?_, ?_⟩
  · refine ⟨(R.positiveCompatibilityClass_iff x0 x).mpr hx.1, ?_⟩
    exact (R.steadyState_iff x).mpr (hx.2.isMassActionSteadyState R.network R.rates)
  · intro y hy
    have hyClass : y ∈ R.network.positiveCompatibilityClass x0 :=
      (R.positiveCompatibilityClass_iff x0 y).mp hy.1
    have hySS : R.network.IsMassActionSteadyState R.rates y :=
      (R.steadyState_iff y).mp hy.2
    have hyCB : R.network.IsComplexBalanced R.rates y :=
      R.network.deficiencyZero_positiveSteadyState_isComplexBalanced_complete
        R.rates hwr hδ hyClass.2 hySS
    exact huniq y ⟨hyClass, hyCB⟩

end StoichiometricMassActionRealization

/-- A stoichiometric WR0 realization is a complete certificate of classwise positive steady-state
uniqueness for the original mass-action system. -/
theorem existsUnique_steadyState_in_positiveClass_of_hasStoichiometricWR0Realization
    (N : Network S) (κN : N.RateConstants)
    (hR : N.HasStoichiometricWR0Realization κN)
    {x0 : Concentration S} (hx0 : x0.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x0 ∧ N.IsMassActionSteadyState κN x := by
  rcases hR with ⟨R, hwr, hδ⟩
  exact R.existsUnique_steadyState_in_positiveClass_of_wr0 hwr hδ hx0

/-- A packaged positive-diagonal linearly conjugate realization, including the structural
stoichiometric conjugacy needed to transport compatibility classes. -/
structure LinearlyConjugateRealization (N : Network S) (κN : N.RateConstants) where
  network : Network S
  rates : network.RateConstants
  change : PositiveDiagonalChange S
  conjugate : N.MassActionLinearlyConjugate network κN rates change
  stoichConjugate : N.StoichiometricallyConjugate network change

namespace LinearlyConjugateRealization

variable {N : Network S} {κN : N.RateConstants}

/-- The coordinate change sends original steady states to realization steady states. -/
theorem map_steadyState (R : LinearlyConjugateRealization N κN)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κN x) :
    R.network.IsMassActionSteadyState R.rates (R.change.map x) :=
  R.conjugate.map_steadyState hx

/-- The coordinate change sends original compatibility classes into realization classes. -/
theorem map_compatible (R : LinearlyConjugateRealization N κN)
    {x y : Concentration S} (hxy : N.StoichCompatible x y) :
    R.network.StoichCompatible (R.change.map x) (R.change.map y) :=
  R.stoichConjugate.map_compatible hxy

end LinearlyConjugateRealization

end Network
end CRNT
