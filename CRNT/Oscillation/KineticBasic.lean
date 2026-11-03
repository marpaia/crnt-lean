import CRNT.Oscillation.Basic
import CRNT.Kinetics.General

/-!
# Oscillation under general admissible kinetics

The mass-action oscillation API in `Basic` intentionally quantifies only over positive mass-action
rate constants.  Recent structural oscillatory-core results are proved for broader parameter-rich
kinetic classes, so this file provides a separate semantics for an arbitrary admissible `Kinetics`.

This separation is important: a structural theorem proved for parameter-rich kinetics must not be
silently promoted to a mass-action theorem.  Mass action embeds into this layer, but not conversely.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A positive nonconstant exact periodic orbit for one admissible kinetics. -/
structure PositiveKineticPeriodicOrbit (N : Network S) (K : N.Kinetics) : Type where
  trajectory : PeriodicTrajectory K.vectorField
  positive : ∀ t s, 0 < trajectory.orbit t s

/-- Propositional fixed-kinetics oscillation predicate. -/
def HasPositiveKineticPeriodicOrbit (N : Network S) (K : N.Kinetics) : Prop :=
  Nonempty (N.PositiveKineticPeriodicOrbit K)

/-- Capacity for a positive periodic orbit under some admissible kinetics.

This is deliberately broader than mass-action `OscillatoryCapacity`.  A theorem for a
parameter-rich subclass can soundly conclude this proposition after constructing the corresponding
`Kinetics`, but the reverse implication is not claimed. -/
def KineticOscillatoryCapacity (N : Network S) : Prop :=
  ∃ K : N.Kinetics, N.HasPositiveKineticPeriodicOrbit K

/-- Structural exclusion over the full admissible-kinetics class.  This is strictly stronger than
`NeverPositivePeriodic`, which quantifies only over positive mass-action rate constants. -/
def NeverPositiveKineticPeriodic (N : Network S) : Prop :=
  ∀ K : N.Kinetics, ¬ N.HasPositiveKineticPeriodicOrbit K

/-- All-kinetics exclusion is exactly the negation of all-kinetics oscillatory capacity. -/
theorem neverPositiveKineticPeriodic_iff_not_kineticOscillatoryCapacity (N : Network S) :
    N.NeverPositiveKineticPeriodic ↔ ¬ N.KineticOscillatoryCapacity := by
  constructor
  · intro h hcap
    obtain ⟨K, hK⟩ := hcap
    exact h K hK
  · intro h K hK
    exact h ⟨K, hK⟩

/-- A positive mass-action periodic orbit is also a periodic orbit for the corresponding general
kinetics object. -/
noncomputable def PositivePeriodicOrbit.toKinetic {N : Network S} {κ : N.RateConstants}
    (P : N.PositivePeriodicOrbit κ) :
    N.PositiveKineticPeriodicOrbit (N.massActionKinetics κ) where
  trajectory := P.toPeriodicTrajectory
  positive := P.positive

/-- Mass-action oscillatory capacity embeds into admissible-kinetics oscillatory capacity. -/
theorem kineticOscillatoryCapacity_of_oscillatoryCapacity {N : Network S}
    (h : N.OscillatoryCapacity) : N.KineticOscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨N.massActionKinetics κ, ⟨P.toKinetic⟩⟩

/-- Exclusion for every admissible kinetics implies exclusion for every mass-action parameterization. -/
theorem neverPositivePeriodic_of_neverPositiveKineticPeriodic {N : Network S}
    (h : N.NeverPositiveKineticPeriodic) : N.NeverPositivePeriodic := by
  intro κ hκ
  obtain ⟨P⟩ := hκ
  exact h (N.massActionKinetics κ) ⟨P.toKinetic⟩

/-- Contrapositive form: mass-action capacity rules out an all-kinetics exclusion certificate. -/
theorem not_neverPositiveKineticPeriodic_of_oscillatoryCapacity {N : Network S}
    (h : N.OscillatoryCapacity) : ¬ N.NeverPositiveKineticPeriodic := by
  intro hnever
  have hma : N.NeverPositivePeriodic :=
    neverPositivePeriodic_of_neverPositiveKineticPeriodic hnever
  exact (N.neverPositivePeriodic_iff_not_oscillatoryCapacity.mp hma) h

end Network

end CRNT
