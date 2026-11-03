import CRNT.Dynamics.MassActionField
import CRNT.Equilibria.CompatibilityClass
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Periodic trajectories and oscillatory capacity

This module provides the common vocabulary used by the oscillation layer.  The central distinction is
between a periodic trajectory of a fixed vector field, a positive periodic orbit of a fixed
mass-action parameterization, and *oscillatory capacity* of a reaction network (existence for some
positive rate constants).

The definitions deliberately do not identify a finite simulation with an oscillation.  A periodic
orbit is an exact ODE solution with a strictly positive period and an explicit nonconstancy witness.
For CRNs the orbit is additionally required to remain in the open positive orthant.

`GloballyAttracts` records the strongest target used by the global-oscillation program: every state
in a chosen basin eventually approaches the periodic orbit up to phase.  It is a definition, not a
claim that arbitrary CRNs admit such an orbit.

Depends on: `CRNT.Dynamics.MassActionField`.
-/

namespace CRNT

-- `ℝ≥0` is scoped notation for `NNReal`; without this open it parses as the proposition
-- `ℝ ≥ 0`, which is how this file failed to elaborate (`failed to synthesize LE Type`).
-- Every other module in the repository that uses `ℝ≥0` opens it the same way.
open scoped NNReal

/-- An exact nonconstant periodic solution of an autonomous vector field `field`.

The derivative is stated in the ambient normed vector space.  No stability claim is included: a
periodic trajectory may be stable, unstable, or neutrally stable. -/
structure PeriodicTrajectory {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) where
  /-- The trajectory. -/
  orbit : ℝ → E
  /-- A positive period. -/
  period : ℝ
  /-- The period is genuinely forward in time. -/
  period_pos : 0 < period
  /-- The trajectory solves the ODE exactly. -/
  solution : ∀ t, HasDerivAt orbit (field (orbit t)) t
  /-- The trajectory closes after `period`. -/
  periodic : Function.Periodic orbit period
  /-- The orbit is not an equilibrium trajectory. -/
  nonconstant : ∃ t, orbit t ≠ orbit 0


/-- The periodic orbit reparameterized to the unit interval:
`normalizedLoop s = orbit (s * period)`.  Used by the planar Jordan-curve machinery, which
needs a loop on `[0,1]`.  (It was referenced by `PlanarJordanBoundaryCurrent` and
`PlanarJordanSeparation` but defined nowhere; the intended body is pinned down by
`normalizedLoop_hasDeriv`.) -/
noncomputable def PeriodicTrajectory.normalizedLoop {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {field : E → E} (P : PeriodicTrajectory field) (s : ℝ) : E :=
  P.orbit (s * P.period)

/-- The orbit of a periodic trajectory is continuous (it is differentiable everywhere). -/
theorem PeriodicTrajectory.continuous_orbit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {field : E → E} (P : PeriodicTrajectory field) :
    Continuous P.orbit :=
  continuous_iff_continuousAt.2 fun t => (P.solution t).continuousAt
namespace PeriodicTrajectory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E}

/-- Transport a periodic trajectory across an equality of autonomous vector fields.
Only the field index changes; the orbit, period, and dynamical witness are unchanged. -/
noncomputable def congrField {field' : E → E} (P : PeriodicTrajectory field)
    (h : field = field') : PeriodicTrajectory field' := by
  subst field'
  exact P

@[simp] theorem congrField_orbit {field' : E → E} (P : PeriodicTrajectory field)
    (h : field = field') : (P.congrField h).orbit = P.orbit := by
  subst field'
  rfl

@[simp] theorem congrField_period {field' : E → E} (P : PeriodicTrajectory field)
    (h : field = field') : (P.congrField h).period = P.period := by
  subst field'
  rfl

/-- The geometric image of a periodic trajectory, forgetting its phase parameterization. -/
def orbitSet (P : PeriodicTrajectory field) : Set E := Set.range P.orbit

/-- The seed point belongs to the orbit set. -/
theorem zero_mem_orbitSet (P : PeriodicTrajectory field) : P.orbit 0 ∈ P.orbitSet :=
  ⟨0, rfl⟩

/-- A periodic trajectory returns to its seed after one period. -/
theorem closes (P : PeriodicTrajectory field) : P.orbit P.period = P.orbit 0 := by
  have h := P.periodic 0
  simpa using h

/-- A global-attraction predicate for a periodic orbit, modulo phase.

`flow t x` is intentionally kept abstract.  Every state in `basin` must eventually lie within every
positive tolerance of *some phase* of the periodic orbit.  This is the natural target for a globally
attracting limit cycle and avoids choosing a phase synchronization convention. -/
def GloballyAttracts (P : PeriodicTrajectory field)
    (flow : ℝ≥0 → E → E) (basin : Set E) : Prop :=
  ∀ x ∈ basin, ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ≥0, ∀ t : ℝ≥0, T ≤ t → ∃ phase : ℝ, dist (flow t x) (P.orbit phase) < ε

end PeriodicTrajectory

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A nonconstant periodic mass-action solution that remains in the positive orthant. -/
structure PositivePeriodicOrbit (N : Network S) (κ : N.RateConstants) where
  /-- Concentration trajectory. -/
  orbit : ℝ → Concentration S
  /-- Positive period. -/
  period : ℝ
  /-- The period is strictly positive. -/
  period_pos : 0 < period
  /-- Every point of the orbit is a positive concentration. -/
  positive : ∀ t, (orbit t).Positive
  /-- Componentwise mass-action ODE solution. -/
  solution : ∀ t s,
    HasDerivAt (fun τ => orbit τ s) (N.massActionVectorField κ (orbit t) s) t
  /-- Exact periodicity. -/
  periodic : Function.Periodic orbit period
  /-- The periodic solution is not an equilibrium. -/
  nonconstant : ∃ t, orbit t ≠ orbit 0

namespace PositivePeriodicOrbit

variable {N : Network S} {κ : N.RateConstants}

/-- Forget positivity and package a positive CRN orbit as an ambient periodic trajectory. -/
noncomputable def toPeriodicTrajectory (P : N.PositivePeriodicOrbit κ) :
    PeriodicTrajectory (N.massActionVectorField κ) where
  orbit := P.orbit
  period := P.period
  period_pos := P.period_pos
  solution := fun t => hasDerivAt_pi.mpr (fun s => P.solution t s)
  periodic := P.periodic
  nonconstant := P.nonconstant

/-- The orbit closes after one period. -/
theorem closes (P : N.PositivePeriodicOrbit κ) : P.orbit P.period = P.orbit 0 := by
  have h := P.periodic 0
  simpa using h

/-- A trajectory-level notion of global attraction to a positive periodic orbit.

Every forward mass-action solution starting in `basin` must eventually approach the geometric cycle
to arbitrary accuracy, with phase left free.  Stating the property over all exact solutions avoids
assuming a globally defined flow or uniqueness theorem that the generic CRN layer does not yet
provide.  This is the precise fixed-parameter target for a globally attracting limit cycle. -/
def GloballyAttractsSolutions (P : N.PositivePeriodicOrbit κ)
    (basin : Set (Concentration S)) : Prop :=
  ∀ x ∈ basin, ∀ γ : ℝ → Concentration S,
    γ 0 = x →
    (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
        ∃ phase : ℝ, dist (γ t) (P.orbit phase) < ε

end PositivePeriodicOrbit

/-- A fixed mass-action parameterization admits a positive nonconstant periodic orbit. -/
def HasPositivePeriodicOrbit (N : Network S) (κ : N.RateConstants) : Prop :=
  Nonempty (N.PositivePeriodicOrbit κ)

/-- A positive periodic orbit that attracts every positive exact solution in its own
stoichiometric compatibility class.  This is the class-global limit-cycle object: the reference
class is anchored at the cycle itself, so no arbitrary external basin can make the claim vacuous. -/
structure GlobalLimitCycleOnClass (N : Network S) (κ : N.RateConstants) : Type where
  orbit : N.PositivePeriodicOrbit κ
  attracts : orbit.GloballyAttractsSolutions
    (N.positiveCompatibilityClass (orbit.orbit 0))

/-- A fixed mass-action parameterization admits a class-global attracting positive limit cycle. -/
def HasGlobalLimitCycleOnClass (N : Network S) (κ : N.RateConstants) : Prop :=
  Nonempty (N.GlobalLimitCycleOnClass κ)

/-- A class-global limit cycle is in particular a positive periodic orbit. -/
theorem HasGlobalLimitCycleOnClass.hasPositivePeriodicOrbit
    {N : Network S} {κ : N.RateConstants} (h : N.HasGlobalLimitCycleOnClass κ) :
    N.HasPositivePeriodicOrbit κ := by
  obtain ⟨G⟩ := h
  exact ⟨G.orbit⟩


/-- A fixed mass-action parameterization has a positive periodic orbit that globally attracts all
exact forward solutions starting in `basin`, up to phase along the cycle. -/
def HasGloballyAttractingPositivePeriodicOrbit (N : Network S) (κ : N.RateConstants)
    (basin : Set (Concentration S)) : Prop :=
  ∃ P : N.PositivePeriodicOrbit κ, P.GloballyAttractsSolutions basin

/-- A globally attracting positive periodic orbit is, in particular, a positive periodic orbit. -/
theorem HasGloballyAttractingPositivePeriodicOrbit.hasPositivePeriodicOrbit
    {N : Network S} {κ : N.RateConstants} {basin : Set (Concentration S)}
    (h : N.HasGloballyAttractingPositivePeriodicOrbit κ basin) :
    N.HasPositivePeriodicOrbit κ := by
  obtain ⟨P, _⟩ := h
  exact ⟨P⟩

/-- **Oscillatory capacity.** Some choice of positive rate constants admits a positive nonconstant
periodic mass-action orbit.  This is existential in parameters; it does not mean every
parameterization oscillates. -/
def OscillatoryCapacity (N : Network S) : Prop :=
  ∃ κ : N.RateConstants, N.HasPositivePeriodicOrbit κ

/-- **Global oscillatory capacity.** Some positive mass-action parameterization admits a periodic
orbit attracting every positive exact solution in the orbit's stoichiometric compatibility class.
This is strictly stronger than mere oscillatory capacity at the level of definitions. -/
def GlobalOscillatoryCapacity (N : Network S) : Prop :=
  ∃ κ : N.RateConstants, N.HasGlobalLimitCycleOnClass κ

/-- Global oscillatory capacity implies ordinary oscillatory capacity. -/
theorem oscillatoryCapacity_of_globalOscillatoryCapacity {N : Network S}
    (h : N.GlobalOscillatoryCapacity) : N.OscillatoryCapacity := by
  obtain ⟨κ, hκ⟩ := h
  exact ⟨κ, hκ.hasPositivePeriodicOrbit⟩

/-- A fixed-parameter globally attracting positive cycle witnesses structural oscillatory capacity. -/
theorem oscillatoryCapacity_of_globallyAttractingPositivePeriodicOrbit
    {N : Network S} {κ : N.RateConstants} {basin : Set (Concentration S)}
    (h : N.HasGloballyAttractingPositivePeriodicOrbit κ basin) : N.OscillatoryCapacity :=
  ⟨κ, h.hasPositivePeriodicOrbit⟩

/-- **Structural non-oscillation.** No choice of positive rate constants admits a positive
nonconstant periodic mass-action orbit. -/
def NeverPositivePeriodic (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, ¬ N.HasPositivePeriodicOrbit κ

/-- Structural non-oscillation is exactly negation of oscillatory capacity. -/
theorem neverPositivePeriodic_iff_not_oscillatoryCapacity (N : Network S) :
    N.NeverPositivePeriodic ↔ ¬ N.OscillatoryCapacity := by
  constructor
  · intro h hcap
    obtain ⟨κ, hκ⟩ := hcap
    exact h κ hκ
  · intro h κ hκ
    exact h ⟨κ, hκ⟩

/-- Structural exclusion of every positive periodic orbit also excludes class-global attracting
limit cycles. -/
theorem not_globalOscillatoryCapacity_of_neverPositivePeriodic {N : Network S}
    (hnever : N.NeverPositivePeriodic) : ¬ N.GlobalOscillatoryCapacity := by
  intro hglobal
  exact (N.neverPositivePeriodic_iff_not_oscillatoryCapacity.mp hnever)
    (oscillatoryCapacity_of_globalOscillatoryCapacity hglobal)

end Network

end CRNT
