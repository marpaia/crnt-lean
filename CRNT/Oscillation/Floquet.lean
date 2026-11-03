import CRNT.Oscillation.Basic
import CRNT.Oscillation.OrbitTube
import CRNT.Oscillation.MatrixCriteria
import CRNT.Kinetics.MassActionJacobian

/-!
# Floquet data, nondegenerate periodic orbits, and linear orbital stability

This module supplies the finite-dimensional Floquet vocabulary needed by oscillation-inheritance
results.  It deliberately separates the *linear variational data* from the deep theorem that turns
Floquet multipliers into nonlinear orbital stability.

For a positive periodic mass-action orbit `P`, a `MassActionFloquetData` is a fundamental-matrix
solution of

`Z' = J(P(t)) Z,   Z(0) = I`,

where `J` is the mass-action Jacobian.  Its monodromy matrix is `Z(T)` at the period `T` of `P`.
The associated characteristic polynomial defines the Floquet multipliers.

A periodic orbit is called **nondegenerate** when the autonomous multiplier `1` is a simple root of
the monodromy characteristic polynomial.  It is called **linearly stable** when it is nondegenerate
and every other Floquet multiplier lies strictly inside the unit disk.  These are the notions used
in the CRN inheritance literature.

The module does not assume a Floquet theorem as an axiom.  The nonlinear implication from the
multiplier condition to orbital asymptotic stability remains isolated as
`FloquetOrbitalStabilityTarget`.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Jacobian sampled along a positive periodic mass-action orbit is periodic with the same
period. -/
theorem massActionJacobian_along_periodicOrbit_periodic
    {N : Network S} {κ : N.RateConstants} (P : N.PositivePeriodicOrbit κ) :
    Function.Periodic (fun t => N.massActionJacobian κ (P.orbit t)) P.period := by
  intro t
  dsimp only
  rw [P.periodic t]

/-- A fundamental-matrix solution of the linear variational equation along a positive periodic
mass-action orbit.  The matrix equation is stated entrywise so it uses only the existing scalar
`HasDerivAt` API. -/
structure MassActionFloquetData (N : Network S) (κ : N.RateConstants)
    (P : N.PositivePeriodicOrbit κ) where
  /-- Fundamental matrix `Z(t)`. -/
  fundamental : ℝ → Matrix S S ℝ
  /-- Standard normalization `Z(0)=I`. -/
  initial : fundamental 0 = 1
  /-- Variational equation `Z' = J(P(t)) Z`. -/
  solves : ∀ t i j,
    HasDerivAt (fun τ => fundamental τ i j)
      ((N.massActionJacobian κ (P.orbit t) * fundamental t) i j) t

namespace MassActionFloquetData

variable {N : Network S} {κ : N.RateConstants} {P : N.PositivePeriodicOrbit κ}

/-- Monodromy matrix after one period. -/
def monodromy (F : N.MassActionFloquetData κ P) : Matrix S S ℝ :=
  F.fundamental P.period

/-- Complexified characteristic polynomial of the monodromy matrix.

`noncomputable` because `Matrix.charpoly` is. -/
noncomputable def floquetPolynomial (F : N.MassActionFloquetData κ P) : Polynomial ℂ :=
  ((F.monodromy).map (algebraMap ℝ ℂ)).charpoly

/-- `μ` is a Floquet multiplier when it is a root of the monodromy characteristic polynomial. -/
def HasMultiplier (F : N.MassActionFloquetData κ P) (μ : ℂ) : Prop :=
  μ ∈ F.floquetPolynomial.roots

/-- The autonomous multiplier `1` is a simple root.  The derivative criterion is equivalent to
algebraic multiplicity one for a polynomial root and avoids introducing a separate multiplicity
API. -/
def OneIsSimpleMultiplier (F : N.MassActionFloquetData κ P) : Prop :=
  F.floquetPolynomial.eval 1 = 0 ∧ F.floquetPolynomial.derivative.eval 1 ≠ 0

/-- Floquet nondegeneracy of a periodic orbit: the trivial autonomous multiplier `1` is simple. -/
def Nondegenerate (F : N.MassActionFloquetData κ P) : Prop :=
  F.OneIsSimpleMultiplier

/-- Linear stability of a periodic orbit: the trivial multiplier is simple and every other
multiplier lies strictly inside the unit circle. -/
def LinearlyStable (F : N.MassActionFloquetData κ P) : Prop :=
  F.Nondegenerate ∧
    ∀ μ : ℂ, F.HasMultiplier μ → μ ≠ 1 → ‖μ‖ < 1

/-- Linear stability includes Floquet nondegeneracy. -/
theorem LinearlyStable.nondegenerate {F : N.MassActionFloquetData κ P}
    (h : F.LinearlyStable) : F.Nondegenerate :=
  h.1

end MassActionFloquetData

/-- A positive periodic orbit equipped with a fundamental variational matrix and a proof of
Floquet nondegeneracy. -/
structure NondegeneratePositivePeriodicOrbit (N : Network S) (κ : N.RateConstants) : Type where
  orbit : N.PositivePeriodicOrbit κ
  floquet : N.MassActionFloquetData κ orbit
  nondegenerate : floquet.Nondegenerate

/-- A positive periodic orbit whose nontrivial Floquet multipliers all lie strictly inside the unit
circle. -/
structure LinearlyStablePositivePeriodicOrbit (N : Network S) (κ : N.RateConstants) : Type where
  orbit : N.PositivePeriodicOrbit κ
  floquet : N.MassActionFloquetData κ orbit
  stable : floquet.LinearlyStable

namespace LinearlyStablePositivePeriodicOrbit

variable {N : Network S} {κ : N.RateConstants}

/-- Forget linear stability but retain the nondegenerate periodic orbit. -/
def toNondegenerate (P : N.LinearlyStablePositivePeriodicOrbit κ) :
    N.NondegeneratePositivePeriodicOrbit κ where
  orbit := P.orbit
  floquet := P.floquet
  nondegenerate := P.stable.nondegenerate

end LinearlyStablePositivePeriodicOrbit

/-- Some positive mass-action parameterization admits a nondegenerate positive periodic orbit. -/
def NondegenerateOscillatoryCapacity (N : Network S) : Prop :=
  ∃ κ : N.RateConstants, Nonempty (N.NondegeneratePositivePeriodicOrbit κ)

/-- Some positive mass-action parameterization admits a linearly stable positive periodic orbit. -/
def LinearlyStableOscillatoryCapacity (N : Network S) : Prop :=
  ∃ κ : N.RateConstants, Nonempty (N.LinearlyStablePositivePeriodicOrbit κ)

/-- Nondegenerate oscillation implies ordinary oscillatory capacity. -/
theorem oscillatoryCapacity_of_nondegenerateOscillatoryCapacity {N : Network S}
    (h : N.NondegenerateOscillatoryCapacity) : N.OscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨κ, ⟨P.orbit⟩⟩

/-- Linearly stable oscillation implies nondegenerate oscillation. -/
theorem nondegenerateOscillatoryCapacity_of_linearlyStable {N : Network S}
    (h : N.LinearlyStableOscillatoryCapacity) : N.NondegenerateOscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨κ, ⟨P.toNondegenerate⟩⟩

/-- Hence linearly stable oscillation implies ordinary oscillatory capacity. -/
theorem oscillatoryCapacity_of_linearlyStableOscillatoryCapacity {N : Network S}
    (h : N.LinearlyStableOscillatoryCapacity) : N.OscillatoryCapacity :=
  oscillatoryCapacity_of_nondegenerateOscillatoryCapacity
    (nondegenerateOscillatoryCapacity_of_linearlyStable h)

/-- Exact remaining nonlinear Floquet theorem interface: a linearly stable positive periodic orbit
is orbitally asymptotically stable, i.e. it attracts every solution started in some tube of
positive radius around it.  This is kept as a `Prop`, not an axiom; the linear Floquet objects
above are fully available independently of it.

**The tube radius is the whole content.** An earlier form of this statement read

```
∃ basin, Set.range P.orbit.orbit ⊆ basin ∧ P.orbit.GloballyAttractsSolutions basin
```

which is provable with no Floquet theory at all: take `basin := Set.range P.orbit.orbit`.  For `x`
on the orbit, forward uniqueness of mass-action solutions makes any `γ` with `γ 0 = x` equal to a
phase shift of the orbit, so `dist (γ t) (P.orbit phase) = 0 < ε` on choosing that phase.  A basin
that is merely a superset of the orbit therefore says nothing; it has to be a *neighbourhood*.  See
`docs/math-review.md`. -/
def FloquetOrbitalStabilityTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T)
    (κ : N.RateConstants) (P : N.LinearlyStablePositivePeriodicOrbit κ),
      ∃ δ : ℝ, 0 < δ ∧ P.orbit.GloballyAttractsSolutions (P.orbit.orbitTube δ)

/-- Consume a future proof of the Floquet orbital-stability theorem for one certified orbit. -/
theorem LinearlyStablePositivePeriodicOrbit.hasLocallyAttractingCycle
    {N : Network S} {κ : N.RateConstants}
    (hFloquet : FloquetOrbitalStabilityTarget)
    (P : N.LinearlyStablePositivePeriodicOrbit κ) :
    ∃ δ : ℝ, 0 < δ ∧ P.orbit.GloballyAttractsSolutions (P.orbit.orbitTube δ) :=
  hFloquet N κ P

/-- The weak form, recovered from the strong one: a tube of positive radius contains the orbit.
Kept so that any consumer written against the old signature still type-checks, but note that this
weak statement is trivially true on its own and carries no information. -/
theorem LinearlyStablePositivePeriodicOrbit.hasAttractingBasin
    {N : Network S} {κ : N.RateConstants}
    (hFloquet : FloquetOrbitalStabilityTarget)
    (P : N.LinearlyStablePositivePeriodicOrbit κ) :
    ∃ basin : Set (Concentration S),
      Set.range P.orbit.orbit ⊆ basin ∧ P.orbit.GloballyAttractsSolutions basin := by
  obtain ⟨δ, hδ, hattr⟩ := hFloquet N κ P
  exact ⟨P.orbit.orbitTube δ, P.orbit.range_subset_orbitTube hδ, hattr⟩

end Network

end CRNT
