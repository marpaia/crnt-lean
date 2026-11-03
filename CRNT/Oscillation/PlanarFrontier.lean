import CRNT.Oscillation.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Planar global-oscillation interfaces

For stoichiometric classes of dimension two, Poincare--Bendixson and Bendixson--Dulac are the natural
global tools.  Mathlib/this repository do not yet contain the required Jordan-curve/Green-theorem
stack needed for a complete proof, so this module does two useful things without introducing axioms or
`sorry`:

* fixes precise certificate-shaped hypotheses for a compact equilibrium-free trapping region;
* fixes a concrete coordinate definition of planar divergence and the data of a Dulac function.

These definitions make the remaining analytic theorem small and auditable instead of leaving the
frontier as prose.  No theorem in this file pretends that the missing Poincare--Bendixson or
Bendixson--Dulac implication is already proved.
-/

namespace CRNT

/-- The standard two-dimensional real phase space.

This is `EuclideanSpace ℝ (Fin 2)` rather than the bare pi type `Fin 2 → ℝ`: the transversal
section machinery in `Dynamics.TransversalCrossingTime` is stated over an
`InnerProductSpace ℝ E`, and the pi type carries the sup norm, which is not induced by any
inner product.  `EuclideanSpace ℝ (Fin 2)` unfolds to the same underlying function type, so
componentwise definitions still typecheck. -/
abbrev Phase2 := EuclideanSpace ℝ (Fin 2)

namespace Planar

/-- A componentwise classical solution of a planar autonomous ODE. -/
def IsSolution (field : Phase2 → Phase2) (γ : ℝ → Phase2) : Prop :=
  ∀ t i, HasDerivAt (fun τ => γ τ i) (field (γ t) i) t

/-- Concrete data for the global Poincare--Bendixson route.

The structure carries an actual forward trajectory rather than merely a forward-invariant set.  This
avoids a vacuous certificate when existence of ODE solutions has not yet been established.  A future
Poincare--Bendixson theorem can consume this record together with the regularity of `field`. -/
structure TrappedOrbit (field : Phase2 → Phase2) where
  region : Set Phase2
  compact : IsCompact region
  orbit : ℝ → Phase2
  solution : IsSolution field orbit
  seed_mem : orbit 0 ∈ region
  trapped : ∀ t, 0 ≤ t → orbit t ∈ region
  equilibriumFree : ∀ x ∈ region, field x ≠ 0

/-- Replace coordinate `i` of a planar point by the scalar `a`. -/
def setCoord (x : Phase2) (i : Fin 2) (a : ℝ) : Phase2 :=
  WithLp.toLp 2 (Function.update x.ofLp i a)

/-- Coordinate partialDeriv derivative of a scalar function on `Phase2`, using the classical real
`deriv`.  The regularity hypotheses needed to reason about this quantity belong in theorems using it. -/
noncomputable def partialDeriv (g : Phase2 → ℝ) (i : Fin 2) (x : Phase2) : ℝ :=
  deriv (fun a => g (setCoord x i a)) (x i)

/-- Classical divergence of a planar vector field in coordinates. -/
noncomputable def divergence (field : Phase2 → Phase2) (x : Phase2) : ℝ :=
  partialDeriv (fun y => field y 0) 0 x + partialDeriv (fun y => field y 1) 1 x

/-- A real function has one strict sign on a region. -/
def StrictOneSignOn (g : Phase2 → ℝ) (region : Set Phase2) : Prop :=
  (∀ x ∈ region, 0 < g x) ∨ (∀ x ∈ region, g x < 0)

/-- The data consumed by the Bendixson--Dulac exclusion theorem: a region, a scalar Dulac function,
and a proof that the divergence of the scaled field has one strict sign there.

Simply connectedness and the regularity assumptions needed for Green's theorem are intentionally not
encoded as ad-hoc substitutes; they belong in the eventual theorem once the corresponding Mathlib
infrastructure is available. -/
structure DulacData (field : Phase2 → Phase2) where
  region : Set Phase2
  dulac : Phase2 → ℝ
  oneSign : StrictOneSignOn (divergence (fun x => dulac x • field x)) region


/-- Fully packaged hypotheses for the Poincare--Bendixson route.  The deep theorem itself remains the
single explicit dependency `PoincareBendixsonTarget`; callers do not need to repeatedly restate its
regularity assumptions. -/
structure PoincareBendixsonData (field : Phase2 → Phase2) extends TrappedOrbit field where
  smooth : ContDiff ℝ 1 field

/-- Fully packaged hypotheses for the Bendixson--Dulac exclusion route on a convex open region.
Convexity is stronger than simple connectedness but is already available in Mathlib and is sufficient
for the intended certificate pipeline. -/
structure BendixsonDulacData (field : Phase2 → Phase2) extends DulacData field where
  open_region : IsOpen region
  convex_region : Convex ℝ region
  smooth_field : ContDiffOn ℝ 1 field region
  smooth_dulac : ContDiffOn ℝ 1 dulac region

/-- The exact missing global theorem interface.  A proof of this proposition would turn a bounded
forward orbit of a sufficiently smooth planar field whose trapping region contains no equilibrium
into a periodic trajectory.  Keeping it as a named `Prop` lets downstream design work state the
dependency without adding an axiom. -/
def PoincareBendixsonTarget : Prop :=
  ∀ (field : Phase2 → Phase2), ContDiff ℝ 1 field → TrappedOrbit field →
    Nonempty (PeriodicTrajectory field)

/-- Exact frontier for a Bendixson--Dulac exclusion theorem.  The simply-connectedness and regularity
hypotheses are parameters of the proposition rather than silently assumed by `DulacData`. -/
def BendixsonDulacTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : DulacData field),
    IsOpen D.region → Convex ℝ D.region →
    ContDiffOn ℝ 1 field D.region → ContDiffOn ℝ 1 D.dulac D.region →
    ∀ P : PeriodicTrajectory field, Set.range P.orbit ⊆ D.region → False



/-- Once the global Poincare--Bendixson frontier is closed, packaged trapping data becomes an exact
periodic-trajectory certificate by direct application. -/
theorem periodicTrajectory_of_poincareBendixsonTarget
    (hPB : PoincareBendixsonTarget) {field : Phase2 → Phase2}
    (D : PoincareBendixsonData field) : Nonempty (PeriodicTrajectory field) :=
  hPB field D.smooth D.toTrappedOrbit

/-- Once the Bendixson--Dulac frontier is closed, packaged Dulac data excludes every exact periodic
trajectory whose geometric orbit stays inside the certified region. -/
theorem noPeriodicTrajectoryInRegion_of_bendixsonDulacTarget
    (hBD : BendixsonDulacTarget) {field : Phase2 → Phase2}
    (D : BendixsonDulacData field) (P : PeriodicTrajectory field)
    (hinside : Set.range P.orbit ⊆ D.region) : False :=
  hBD field D.toDulacData D.open_region D.convex_region D.smooth_field D.smooth_dulac P hinside


end Planar

end CRNT
