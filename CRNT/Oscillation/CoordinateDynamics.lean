import CRNT.Oscillation.Basic
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Kinetics.Concentration

/-!
# Stoichiometric-coordinate dynamics

The CRN library already defines the reduced mass-action field

`G(y) = stoichProj (F(affineChart x₀ y))`

on the `stoichRank`-dimensional compatibility-class chart.  This module supplies the dynamical bridge
needed by the oscillation layer: an exact solution of the reduced ODE lifts through `affineChart` to
an exact solution of the full mass-action ODE, and an exact nonconstant periodic reduced solution
lifts to a positive CRN periodic orbit whenever its chart image stays in the positive orthant.

This is the missing algebraic/differential link between the existing reduced-Jacobian machinery and
future rank-two Poincare--Bendixson certificates.  No global planar theorem is assumed here.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The full mass-action velocity is recovered exactly by lifting the reduced velocity through the
stoichiometric chart. -/
theorem stoichChart_reducedField (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChart (N.reducedField κ x₀ y) =
      N.massActionVectorField κ (N.affineChart x₀ y) := by
  have hmem : N.massActionVectorField κ (N.affineChart x₀ y) ∈ N.stoichSubspace := by
    have h := (N.massActionKinetics κ).vectorField_mem_stoichSubspace (N.affineChart x₀ y)
    simpa [N.massActionKinetics_vectorField κ] using h
  simpa [Network.reducedField] using N.stoichChart_stoichProj hmem

/-- **Reduced solutions lift to full CRN solutions.**

The affine chart has derivative `stoichChart`; composing it with a reduced exact solution therefore
produces derivative `stoichChart (reducedField ...)`, which is the full mass-action velocity by
`stoichChart_reducedField`. -/
theorem reducedSolution_lifts (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : ℝ → (Fin N.stoichRank → ℝ))
    (hy : ∀ t, HasDerivAt y (N.reducedField κ x₀ (y t)) t) :
    ∀ t, HasDerivAt (fun τ => N.affineChart x₀ (y τ))
      (N.massActionVectorField κ (N.affineChart x₀ (y t))) t := by
  intro t
  have hcomp := (N.affineChart_hasFDerivAt x₀ (y t)).comp_hasDerivAt t (hy t)
  refine hcomp.congr_deriv ?_
  exact N.stoichChart_reducedField κ x₀ (y t)

/-- The positive part of the affine stoichiometric chart. -/
def positiveChartRegion (N : Network S) (x₀ : Concentration S) :
    Set (Fin N.stoichRank → ℝ) :=
  {y | Concentration.Positive (N.affineChart x₀ y)}

@[simp] theorem mem_positiveChartRegion_iff (N : Network S) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    y ∈ N.positiveChartRegion x₀ ↔ Concentration.Positive (N.affineChart x₀ y) :=
  Iff.rfl

/-- **A positive periodic reduced orbit lifts to a positive periodic mass-action orbit.**

This is the exact consumer needed after a future planar theorem has produced a periodic orbit of the
rank-two reduced field inside a trapping region known to lie in `positiveChartRegion`. -/
noncomputable def positivePeriodicOrbitOfReducedTrajectory
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.reducedField κ x₀))
    (hpos : ∀ t, Concentration.Positive (N.affineChart x₀ (P.orbit t))) :
    N.PositivePeriodicOrbit κ where
  orbit := fun t => N.affineChart x₀ (P.orbit t)
  period := P.period
  period_pos := P.period_pos
  positive := hpos
  solution := by
    intro t s
    exact hasDerivAt_pi.mp (N.reducedSolution_lifts κ x₀ P.orbit P.solution t) s
  periodic := by
    intro t
    exact congrArg (N.affineChart x₀) (P.periodic t)
  nonconstant := by
    obtain ⟨t, ht⟩ := P.nonconstant
    refine ⟨t, ?_⟩
    intro h
    exact ht (N.affineChart_injective x₀ h)

/-- Set-containment form of the preceding lift: it is enough to know that the reduced orbit lies in
`positiveChartRegion`. -/
noncomputable def positivePeriodicOrbitOfReducedTrajectoryInPositiveRegion
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.reducedField κ x₀))
    (hinside : Set.range P.orbit ⊆ N.positiveChartRegion x₀) :
    N.PositivePeriodicOrbit κ :=
  N.positivePeriodicOrbitOfReducedTrajectory κ x₀ P (fun t => hinside ⟨t, rfl⟩)

/-- A periodic reduced orbit inside the positive chart region is already a fixed-parameter
oscillation witness. -/
theorem hasPositivePeriodicOrbit_of_reducedTrajectory
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.reducedField κ x₀))
    (hinside : Set.range P.orbit ⊆ N.positiveChartRegion x₀) :
    N.HasPositivePeriodicOrbit κ :=
  ⟨N.positivePeriodicOrbitOfReducedTrajectoryInPositiveRegion κ x₀ P hinside⟩

end Network

end CRNT
