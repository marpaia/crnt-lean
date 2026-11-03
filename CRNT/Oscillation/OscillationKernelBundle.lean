import CRNT.Oscillation.PlanarEndToEnd
import CRNT.Oscillation.PlanarFlowRegularity
import CRNT.Oscillation.PlanarJordanTopology
import CRNT.Oscillation.PlanarJordanBoundaryCurrent
import CRNT.Oscillation.GlobalHopfIndexTheorem
import CRNT.Oscillation.VassenaEndToEnd
import CRNT.Oscillation.VassenaPrincipal
import CRNT.Oscillation.ParameterRichGlobalHopf
import CRNT.Oscillation.OscillatoryCoreEndToEnd
import CRNT.Oscillation.FloquetOrbitalStability
import CRNT.Oscillation.FloquetPersistenceGeneral
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.DiagonalScaling
import CRNT.Oscillation.FisherFullerScaling
import CRNT.Oscillation.StableCodimOneDHopf
import CRNT.Oscillation.DHopfOpenness

/-!
# Closed theorem-kernel bundle for global CRN oscillation

This file assembles the oscillation routes from explicit theorem targets. The planar topology,
Jordan-grid boundary current, global Hopf, reduced principal-block realization, nonlinear D-Hopf,
Recipe-0, and Floquet stability results remain caller-supplied mathematical obligations. Keeping
them in the bundle makes the dependency boundary visible to downstream CRN code.
-/

namespace CRNT

/-- Full-matrix Vassena/Fiedler theorem bundle. -/
structure VassenaKernelBundle : Prop where
  pMinusScaling : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0}
  fisherFullerScaling : Matrix.FisherFullerStabilizingScalingTarget.{0}
  analyticGlobalHopfIndex : AnalyticGlobalHopfIndexTarget
  principalRealization : Network.VassenaPrincipalFluxCriteriaRealizationTarget

namespace VassenaKernelBundle

theorem fluxCriteriaRealization (K : VassenaKernelBundle) :
    Network.VassenaFluxCriteriaRealizationTarget :=
  Network.vassenaFluxCriteriaRealization_of_fiedler
    K.pMinusScaling K.fisherFullerScaling
    (fiedlerAnalyticGlobalHopf_of_index K.analyticGlobalHopfIndex)

end VassenaKernelBundle

/-- Parameter-rich structural route. -/
structure ParameterRichCoreKernelBundle : Prop where
  pMinusScaling : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0}
  fisherFullerScaling : Matrix.FisherFullerStabilizingScalingTarget.{0}
  rootClusterContinuity : Polynomial.ZeroBorderRootClusterContinuityTarget
  matrixOpenness : Matrix.StrongDHopfPerturbationTarget
  nonlinearDHopf : Network.ParameterRichDHopfContinuationTarget

namespace ParameterRichCoreKernelBundle

theorem childSelectionPerturbation (K : ParameterRichCoreKernelBundle) :
    Network.ChildSelectionDHopfPerturbationTarget :=
  Network.childSelectionDHopfPerturbation_of_matrixOpenness K.matrixOpenness

theorem theoremFacingCoreRealization (K : ParameterRichCoreKernelBundle) :
    Network.ParameterRichOscillatoryCoreRealizationTarget :=
  Network.parameterRichOscillatoryCoreRealization_of_kernels
    K.pMinusScaling K.fisherFullerScaling
    (Matrix.stableCodimOneClassIIImpliesStrongDHopfBlock K.rootClusterContinuity)
    K.childSelectionPerturbation K.nonlinearDHopf

end ParameterRichCoreKernelBundle

/-- Universal planar-analysis kernels. -/
abbrev PlanarKernelBundle := Planar.PlanarGlobalKernelBundle

/-- Nonlinear Floquet and Banaji inheritance results, now all-dimensional. -/
structure StabilityInheritanceKernelBundle : Prop where
  floquetOrbitalStability : Network.FloquetOrbitalStabilityTarget
  nondegenerateDependentReaction :
    Network.NondegenerateDependentReactionPersistenceAllTypesTarget
  stableDependentReaction : Network.StableDependentReactionPersistenceAllTypesTarget

/-- Recipe-0 continuation theorem. -/
structure RecipeZeroKernelBundle : Prop where
  smoothContinuationHopf : Network.RecipeZeroSmoothContinuationTarget

namespace RecipeZeroKernelBundle

theorem realization (K : RecipeZeroKernelBundle) :
    Network.ParameterRichRecipeZeroRealizationTarget :=
  Network.parameterRichRecipeZeroRealization_of_smoothContinuation K.smoothContinuationHopf

end RecipeZeroKernelBundle

/-- Top-level theorem bundle.  Every field has a repository implementation below. -/
structure OscillationKernelBundle : Prop where
  planar : PlanarKernelBundle
  vassena : VassenaKernelBundle
  parameterRichCore : ParameterRichCoreKernelBundle
  stabilityInheritance : StabilityInheritanceKernelBundle
  recipeZero : RecipeZeroKernelBundle

/-- Historical residual bundle retained as a compatibility view.  Its fields are now derivable. -/
structure ResidualOscillationKernelBundle : Prop where
  principalVassena : Network.VassenaPrincipalFluxCriteriaRealizationTarget
  nondegenerateDependentReaction :
    Network.NondegenerateDependentReactionPersistenceAllTypesTarget
  stableDependentReaction : Network.StableDependentReactionPersistenceAllTypesTarget

structure CompleteOscillationKernelBundle : Prop extends OscillationKernelBundle where
  residual : ResidualOscillationKernelBundle

/-! ## Explicitly conditional kernel bundles -/

/-- Assemble the closed planar kernels with the still-open flow-regularity theorem supplied
explicitly. -/
noncomputable def planarKernelBundle_of_targets
    (hflow : Planar.CanonicalFlowRegularityTarget)
    (hJordan : Planar.SimplePlanarLoop.JordanSeparationTarget)
    (hside : Planar.StraightEdgeJordanSideTarget)
    (hboundary : Planar.JordanBoundaryCurrentConvergenceTarget) : PlanarKernelBundle where
  flowRegularity := hflow
  jordanSeparation := Planar.SimplePlanarLoop.jordanSeparation_of_target hJordan
  straightEdgeLocalSide := Planar.straightEdgeJordanSide_of_target hside
  jordanGridApproximation := Planar.jordanGridApproximation_proved hboundary

/-- Vassena bundle assembled from the explicit global-Hopf and principal-realization targets. -/
noncomputable def vassenaKernelBundle_of_targets
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hindex : AnalyticGlobalHopfIndexTarget)
    (hprincipal : Network.VassenaPrincipalFluxCriteriaRealizationTarget) : VassenaKernelBundle where
  pMinusScaling := hP0
  fisherFullerScaling := hFF
  analyticGlobalHopfIndex := analyticGlobalHopfIndex hindex
  principalRealization := Network.vassenaPrincipalFluxCriteriaRealization_of_target hprincipal

/-- Parameter-rich oscillatory-core bundle assembled from its nonlinear continuation target. -/
noncomputable def parameterRichCoreKernelBundle_of_targets
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hrootCluster : Polynomial.ZeroBorderRootClusterContinuityTarget)
    (hOpen : Matrix.StrongDHopfPerturbationTarget)
    (hDHopf : Network.ParameterRichDHopfContinuationTarget) :
    ParameterRichCoreKernelBundle where
  pMinusScaling := hP0
  fisherFullerScaling := hFF
  rootClusterContinuity := hrootCluster
  matrixOpenness := hOpen
  nonlinearDHopf := Network.parameterRichDHopfContinuation_of_target hDHopf

/-- Nonlinear stability/inheritance bundle.  **Not zero-input**: the Floquet field needs the tube
obligation, because the orbital-stability statement was strengthened from "some basin containing
the orbit" (vacuous) to "some tube of positive radius around the orbit".  See
`docs/math-review.md` and `docs/floquet-obligations.md`. -/
noncomputable def stabilityInheritanceKernelBundle_of_targets
    (hfloquet : Network.FloquetOrbitalStabilityObligation)
    (hnondegenerate : Network.NondegenerateDependentReactionPersistenceAllTypesTarget)
    (hstable : Network.StableDependentReactionPersistenceAllTypesTarget) :
    StabilityInheritanceKernelBundle where
  floquetOrbitalStability := Network.floquetOrbitalStability_of_obligation hfloquet
  nondegenerateDependentReaction :=
    Network.nondegenerateDependentReactionPersistence_of_target hnondegenerate
  stableDependentReaction := Network.stableDependentReactionPersistence_of_target hstable

/-- Recipe-0 bundle assembled from the nonlinear smooth-continuation target. -/
noncomputable def recipeZeroKernelBundle_of_target
    (hHopf : Network.RecipeZeroSmoothContinuationTarget) : RecipeZeroKernelBundle where
  smoothContinuationHopf := hHopf

/-- Historical residual view assembled from its three explicit targets. -/
noncomputable def residualOscillationKernelBundle_of_targets
    (hprincipal : Network.VassenaPrincipalFluxCriteriaRealizationTarget)
    (hnondegenerate : Network.NondegenerateDependentReactionPersistenceAllTypesTarget)
    (hstable : Network.StableDependentReactionPersistenceAllTypesTarget) :
    ResidualOscillationKernelBundle where
  principalVassena := Network.vassenaPrincipalFluxCriteriaRealization_of_target hprincipal
  nondegenerateDependentReaction :=
    Network.nondegenerateDependentReactionPersistence_of_target hnondegenerate
  stableDependentReaction := Network.stableDependentReactionPersistence_of_target hstable

/-- Complete theorem bundle from the explicit planar, Vassena, parameter-rich, Recipe-0, and
Floquet targets. Every required classical theorem is part of the function's input type. -/
noncomputable def completeOscillationKernelBundle_of_targets
    (hflow : Planar.CanonicalFlowRegularityTarget)
    (hJordan : Planar.SimplePlanarLoop.JordanSeparationTarget)
    (hside : Planar.StraightEdgeJordanSideTarget)
    (hboundary : Planar.JordanBoundaryCurrentConvergenceTarget)
    (hindex : AnalyticGlobalHopfIndexTarget)
    (hprincipal : Network.VassenaPrincipalFluxCriteriaRealizationTarget)
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hrootCluster : Polynomial.ZeroBorderRootClusterContinuityTarget)
    (hOpen : Matrix.StrongDHopfPerturbationTarget)
    (hDHopf : Network.ParameterRichDHopfContinuationTarget)
    (hrecipeZero : Network.RecipeZeroSmoothContinuationTarget)
    (hfloquet : Network.FloquetOrbitalStabilityObligation)
    (hnondegenerate : Network.NondegenerateDependentReactionPersistenceAllTypesTarget)
    (hstable : Network.StableDependentReactionPersistenceAllTypesTarget) : CompleteOscillationKernelBundle where
  planar := planarKernelBundle_of_targets hflow hJordan hside hboundary
  vassena := vassenaKernelBundle_of_targets hP0 hFF hindex hprincipal
  parameterRichCore := parameterRichCoreKernelBundle_of_targets
    hP0 hFF hrootCluster hOpen hDHopf
  stabilityInheritance := stabilityInheritanceKernelBundle_of_targets
    hfloquet hnondegenerate hstable
  recipeZero := recipeZeroKernelBundle_of_target hrecipeZero
  residual := residualOscillationKernelBundle_of_targets
    hprincipal hnondegenerate hstable

namespace ResidualOscillationKernelBundle

/-- Nondegenerate inheritance across an explicit one-dependent-reaction extension. -/
theorem nondegenerateSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.NondegenerateOscillationPreserving Nlarge := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.nondegenerateDependentReaction Nsmall q hdep ⟨k, hk⟩

/-- Stable inheritance across an explicit one-dependent-reaction extension. -/
theorem stableSingleDependentReaction
    (K : ResidualOscillationKernelBundle)
    {S : Type} [DecidableEq S] [Fintype S]
    {Nsmall Nlarge : Network S}
    (hext : Network.IsSingleDependentReactionExtension Nsmall Nlarge) :
    Nsmall.LinearlyStableOscillationPreserving Nlarge := by
  rintro ⟨k, hk⟩
  obtain ⟨q, hdep, rfl⟩ := hext
  exact K.stableDependentReaction Nsmall q hdep ⟨k, hk⟩

end ResidualOscillationKernelBundle

end CRNT
