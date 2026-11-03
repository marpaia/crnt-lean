import CRNT.Oscillation.Basic
import CRNT.Oscillation.Floquet
import CRNT.Oscillation.GlobalAttraction
import CRNT.Oscillation.KineticBasic
import CRNT.Oscillation.ParameterRich
import CRNT.Oscillation.Exclusion
import CRNT.Oscillation.LowRank
import CRNT.Oscillation.CoordinateDynamics
import CRNT.Oscillation.ReturnMap
import CRNT.Oscillation.ReturnMapPersistence
import CRNT.Oscillation.ReturnMapAttraction
import CRNT.Oscillation.ScalarReturnStability
import CRNT.Oscillation.ReturnInterval
import CRNT.Oscillation.ReactionRestriction
import CRNT.Oscillation.Inheritance
import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.MatrixCriteria
import CRNT.Oscillation.StructuralCore
import CRNT.Oscillation.RecipeZero
import CRNT.Oscillation.VassenaCriteria
import CRNT.Oscillation.VassenaContinuation
import CRNT.Oscillation.PlanarFrontier
import CRNT.Oscillation.PlanarDulac
import CRNT.Oscillation.PlanarOmega
import CRNT.Oscillation.RankTwoPlanar
import CRNT.Oscillation.Certificate
import CRNT.Oscillation.Analyze
import CRNT.Oscillation.ReturnMapFamilyPersistence
import CRNT.Oscillation.FloquetReturnBridge
import CRNT.Oscillation.ContinuousTimeAttraction
import CRNT.Oscillation.SimpleCycle
import CRNT.Oscillation.ScalarSectionInterpolation
import CRNT.Oscillation.DependentReactionPersistence
import CRNT.Oscillation.PlanarRecurrentSection
import CRNT.Oscillation.GreenJordanReduction
import CRNT.Oscillation.FloquetPersistenceBridge
import CRNT.Oscillation.ScalarReturnMapFamilyPersistence
import CRNT.Oscillation.BanajiDependentReaction
import CRNT.Oscillation.DulacAreaSign
import CRNT.Oscillation.VassenaFiniteDimHopf
import CRNT.Oscillation.PlanarFloquetAttraction
import CRNT.Oscillation.PlanarMinimalSet
import CRNT.Oscillation.PlanarTransversalGeometry
import CRNT.Oscillation.GlobalHopfContinuation
import CRNT.Oscillation.PlanarCanonicalReturn
import CRNT.Oscillation.ChildSelectionSearch
import CRNT.Oscillation.GlobalHopfSpectralCrossing
import CRNT.Oscillation.FiedlerGlobalHopf
import CRNT.Oscillation.VassenaAnalyticity
import CRNT.Oscillation.DHopf
import CRNT.Oscillation.ChildSelectionReactivity
import CRNT.Oscillation.ReactivityScaling
import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.DulacLineIntegral
import CRNT.Oscillation.PlanarSectionCoordinates
import CRNT.Oscillation.PlanarNoCrossing
import CRNT.Oscillation.PlanarReturnOrdering
import CRNT.Oscillation.VassenaEndToEnd
import CRNT.Oscillation.DHopfOpenness
import CRNT.Oscillation.OscillatoryCoreEndToEnd
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.GreenJordanFoundations
import CRNT.Oscillation.PlanarEndToEnd
import CRNT.Oscillation.BanajiEndToEnd
import CRNT.Oscillation.CompatibilityAdapters
import CRNT.Oscillation.OscillationKernelBundle
import CRNT.Oscillation.PlanarFlowBox
import CRNT.Oscillation.PlanarLateSectionReturn
import CRNT.Oscillation.PlanarJordanSeparation
import CRNT.Oscillation.PlanarReturnSequence
import CRNT.Oscillation.PlanarOneSidedReturns
import CRNT.Oscillation.PlanarDivergenceRegularity
import CRNT.Oscillation.GlobalHopfIndex
import CRNT.Oscillation.PlanarSectionHitIsolation
import CRNT.Oscillation.PlanarAdjacentReturnLoop
import CRNT.Oscillation.PlanarReturnMonotonicity
import CRNT.Oscillation.PlanarLocalReturns
import CRNT.Oscillation.PlanarLocalReturnLoops
import CRNT.Oscillation.PlanarJordanCrossingOrder
import CRNT.Oscillation.PlanarPoincareBendixson
import CRNT.Oscillation.PlanarGreenRectangle
import CRNT.Oscillation.PlanarGreenGrid
import CRNT.Oscillation.PlanarGreenJordanApproximation
import CRNT.Oscillation.PlanarJordanDyadic
import CRNT.Oscillation.PlanarJordanTopology
import CRNT.Oscillation.PlanarJordanBoundaryCurrent
import CRNT.Oscillation.PlanarFlowRegularity
import CRNT.Oscillation.GlobalHopfIndexTheorem
import CRNT.Oscillation.SmoothGlobalHopf
import CRNT.Oscillation.ReducedKineticContinuation
import CRNT.Oscillation.ParameterRichGlobalHopf
import CRNT.Oscillation.VassenaPrincipal
import CRNT.Oscillation.FloquetOrbitalStability
import CRNT.Oscillation.FloquetPersistenceGeneral
/-!
# Oscillation umbrella import

Proof-carrying qualitative oscillation infrastructure for finite mass-action CRNs.  The library
separates closed kernel theorems from explicit frontier propositions: an unsupported sufficient test
returns `unknown`, never a fabricated positive or negative verdict.
-/

















-- Closed foundational kernels and final end-to-end assembly.
