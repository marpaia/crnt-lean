-- Deriving handlers used by example and generated networks (`deriving Fintype`)
import Mathlib.Tactic.DeriveFintype
import CRNT.Multistationarity.ConcordanceBoundary

-- General-purpose combinatorics (decidable undirected cycles; digraph excess function)
import CRNT.Combinatorics.DecidableCycle
import CRNT.Combinatorics.DigraphExcess

-- Basic CRN data structures
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network

-- Reaction graph: reachability, weak reversibility, linkage classes
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.CycleCover
import CRNT.Graph.SourceBlocks
import CRNT.Graph.LinkageClass
import CRNT.Graph.Crossing

-- Decision procedures: decidable bounded reachability, weak reversibility, linkage classes,
-- strong linkage classes, and rank/deficiency certificates over ℚ
import CRNT.Decision.Reachability
import CRNT.Decision.Linkage
import CRNT.Decision.StrongLinkage
import CRNT.Decision.DirectedReachability
import CRNT.Decision.Rank
import CRNT.Decision.Tactic
import CRNT.Decision.RankExact
import CRNT.Decision.ACRCheck
import CRNT.Decision.GaussianRank
import CRNT.Decision.ExactDeficiency
import CRNT.Decision.StoichBasisQ
import CRNT.Decision.LinkageDeficiencyExact
import CRNT.Decision.ComputableDeficiency
import CRNT.Decision.DeficiencyOneConditionsDecide
import CRNT.Decision.MinorSearch
import CRNT.Decision.DeficiencyZeroTactic
import CRNT.Decision.IsCriticalSiphonDecidable
import CRNT.Decision.ConservationConeStrict
import CRNT.Decision.CriticalSiphonDecide
import CRNT.Decision.PersistenceVerdict
import CRNT.Decision.PersistenceCertified
import CRNT.Decision.PersistenceSingleLinkage
import CRNT.Decision.RationalFarkas
import CRNT.Decision.RationalFarkasDecide
import CRNT.Decision.RationalFarkasStrict

-- Stoichiometry: reaction vectors, subspace, rank
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace

-- Linear-algebra building blocks (Perron–Frobenius positivity; dot-product orthogonality;
-- finrank subadditivity over finite suprema; sign vectors of subspaces)
import CRNT.LinearAlgebra.PerronFrobenius
import CRNT.LinearAlgebra.DetCycleCover
import CRNT.LinearAlgebra.CauchyBinet
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.LinearAlgebra.FinrankSup
import CRNT.LinearAlgebra.SignVector
import CRNT.LinearAlgebra.OrientedMatroid
import CRNT.LinearAlgebra.ConformalDecomposition
import CRNT.LinearAlgebra.Substochastic
import CRNT.LinearAlgebra.PowerProductMono
import CRNT.LinearAlgebra.PowerProductMonoFinset

-- Convex geometry: generated cones, dual cones, Newton polytopes (endotactic / toric-inclusion routes)
import CRNT.Geometry.PolyhedralFan
import CRNT.Geometry.PolyhedralBarrier
import CRNT.Geometry.ConvexBarrierObstruction
import CRNT.Geometry.FanFaceLattice
import CRNT.Geometry.ConeFaceIncidence
import CRNT.Geometry.Endotactic
import CRNT.Geometry.ToricFan
import CRNT.Geometry.CraciunZSH
import CRNT.Geometry.ZeroSeparatingSurface
import CRNT.Geometry.ConeFace
import CRNT.Geometry.ZeroSeparatingCurve2D
import CRNT.Geometry.PlanarZSH
import CRNT.Geometry.PlanarZSHTrap
import CRNT.Geometry.PlanarFanSlopes
import CRNT.Geometry.PolyRegionSeparating
import CRNT.Geometry.HalfPlaneSeparatingSurface
import CRNT.Geometry.ToricFieldPolar
import CRNT.Geometry.ToricFieldPolarMulti
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.FaithfulCurveExistence
import CRNT.Geometry.FaithfulCurveGeneral
import CRNT.Geometry.FaithfulCurve2D
import CRNT.Geometry.FaithfulCurve2DFan
import CRNT.Geometry.ToricStrictSupport
import CRNT.Geometry.ToricWRStrictInward
import CRNT.Geometry.FanWallsCrossed
import CRNT.Geometry.FanActiveWalls
import CRNT.Geometry.FanSeparationWitness
import CRNT.Geometry.FanWallActivityDecide
import CRNT.Geometry.FanFaceProperness
import CRNT.Geometry.ReactionFanGeneration
import CRNT.Geometry.SimplicialConeClosed
import CRNT.Geometry.FiniteConeClosed
import CRNT.Geometry.ReactionHullCone
import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FanRefinement
import CRNT.LinearAlgebra.LogSumInj
import CRNT.Analysis.FixedPoint
import CRNT.Analysis.Sperner
import CRNT.Analysis.Sperner2D
import CRNT.Analysis.Sperner2DMulti
import CRNT.Analysis.SpernerTriangulation
import CRNT.Analysis.SpernerMultiIncidence
import CRNT.Analysis.SpernerGridMulti
import CRNT.Analysis.SpernerGridGeometric
import CRNT.Analysis.SpernerLattice
import CRNT.Analysis.SpernerLatticeColoring
import CRNT.Analysis.SpernerLatticeIncidence
import CRNT.Analysis.SpernerLatticeIncidenceHV
import CRNT.Analysis.SpernerLatticeCellColor
import CRNT.Analysis.SpernerLatticeDoorGraph
import CRNT.Analysis.SpernerLatticeBipartite
import CRNT.Analysis.SpernerLatticeNeighbor
import CRNT.Analysis.SpernerLatticeFullGraph
import CRNT.Analysis.SpernerLatticeBoundary
import CRNT.Analysis.SpernerLatticeCellDegree
import CRNT.Analysis.SpernerLatticeSperner
import CRNT.Analysis.SpernerLatticeGeometric
import CRNT.Analysis.SpernerSimplexLimit
import CRNT.Analysis.SpernerSimplexLimitN
import CRNT.Analysis.SpernerBrouwer2D
import CRNT.Analysis.SpernerLatticeN
import CRNT.Analysis.SpernerNGeometric
import CRNT.Analysis.SpernerNParity
import CRNT.Analysis.SpernerNIncidence
import CRNT.Analysis.SpernerNBaseShift
import CRNT.Analysis.SpernerNBoundary
import CRNT.Analysis.SpernerNDoor
import CRNT.Analysis.SpernerNBoundaryCell
import CRNT.Analysis.SpernerNBoundaryCorr
import CRNT.Analysis.SpernerNFintype
import CRNT.Analysis.SpernerNFacetCount
import CRNT.Analysis.SpernerNSperner
import CRNT.Analysis.SpernerNBoundaryCount
import CRNT.Analysis.SpernerNHandshake
import CRNT.Analysis.SpernerNInterior
import CRNT.Analysis.SpernerNClose
import CRNT.Analysis.SpernerBrouwerN
import CRNT.Analysis.BrouwerConvex
import CRNT.Analysis.ConvexProjection
import CRNT.Analysis.BrouwerZero
import CRNT.Analysis.ConcentrationZero
import CRNT.Analysis.SpernerGrid

-- Kinetics: concentrations, mass action, and the general kinetics abstraction
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.MassActionJacobian
import CRNT.Kinetics.General
import CRNT.Kinetics.Generalized

-- Open networks: inflow/outflow pseudo-reactions and the fully open extension
import CRNT.Open.Augmentation
import CRNT.Open.Deficiency
import CRNT.Open.Boundary
import CRNT.Open.PartialOpen

-- Equilibria: steady states, compatibility classes, complex balancing
import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.CompatibilityClass
import CRNT.Equilibria.ComplexBalanced
import CRNT.Equilibria.DetailedBalanced
import CRNT.Equilibria.BrouwerSteadyState
import CRNT.Equilibria.BrouwerNormalCone

-- Dynamics: algebraic (complex-space) form of mass-action kinetics; ODE regularity and
-- local existence; LaSalle invariance
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Dynamics.MassActionField
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.FlowConstruction
import CRNT.Dynamics.VariationalEquation
import CRNT.Dynamics.FlowDifferentiable
import CRNT.Dynamics.Monotone
import CRNT.Dynamics.RouthHurwitz
import CRNT.Dynamics.Hurwitz
import CRNT.Dynamics.HopfGate
import CRNT.Dynamics.RouthHurwitz4
import CRNT.Dynamics.RouthHurwitz4Suff
import CRNT.Dynamics.HopfGate4
import CRNT.Dynamics.Hurwitz2Matrix
import CRNT.Dynamics.Hurwitz3Matrix
import CRNT.Dynamics.HopfAdmissible
import CRNT.Dynamics.HopfNormalForm
import CRNT.Dynamics.HopfLimitCycle
import CRNT.Dynamics.HopfPersistentOrbit
import CRNT.Dynamics.TransversalCrossingTime
import CRNT.Dynamics.PoincareReturnMap
import CRNT.Dynamics.ReturnMapPeriodicOrbit
import CRNT.Dynamics.HopfRealizes
import CRNT.Dynamics.SpectralSplitting
import CRNT.Dynamics.SpectralSplittingReal
import CRNT.Dynamics.ExponentialDichotomy
import CRNT.Dynamics.ExponentialDecay
import CRNT.Dynamics.HopfGate3Matrix
import CRNT.Dynamics.HopfTransversality3
import CRNT.Examples.HopfOscillator3
import CRNT.Examples.HopfNetwork3
import CRNT.Examples.HopfNetwork3Branches
import CRNT.Examples.CycleRateNonMonotone
import CRNT.Dynamics.HurwitzGershgorin
import CRNT.Dynamics.HurwitzGershgorinColumn
import CRNT.Dynamics.QSSA
import CRNT.Dynamics.Nagumo
import CRNT.Dynamics.Tikhonov
import CRNT.Dynamics.MichaelisMenten
import CRNT.Dynamics.Fenichel
import CRNT.Dynamics.FenichelManifold
import CRNT.Dynamics.FenichelSlowDrift
import CRNT.Dynamics.FenichelC1Manifold
import CRNT.Dynamics.GraphTransform
import CRNT.Dynamics.CenterManifold
import CRNT.Dynamics.CenterManifoldReduction
import CRNT.Dynamics.FenichelPersistence
import CRNT.Dynamics.FenichelPersistenceConcrete
import CRNT.Dynamics.FenichelPersistenceContracting
import CRNT.Dynamics.FenichelCoupledBase
import CRNT.Dynamics.FenichelGeneralDrift
import CRNT.Dynamics.FenichelMovingGeneralDrift
import CRNT.Dynamics.FenichelLogisticInstance
import CRNT.Dynamics.FenichelContinuousMovingTarget
import CRNT.Dynamics.FenichelComovingManifold
import CRNT.Dynamics.FenichelReductionPrinciple
import CRNT.Dynamics.FenichelStabilityTransfer
import CRNT.Dynamics.MichaelisMentenManifold
import CRNT.Dynamics.MichaelisMentenReduced
import CRNT.Dynamics.MichaelisMentenC1
import CRNT.Dynamics.MichaelisMentenRegularized
import CRNT.Dynamics.MichaelisMentenSlowDrift
import CRNT.Dynamics.MichaelisMentenSlowDriftSpeed
import CRNT.Dynamics.MichaelisMentenDepletion
import CRNT.Dynamics.MichaelisMentenCertified
import CRNT.Dynamics.DissipativeTracking
import CRNT.Dynamics.MichaelisMentenCertifiedUniform
import CRNT.Dynamics.MichaelisMentenCoupledContraction
import CRNT.Dynamics.MichaelisMentenFenichel
import CRNT.Dynamics.MichaelisMentenFenichelAllTime
import CRNT.Dynamics.MichaelisMentenLipschitz
import CRNT.Dynamics.CertifiedReduction

-- Deficiency
import CRNT.Deficiency.Definition
import CRNT.Deficiency.Consistent
import CRNT.Deficiency.ConsistentWR
import CRNT.Deficiency.CutPair
import CRNT.Deficiency.Regular
import CRNT.Deficiency.Signature
import CRNT.Deficiency.KernelDimension
import CRNT.Deficiency.DeficiencyOne
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Deficiency.DeficiencyOneStructure
import CRNT.Deficiency.IncidenceBlock
import CRNT.Deficiency.DeficiencyOneDecomp
import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Deficiency.ComplexBalancedRatio
import CRNT.Deficiency.SignedDrainage
import CRNT.Deficiency.KineticExcess
import CRNT.Deficiency.ExcessPositivity
import CRNT.Deficiency.LevelSetSign
import CRNT.Deficiency.StructuredPreimage
import CRNT.Deficiency.DeficientClassKernel
import CRNT.Deficiency.TerminalSLC
import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.ClassConservation
import CRNT.Deficiency.Confluence
import CRNT.Deficiency.Shelf
import CRNT.Deficiency.DeficiencyOneAlgorithm
import CRNT.Deficiency.DOAForward
import CRNT.Deficiency.Colinearity
import CRNT.Deficiency.ColinearityClasses
import CRNT.Deficiency.AdvancedDeficiencyAlgorithm
import CRNT.Deficiency.PerClassKernel
import CRNT.Deficiency.KernelDimensionBound
import CRNT.Deficiency.PerClassKernelPos
import CRNT.Deficiency.PerClassKernelUnique
import CRNT.Deficiency.KernelDimensionWR
import CRNT.Deficiency.RangeKineticWR
import CRNT.Deficiency.KineticSubspace
import CRNT.Kinetics.HungarianLemma
import CRNT.Deficiency.ClosedSetKernel
import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.TerminalKernelBound
import CRNT.Deficiency.TerminalReachable
import CRNT.Deficiency.Drainage
import CRNT.Deficiency.HigherDeficiency

-- Theorem statement interfaces and proved components
import CRNT.Theorems.DeficiencyZero.Statement
import CRNT.Theorems.DeficiencyZero.PositiveKernel
import CRNT.Theorems.DeficiencyZero.Birch
import CRNT.Theorems.DeficiencyZero.BirchExistence
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Stability
import CRNT.Theorems.DeficiencyZero.Confinement
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit
import CRNT.Theorems.DeficiencyZero.NoPeriodicOrbitComplexBalanced

-- Oscillation: periodic-orbit vocabulary, the proved exclusion theorems, matrix criteria,
-- reaction-restriction/inheritance interfaces, and the planar/Vassena/Floquet routes.
-- The whole subtree is re-exported through the `CRNT.Oscillation` umbrella below; these four
-- are listed early because the analyzer contract depends on them directly.
import CRNT.Oscillation.Basic
import CRNT.Oscillation.Exclusion
import CRNT.Oscillation.LowRank
import CRNT.Oscillation.KineticBasic
import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Theorems.DeficiencyOne.LogRatioUniqueness
import CRNT.Theorems.DeficiencyOne.ToricReduction
import CRNT.Theorems.DeficiencyOne.Uniqueness
import CRNT.Theorems.DeficiencyOne.MultiClass
import CRNT.Theorems.DeficiencyOne.Existence
import CRNT.Theorems.DeficiencyOne.ExistenceDynamical

-- Multistationarity: species-reaction graph, injectivity criteria
import CRNT.Multistationarity.SRGraph
import CRNT.Multistationarity.SRGraphCriterion
import CRNT.Multistationarity.SignedSRGraph
import CRNT.Multistationarity.SRGraphCycleDict
-- Shinar--Feinberg true-SR theorem, proved by the Banaji--Craciun determinant route
import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Multistationarity.JacobianDeterminantSign
import CRNT.Multistationarity.JacobianCycleSign
import CRNT.Multistationarity.JacobianCycleSelection
import CRNT.Multistationarity.Injectivity
import CRNT.Multistationarity.SourceWeightPairing
import CRNT.Multistationarity.GainPotential
import CRNT.Multistationarity.Concordance
import CRNT.Multistationarity.Capacity
import CRNT.Multistationarity.JacobianInjectivity
import CRNT.Multistationarity.PMatrix
import CRNT.Multistationarity.PMatrixSchur
import CRNT.Multistationarity.PMatrixSignature
import CRNT.Multistationarity.GaleNikaido
import CRNT.Multistationarity.GaleNikaidoBox
import CRNT.Multistationarity.PMatrixUnivalence
import CRNT.Multistationarity.GaleNikaidoUniv
import CRNT.Multistationarity.StoichChart
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Multistationarity.ReducedCoverSign
import CRNT.Multistationarity.ReducedJacobianSign
import CRNT.Multistationarity.ReducedSRGraph
import CRNT.Multistationarity.PivotChartInjectivity
import CRNT.Multistationarity.PivotReducedInjectivity
import CRNT.Multistationarity.ReducedPMatrixDecide
import CRNT.Multistationarity.PointIndepDecidable
import CRNT.Multistationarity.ReducedSRGraphBridge
import CRNT.Multistationarity.SRCoverPointIndependence
import CRNT.Multistationarity.SRCycleInjectivity
import CRNT.Multistationarity.SRInjectivityClass
import CRNT.Multistationarity.SRSignDecidable
import CRNT.Multistationarity.Toric
import CRNT.Multistationarity.RegularValueDegree
import CRNT.Multistationarity.LinearDegree
import CRNT.Multistationarity.DegreeAdditivity
import CRNT.Multistationarity.DegreeStability
import CRNT.Multistationarity.DegreeLocallyConstant
import CRNT.Multistationarity.DegreeProperConstant
import CRNT.Multistationarity.DegreeHomotopyInvariant

-- Design: robustness and special equilibria
import CRNT.Design.ACR
import CRNT.Design.ACRUnconditional
import CRNT.Design.ACRCrossClass
import CRNT.Design.Adaptation

-- Persistence: Petri-net siphons; siphon-face tangency; single-linkage-class global stability
import CRNT.Dynamics.Siphon
import CRNT.Dynamics.SiphonLinkage
import CRNT.Dynamics.FirstOrderGAC
import CRNT.Dynamics.SiphonConservation
import CRNT.Dynamics.ConservationLaw
import CRNT.Dynamics.Persistence
import CRNT.Dynamics.GlobalStability
import CRNT.Dynamics.ForwardInvariance
import CRNT.Dynamics.GenuineConfinement
import CRNT.Dynamics.PersistenceGAC
import CRNT.Dynamics.GACConfinement
import CRNT.Dynamics.GACSeparatingRegion
import CRNT.Dynamics.GACSeparatingRegionNagumo
import CRNT.Dynamics.GACSeparatingCapstone
import CRNT.Dynamics.PersistenceTheorem
import CRNT.Dynamics.PersistenceConfined
import CRNT.Dynamics.ConfinedInvariance
import CRNT.Dynamics.BoundaryDescent
import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.NegativeInvariance
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.CriticalSiphonOmega
import CRNT.Dynamics.NoCriticalSiphonPersistence
import CRNT.Dynamics.GACNoCriticalSiphon
import CRNT.Dynamics.GACOmegaPositive
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Dynamics.GACSeparatingWitness
import CRNT.Dynamics.GACCertificate
import CRNT.Dynamics.IsolatedInvariant
import CRNT.Dynamics.DifferentialInclusion
import CRNT.Dynamics.DissipationBound
import CRNT.Dynamics.ButlerMcGehee
import CRNT.Dynamics.EscapeSiphonFace
import CRNT.Dynamics.MinimalInvariant
import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.ToricEmbedding
import CRNT.Dynamics.ToricEmbeddingOrder
import CRNT.Dynamics.ToricEmbeddingWR
import CRNT.Dynamics.ToricCycleSortedBase
import CRNT.Dynamics.ToricCycleOrderLimits
import CRNT.Dynamics.ZeroSeparating
import CRNT.Dynamics.Viability
import CRNT.Dynamics.FirstExit
import CRNT.Dynamics.SublevelInvariant
import CRNT.Dynamics.SublevelNagumo
import CRNT.Dynamics.ClosedSetNagumo
import CRNT.Dynamics.SupportDiniBridge
import CRNT.Dynamics.PolyRegionInvariant
import CRNT.Dynamics.PolyRegionStrictInvariant
import CRNT.Dynamics.ThmBGenuine
import CRNT.Dynamics.EndotacticPermanence
import CRNT.Dynamics.FacetRepulsion
import CRNT.Dynamics.FacetRepulsionAndersonShiu
import CRNT.Dynamics.FaceCodimension
import CRNT.Dynamics.ToricBarrierTrapping
import CRNT.Dynamics.FaceDirectionCone
import CRNT.Dynamics.ToricBarrierExplicit
import CRNT.Dynamics.OrbitRegularity
import CRNT.Dynamics.VertexOmegaExclusion
import CRNT.Dynamics.SourceOrderDescent
import CRNT.Dynamics.TransversalPlanarDescent
import CRNT.Dynamics.CriticalSiphonNearFacetInflux
import CRNT.Dynamics.SingletonFacetEscape
import CRNT.Dynamics.SiphonFacetEscape
import CRNT.Dynamics.CriticalSiphonDissipationRepulsion

-- Stochastic CRN: Anderson–Craciun–Kurtz product-form objects
import CRNT.Stochastic.ProductForm
import CRNT.Stochastic.Generator
import CRNT.Stochastic.CTMC
import CRNT.Stochastic.JumpKernel
import CRNT.Stochastic.Kernel
import CRNT.Stochastic.KernelInvariant
import CRNT.Stochastic.KernelStationary
import CRNT.Stochastic.KernelIrreducible
import CRNT.Stochastic.KernelNormalized
import CRNT.Stochastic.KernelSupport
import CRNT.Stochastic.KernelProductForm
import CRNT.Stochastic.KernelMaximalRegion
import CRNT.Stochastic.Ergodicity
import CRNT.Stochastic.ErgodicConvergence
import CRNT.Stochastic.CountWitnessPath
import CRNT.Stochastic.ErgodicConvergenceGeneral
import CRNT.Stochastic.JumpReachabilityLift
import CRNT.Stochastic.RegionPrimitive
import CRNT.Stochastic.RegionStronglyConnected
import CRNT.Stochastic.Semigroup
import CRNT.Stochastic.SemigroupComposition
import CRNT.Stochastic.UniformizedConvergence
import CRNT.Stochastic.ConservationClassRegion
import CRNT.Stochastic.SemigroupConvergence
import CRNT.Stochastic.KurtzScaling
import CRNT.Stochastic.KurtzFluidLimit
import CRNT.Stochastic.PoissonFluctuation
import CRNT.Stochastic.MultiPoissonFluctuation
import CRNT.Stochastic.PoissonClockFamily
import CRNT.Stochastic.TimeChangedFluctuation

-- Network composition
import CRNT.Compose.Interconnect
import CRNT.Compose.InterconnectKinetics
import CRNT.Compose.InterconnectSiphon
import CRNT.Compose.InterconnectMonostationary
import CRNT.Compose.StoichIndependent

-- Deficiency-one decidable structural conditions
import CRNT.Deficiency.DeficiencyOneDecide

-- Interoperability and certificate workflow
import CRNT.Interop.Certificates
import CRNT.Interop.NetworkData
import CRNT.Interop.Analysis
import CRNT.Examples.StochasticConvergenceExample
import CRNT.Decision.ComputableTerminalSLC
import CRNT.Decision.InjectivityMargin
import CRNT.Dynamics.HopfBoundaryQ
import CRNT.Dynamics.GershgorinMarginQ
import CRNT.Dynamics.GershgorinColumnMarginQ
import CRNT.Multistationarity.Sard
import CRNT.Multistationarity.SteadyStateDegree
import CRNT.Deficiency.DOACapacityConstruction

-- Global persistence/permanence API and theorem-frontier infrastructure.
--
-- The three modules that used to be hollow (`GlobalPersistence`, `GlobalPersistenceCertificates`,
-- `SiphonAutocatalysis` -- `:= True`, `dummy : True`, `isTrue` deciders) now carry real content
-- from the global-persistence branch, so they are re-exported again.  `scripts/check_stubs.py`
-- reports zero hollow definitions in the tree; if that regresses, these imports are the first
-- thing to remove.
import CRNT.Geometry.EndotacticGlobal
import CRNT.Geometry.SpeciesProjection
import CRNT.Kinetics.SpeciesProjectionMassAction
import CRNT.Kinetics.VariableMassAction
import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.SiphonAutocatalysis
import CRNT.Dynamics.GlobalPersistenceCertificates
import CRNT.Dynamics.SingleLinkageStructure
import CRNT.Dynamics.ReactionConeDisplacement
import CRNT.Dynamics.NoDrainableSiphonPersistence
import CRNT.Dynamics.GlobalPermanence
import CRNT.Decision.StrictConeRealization

-- Tier decomposition and the Lemma 4.4 scale-extraction chain (the permanence route).
import CRNT.Dynamics.TierPersistence
import CRNT.Dynamics.TierDirectionFeasibility
import CRNT.Dynamics.TierDirectionProjection
import CRNT.Dynamics.TierLyapunov
import CRNT.Dynamics.TierOriginGeometry
import CRNT.Dynamics.FiniteNegativeBudget
import CRNT.Dynamics.TierScaleMagnitude
import CRNT.Dynamics.TierScaleTruncation
import CRNT.Dynamics.TierScaleDecomposition
import CRNT.Dynamics.TierScaleExtractionLemma44
import CRNT.Dynamics.TierExtractionCompleted
import CRNT.Dynamics.ProperTierTransversal
import CRNT.Dynamics.TierSubsequenceExtraction
import CRNT.Dynamics.TierOrderAlgebra
import CRNT.Dynamics.TierExtraction
import CRNT.Dynamics.TierSequentialReduction
import CRNT.Dynamics.TierCompactNegativity
import CRNT.Dynamics.VariableTierLyapunov
import CRNT.Dynamics.PermanenceAssembly
-- Detailed balance / Wegscheider, buffering, translation (new)
import CRNT.Stoich.Transpose
import CRNT.Graph.Reversibility
import CRNT.Equilibria.Wegscheider
import CRNT.Equilibria.WegscheiderConverse
import CRNT.Design.BufferingStructure
import CRNT.Design.OutputCompleteClosure
import CRNT.Translation.DynamicalEquivalence
import CRNT.Translation.ReactionTranslation
-- expanded checkpoint (latest drop): modules that elaborate
import CRNT.Design.ACRStandard
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Flux.PSemiflow
import CRNT.Algebra.SiphonSupport
import CRNT.Decomposition.ReactionPartition
import CRNT.Design.GeneratedClosure
import CRNT.Multistationarity.SignConstruction
import CRNT.Stochastic.FosterLyapunov
import CRNT.Translation.ComplexBalance
import CRNT.Translation.StructuralInvariants
import CRNT.Stability.BDC
import CRNT.Kinetics.GeneralizedConditions
import CRNT.LinearAlgebra.OrientedMatroidConditions
import CRNT.Geometry.CompatibilityFaces
import CRNT.Stoich.ConservationDimension
import CRNT.Subnetwork.ReactionRestriction
import CRNT.Stochastic.IntegerLattice
import CRNT.Dynamics.FlowSmoothDependence
import CRNT.Dynamics.KnownGlobalPersistenceClasses
import CRNT.Oscillation.CoordinateDynamics
import CRNT.Oscillation.Floquet
import CRNT.Oscillation.GlobalAttraction
import CRNT.Oscillation.MatrixCriteria
import CRNT.Oscillation.ReturnMap
import CRNT.Oscillation.ReturnMapContraction
import CRNT.Oscillation.ParameterRich
import CRNT.Oscillation.ReturnMapPersistence
import CRNT.Oscillation.Certificate
import CRNT.Oscillation.ReactionRestriction
import CRNT.Oscillation.RecipeZero
import CRNT.Oscillation.StructuralCore
import CRNT.Oscillation.PlanarFrontier
import CRNT.Oscillation.DulacAreaSign
import CRNT.Oscillation.GreenJordanReduction
import CRNT.Oscillation.PlanarDulac
import CRNT.Oscillation.SimpleCycle
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.ReturnInterval
import CRNT.Oscillation.ReturnMapAttraction
import CRNT.Oscillation.DulacLineIntegral
import CRNT.Oscillation.PlanarOmega
import CRNT.Oscillation.ChildSelectionSearch

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Equilibria.SteadyStateFlux
import CRNT.Flux.Cone
import CRNT.Flux.Elementary
import CRNT.Oscillation.Analyze
import CRNT.Oscillation.PlanarCanonicalReturn
import CRNT.Oscillation.PlanarMinimalSet
import CRNT.Oscillation.PlanarRecurrentSection
import CRNT.Oscillation.PlanarTransversalGeometry
import CRNT.Oscillation.RankTwoPlanar
import CRNT.Oscillation.VassenaCriteria

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Deficiency.ExactSequence
import CRNT.Design.EmergentCycles
import CRNT.Kinetics.GeneralizedNondegeneracy
import CRNT.Reduction.Intermediates
import CRNT.Subnetwork.EmbeddedNetwork

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.ReturnMapFamilyPersistence

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Equilibria.LinkageComplexBalance

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Design.EmergentConservation
import CRNT.Design.Localization

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Dynamics.Trap

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Graph.Condensation
import CRNT.Kinetics.GeneralizedNetwork

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Basic.Isomorphism
import CRNT.Basic.IsomorphismKinetics
import CRNT.Decomposition.BlockDeficiency
import CRNT.Decomposition.Deficiency
import CRNT.Decomposition.Rank
import CRNT.Deficiency.CycleExactSequence
import CRNT.Deficiency.LinkageCoupling
import CRNT.Design.MaxRPA
import CRNT.Design.MaxRPAIntegrator
import CRNT.Design.MaxRPAStochastic
import CRNT.Design.ShinarFeinbergTheorem
import CRNT.Equilibria.WegscheiderDeficiency
import CRNT.Equilibria.WegscheiderGenerators
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Kinetics.GeneralizedCycleExactSequence
import CRNT.Kinetics.GeneralizedDeficiencyComparison
import CRNT.LinearAlgebra.OrientedMatroidNondegeneracy
import CRNT.Stochastic.Absorbing
import CRNT.Stochastic.ConservativeClasses

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Equilibria.TreeConstantBinomials
import CRNT.Equilibria.TreeConstantCriterion
import CRNT.Equilibria.TreeConstantKernelBasis
import CRNT.Equilibria.TreeConstants

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Algebra.DeficiencyIdeal
import CRNT.Algebra.PositiveTorusIdeals
import CRNT.Algebra.SteadyStateIdeal
import CRNT.Deficiency.DeficiencyOneLinkageScalars
import CRNT.Deficiency.DeficiencyOneMonotonicity
import CRNT.Deficiency.DeficiencyOneScalarReduction
import CRNT.Deficiency.DeficiencyZeroConsistency
import CRNT.Deficiency.TerminalKernelCone
import CRNT.Deficiency.TerminalKernelDimension
import CRNT.Deficiency.TerminalKernelFaces
import CRNT.Design.ShinarFeinbergCrossClass
import CRNT.Design.ShinarFeinbergTreeFormula
import CRNT.Equilibria.BoundarySiphon
import CRNT.Equilibria.GeneralizedComplexBalanceToric
import CRNT.Equilibria.GeneralizedTreeConstantCriterion
import CRNT.Graph.PositiveCirculation
import CRNT.Multistationarity.DeficiencyObstruction
import CRNT.Oscillation.ChildSelectionReactivity
import CRNT.Oscillation.DHopf
import CRNT.Oscillation.OscillatoryCoreEndToEnd
import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.ReactivityScaling
import CRNT.Oscillation.VassenaContinuation
import CRNT.Stability.RobustLyapunov
import CRNT.Theorems.DeficiencyZero.Characterization
import CRNT.Theorems.DeficiencyZero.HornCharacterization
import CRNT.Theorems.DeficiencyZero.GeneralKinetics
import CRNT.Equilibria.QuasiThermostatic

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Deficiency.CycleSplitting
import CRNT.Equilibria.WegscheiderDeficiencyOne

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Design.LabeledBufferingRPA
import CRNT.Design.LabeledBufferingStructure
import CRNT.Design.LocalizationDifferential
import CRNT.Design.MinimalForm
import CRNT.Design.StrongBufferingFluxRPA
import CRNT.Reduction.IntermediateSchurComplement
import CRNT.Reduction.SingleIntermediateElimination
import CRNT.Stochastic.DetailedBalance
import CRNT.Stochastic.FirstOrderFoster
import CRNT.Translation.ParallelAggregation
import CRNT.Translation.ParallelStructural
import CRNT.Translation.SourceCoefficientEquivalence

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Equilibria.ComplexBalanceGeometry
import CRNT.Equilibria.ConservationCoordinates
import CRNT.Equilibria.DetailedBalanceEntropy
import CRNT.Equilibria.DetailedBalanceLinearStability
import CRNT.Equilibria.DetailedBalanceToric
import CRNT.Equilibria.GeneralizedComplexBalanceGeometry
import CRNT.Oscillation.ContinuousTimeAttraction
import CRNT.Oscillation.GreenJordanFoundations
import CRNT.Oscillation.PlanarFlowBox
import CRNT.Oscillation.PlanarJordanSeparation
import CRNT.Oscillation.PlanarLateSectionReturn
import CRNT.Oscillation.PlanarNoCrossing
import CRNT.Oscillation.PlanarReturnOrdering
import CRNT.Oscillation.PlanarReturnSequence
import CRNT.Oscillation.PlanarSectionCoordinates
import CRNT.Translation.Improper
import CRNT.Translation.ResolvedComplexBalance
import CRNT.Translation.SourceComplexes

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.FloquetPersistenceBridge
import CRNT.Oscillation.FloquetReturnBridge
import CRNT.Oscillation.Inheritance
import CRNT.Oscillation.ScalarReturnStability

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Dynamics.GlobalPersistenceFrontier
import CRNT.Dynamics.TierStrictUpwardPartner

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Translation.ImproperComplexBalance
import CRNT.Translation.LinearConjugacy
import CRNT.Translation.LinearConjugacySpectral

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.FiedlerGlobalHopf
import CRNT.Oscillation.GlobalHopfContinuation

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.PlanarFloquetAttraction
import CRNT.Oscillation.ScalarReturnMapFamilyPersistence
import CRNT.Oscillation.ScalarSectionInterpolation

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.VassenaAnalyticity
import CRNT.Oscillation.VassenaEndToEnd

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.VassenaFiniteDimHopf

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Oscillation.PlanarOneSidedReturns

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Equilibria.TreePotentialIntegration
import CRNT.Theorems.DeficiencyZero.TreeConstantConstruction
import CRNT.Theorems.DeficiencyZero.TreeConstantProofComplete

-- Promoted from the frontier ledger (elaborated, closure sorry-free).
import CRNT.Stability.BDCCauchyBinetProof
import CRNT.Stability.BDCPrincipalMinors
import CRNT.Stability.BDCStructuralNonsingularity
import CRNT.Kinetics.CatalystFace
import CRNT.Kinetics.GeneralizedBirchExistence
import CRNT.Multistationarity.LocalDegreeOn
import CRNT.Multistationarity.ParametrizedLocalDegree
import CRNT.Theorems.DeficiencyOne.JacobianKernel
import CRNT.Basic.IsomorphismStructural
import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Equilibria.ComplexBalanceObstruction
import CRNT.Equilibria.DirectedMatrixTreeProof
import CRNT.Equilibria.MatrixTreeCofactor
import CRNT.Equilibria.WegscheiderInteger
import CRNT.Flux.CircuitTheory
import CRNT.Flux.ConformalDecomposition
import CRNT.Flux.ExtremeRay
import CRNT.Flux.IntegerTInvariant
import CRNT.Graph.CirculationDecomposition
import CRNT.Kinetics.GeneralizedComplexBalanceObstruction
import CRNT.Kinetics.GeneralizedDeficiencyZero
import CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT
import CRNT.Kinetics.GeneralizedDeficiencyZeroExistence
import CRNT.Kinetics.GeneralizedDeficiencyZeroProof
import CRNT.Multistationarity.InfluenceConcordance
import CRNT.Multistationarity.Normality
import CRNT.Multistationarity.NormalityTerminal
import CRNT.Multistationarity.StrongConcordance
import CRNT.Multistationarity.StrongConcordanceStability
import CRNT.Multistationarity.WeakNormality
import CRNT.Multistationarity.WeakNormalityCriterion
import CRNT.Stochastic.BirthDeathExhaustive
import CRNT.Stochastic.ProductFormConverse
import CRNT.Translation.DeficiencyImprovement
import CRNT.Oscillation.BanajiDependentReaction
import CRNT.Oscillation.BanajiEndToEnd
import CRNT.Oscillation.DependentReactionPersistence
-- The Global Attractor Theorem in full generality (both former holes closed).
-- `CRNT.Persistence.*`: bounded complex-balanced trajectories have a positive floor.
import CRNT.Persistence.ComplexBalancedFloor
import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Dynamics.GACLowRank
import CRNT.Dynamics.GACVertexFacet
import CRNT.Examples.CatalyticChainGAC

-- Field-map leaves added 2026-10-11c (identifiability, Hill kinetics, Turing, Descartes,
-- toric steady states, chemical computation, antithetic feedback, contraction)
import CRNT.Identifiability.RateConstants
import CRNT.Kinetics.Hill
import CRNT.Extensions.Turing
import CRNT.Equilibria.OneSpeciesDescartes
import CRNT.Equilibria.ToricSteadyStates
import CRNT.Computation.StableComputation
import CRNT.Design.Antithetic
import CRNT.Dynamics.Contraction
import CRNT.Kinetics.SignVectorCriterion
import CRNT.Translation.LinearConjugacyCharacterization
import CRNT.Open.DeficiencyZeroOpen
import CRNT.Open.DeficiencyOneOpen
import CRNT.Kinetics.GeneralizedSignCriterion
import CRNT.Multistationarity.InheritanceAddReactions
import CRNT.Dynamics.MonotoneComparison
import CRNT.Dynamics.CooperativeNetworks
import CRNT.Reduction.LinearElimination
import CRNT.Reduction.DrainedIntermediateBlock
import CRNT.Equilibria.ToricCriterion
import CRNT.Thermo.FreeEnergyMinimization
import CRNT.Stochastic.FiniteAbsorption
import CRNT.Stochastic.JumpAbsorption
import CRNT.Stochastic.ACRExtinctionExample
import CRNT.Stochastic.FosterRecurrence
import CRNT.Kinetics.HillConcordance
import CRNT.Dynamics.EnzymeFastContraction
import CRNT.Examples.LotkaFirstIntegral
import CRNT.Stochastic.NonExplosion
import CRNT.Examples.LotkaPeriodic
import CRNT.Multistationarity.OneSpeciesCapacity
import CRNT.Multistationarity.CapacityCharacterization
import CRNT.Extensions.DelayMassAction
import CRNT.Multistationarity.OneSpeciesNecessity
import CRNT.Stochastic.NonExplosionAS
-- Weakly reversible persistence (2026-10-11d): bounded weakly reversible trajectories have a
-- positive floor; conservative weakly reversible networks are persistent.
import CRNT.Persistence.WeaklyReversibleField
import CRNT.Persistence.WeaklyReversibleFloor
import CRNT.Persistence.ConservativePersistence
import CRNT.Examples.ConservativeNonPersistent
import CRNT.Persistence.UniformFieldBound
import CRNT.Persistence.VariableRateFloor
import CRNT.Persistence.OrbitClosureSiphon
import CRNT.Examples.InflowNoDrainable
import CRNT.Dynamics.GordanAlternative
import CRNT.Dynamics.CriticalSiphonDichotomy
import CRNT.Examples.CriticalSiphonDichotomyCounterexample
import CRNT.Examples.MinimalDGCritical
import CRNT.Persistence.DGCriticalPersistence
import CRNT.Persistence.BoundedWRPersistence
import CRNT.Persistence.FacetRepulsion
import CRNT.Examples.FacetRepulsionPair
import CRNT.Dynamics.EnzymeQSSA
import CRNT.Examples.EnzymeQSSAUnconditional
import CRNT.Reduction.NetworkDrainage
import CRNT.Examples.EnzymeIntermediate
import CRNT.Dynamics.TierDirectionExistence
import CRNT.Dynamics.StrongEndotacticTier
import CRNT.Dynamics.TierFixedRateRegion
import CRNT.Persistence.EndotacticPersistence
import CRNT.Multistationarity.InheritanceDependent
import CRNT.Multistationarity.InheritanceAddSpecies
import CRNT.Examples.OneReactionAtom
import CRNT.Multistationarity.OneReactionUniqueness
import CRNT.Multistationarity.OneReactionExistence
import CRNT.Multistationarity.OneReactionReversible
import CRNT.Analysis.NegDerivAtZeros
import CRNT.Multistationarity.OneReactionReversibleUnique

-- Field-map leaves added 2026-10-12 (formerly missing: A4 tropical equilibration, P9 diffusion and
-- linear noise generators, M13 rank-one parameter regions, A2 elimination).
import CRNT.Algebra.TropicalEquilibration
import CRNT.Stochastic.DiffusionApproximation
import CRNT.Multistationarity.RankOneParameterRegion
import CRNT.Algebra.SteadyStateElimination
import CRNT.Stochastic.ACRExtinction
import CRNT.Kinetics.GeneralKineticsComplexBalance
import CRNT.Dynamics.KineticMapPairing
import CRNT.Extensions.DelayLyapunov
import CRNT.Examples.ACRExtinctionInstance
import CRNT.Stochastic.StationaryIdentity
import CRNT.Multistationarity.TwoReaction
import CRNT.Algebra.TropicalExistence
import CRNT.Stochastic.ClosedSetAbsorption
import CRNT.Stochastic.ACRExtinctionAbsorption
import CRNT.Dynamics.OrthantMonotone
import CRNT.Algebra.GroebnerBasis
import CRNT.Algebra.Buchberger
import CRNT.Examples.LotkaAverages
import CRNT.Multistationarity.TwoReactionNondegenerate
import CRNT.Multistationarity.RevIrrReaction
import CRNT.Multistationarity.RankOneLifting
import CRNT.Multistationarity.RevRevReaction
import CRNT.Multistationarity.RankOneLowerBound
import CRNT.Multistationarity.DecoratedSimplices
import CRNT.Examples.DecoratedCellsInstance
import CRNT.Algebra.Patchworking
import CRNT.Multistationarity.DecoratedSimplicesConservation
import CRNT.Examples.AugmentedCellsInstance
import CRNT.Algebra.TropicalLifting
import CRNT.Algebra.TropicalLiftingNetwork
import CRNT.Multistationarity.MultistationarityRegionOpen
import CRNT.Dynamics.TierUniformNegativity
import CRNT.Persistence.StronglyEndotacticPersistence
import CRNT.Persistence.StronglyEndotacticPermanence
import CRNT.Persistence.StronglyEndotacticConsequences
import CRNT.Geometry.EndotacticStandard
import CRNT.Examples.WeakEndotactic
import CRNT.Persistence.FirstOrderEndotacticPersistence
import CRNT.Examples.FlowVacuity
import CRNT.Examples.NoDrainableUnbounded
import CRNT.Persistence.StronglyEndotacticVarK
import CRNT.Persistence.LinkageSpanPermanence
import CRNT.Examples.TwoLinkageSpan
import CRNT.Dynamics.SignedGraphMonotone
import CRNT.Dynamics.EuclideanContraction
import CRNT.Examples.ContractionInstance
import CRNT.Stochastic.MinimalSemigroup
import CRNT.Stochastic.MinimalSemigroupStochastic
import CRNT.Stochastic.MinimalSemigroupNetwork
-- Field-map leaves added 2026-10-13
import CRNT.Stochastic.MinimalSemigroupChapmanKolmogorov
import CRNT.Stochastic.MinimalSemigroupNonExplosion
import CRNT.Stochastic.MinimalSemigroupFoster
import CRNT.Examples.StochasticFosterInstances
import CRNT.Stochastic.MinimalSemigroupMinimality
import CRNT.Stochastic.MinimalSemigroupStationary
import CRNT.Stochastic.ProductFormInvariance
import CRNT.Stochastic.MinimalSemigroupErgodic
import CRNT.Stochastic.ProductFormErgodic
import CRNT.Examples.ProductFormErgodicInstance
import CRNT.Stochastic.ComplexBalancedNonExplosion
import CRNT.Stochastic.DeficiencyZeroStochastic
import CRNT.Stochastic.MinimalSemigroupErgodicInfinite
import CRNT.Stochastic.ProductFormConvergence
import CRNT.Stochastic.MinimalSemigroupDynkin
import CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov
import CRNT.Stochastic.NetworkFosterErgodic
import CRNT.Stochastic.FullyOpenErgodic
import CRNT.Stochastic.ForwardCME
import CRNT.Stochastic.JahnkeHuisinga
import CRNT.Stochastic.RecurrenceDichotomy
import CRNT.Stochastic.MinimalSemigroupForward
import CRNT.Stochastic.NetworkForwardEquation
import CRNT.Stochastic.MonomolecularLLN
import CRNT.Stochastic.MinimalSemigroupMoments
import CRNT.Stochastic.FullyOpenMoments
import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.FullyOpenGeometric
import CRNT.Stochastic.FullyOpenPoisson
import CRNT.Dynamics.SimplicialConeMonotone
import CRNT.Stochastic.PoissonCLT
import CRNT.Stochastic.MonomolecularCLT
import CRNT.Stochastic.MinimalSemigroupExpect
import CRNT.Stochastic.MonomolecularMeans
import CRNT.Stochastic.ConservativeLLN
import CRNT.Stochastic.InvariantMoments
import CRNT.Design.AntitheticErgodic
-- Field-map leaves added 2026-10-14
import CRNT.Persistence.EndotacticFloor
import CRNT.Examples.EndotacticConservative
import CRNT.Persistence.PlanarRegion
import CRNT.Persistence.TwoSpeciesEndotactic
import CRNT.Examples.TwoSpeciesEndotactic
import CRNT.Persistence.EndotacticConsequences
import CRNT.Dynamics.FamilyAbsorption
import CRNT.Persistence.TwoSpeciesPermanence
import CRNT.Persistence.ConservativeEndotacticPermanence
import CRNT.Dynamics.WeightedL1Contraction
import CRNT.Examples.L1Contraction
import CRNT.Stochastic.SubconservativeLLN
import CRNT.Multistationarity.DSRCriterion
import CRNT.Examples.DSRStrict
import CRNT.Stochastic.OpenLLN
import CRNT.Stochastic.KurtzLLN
import CRNT.Stochastic.KurtzPathwise
import CRNT.Stochastic.KacFormula
import CRNT.Stochastic.NonlinearCLT
import CRNT.Examples.DimerCLT
import CRNT.Stochastic.NonlinearCLTTraj
import CRNT.Examples.IsomerCLT
import CRNT.Stochastic.NonlinearCLTOpen
import CRNT.Stochastic.MultivariateCLT
import CRNT.Stochastic.MultivariateCLTOpen
import CRNT.Analysis.LinearODE
import CRNT.Stochastic.MultivariateCLTTraj
import CRNT.Design.AntitheticMeanOutput
import CRNT.Multistationarity.OneReactionNondegenerate
import CRNT.Multistationarity.OneReactionReversibleNondegenerate
import CRNT.Algebra.CircuitBound
import CRNT.Dynamics.StrongMonotone
import CRNT.Dynamics.SlowFast
import CRNT.Algebra.CircuitDescartes
import CRNT.Dynamics.HopfAveraging
import CRNT.Dynamics.NormalFormCubic
import CRNT.Dynamics.LaSalleConvergence
import CRNT.Stochastic.ExitMass
import CRNT.Stochastic.EndotacticPositiveRecurrence
import CRNT.Algebra.TropicalReduction
import CRNT.Extensions.NonIsothermal
import CRNT.Equilibria.SingletonSource
import CRNT.Design.GeneralPlantRPA
import CRNT.Multistationarity.DegreeExistence
import CRNT.Oscillation.PlanarOscillationCriterion
import CRNT.Multistationarity.MultistationarityRegion
import CRNT.Stochastic.EndotacticTierPositiveRecurrence
import CRNT.Computation.PiecewiseNatAffine
import CRNT.Dynamics.HopfLyapunovCalibration
import CRNT.Extensions.ReactionDiffusion
import CRNT.Extensions.DelaySemistability
import CRNT.Multistationarity.DeficiencyOneAlgorithm
import CRNT.Multistationarity.TwoReactionAtoms
import CRNT.Multistationarity.AdvancedDeficiencyAlgorithm
import CRNT.Equilibria.ToricParametrization
import CRNT.Dynamics.TikhonovLocal
import CRNT.Stochastic.CLTWeak
import CRNT.Multistationarity.DegreeStructural
import CRNT.Oscillation.TrappingRegion
import CRNT.Multistationarity.DegreeMultistationarity
import CRNT.Dynamics.OmegaLimitOrderConvex
import CRNT.Stochastic.EndotacticTierDomination
import CRNT.Oscillation.MinimalSetClassification
import CRNT.Design.GeneralPlantDrift
import CRNT.Dynamics.EscapeDirection
import CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness
import CRNT.Deficiency.ShelfFluxConstruction
import CRNT.Multistationarity.ParityOfSteadyStates
import CRNT.Computation.PiecewiseNatAffineRealization
import CRNT.Multistationarity.MultistationarityRegionDescription
import CRNT.Thermo.GibbsFreeEnergy
import CRNT.Equilibria.NilpotentJacobian
import CRNT.Stochastic.PathExitEvent
import CRNT.Algebra.ExcludedCircuit
import CRNT.Equilibria.KingAltman
import CRNT.Multistationarity.MultiShelfConverse
import CRNT.Stochastic.EndotacticFull
import CRNT.Dynamics.MassActionHopfTaylorData
import CRNT.Dynamics.TikhonovTube
import CRNT.Multistationarity.TotalDegree
import CRNT.Multistationarity.MMatrixDeterminant
import CRNT.Stochastic.ExitMassIdentification
import CRNT.Dynamics.StrongOrderConvex
import CRNT.Multistationarity.TwoReactionClassification
import CRNT.Algebra.TropicalSlowFast
import CRNT.Dynamics.AveragingRemainder
import CRNT.Design.MolecularControllerDrift
import CRNT.Equilibria.JacobianSpectrum
import CRNT.Multistationarity.ReducedDeterminantCircuits
import CRNT.Algebra.MixedVolume
import CRNT.Dynamics.DelayExistence
import CRNT.Dynamics.Gronwall
import CRNT.Stochastic.EndotacticTwoSpecies
import CRNT.Stochastic.EndotacticCoupledTwoSpecies
import CRNT.Stochastic.JumpCountPoisson
import CRNT.Stochastic.FluctuationSecondMoment
import CRNT.Deficiency.DOASignDecomposition
import CRNT.Dynamics.DelayHalanay
import CRNT.Multistationarity.ReducedDetHomogeneity
import CRNT.Persistence.BoundedPersistence
import CRNT.Equilibria.JacobianSpectrumEigen
import CRNT.Design.AntitheticInstance
import CRNT.Decision.DeficiencyOneHypothesesDecide
import CRNT.Dynamics.HopfFloquet
import CRNT.Multistationarity.TwoReactionCompleteness
import CRNT.Multistationarity.ParityGeneral
import CRNT.Oscillation.ReturnMapRotation
import CRNT.Dynamics.UniformContraction
import CRNT.Algebra.VolumePolynomial
import CRNT.Stochastic.CountableStateFoster
import CRNT.Multistationarity.TotalDegreeGeneral
import CRNT.Multistationarity.TotalDegreeSign
import CRNT.Dynamics.DelayComparison
import CRNT.Multistationarity.MultiShelfMoments
import CRNT.Extensions.ReactionDiffusionSpectrum
import CRNT.Stochastic.CompensatedSecondMoment
import CRNT.Computation.PiecewiseNatAffineMax
import CRNT.Algebra.TropicalDynamics
import CRNT.Dynamics.DelayComparisonLattice
import CRNT.Dynamics.DelayComparisonLocal
import CRNT.Dynamics.MassActionDelayComparison
import CRNT.Dynamics.MassActionLocalDelayComparison
import CRNT.Dynamics.DelayMassActionInvariance
import CRNT.Dynamics.MassActionDelayExistence
import CRNT.Examples.DelayedDimerization
import CRNT.Examples.DelayedQuadraticDecay
import CRNT.Deficiency.DOACapacityKernel
import CRNT.Deficiency.ADACoplanar
import CRNT.Multistationarity.TwoReactionCompleteness2
import CRNT.Dynamics.AveragingRegularity
import CRNT.Computation.StableComposition
import CRNT.Dynamics.StrongOrderStrict
import CRNT.Stochastic.CountTierCardinality
import CRNT.Extensions.ReactionDiffusionGlobal
import CRNT.Design.AntitheticFoster
import CRNT.Equilibria.PerronFrobenius
import CRNT.Multistationarity.CFMWHigherRank
import CRNT.Extensions.ReactionDiffusionFlow
import CRNT.Design.AntitheticExponential
import CRNT.Extensions.NonIsothermalLyapunov
import CRNT.Dynamics.FlowSmoothDependenceProof
import CRNT.Stochastic.FluctuationUniform
import CRNT.Algebra.MixedVolumeBKK
import CRNT.Multistationarity.TwoReactionTable
import CRNT.Thermo.MinimumEntropyProduction
import CRNT.Dynamics.SimplicialConeNetwork
import CRNT.Theorems.DeficiencyZero.Prigogine
import CRNT.Open.ConservationLaws
import CRNT.Dynamics.MarkusYamabe
import CRNT.Equilibria.DegenerateDichotomy
import CRNT.Theorems.DeficiencyZero.DecayRate
import CRNT.Algebra.ConvexVolume
import CRNT.Dynamics.RateSensitive
import CRNT.Multistationarity.EquilibriumSmoothness
import CRNT.Theorems.DeficiencyZero.AbsolutePseudoHelmholtz
import CRNT.Reduction.ToricReduction
import CRNT.Stochastic.ProductFormGeometric
import CRNT.Multistationarity.InheritanceCapacity
import CRNT.Theorems.DeficiencyZero.EntropyDissipation

-- Still outside the umbrella: CRNT.Dynamics.GlobalPersistenceFrontier and
-- CRNT.Dynamics.KnownGlobalPersistenceClasses.  Both now resolve all their names, but neither has
-- been elaborated; see scripts/unverified_modules.txt.

-- The deterministic oscillation development (planar Poincare-Bendixson/Dulac route, Vassena and
-- Fiedler criteria, parameter-rich D-Hopf cores, Floquet stability, network inheritance) is also in
-- the frontier target.  Only the four modules imported above -- Basic, Exclusion, LowRank,
-- KineticBasic -- are part of the verified core, because the analyzer contract depends on them.

/-!
# `crnt-lean`: Chemical Reaction Network Theory in Lean 4

Top-level import for the stable core of the `CRNT` library. It re-exports the basic
CRN data structures, the reaction-graph and stoichiometry layers, mass-action
kinetics, the deficiency definition, and the deficiency-zero statement interface.

The stable core plus the global-persistence and oscillation APIs is re-exported
here.  Research-frontier statements in those layers are represented as ordinary
propositions, never as axioms; importing `CRNT` therefore does not turn an
unproved global claim into an available theorem.

Two caveats, both machine-checked by `scripts/`:

* Modules whose definitions do not yet carry their intended meaning (`:= True`,
  `dummy : True`, `isTrue` deciders) are listed in `LEDGER.md` and are deliberately
  excluded from this umbrella.  `scripts/check_stubs.py` fails if a new one appears
  or if one of them is re-exported here.
* Modules that do not elaborate are listed in `scripts/known_broken.txt`, which the
  lakefile consumes as its exclusion list.  `scripts/check_exclusions.py` fails if
  that list grows.
-/
