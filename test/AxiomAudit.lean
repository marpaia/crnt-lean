import CRNT
import CRNT.Multistationarity.MMatrixDeterminant
import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Dynamics.GACLowRank
import CRNT.Dynamics.GACVertexFacet
import CRNT.Examples.CatalyticChainGAC

/-!
# Axiom-cleanliness regression guard

`#print axioms` on the headline results, each pinned with `#guard_msgs` so the build
fails if any of them ever acquires an axiom beyond Mathlib's `propext`, `Classical.choice`,
and `Quot.sound` — in particular if a `sorry` (`sorryAx`) creeps into a dependency.

The `(whitespace := lax)` mode makes the comparison insensitive to how long names wrap.
-/

/-- info: 'CRNT.Network.exists_isComplexBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_isComplexBalanced

/-- info: 'CRNT.Network.gac_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.singleLinkageClass_gac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.singleLinkageClass_gac

/-- info: 'CRNT.Network.gac_of_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_persistent

/-- info: 'CRNT.Network.deficiencyOneUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.deficiencyOneUniqueness

/-- info: 'CRNT.omegaLimit_negInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.omegaLimit_negInvariant

/-- info: 'CRNT.ZeroSeparatingCurve2D.polyRegion_invariant_of_strictSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ZeroSeparatingCurve2D.polyRegion_invariant_of_strictSupport

/-- info: 'CRNT.FaithfulCurve2D.apexField_region_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.FaithfulCurve2D.apexField_region_persistent

/-- info: 'CRNT.Analysis.SpernerN.sperner_exists_rainbow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Analysis.SpernerN.sperner_exists_rainbow

/-- info: 'CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin

/-- info: 'CRNT.injOn_of_pmatrix_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.injOn_of_pmatrix_fderiv

/-- info: 'CRNT.Network.jumpKernel_invariantProb_singleton_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.jumpKernel_invariantProb_singleton_pos

/-- info: 'ODE.SlowManifoldC1Seed.contDiff_manifoldMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.SlowManifoldC1Seed.contDiff_manifoldMap
/-- info: 'CRNT.Network.isCriticalSiphon_iff_no_supported_cone_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isCriticalSiphon_iff_no_supported_cone_vector

/-- info: 'CRNT.Network.mem_conservationCone_iff_farkas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.mem_conservationCone_iff_farkas
/-- info: 'CRNT.Network.cmeSemigroup_preserves_stationarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.cmeSemigroup_preserves_stationarity

/-- info: 'CRNT.det_ne_zero_of_coverTerm_signDefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.det_ne_zero_of_coverTerm_signDefinite
/-- info: 'CRNT.Network.isCriticalSiphon_iff_exists_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isCriticalSiphon_iff_exists_pointwise
/-- info: 'CRNT.Network.cmeSemigroup_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.cmeSemigroup_comp

/-- info: 'CRNT.hopf_transversal_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.hopf_transversal_crossing

/-- info: 'CRNT.TransversalSection.hasFDerivAt_returnMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.TransversalSection.hasFDerivAt_returnMap

/-- info: 'CRNT.PlanarHopfData.hopf_andronov_full_field_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PlanarHopfData.hopf_andronov_full_field_realized

/-- info: 'CRNT.Examples.HopfOscillator3.admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfOscillator3.admissible

/-- info: 'CRNT.Examples.HopfNetwork3.hopf_crossing_at_μ₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfNetwork3.hopf_crossing_at_μ₀

/-- info: 'CRNT.Examples.HopfNetwork3.boundary_crossing_transversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.HopfNetwork3.boundary_crossing_transversal

/-- info: 'CRNT.Network.coverProductSingle_eq_magnitude_mul_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coverProductSingle_eq_magnitude_mul_sign

/-- info: 'CRNT.MichaelisMenten.mmRegManifoldMap_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.MichaelisMenten.mmRegManifoldMap_contDiff

/-- info: 'CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_massActionJacobian_of_consistentSRSign

/-- info: 'CRNT.primitive_of_stronglyConnected_self_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.primitive_of_stronglyConnected_self_loop

/-- info: 'CRNT.Network.regionPrimitive_of_stronglyConnected_self_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.regionPrimitive_of_stronglyConnected_self_loop

/-- info: 'CRNT.Network.weaklyReversible_pow_mulVec_tendsto_stationaryVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_pow_mulVec_tendsto_stationaryVec
/-- info: 'CRNT.Network.subsingleton_steadyState_of_consistentSRSign_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.subsingleton_steadyState_of_consistentSRSign_decide

/-- info: 'CRNT.NetworkData.analyze_srSignConsistent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_srSignConsistent_eq

/-- info: 'CRNT.NetworkData.isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep

/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix

/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_concretePivotChart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_concretePivotChart

/-- info: 'CRNT.Network.isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ

/-- info: 'CRNT.NetworkData.analyze_hasCriticalSiphon_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_hasCriticalSiphon_eq

/-- info: 'CRNT.NetworkData.singleLinkageHypotheses_of_persistenceSingleLinkage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.singleLinkageHypotheses_of_persistenceSingleLinkage

/-- info: 'CRNT.NetworkData.deficiencyOneConditions_of_analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.deficiencyOneConditions_of_analyze

/-- info: 'CRNT.RationalFarkas.feasibleStrict_eliminateLast_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.RationalFarkas.feasibleStrict_eliminateLast_iff

/-- info: 'CRNT.Network.complexShiftRegion_pow_mulVec_tendsto_stationaryVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexShiftRegion_pow_mulVec_tendsto_stationaryVec
/-- info: 'CRNT.Network.feasible_supportedFeasSystem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.feasible_supportedFeasSystem_iff

/-- info: 'CRNT.RationalFarkas.feasibleℝ_iff_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.RationalFarkas.feasibleℝ_iff_feasible
/-- info: 'CRNT.Network.massActionInjectiveOnClass_of_compressionSRSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionInjectiveOnClass_of_compressionSRSign

/-- info: 'ODE.SlowManifoldC1Seed.certified_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.SlowManifoldC1Seed.certified_reduction

/-- info: 'CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract
/-- info: 'CRNT.ExponentialDichotomy.mulVec_exp_smul_mapsTo_realStableSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ExponentialDichotomy.mulVec_exp_smul_mapsTo_realStableSubspace
/-- info: 'CRNT.Network.uRegionMatrix_pow_mulVec_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.uRegionMatrix_pow_mulVec_tendsto
/-- info: 'CRNT.Network.chartProjQ_mul_chartBasisQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.chartProjQ_mul_chartBasisQ
/-- info: 'CRNT.Network.gac_of_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_decide

/-- info: 'CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural

/-- info: 'ODE.GraphTransformData.manifold_dist_base_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.GraphTransformData.manifold_dist_base_le

/-- info: 'CRNT.ExponentialDecay.LyapunovCertificate.norm_exp_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ExponentialDecay.LyapunovCertificate.norm_exp_smul_le
/-- info: 'CRNT.Network.gac_of_deficiencyZero_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_deficiencyZero_decide

/-- info: 'CRNT.NetworkData.gac_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.gac_of_persistenceCertified

/-- info: 'CRNT.Network.gac_of_singleLinkage_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_singleLinkage_decide

/-- info: 'CRNT.Network.isPMatrix_massActionJacobian_box_of_pointIndep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isPMatrix_massActionJacobian_box_of_pointIndep

/-- info: 'CRNT.tendsto_poissonAverage_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.tendsto_poissonAverage_atTop

/-- info: 'CRNT.Examples.ConservationClassRegion.conservationClass_cmeRegionVec_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.ConservationClassRegion.conservationClass_cmeRegionVec_tendsto
/-- info: 'ODE.graphTransform_discrete_invariant_and_dist_le_contracting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.graphTransform_discrete_invariant_and_dist_le_contracting

/-- info: 'ODE.slowManifold_reduction_conjugacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.slowManifold_reduction_conjugacy

/-- info: 'ODE.equilibrium_lift_of_baseEquilibrium' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.equilibrium_lift_of_baseEquilibrium

/-- info: 'ODE.invariantSet_lift_of_baseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.invariantSet_lift_of_baseInvariant

/-- info: 'CRNT.Network.WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.WeaklyReversible.toricMassActionField_isStrictSupportField_of_activeWalls

/-- info: 'CRNT.Stochastic.variance_id_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_id_poissonMeasure

/-- info: 'CRNT.Stochastic.tendsto_meas_scaled_centered_poisson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_scaled_centered_poisson

/-- info: 'CRNT.Stochastic.variance_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate
/-- info: 'CRNT.eventually_localDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_localDegree_eq

/-- info: 'CRNT.regularDegree_comp_continuousLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_comp_continuousLinearMap

/-- info: 'CRNT.Stochastic.indepFun_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.indepFun_scaledClock

/-- info: 'CRNT.Stochastic.variance_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_scaledClock

/-- info: 'CRNT.Stochastic.variance_aggregate_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate_scaledClock

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate_scaledClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate_scaledClock
/-- info: 'CRNT.eventually_regularDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_regularDegree_eq

/-- info: 'CRNT.Stochastic.variance_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_centeredTimeChange

/-- info: 'CRNT.Stochastic.variance_aggregate_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.variance_aggregate_centeredTimeChange

/-- info: 'CRNT.Stochastic.tendsto_meas_aggregate_centeredTimeChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.tendsto_meas_aggregate_centeredTimeChange

/-- info: 'CRNT.Stochastic.exists_timeChanged_fluct_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Stochastic.exists_timeChanged_fluct_bound
/-- info: 'CRNT.eventually_confinement_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_confinement_of_isProperMap

/-- info: 'CRNT.eventually_regularDegree_eq_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.eventually_regularDegree_eq_of_isProperMap

/-- info: 'CRNT.isLocallyConstant_regularDegree_of_isProperMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.isLocallyConstant_regularDegree_of_isProperMap

/-- info: 'CRNT.regularDegree_param_eq_of_disjointCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_param_eq_of_disjointCover

/-- info: 'CRNT.regularDegree_homotopy_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.regularDegree_homotopy_invariant
/-- info: 'ODE.tendsto_flow_difference_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.tendsto_flow_difference_quotient

/-- info: 'ODE.hasDerivAt_flow_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.hasDerivAt_flow_initial
/-- info: 'ODE.tendsto_dist_slowManifold_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.tendsto_dist_slowManifold_zero

/-- info: 'ODE.asymptoticStability_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.asymptoticStability_lift

/-- info: 'CRNT.Network.separatingConfinement_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_local

/-- info: 'CRNT.Network.separatingConfinement_of_persistentFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_persistentFrom

/-- info: 'CRNT.Network.persistentFrom_of_omegaLimit_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistentFrom_of_omegaLimit_singleton

/-- info: 'CRNT.Network.persistentFrom_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistentFrom_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.separatingConfinement_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.separatingConfinement_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.genuineOrbit_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.genuineOrbit_unique

/-- info: 'CRNT.IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.IsPolyhedralFan.toricMassActionField_isStrictSupportField_of_inwardReactions

/-- info: 'CRNT.Network.gac_of_gacCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_gacCertificate

/-- info: 'CRNT.Network.gacCertificate_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gacCertificate_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.omegaLimit_eq_singleton_of_comparableGrowthDescent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.omegaLimit_eq_singleton_of_comparableGrowthDescent

/-- info: 'CRNT.Network.eq_of_periodic_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.eq_of_periodic_solution

/-- info: 'CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.siphonFacet_floor_of_nearFacet_dissipation

/-- info: 'CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.computeNumTerminalSLC_eq_numTerminalSLC

/-- info: 'CRNT.Network.numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.numDiagonalDriveSpecies_eq_card_iff

/-- info: 'CRNT.hopfBoundaryQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.hopfBoundaryQ_cast

/-- info: 'CRNT.Network.hopfBoundaryMarginQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hopfBoundaryMarginQ_cast

/-- info: 'CRNT.NetworkData.analyze_numTerminalSLC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_numTerminalSLC_eq

/-- info: 'CRNT.NetworkData.analyze_numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_numDiagonalDriveSpecies_eq_card_iff

/-- info: 'CRNT.NetworkData.analyze_hopfBoundaryMargin_eq_none_of_ne_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_hopfBoundaryMargin_eq_none_of_ne_three

/-- info: 'CRNT.measure_criticalValues_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.measure_criticalValues_eq_zero

/-- info: 'CRNT.dense_regularValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.dense_regularValues

/-- info: 'CRNT.Network.exists_isMassActionSteadyState_of_reducedDegree_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_isMassActionSteadyState_of_reducedDegree_ne_zero

/-- info: 'CRNT.Network.hasMultistationarityCapacity_of_signIndefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasMultistationarityCapacity_of_signIndefinite

/-- info: 'CRNT.Network.exists_compatible_pair_sameSign_logRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_compatible_pair_sameSign_logRatio

/-- info: 'CRNT.gershgorinRowValueQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.gershgorinRowValueQ_cast

/-- info: 'CRNT.Network.gershgorinStabilityMarginQ_hurwitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gershgorinStabilityMarginQ_hurwitz

/-- info: 'CRNT.NetworkData.analyze_gershgorinStabilityMargin_eq_none_of_zero_species' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_gershgorinStabilityMargin_eq_none_of_zero_species

/-- info: 'CRNT.gershgorinColValueQ_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.gershgorinColValueQ_cast

/-- info: 'CRNT.Network.gershgorinColStabilityMarginQ_hurwitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gershgorinColStabilityMarginQ_hurwitz

/-- info: 'CRNT.NetworkData.analyze_gershgorinColStabilityMargin_eq_none_of_zero_species' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.analyze_gershgorinColStabilityMargin_eq_none_of_zero_species

/-!
## Oscillation exclusion theorems

These four were `by sorry` in the previous core (`CRNT/Oscillation/Exclusion.lean` and
`LowRank.lean` were two-line stub files), and `CRNT.Oscillation.KineticBasic` defined its three
predicates as `True`.  The oscillation expansion replaced all of that with real proofs, and the
analyzer's `noPositivePeriodicOrbitCertified` flag routes through them, so they are pinned here:
if any of them regresses to `sorry`, `sorryAx` shows up and this test fails.
-/

/-- info: 'CRNT.Network.neverPositivePeriodic_of_weaklyReversible_deficiencyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.neverPositivePeriodic_of_weaklyReversible_deficiencyZero

/-- info: 'CRNT.Network.neverPositivePeriodic_of_stoichRank_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.neverPositivePeriodic_of_stoichRank_le_one

/-- info: 'CRNT.Network.not_oscillatoryCapacity_of_stoichRank_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.not_oscillatoryCapacity_of_stoichRank_le_one

/-- info: 'CRNT.NetworkData.neverPositivePeriodic_of_analyze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.neverPositivePeriodic_of_analyze

/-!
## Analyzer verdicts that produce proofs

Each of these turns a decidable Boolean into a mathematical conclusion, so each is a place where a
hollow definition would become an unconditional-looking theorem.  Pinning them means a regression in
any dependency shows up here rather than in a downstream consumer.
-/

/-- info: 'CRNT.NetworkData.gac_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.gac_of_persistenceCertified

/-- info: 'CRNT.NetworkData.certifiedHypotheses_of_persistenceCertified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.certifiedHypotheses_of_persistenceCertified

/-- info: 'CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NetworkData.hasNoCriticalSiphon_of_persistenceStructural

/-!
## Global persistence: the previously-hollow layer

Every result below lives in a module that used to consist of `:= True` definitions, `dummy : True`
certificates and `isTrue` deciders.  `scripts/check_stubs.py` now reports zero hollow definitions,
but a syntactic check cannot tell whether a definition carries its *intended* meaning -- so these
pins exist to make any regression in the layer show up as an axiom change rather than as a silently
weaker theorem.

`isDrainable_iff_feasible_negativeFluxSystem` and its self-replicable twin are the two that matter
most: they are what replaced `def HasNoDrainableSiphon : Prop := ∃ (_ : Unit), True` together with
its `isTrue` decider, and they are what the analyzer's `noDrainableSiphon` flag now reduces through.
-/

/-- info: 'CRNT.Network.isDrainable_iff_feasible_negativeFluxSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isDrainable_iff_feasible_negativeFluxSystem

/-- info: 'CRNT.Network.isSelfReplicable_iff_feasible_positiveFluxSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isSelfReplicable_iff_feasible_positiveFluxSystem

/-- info: 'CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon

/-- info: 'CRNT.Network.gac_of_structurallyPersistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_structurallyPersistent

/-- info: 'CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon

/-- info: 'CRNT.Network.boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.boundaryOmegaExcludedForFlow_of_hasNoDrainableSiphon

/-- info: 'CRNT.Network.permanentForFlow_of_entry_and_uniform_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.permanentForFlow_of_entry_and_uniform_bounds

/-- info: 'CRNT.Network.everyTierSequenceHasScaleDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.everyTierSequenceHasScaleDecomposition

/-!
## The two hole chains: full transitive axiom audit

The pins above are a hand-picked list, so they can only ever check what somebody remembered to
add.  The two chains that still contain a `sorry` are checked here *exhaustively* instead: the
`#crnt_axiom_audit` command below walks the entire transitive constant-dependency closure of each
hole and reports every axiom set that occurs.  A declaration nobody thought to pin still shows up,
because the walk starts from the hole and follows the environment, not a list.

Design notes, since a walk this size is easy to get subtly wrong:

* The closure is built with an explicit stack and an `ST`-backed seen set.  A `List`-based walk with
  `Array.contains` is quadratic and does not terminate in reasonable time over this environment.
* Dependencies are pushed *after* a constant is popped, so in the resulting array every dependency
  appears strictly later than its dependent.  One reverse pass therefore suffices to propagate axiom
  sets -- no topological sort, and no per-theorem re-walk of the environment.
* Axioms are attributed to a constant when the constant *is* an axiom or when its value expression
  mentions one.  `.thmInfo` and `.defnInfo` values are walked; `.opaqueInfo` values are too, which
  is stricter than Lean's own `#print axioms` and can only report more, never less.

Run standalone with:
    lake env lean test/AxiomAudit.lean
-/

/-!
## The two hole chains: pinned

The pins above are a hand-picked list, so they only ever check what somebody remembered to add.
These extend that to the two hole chains (chain B is now closed and pinned clean), by pinning every theorem on each
chain that a consumer is most likely to reach through.

The axiom set recorded for each is **exactly** `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, nothing else. So a hole is the *only* way for taint to enter these chains, and a
regression anywhere upstream shows up as an axiom-set change on one of these names.

Chain A is Craciun v3 Theorem B (the residual obligation of the Global Attractor Theorem); chain B
is Shinar--Feinberg (the true-chemistry strong-concordance criterion).
-/

open Filter
open scoped NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

section ChainA

/-- info: 'CRNT.Network.highCodimension_of_not_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.highCodimension_of_not_facet

/-- info: 'CRNT.Network.persistentFrom_of_upperRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistentFrom_of_upperRegion

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_upperRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_upperRegion

/-- info: 'CRNT.Network.hsep_fails_of_boundaryPoint_mem_sublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hsep_fails_of_boundaryPoint_mem_sublevel

/-- info: 'CRNT.Network.barrier_le_of_mem_omegaLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.barrier_le_of_mem_omegaLimit

/-- info: 'CRNT.Network.not_persistentFrom_of_mem_omegaLimit_notPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.not_persistentFrom_of_mem_omegaLimit_notPositive

/-- info: 'CRNT.Network.omegaPoint_zeroSet_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.omegaPoint_zeroSet_trichotomy

/-- info: 'CRNT.Network.hface_of_trichotomyThird' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hface_of_trichotomyThird

/-- info: 'CRNT.Network.comparableGrowthDescent_iff_omegaPointPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.comparableGrowthDescent_iff_omegaPointPositive

/-- info: 'CRNT.Network.isInclusionSolutionOn_massAction_relativeSourceOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isInclusionSolutionOn_massAction_relativeSourceOrder

/-- info: 'CRNT.Network.relativeSourceOrderNegativeStoichFan_isPolyhedralFan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relativeSourceOrderNegativeStoichFan_isPolyhedralFan

end ChainA

section ChainB

/-- info: 'CRNT.Network.fullyOpen_trueSRCriterion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.fullyOpen_trueSRCriterion_iff

/-- info: 'CRNT.Network.TrueSRCycle.sCycleNet_iff_sCycle_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.TrueSRCycle.sCycleNet_iff_sCycle_of_separated

/-- info: 'CRNT.Network.TrueSRCycle.no_strict_gain_net'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.TrueSRCycle.no_strict_gain_net'

/-- info: 'CRNT.Network.nonAdjacent_cycleClassFlux_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.nonAdjacent_cycleClassFlux_eq_zero

/-- info: 'CRNT.Network.no_degree_two_aggregate_causal_cycle_of_offCycle_hrest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.no_degree_two_aggregate_causal_cycle_of_offCycle_hrest

/-- info: 'CRNT.Network.sharpened_source_inequality_at_cycle_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sharpened_source_inequality_at_cycle_separator

/-- info: 'CRNT.Network.exists_positive_off_cycle_aggregate_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_off_cycle_aggregate_class

/-- info: 'CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyReversible

/-- info: 'CRNT.Network.injective_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.injective_of_trueSRCriterion

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion_bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion_bc

end ChainB

/-!
## The former Global Attractor hole, pinned clean

Both holes are closed.  The true-SR hole (chain B) by the Banaji--Craciun determinant route
(`CRNT/Multistationarity/BCFullyOpen.lean`); the GAC residual
`exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex` by the persistence route
`CRNT/Persistence/` (`Network.complexBalanced_forward_floor`: bounded complex-balanced
trajectories have a positive coordinate floor, via a zero-separating polyhedral region).  No
`sorryAx` is expected anywhere; these pins fail if one reappears.
-/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex

/-- info: 'CRNT.Network.three_le_stoichRank_of_nonVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.three_le_stoichRank_of_nonVertex

/-- info: 'CRNT.Network.false_of_vertex_omegaPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.false_of_vertex_omegaPoint

/-- info: 'CRNT.PlanarZSH.Rays.exists_polygon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PlanarZSH.Rays.exists_polygon

/-- info: 'CRNT.PlanarZSH.Rays.exists_trapping_polygon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PlanarZSH.Rays.exists_trapping_polygon

/-- info: 'CRNT.PlanarZSH.Rays.pair_ge_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PlanarZSH.Rays.pair_ge_of_good

/-- info: 'CRNT.Network.inner_nonneg_of_sourceOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_nonneg_of_sourceOrder

/-- info: 'CRNT.Network.transversal_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.transversal_descent

/-- info: 'CRNT.Network.local_codimTwo_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.local_codimTwo_trap

/-- info: 'CRNT.Network.forall_complexBalanced_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.forall_complexBalanced_iff

/-- info: 'CRNT.Network.weaklyReversible_and_deficiencyZero_of_forall_complexBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_and_deficiencyZero_of_forall_complexBalanced

/-- info: 'CRNT.Network.kineticSubspace_eq_stoichSubspace_of_numTerminalSLC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.kineticSubspace_eq_stoichSubspace_of_numTerminalSLC

/-- info: 'CRNT.Network.kineticSubspace_eq_stoichSubspace_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.kineticSubspace_eq_stoichSubspace_of_weaklyReversible

/-- info: 'CRNT.Network.span_complexMonomialVector_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.span_complexMonomialVector_eq_top

/-- info: 'CRNT.Network.deficiencyZero_not_weaklyReversible_no_positive_steadyState_or_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.deficiencyZero_not_weaklyReversible_no_positive_steadyState_or_cycle

/-- info: 'CRNT.Network.weaklyReversible_of_deficiencyZero_of_cyclic_trajectory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_of_deficiencyZero_of_cyclic_trajectory

/-- info: 'CRNT.Network.positiveSteadyState_iff_logRatio_mem_orthStoich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.positiveSteadyState_iff_logRatio_mem_orthStoich

/-- info: 'CRNT.Network.isComplexBalanced_of_positive_steadyState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isComplexBalanced_of_positive_steadyState

/-- info: 'CRNT.Network.isSiphon_iff_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isSiphon_iff_of_weaklyReversible

/-- info: 'CRNT.Network.meets_iff_of_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.meets_iff_of_linked

/-- info: 'CRNT.Network.eq_of_periodic_solution_of_complexBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.eq_of_periodic_solution_of_complexBalanced

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent_of_codimTwoCriticalSiphonsAreVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent_of_codimTwoCriticalSiphonsAreVertices

/-- info: 'CRNT.Network.complexBalanced_trajectory_converges_of_codimTwoCriticalSiphonsAreVertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_trajectory_converges_of_codimTwoCriticalSiphonsAreVertices

/-- info: 'CRNT.Network.codimTwoCriticalSiphonsAreVertices_of_stoichRank_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.codimTwoCriticalSiphonsAreVertices_of_stoichRank_le_two

/-- info: 'CRNT.Network.gac_of_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.gac_of_firstOrder

/-- info: 'CRNT.Network.hasNoCriticalSiphon_of_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasNoCriticalSiphon_of_firstOrder

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent_of_stoichRank_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent_of_stoichRank_le_two

/-- info: 'CRNT.Network.complexBalanced_trajectory_converges_of_stoichRank_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_trajectory_converges_of_stoichRank_le_two

/-- info: 'CRNT.Network.exists_massAction_realization_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_massAction_realization_iff

/-- info: 'CRNT.Network.exists_massAction_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_massAction_realization

/-- info: 'CRNT.Network.negTerm_contains_of_massAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.negTerm_contains_of_massAction

/-- info: 'CRNT.Examples.CatalyticChain.globalAttractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.CatalyticChain.globalAttractor

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_permanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor

/-!
## The newest wave of modules, pinned module by module

The sections above are the historical audit trail; the pins below are the ones for the modules
added most recently, grouped by module in the order the modules landed.  They follow the same
convention as the rest of this file: one `#guard_msgs`-pinned `#print axioms` per headline
declaration, so that a `sorry` (or any other axiom) creeping into a dependency of any of these
shows up as a failing build rather than as a silently weaker theorem.

Every module below is reachable from `import CRNT` (the root module imports all of them), so no
extra `import` line is needed here.
-/

/-! ### `CRNT/Dynamics/HopfAveraging.lean` -/

/-- info: 'CRNT.Hopf.radialDrift_normalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.radialDrift_normalForm

/-- info: 'CRNT.Hopf.truncatedFullRadialField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.truncatedFullRadialField

/-- info: 'CRNT.Hopf.averagedRadialField_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.averagedRadialField_amplitude

/-! ### `CRNT/Dynamics/NormalFormCubic.lean` -/

/-- info: 'CRNT.Hopf.cubic_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.cubic_normal_form

/-- info: 'CRNT.Hopf.cubic_normal_form_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.cubic_normal_form_cubic

/-- info: 'CRNT.Hopf.homologicalQuad_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.homologicalQuad_solution

/-- info: 'CRNT.Hopf.homologicalQuad_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.homologicalQuad_unique

/-! ### `CRNT/Dynamics/HopfLyapunovCalibration.lean` -/

/-- info: 'CRNT.Hopf.classical_lyapunov_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.classical_lyapunov_formula

/-- info: 'CRNT.Hopf.hopf_lyapunov_calibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.hopf_lyapunov_calibration

/-- info: 'CRNT.Hopf.cubicCombination_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Hopf.cubicCombination_eq

/-! ### `CRNT/Dynamics/LaSalleConvergence.lean` -/

/-- info: 'CRNT.converges_of_lasalle_of_stronglyMonotoneOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.converges_of_lasalle_of_stronglyMonotoneOperator

/-- info: 'CRNT.massAction_converges_of_lasalle_of_stronglyMonotoneOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.massAction_converges_of_lasalle_of_stronglyMonotoneOperator

/-! ### `CRNT/Dynamics/OmegaLimitOrderConvex.lean` -/

/-- info: 'CRNT.omegaLimit_orderConvex_of_stronglyMonotoneOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.omegaLimit_orderConvex_of_stronglyMonotoneOperator

/-- info: 'CRNT.converges_of_lasalle_of_stronglyMonotoneOperator_of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.converges_of_lasalle_of_stronglyMonotoneOperator_of_monotone

/-! ### `CRNT/Dynamics/EscapeDirection.lean` -/

/-- info: 'CRNT.Network.escape_in_orthogonalComplement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.escape_in_orthogonalComplement

/-- info: 'CRNT.Network.no_escape_of_positive_conservation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.no_escape_of_positive_conservation_law

/-- info: 'CRNT.Network.persistenceConjectureStrong_of_positive_conservation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistenceConjectureStrong_of_positive_conservation_law

/-! ### `CRNT/Dynamics/TikhonovLocal.lean` -/

/-- info: 'CRNT.tikhonov_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.tikhonov_local

/-- info: 'CRNT.tikhonov_local_attraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.tikhonov_local_attraction

/-- info: 'CRNT.exists_local_slow_manifold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.exists_local_slow_manifold

/-- info: 'CRNT.hurwitz_linear_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.hurwitz_linear_decay

/-! ### `CRNT/Stochastic/ExitMass.lean` -/

/-- info: 'CRNT.JumpSystem.exitMass_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.JumpSystem.exitMass_factor

/-- info: 'CRNT.JumpSystem.outsideMassENN_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.JumpSystem.outsideMassENN_factor

/-! ### `CRNT/Stochastic/EndotacticPositiveRecurrence.lean` -/

/-- info: 'CRNT.Network.positiveRecurrence_of_linearLyapunovData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.positiveRecurrence_of_linearLyapunovData

/-- info: 'CRNT.Network.foster_hitting_time_of_linearLyapunovData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.foster_hitting_time_of_linearLyapunovData

/-! ### `CRNT/Stochastic/EndotacticTierPositiveRecurrence.lean` -/

/-- info: 'CRNT.Network.tier_positiveRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tier_positiveRecurrence

/-- info: 'CRNT.Network.tier_nonExplosion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tier_nonExplosion

/-- info: 'CRNT.Network.tier_geometricErgodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tier_geometricErgodic

/-! ### `CRNT/Stochastic/EndotacticTierDomination.lean` -/

/-- info: 'CRNT.Network.tierBalanceDrift_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tierBalanceDrift_le_of

/-- info: 'CRNT.Network.tierBalance_positiveRecurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tierBalance_positiveRecurrence

/-- info: 'CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate

/-! ### `CRNT/Stochastic/CLTWeak.lean` -/

/-- info: 'CRNT.Network.multivariate_clt_open_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.multivariate_clt_open_weak

/-- info: 'CRNT.Network.fluctuation_uniform_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.fluctuation_uniform_concentration

/-! ### `CRNT/Multistationarity/DegreeExistence.lean` -/

/-- info: 'CRNT.Network.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero

/-! ### `CRNT/Multistationarity/DegreeStructural.lean` -/

/-- info: 'CRNT.Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage

/-- info: 'CRNT.Network.exists_positiveSteadyState_of_positive_reducedDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positiveSteadyState_of_positive_reducedDet

/-! ### `CRNT/Multistationarity/DegreeMultistationarity.lean` -/

/-- info: 'CRNT.Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree

/-! ### `CRNT/Multistationarity/DeficiencyOneAlgorithm.lean` -/

/-- info: 'CRNT.Network.hasMultistationarityCapacity_iff_doaFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasMultistationarityCapacity_iff_doaFeasible

/-- info: 'CRNT.Network.oneRxn_doaFeasible_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_doaFeasible_iff

/-! ### `CRNT/Multistationarity/AdvancedDeficiencyAlgorithm.lean` -/

/-- info: 'CRNT.Network.hasMultistationarityCapacity_iff_adaFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasMultistationarityCapacity_iff_adaFeasible

/-- info: 'CRNT.Network.adaFeasible_implies_adaAffirmsCapacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.adaFeasible_implies_adaAffirmsCapacity

/-! ### `CRNT/Multistationarity/TwoReactionAtoms.lean` -/

/-- info: 'CRNT.Network.twoRxnOpen_isAtom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.twoRxnOpen_isAtom_iff

/-! ### `CRNT/Multistationarity/MultistationarityRegion.lean` -/

/-- info: 'CRNT.Network.rankOne_multistationary_iff_det_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.rankOne_multistationary_iff_det_pos

/-- info: 'CRNT.Network.isOpen_multistationarityRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isOpen_multistationarityRegion

/-! ### `CRNT/Equilibria/SingletonSource.lean` -/

/-- info: 'CRNT.Network.singletonSource_steadyState_iff_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.singletonSource_steadyState_iff_linear

/-- info: 'CRNT.Network.singletonSource_no_exactly_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.singletonSource_no_exactly_two

/-- info: 'CRNT.Network.singletonSource_linearInvariant_iff_rowSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.singletonSource_linearInvariant_iff_rowSpace

/-! ### `CRNT/Equilibria/ToricParametrization.lean` -/

/-- info: 'CRNT.Network.toric_positiveSteadyStates_eq_parametrization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.toric_positiveSteadyStates_eq_parametrization

/-- info: 'CRNT.Network.steadyStateInvariant_iff_log_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.steadyStateInvariant_iff_log_orthogonal

/-! ### `CRNT/Extensions/NonIsothermal.lean` -/

/-- info: 'CRNT.NonIsothermal.isothermal_species_eq_massAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NonIsothermal.isothermal_species_eq_massAction

/-- info: 'CRNT.NonIsothermal.temperatureEquation_eq_neg_sum_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.NonIsothermal.temperatureEquation_eq_neg_sum_heat

/-! ### `CRNT/Extensions/DelaySemistability.lean` -/

/-- info: 'CRNT.Network.delay_semistability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delay_semistability

/-- info: 'CRNT.Network.delay_limit_isSteadyState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delay_limit_isSteadyState

/-! ### `CRNT/Extensions/ReactionDiffusion.lean` -/

/-- info: 'CRNT.ReactionDiffusion.exists_reactionDiffusion_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ReactionDiffusion.exists_reactionDiffusion_solution

/-- info: 'CRNT.ReactionDiffusion.brusselator_turing_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ReactionDiffusion.brusselator_turing_instance

/-! ### `CRNT/Design/GeneralPlantRPA.lean` -/

/-- info: 'CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_setpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_setpoint

/-- info: 'CRNT.Design.GeneralPlant.ergodic_of_fosterDrift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Design.GeneralPlant.ergodic_of_fosterDrift

/-! ### `CRNT/Oscillation/PlanarOscillationCriterion.lean` -/

/-- info: 'CRNT.Oscillation.periodicSolution_constant_of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Oscillation.periodicSolution_constant_of_monotone

/-- info: 'CRNT.Oscillation.Network.neverPositivePeriodic_of_cooperative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Oscillation.Network.neverPositivePeriodic_of_cooperative

/-! ### `CRNT/Oscillation/TrappingRegion.lean` -/

/-- info: 'CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion

/-! ### `CRNT/Oscillation/MinimalSetClassification.lean` -/

/-- info: 'CRNT.Planar.omegaSet_no_nonregular_minimal_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Planar.omegaSet_no_nonregular_minimal_subset

/-! ### `CRNT/Algebra/CircuitDescartes.lean` -/

/-- info: 'CRNT.CircuitDescartes.card_zeros_exp_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.CircuitDescartes.card_zeros_exp_sum_le

/-- info: 'CRNT.Circuit.card_circuit_solutions_le_signVariations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Circuit.card_circuit_solutions_le_signVariations

/-! ### `CRNT/Algebra/TropicalReduction.lean` -/

/-- info: 'CRNT.Network.tropicalReduced_species_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.tropicalReduced_species_eq

/-- info: 'CRNT.Network.leadingSystem_eq_reduced_of_equilibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.leadingSystem_eq_reduced_of_equilibration

/-! ### `CRNT/Computation/PiecewiseNatAffine.lean` -/

/-- info: 'CRNT.Computation.not_piecewiseNatAffine_pow2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Computation.not_piecewiseNatAffine_pow2

/-- info: 'CRNT.Computation.affineCRN_stablyComputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Computation.affineCRN_stablyComputes

/-! ### `CRNT/Deficiency/DeficiencyOneAlgorithmCorrectness.lean` -/

/-- info: 'CRNT.Network.doaRun_hasMultistationarityCapacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.doaRun_hasMultistationarityCapacity

/-- info: 'CRNT.Network.det_pos_of_negZMatrix_of_pos_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.det_pos_of_negZMatrix_of_pos_mulVec

/-- info: 'CRNT.Network.sourceDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sourceDegree

/-- info: 'CRNT.Network.massActionLipschitzConstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionLipschitzConstant

/-- info: 'CRNT.Network.massActionLipschitzConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionLipschitzConstant_nonneg

/-- info: 'CRNT.Network.massActionVectorField_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionVectorField_fderiv

/-- info: 'CRNT.Network.abs_massActionMonomialGrad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.abs_massActionMonomialGrad_le

/-- info: 'CRNT.Network.sum_abs_massActionMonomialGrad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sum_abs_massActionMonomialGrad_le

/-- info: 'CRNT.Network.massActionJacobianCLM_apply_sum_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianCLM_apply_sum_coordinate

/-- info: 'CRNT.Network.massActionJacobianConstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianConstant

/-- info: 'CRNT.Network.massActionJacobianConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianConstant_nonneg

/-- info: 'CRNT.Network.massActionJacobianCLM_norm_le_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianCLM_norm_le_aux

/-- info: 'CRNT.Network.massActionJacobianConstant_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianConstant_le

/-- info: 'CRNT.Network.massActionJacobianCLM_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianCLM_norm_le

/-- info: 'CRNT.Network.massActionVectorField_nnnorm_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionVectorField_nnnorm_fderiv_le

/-- info: 'CRNT.Network.massActionVectorField_lipschitzOnWith_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionVectorField_lipschitzOnWith_closedBall

/-- A nonlinear two-species mass-action field is covered by the local Lipschitz theorem. -/
example : ∃ L : ℝ≥0, LipschitzOnWith L
    (CRNT.Network.twoSpeciesDegradation.massActionVectorField CRNT.Network.twoSpeciesDegradationRates)
    (Metric.closedBall (0 : CRNT.Concentration (Fin 2)) 1) := by
  exact ⟨Real.toNNReal (CRNT.Network.massActionLipschitzConstant CRNT.Network.twoSpeciesDegradation
    CRNT.Network.twoSpeciesDegradationRates 1),
    CRNT.Network.massActionVectorField_lipschitzOnWith_closedBall CRNT.Network.twoSpeciesDegradation
      CRNT.Network.twoSpeciesDegradationRates 1⟩
/-- info: 'CRNT.Network.delayField_coord_mono_of_singleSpeciesSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_coord_mono_of_singleSpeciesSources

/-- info: 'CRNT.Dynamics.delay_comparison_step_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Dynamics.delay_comparison_step_local

/-- info: 'CRNT.Dynamics.delay_comparison_subsolution_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Dynamics.delay_comparison_subsolution_local

/-- info: 'CRNT.Network.currentConsumptionVectorField_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.currentConsumptionVectorField_apply

/-- info: 'CRNT.Network.massActionDelayField_eq_delayedProduction_add_consumption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_eq_delayedProduction_add_consumption

/-- info: 'CRNT.Network.massActionDelayField_lipschitzOnWith_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_lipschitzOnWith_closedBall

/-- info: 'CRNT.Network.massActionDelayField_currentConsumption_coord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_currentConsumption_coord_eq

/-- info: 'CRNT.Network.massActionDelayField_kamke_of_singleSpeciesSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_kamke_of_singleSpeciesSources

/-- info: 'CRNT.Network.massActionDelayField_monotoneDelayed_of_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_monotoneDelayed_of_nonnegative

/-- info: 'CRNT.Network.boundedNonnegativeConcentrationRegion_sup_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.boundedNonnegativeConcentrationRegion_sup_closed

/-- info: 'CRNT.Network.delay_comparison_massAction_commonDelay_singleSpeciesSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delay_comparison_massAction_commonDelay_singleSpeciesSources

/-- info: 'CRNT.Network.delayField_coord_nonneg_of_current_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_coord_nonneg_of_current_zero

/-- info: 'CRNT.Dynamics.forwardInvariant_nonnegOrthant_step_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Dynamics.forwardInvariant_nonnegOrthant_step_on

/-- info: 'CRNT.Network.delayedProductionByReaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayedProductionByReaction

/-- info: 'CRNT.Network.massActionDelayField_eq_delayedProductionByReaction_add_consumption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_eq_delayedProductionByReaction_add_consumption

/-- info: 'CRNT.Network.massActionDelayField_lipschitzOnWith_closedBall_byReaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_lipschitzOnWith_closedBall_byReaction

/-- info: 'CRNT.Network.instantaneousDelayNetwork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.instantaneousDelayNetwork

/-- info: 'CRNT.Network.instantaneousDelayRates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.instantaneousDelayRates

/-- info: 'CRNT.Network.massActionDelayField_eq_instantaneousDelayNetwork_add_delayedProduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_eq_instantaneousDelayNetwork_add_delayedProduction

/-- info: 'CRNT.Network.massActionDelayField_lipschitzOnWith_zeroDelaySplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_lipschitzOnWith_zeroDelaySplit

/-- info: 'CRNT.Network.massActionDelayField_coord_nonneg_of_current_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelayField_coord_nonneg_of_current_zero

/-- info: 'CRNT.Network.delayField_nonneg_on_interval_of_nonneg_delayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_on_interval_of_nonneg_delayed

/-- info: 'CRNT.Network.delayField_nonneg_on_methodStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_on_methodStep

/-- info: 'CRNT.Network.delayField_nonneg_on_interval_of_nonneg_positive_delayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_on_interval_of_nonneg_positive_delayed

/-- info: 'CRNT.Network.delayField_nonneg_on_mixed_methodStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_on_mixed_methodStep

/-- info: 'CRNT.Network.delayField_nonneg_of_positive_delays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_of_positive_delays

/-- info: 'CRNT.Network.delayField_nonneg_of_nonnegative_delays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayField_nonneg_of_nonnegative_delays

/-- info: 'CRNT.Network.delay_comparison_massAction_commonDelay_singleSpeciesSources_of_nonnegative_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delay_comparison_massAction_commonDelay_singleSpeciesSources_of_nonnegative_history

/-- info: 'CRNT.Network.massActionDelay_local_exists_of_delayGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_local_exists_of_delayGap

/-- info: 'CRNT.Network.massActionDelay_exists_positive_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_exists_positive_step

/-- info: 'CRNT.Network.massActionDelay_local_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_local_exists

/-- info: 'CRNT.Network.massActionDelay_local_exists_nonneg_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_local_exists_nonneg_history

/-- info: 'CRNT.Network.massActionDelay_firstStep_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_firstStep_unique

/-- info: 'CRNT.Network.massActionDelay_solution_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_solution_unique

/-- info: 'CRNT.Network.delayConservedQuantity_hasDerivWithinAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayConservedQuantity_hasDerivWithinAt

/-- info: 'CRNT.Network.delayConservedQuantity_antitone_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayConservedQuantity_antitone_on

/-- info: 'CRNT.Network.delayConservedQuantity_coord_bound_on_of_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayConservedQuantity_coord_bound_on_of_antitone

/-- info: 'CRNT.Network.delayConservedQuantity_norm_bound_on_of_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.delayConservedQuantity_norm_bound_on_of_antitone

/-- info: 'CRNT.Network.massActionDelay_weighted_loss_first_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_weighted_loss_first_step

/-- info: 'CRNT.Network.massActionDelay_weighted_loss_restart_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_weighted_loss_restart_step

/-- info: 'CRNT.Network.massActionDelay_weighted_loss_finite_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_weighted_loss_finite_steps

/-- info: 'CRNT.Network.massActionDelay_weighted_loss_global_from_first_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_weighted_loss_global_from_first_step

/-- info: 'CRNT.Network.massActionDelay_global_exists_of_weighted_subconservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_global_exists_of_weighted_subconservation

/-- info: 'CRNT.Network.massActionDelay_global_exists_of_positive_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionDelay_global_exists_of_positive_conservation

/-- info: 'CRNT.Examples.DelayedQuadraticDecay.strict_weight_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.DelayedQuadraticDecay.strict_weight_loss

/-- info: 'CRNT.Examples.DelayedQuadraticDecay.delayed_global_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.DelayedQuadraticDecay.delayed_global_exists
