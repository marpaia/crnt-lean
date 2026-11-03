import CRNT.Dynamics.ToricBarrierTrapping
import CRNT.Dynamics.FaceDirectionCone
import CRNT.Dynamics.ToricBarrierExplicit
import CRNT.Dynamics.OrbitRegularity
import CRNT.Dynamics.FaceCodimension
import CRNT.Geometry.ConvexBarrierObstruction

/-!
# Axiom-cleanliness regression guard for the GAC descent chain

`test/AxiomAudit.lean` imports all of `CRNT`, which takes hours to build.  This file guards the
same property for just the modules added while narrowing the Global Attractor hole, so it can be
built and run on its own in a few seconds:

```
python3 scripts/offline_build.py test.ToricBarrierAudit
```

Every declaration below must audit as `[propext, Classical.choice, Quot.sound]`.  If any of them
ever acquires `sorryAx` — for instance because someone routes one of them through the remaining
obligation in `CRNT.Dynamics.HighCodimensionSiphonFace` — `#guard_msgs` makes the build fail.

`(whitespace := lax)` makes the comparison insensitive to how long names wrap.
-/

/-! ### The face-codimension dichotomy -/

/-- info: 'CRNT.Network.highCodimension_of_not_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.highCodimension_of_not_facet

/-- info: 'CRNT.Network.ker_finrank_ne_of_face_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.ker_finrank_ne_of_face_point

/-- info: 'CRNT.Network.facet_of_singleton_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.facet_of_singleton_witness

/-- info: 'CRNT.Network.two_le_card_of_not_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.two_le_card_of_not_facet

/-! ### The polyhedral barrier engine -/

/-- info: 'CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_at_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_at_level

/-- info: 'CRNT.PolyhedralBarrier.barrier_le_of_local_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.barrier_le_of_local_descent

/-- info: 'CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent

/-- info: 'CRNT.PolyhedralBarrier.forwardInvariant_minMaxSublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.forwardInvariant_minMaxSublevel

/-! ### Fan axioms, the δ-core, and the descent bridge -/

/-- info: 'CRNT.deltaCore_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.deltaCore_mem

/-- info: 'CRNT.inner_nonneg_of_mem_toricField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.inner_nonneg_of_mem_toricField

/-- info: 'CRNT.forwardInvariant_barrier_toricInclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.forwardInvariant_barrier_toricInclusion

/-- info: 'CRNT.Network.euclideanMassActionField_mem_toricField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.euclideanMassActionField_mem_toricField

/-- info: 'CRNT.Network.inner_euclideanMassActionField_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_euclideanMassActionField_nonneg

/-! ### Transport and the blueprint reduction -/

/-- info: 'CRNT.Network.hasDerivAt_euclideanStoichState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasDerivAt_euclideanStoichState

/-- info: 'CRNT.Network.minMaxBarrier_le_of_toric_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.minMaxBarrier_le_of_toric_descent

/-- info: 'CRNT.Network.coordinate_lower_bounds_of_toric_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coordinate_lower_bounds_of_toric_barrier

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_toric_blueprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_toric_blueprint

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_toric_halfspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_toric_halfspace

/-! ### The convex-barrier obstruction -/

/-- info: 'CRNT.ConvexBarrierObstruction.not_exists_weights_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ConvexBarrierObstruction.not_exists_weights_vector

/-! ### Face localization -/

/-- info: 'CRNT.Network.relativeLogFanState_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relativeLogFanState_eq

/-- info: 'CRNT.Network.sum_smul_mem_faceDirectionCone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sum_smul_mem_faceDirectionCone

/-- info: 'CRNT.Network.relativeLogFanState_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relativeLogFanState_eq_add

/-- info: 'CRNT.Network.infDist_relativeLogFanState_faceDirectionCone_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.infDist_relativeLogFanState_faceDirectionCone_le

/-- info: 'CRNT.Network.exists_dist_lt_faceDirectionCone_of_infDist_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_dist_lt_faceDirectionCone_of_infDist_lt

/-! ### The face-relevant core and the static criterion -/

/-- info: 'CRNT.subfanCore_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.subfanCore_mem

/-- info: 'CRNT.Network.faceRelevantCore_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.faceRelevantCore_mem

/-- info: 'CRNT.Network.mem_of_mem_faceRelevantCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.mem_of_mem_faceRelevantCore

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_faceRelevantCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_faceRelevantCore

/-! ### Angular tiles and the multi-tile criterion -/

/-- info: 'CRNT.Network.relativeLogFanState_eq_faceLogPart_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relativeLogFanState_eq_faceLogPart_add

/-- info: 'CRNT.Network.dist_relativeLogFanState_faceLogPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.dist_relativeLogFanState_faceLogPart

/-- info: 'CRNT.Network.relevantCore_le_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relevantCore_le_of_subset

/-- info: 'CRNT.Network.mem_relevantCones_of_infDist_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.mem_relevantCones_of_infDist_lt

/-- info: 'CRNT.Network.relevantCore_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relevantCore_mem

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_tiled_faceCores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_tiled_faceCores

/-! ### Explicit concentration-space form -/

/-- info: 'CRNT.Network.inner_euclideanStoichStateL_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_euclideanStoichStateL_eq_sum

/-- info: 'CRNT.Network.inner_faceLogPart_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_faceLogPart_eq_sum

/-- info: 'CRNT.Network.inner_offFaceLogPart_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_offFaceLogPart_eq_sum

/-- info: 'CRNT.Network.minMaxBarrier_euclideanStoichState_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.minMaxBarrier_euclideanStoichState_le_iff

/-- info: 'CRNT.Network.coordinate_floor_of_tilewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coordinate_floor_of_tilewise

/-- info: 'CRNT.PolyhedralBarrier.minMaxBarrier_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.minMaxBarrier_le_iff

/-! ### The convex case and separation -/

/-- info: 'CRNT.Network.barrier_euclideanStoichState_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.barrier_euclideanStoichState_le_iff

/-- info: 'CRNT.Network.le_of_halfspace_of_dominant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.le_of_halfspace_of_dominant

/-- info: 'CRNT.Network.coordinate_floor_of_dominant_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coordinate_floor_of_dominant_barrier

/-! ### Convex criterion and the self-consistency reduction -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_convex_tiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_convex_tiles

/-- info: 'CRNT.Network.faceLogPart_mem_activeFaceImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.faceLogPart_mem_activeFaceImage

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_selfConsistent_normals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_selfConsistent_normals

/-! ### The blueprint template with separation discharged -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_blueprintData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_blueprintData

/-! ### Orbit regularity (gap-analysis bridge 3) -/

/-- info: 'CRNT.Network.stoichCompatible_of_forward_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stoichCompatible_of_forward_solution

/-- info: 'CRNT.Network.orbit_pos_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbit_pos_forward

/-! ### Vacuity guard on the angular tiles -/

/-- info: 'CRNT.Network.relevantCones_eq_fan_of_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.relevantCones_eq_fan_of_small

/-- info: 'CRNT.Network.mem_all_cones_of_hm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.mem_all_cones_of_hm

/-- info: 'CRNT.Network.norm_ge_of_mem_activeFaceImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.norm_ge_of_mem_activeFaceImage

/-- info: 'CRNT.Network.not_small_of_mem_activeFaceImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.not_small_of_mem_activeFaceImage

/-! ### Band form of the fencing lemma (breaks the circularity in `hregime`) -/

/-- info: 'CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le

/-- info: 'CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_in_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.le_of_dini_slope_nonpos_in_band

/-- info: 'CRNT.PolyhedralBarrier.barrier_le_of_local_descent_in_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.barrier_le_of_local_descent_in_band

/-- info: 'CRNT.Network.barrier_le_of_toric_descent_in_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.barrier_le_of_toric_descent_in_band

/-! ### Regression guard: the floor condition must use positive parts -/

/-- info: 'CRNT.Network.sum_posPart_le_erase_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sum_posPart_le_erase_abs

/-- info: 'CRNT.Network.inner_le_erase_abs_of_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_le_erase_abs_of_sum_zero

/-- info: 'CRNT.Network.not_level_abs_and_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.not_level_abs_and_start

/-! ### Reducing `hm` to a separation condition -/

/-- info: 'CRNT.Network.hm_of_single_chamber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hm_of_single_chamber

/-- info: 'CRNT.Network.hm_of_single_chamber_activeFaceImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hm_of_single_chamber_activeFaceImage

/-! ### Normal existence -/

/-- info: 'CRNT.Network.coord_euclideanStoichUnit_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coord_euclideanStoichUnit_self

/-- info: 'CRNT.Network.euclideanStoichUnit_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.euclideanStoichUnit_ne_zero

/-- info: 'CRNT.Network.exists_chamber_coord_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_chamber_coord_pos

/-! ### Separation from signed margins -/

/-- info: 'CRNT.Network.dist_ge_of_separating_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.dist_ge_of_separating_margin

/-- info: 'CRNT.Network.hm_of_separating_margins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hm_of_separating_margins

/-! ### Depth buys margin -/

/-- info: 'CRNT.Network.inner_euclideanStoichUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_euclideanStoichUnit

/-- info: 'CRNT.Network.inner_faceLogPart_ge_of_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.inner_faceLogPart_ge_of_depth

/-- info: 'CRNT.Network.margin_of_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.margin_of_depth

/-- info: 'CRNT.Network.exists_depth_for_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_depth_for_margin

/-- info: 'CRNT.Network.margin_of_scale_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.margin_of_scale_ratio

/-! ### Separation only from non-containing cones -/

/-- info: 'CRNT.Network.hm_of_cone_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hm_of_cone_family

/-- info: 'CRNT.Network.hm_of_cone_family_margins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hm_of_cone_family_margins

/-! ### Class-aware floor condition -/

/-- info: 'CRNT.Network.le_of_halfspace_of_dominant_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.le_of_halfspace_of_dominant_class

/-- info: 'CRNT.Network.coordinate_floor_of_dominant_class_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.coordinate_floor_of_dominant_class_barrier
