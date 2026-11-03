# GAC v3 Face-Fill Proof Plan

Goal: remove the remaining `sorry` in `CRNT/Dynamics/GlobalAttractorTheorem.lean`
by completing the Craciun v3 zero-separating construction and connecting it to the
codimension-greater-than-one branch of `Network.complexBalanced_genuinePermanent`.

Canonical checkout: `/Users/akutuva/.codex/worktrees/c259/crnt-lean`, branch
`codex/gac-global-attractor`. Preserve preexisting changes in
`CRNT/Geometry/ZeroSeparatingInduction.lean`, the untracked
`CRNT/Examples/TrueSRNetCoeffCounterexample.lean`, and `scripts/__pycache__/`.

## Paper-to-Lean ledger

| Craciun v3 step | Existing Lean representation | State / remaining work |
| --- | --- | --- |
| §7.3 binary-word scales and projected pre-blueprint neighborhoods | `craciunBinaryWordFiberBox`, `CoordinateProjectedFaceChain.preBlueprintNeighborhood`, scale-separation lemmas | Implemented for a face chain. The dirty theorem proves only the distinct-projection case of Theorem 7.1; retain it. |
| §7.4.3 Case 1.1: lift projected basepoints | `CompactZeroBitFiberPatchCover`, center/basepoint incidence | Local incidence lemmas exist. Need use them in a complete face-indexed construction. |
| §7.4.3 Case 1.2: fill between inherited boundary neighborhoods and subdivide strips | `CompactOneBitFiberPatchCover`, endpoint-graph seam lemmas | Shared strip tiling and compact seams exist. Missing the actual recursive face filler and its boundary-compatibility invariant. |
| §7.4.3 Step 2 / Remarks 7.5–7.7: faithful refinement and approximation | `projectionFiberSubdivisionCenterGraph_*`, compact projective tile refinement | Local tile/basepoint facts exist. Need a global faithful blueprint whose projection and seam data agree across the face lattice. |
| §8 Steps 1–4: arrangement atlas, face filling, exhaustive separating surfaces, invariant region | `FanRefinement` common-face/rank-drop data; `ToricUniformWallMargin` local wall atlas and finite overlap gluing; `ZeroSeparatingSurfaceExists` consumer | Atlas/gluing are local. Missing coherent recursive assembly into a global smooth zero-separating surface, followed by the target consumer. |

## Checklist

- [x] Verify canonical branch, HEAD, target, and preexisting dirty state.
- [x] Read the specified v3 PDF, including §7.3 Theorem 7.1, §7.4.3 Cases 1.1/1.2 and Step 2, and §8 construction outline.
- [x] Build the current geometry-to-target chain; record that the build still accepts the target only because of its `sorry`.
- [ ] Formalize the face-indexed pre-blueprint/faithful-blueprint data required by §7.4.3, reusing current projection chains, shared strips, common-face witnesses, and rank decrease.
- [x] Prove that every non-interior point of a finite arrangement cell is incident to another cell, and convert the common face of those incident cells into actual strip/endpoint predecessor edges.
- [ ] Prove and apply the rank-decreasing extension step: construct a strip/face piece from all inherited proper-face and endpoint data while preserving exact projection, coverage, disjoint interiors, and seam agreement.
- [ ] Recursively assemble a coherent barrier across the whole finite arrangement; local tile offsets and pointwise overlap smooth-max witnesses alone do not establish a global surface.
- [ ] Construct the `ZeroSeparatingSurfaceExists` witness consumed by the trajectory persistence argument and apply it in the target's higher-codimension branch.
- [ ] Build affected modules in dependency order, then `CRNT.Dynamics.GlobalAttractorTheorem`.
- [ ] Confirm the target source has no `sorry`/`admit`; run `#print axioms` on the exact target and ensure no `sorryAx` or new axiom.
- [ ] Commit only verified, task-related changes; preserve unrelated dirty/untracked work; push and verify the remote SHA.

## Current checkpoint

- Baseline HEAD: `2c19d32b8c613fcdd33d65bafe5e694acf6699be`.
- A targeted `lake build` completed 3,401 jobs. It emitted
  `CRNT/Dynamics/GlobalAttractorTheorem.lean:1442:8 declaration uses 'sorry'`;
  this is not proof completion.
- Added the missing proper-face endpoint edge to `OneBitFanFaceDependency` and
  `hyperplaneArrangementFamily_commonEndpoint_tasks_at`, so endpoint seam data
  can recurse through common exposed faces as strip data already could. This
  formalizes one dependency required by the face fill; the generic recursor is
  still not yet used to produce geometric output.
- Extended each task with a base-tile label. The arrangement atlas indexes
  patches by both a fan cell and a projected small tile; the former task index
  could not distinguish those local patches. Adjacent seam certificates now
  retain the respective incident patch labels.
- `lake build CRNT.Geometry.FanRefinement` could not replace the cached `.olean`
  in `.lake/build` (`operation not permitted`). Compiled the modified module to
  `/tmp/FanRefinement.olean`, overlaid it in a temporary Lean search tree, then
  directly compiled `CRNT/Dynamics/GlobalAttractorTheorem.lean` against that
  tree. Both compilations succeeded; the target still warns that it uses
  `sorry`.
- Ran `#print axioms CRNT.Network.complexBalanced_genuinePermanent`; output
  includes `sorryAx`.
- Axiom audit of the new dependency order and common-endpoint theorem contains
  only Lean's standard axioms; neither introduces `sorryAx`.
- Re-read the actual PDF text for §7.3 Theorem 7.1 and §7.4.3 Case 1.1,
  Case 1.2, and Step 2. The paper's construction requires both (a) lifting each
  inherited lower-dimensional basepoint when the face projection preserves
  dimension, and (b) filling between already-built boundary-face neighborhoods
  when dimension drops, followed by a subdivision satisfying the next-stage
  scale inequalities. The PDF then uses that faithful blueprint recursively to
  build the polyhedral ZSH family in §8.
- Current Lean boundary: `CoordinateProjectedFaceChain` and
  `preBlueprintNeighborhood` carry one projected face chain, not a finite
  subdivision face lattice with a jointly compatible family of chains.
  `CompactZeroBitFiberPatchCover` and `CompactOneBitFiberPatchCover` prove
  local Case 1.1 / Case 1.2 coverage, basepoint, compactness, and seam facts.
  `OneBitFanFaceDependency` plus `oneBitFanFaceDependency_recursion` provide
  only the well-founded index relation and a generic recursor. No caller uses
  that recursor to construct geometric data. The fan atlas provides local
  barrier functions and seam derivatives, but not a face-recursive global
  faithful blueprint or a global surface assembled from it.
- The source-level construction theorem that must be formalized next is a
  face-indexed recursive filler: for each arrangement cell and one-bit strip,
  construct the Case 1.1 lift or Case 1.2 filled strip from all proper exposed
  face and adjacent endpoint predecessors, with exact projection, coverage,
  disjoint interiors, and the higher-stage spanning/scale invariant. The
  current `OneBitFanFaceTask` is the index, but there is not yet a type carrying
  this task's geometric output and compatibility invariant. That output must
  then be consumed to construct `ZeroSeparatingSurfaceExists`; it cannot be
  discharged by `InductionStepHypothesis`, which is an implication supplied as
  an assumption.
- Exact target axiom audit run with `#print axioms
  CRNT.Network.complexBalanced_genuinePermanent`: it currently depends on
  `sorryAx` (as well as Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound`).
- The preexisting dirty `CRNT/Geometry/ZeroSeparatingInduction.lean` lemma and
  unrelated untracked artifacts are preserved. The verified checkpoint was
  committed locally as `05900e8`; the target remains open. Push was rejected by
  automatic review because it treats this private repository payload as
  external source-code egress and says general push authorization does not
  authorize that specific destination. Do not retry by an alternate route
  without destination-specific approval.
- After that commit, corrected the product seam task index to retain only the
  projected small-tile label (the fan cell is a separate index), and added
  proper-face endpoint-to-endpoint and strip-to-strip dependency witnesses.
  Compiled `FanRefinement.lean` directly to `/tmp/FanRefinement.olean`, overlaid
  that artifact into the temporary Lean search tree, and compiled
  `GlobalAttractorTheorem.lean` against it. The exact target axiom audit still
  reports `sorryAx`; the well-founded dependency and common-endpoint lemmas
  report only standard Lean axioms.
- Added `oneBitFanFaceTaskPatch`, whose strip and endpoint cases now return the
  actual restricted strip patch and endpoint-graph patch, plus a face-mono
  lemma under projected-tile containment. Recompiled the geometry module and
  target successfully; the target warning and `sorryAx` remain unchanged.
- Added untagged projected cone tiles, proved exposed-face tile nesting, and
  specialized task-patch nesting to the arrangement tile crossed with each
  small blueprint tile. The endpoint graph is now proved to lie in either
  adjacent closed strip, and `oneBitFanFaceDependency.taskPatch_subset` proves
  every dependency constructor gives an inclusion between its actual task
  patches. The target recompiles, and audits of these new lemmas report only
  standard Lean axioms.
- Added `CompactOneBitFiberPatchCover.arrangementTaskPatch_cover`, identifying
  the actual finite arrangement/small-tile cover with the corresponding task
  strip outputs. The geometry module and target compile against this change;
  the coverage and edge-inclusion audits have no `sorryAx`, while the exact
  target audit still does.
- Extended `fanSmallProductTile_adjacentStrip_seam` to identify an adjacent
  strip intersection with the endpoint task over the actual common fan face
  and the pairwise small-tile intersection. Updated its two consumers, then
  compiled `FanRefinement.lean`, `ToricUniformWallMargin.lean`, and the target
  through the temporary Lean search tree. The seam, coverage, and edge
  inclusion audits contain only standard Lean axioms; the target still has
  `sorryAx`.
- Proved that this pair-labelled endpoint seam output is contained in each of
  its incident strip task outputs, using exposed-face tile nesting and the
  adjacent closed-strip endpoint calculation. Updated the two wall-atlas
  consumers to the current task indices. Recompiled all three affected
  modules and audited the exact target; the new seam inclusion lemmas remain
  `sorryAx`-free, but `Network.complexBalanced_genuinePermanent` still reports
  `sorryAx`.
- Added a mixed-label recursion domain with single-tile strip tasks and pair-labelled seam tasks.
  The adjacent-strip certificate now returns actual predecessor edges from the pair seam to both
  incident strips, and `oneBitFanFaceSeamDependency.taskPatch_subset` proves every mixed edge is
  an inclusion between its concrete geometric patches. Direct Lean 4.34 compilation succeeded for
  `FanRefinement.lean`, `ToricUniformWallMargin.lean`, and
  `GlobalAttractorTheorem.lean` using the fresh temporary module search tree. The target still
  warns at line 1442 that it uses `sorry`; the exact axiom audit reports `sorryAx` on
  `Network.complexBalanced_genuinePermanent`, while the mixed recursion, its recursor, the edge
  inclusion theorem, and the adjacent-strip certificate use only `[propext, Classical.choice,
  Quot.sound]`.
- This mixed relation still only orders preassigned set-valued patches. It does not construct the
  faithful blueprint, select compatible basepoints/scales across projected subdivisions, or
  produce the exhaustive zero-separating family. The exact missing endpoint theorem should have
  this Lean shape (with the complete-fan record supplied as part of the formalization):
  ```lean
  theorem exists_zeroSeparatingSurface_of_completePointedPolyhedralFan
      {S : Type*} [Fintype S]
      (F : Fan (EuclideanSpace ℝ S)) (hF : IsCompletePointedPolyhedralFan F)
      (δfan : ℝ) (hδfan : 0 < δfan)
      (f : EuclideanSpace ℝ S → EuclideanSpace ℝ S)
      (hselect : ∀ x, f x ∈ toricInclusionField F δfan x)
      (x₀ : EuclideanSpace ℝ S) :
      DifferentialInclusion.ZeroSeparatingSurfaceExists f x₀
  ```
  `IsCompletePointedPolyhedralFan` is not currently defined: `Fan` is only a `Finset` of proper
  cones, with the face-lattice and covering axioms explicitly omitted in `ToricFan.lean:47–51`.
  The surface module proves the one-dimensional case but leaves its higher-dimensional simplicial
  gluing as the `InductionStepHypothesis` input. Craciun v3 §7.4.3 requires recursive
  faithful-blueprint refinement preserving projection/basepoint and scale compatibility; §8
  Steps 2–4 use that output to build an exhaustive ZSH family and invariant region. No current
  theorem constructs this output from complete pointed fan data, so this is a real missing
  mathematical/formal result rather than another missing wrapper.
- The current task-patch recursion still has no caller that returns recursive covers, barriers, or
  blueprint data. Keep the checklist open until the global `ZeroSeparatingSurfaceExists` result is
  derived and the exact target theorem and kernel axiom audit are clean.
- Extended the §7.4.3 Case 1.1 zero-bit cover with the exact graph invariant
  `center_graph_on_face`, and proved that two independently constructed graph sections agree
  above the projection of their shared face (`centers_agree_on_shared_face`). The red `#check`
  probe for the missing invariant failed before implementation; afterward, Lean 4.34 compiled
  `ZeroSeparatingInduction.lean`, `FanRefinement.lean`, `ToricUniformWallMargin.lean`, and
  `GlobalAttractorTheorem.lean` against the fresh dependency chain. The new theorem and its
  constructor audit to `[propext, Classical.choice, Quot.sound]`. This supplies pairwise Case 1.1
  basepoint agreement, but it still has no finite face-family consumer and does not construct the
  recursive faithful blueprint or global surface.


## Continuation checkpoint — 2026-09-27

- Added `hyperplaneArrangementFamily_boundary_incident_cell` and
  `hyperplaneArrangementFamily_boundary_commonFace_dependency_at` in
  `CRNT/Geometry/FanRefinement.lean`. The first uses finite closed-cell incidence and complete
  arrangement coverage; the second calls `hyperplaneArrangementFamily_commonFace_at` and returns
  actual well-founded predecessor edges for strip and endpoint tasks.
- The new `FanRefinement.lean` source compiled directly with Lean 4.34 into the fresh module tree;
  `ToricUniformWallMargin.lean` and `GlobalAttractorTheorem.lean` then compiled against it.
- `#print axioms` for both new lemmas reports only `[propext, Classical.choice, Quot.sound]`.
  The exact target audit still reports `sorryAx`; this checkpoint closes only arrangement-cell
  boundary incidence. The face-indexed geometric filler, global barrier assembly, and target
  consumer remain open.
- The preexisting unrelated untracked files remain preserved outside this task checkpoint.

## Continuation checkpoint — finite projected-tile seam recursion

- Added `CompactSmallBaseTiling.boundary_incident_tile`: over an interior point of the compact base, failure to be interior to one closed tile yields a distinct incident tile.
- Added a Fin-indexed pair-overlap dependency to the existing fan-face and one-bit endpoint dependency. Its lexicographic rank strictly decreases on every edge, and its recursor returns task data in `Sort`.
- Proved each pair-overlap edge is an inclusion between the actual mixed tile/strip or tile/endpoint patches. A boundary-point lemma now returns the common pair-labeled task and its edges to both incident single-tile tasks.
- Fresh direct Lean compilation succeeded for `ZeroSeparatingInduction.lean`, `FanRefinement.lean`, `ToricUniformWallMargin.lean`, `Dynamics/ComplexBalanceStoichFanInclusion.lean`, and `Dynamics/GlobalAttractorTheorem.lean`. Axiom audits of the new relation and patch consumers report only standard axioms; the exact target still reports `sorryAx`.
- This supplies internal projected-tile seam predecessors for the §7.4.3 fill. It does not yet construct the recursive face-filling geometry, assemble the global ZSH, or discharge the target.

## Continuation checkpoint — concrete boundary-point seam consumer

- Added `CompactSmallBaseTiling.boundary_overlap_patch_at` in
  `CRNT/Geometry/FanRefinement.lean`. Given a point in an actual single-tile strip
  or endpoint patch whose projection is on that tile's boundary, it returns a
  distinct incident tile, the corresponding pair-labelled seam task, both
  predecessor edges to the incident single-tile tasks, and inclusion of the seam
  patch in the original patch.
- The current source compiled directly with Lean 4.34 into the fresh module tree;
  the geometry-to-target dependency chain compiled afterward. Audits of this
  consumer and its dependencies use only standard Lean axioms. The target still
  has its original `sorry` and `sorryAx`.
- This is now an actual pointwise consumer of the projected-tile seam recursion,
  but it remains a boundary-incidence result: it does not extend inherited face
  data, construct compatible scales/basepoints, assemble a faithful blueprint,
  or build the global zero-separating surface. Continue with the rank-decreasing
  geometric extension step rather than treating this helper as completion.

## Continuation checkpoint — boundary seam feeds local barrier gluing

- Added `Network.exists_boundarySmallTile_strip_smoothMax_descent` to
  `CRNT/Geometry/ToricUniformWallMargin.lean`. It consumes the boundary-point
  seam result from `FanRefinement`, follows the pair-seam dependency inclusion to
  the neighboring single-tile patch, and applies the existing finite-overlap
  barrier theorem to obtain a smooth-maximum derivative certificate at that
  actual point.
- A red probe caught and fixed the index mismatch between the small-base tiling
  and the mixed seam labels. The completed temporary probe compiled and its
  axiom audit returned only `[propext, Classical.choice, Quot.sound]`.
- Fresh Lean 4.34 compilation succeeded for `ToricUniformWallMargin.lean`,
  `Dynamics/ComplexBalanceStoichFanInclusion.lean`, and
  `Dynamics/GlobalAttractorTheorem.lean`. The exact target audit still reports
  `sorryAx`. This connects one recursive seam to local dynamics; it does not yet
  assemble the finite face family into one global surface.

## Continuation checkpoint — multiway projected-tile junction

- Added `Network.exists_boundarySmallTile_allIncident_smoothMax_descent` to
  `ToricUniformWallMargin.lean`. At a projected boundary point it enumerates the
  full finite set of other incident base tiles, constructs for each one a
  pair-labelled strip seam and its two predecessor edges, and proves one
  smooth-maximum derivative certificate across all incident local barriers.
- Direct Lean 4.34 compilation succeeded for the modified toric module,
  `Dynamics/ComplexBalanceStoichFanInclusion.lean`, and
  `Dynamics/GlobalAttractorTheorem.lean`. Axiom audits of both boundary-gluing
  theorems report only `[propext, Classical.choice, Quot.sound]`; the target
  continues to report `sorryAx`.
- This handles a multiway small-tile junction for one arrangement cell and one
  fiber strip. The recursive arrangement-face extension and the global
  zero-separating surface remain to be constructed.


## Continuation checkpoint — mixed fan/tile strip junction

- Added `Network.fanSmallProductTile_allIncident_strip_dependency_and_glue` to
  `ToricUniformWallMargin.lean`. It constructs the finite list of every other
  arrangement-cell/small-tile single patch incident to the root strip point, with a
  coverage statement for every such label.
- At the point it takes the common lower arrangement face for the root and all incident
  cells. For each incident patch it supplies an actual lower seam task: a single-tile task
  when both labels agree, or a pair-labelled tile seam otherwise. Each seam has
  `ReflTransGen FiniteOverlapDependency` paths to both the root and incident strip tasks.
- The lemma applies the existing finite smooth-maximum gluing theorem to all incident local
  barriers at the lifted point. Fresh Lean 4.34 compilation succeeded for
  `ToricUniformWallMargin.lean`, `Dynamics/ComplexBalanceStoichFanInclusion.lean`, and
  `Dynamics/GlobalAttractorTheorem.lean`. Its axiom audit is
  `[propext, Classical.choice, Quot.sound]`.
- The exact target audit still reports `sorryAx`. This checkpoint supplies a multiway
  product-junction dependency/gluing result; it does not yet construct the recursive
  face-fill output or the global zero-separating surface.

## Continuation checkpoint — endpoint product-tile junction

- Added `Network.fanSmallProductTile_allIncident_endpoint_dependency_and_glue` to
  `CRNT/Geometry/ToricUniformWallMargin.lean`. At a fiber endpoint it enumerates all incident
  arrangement-cell/small-tile strips on both sides, chooses a common lower arrangement face,
  constructs either a same-tile fiber endpoint task or a pair-labelled product seam, and gives
  dependency paths to the root and every incident strip. It then applies finite smooth-maximum
  gluing to the local wall atlas.
- Fresh Lean 4.34 compilation succeeded for `ZeroSeparatingInduction.lean`, `FanRefinement.lean`,
  the modified `ToricUniformWallMargin.lean`, `Dynamics/ComplexBalanceStoichFanInclusion.lean`,
  and `Dynamics/GlobalAttractorTheorem.lean`. The new theorem's axiom audit is
  `[propext, Classical.choice, Quot.sound]`.
- The exact target still warns that it uses `sorry`, and its axiom audit still contains `sorryAx`.
  This closes an endpoint junction lemma under the supplied local wall atlas; it does not construct
  the §7.4.3 faithful blueprint, the §8 lexicographic face fill, or a global zero-separating surface.
  Continue with that construction.

## Continuation checkpoint — critical-facet overlap collar

- In `CRNT/Geometry/ZeroSeparatingInduction.lean`, proved that when a binary fiber has width only
  in the final coordinate, its zero-bit pre-blueprint is exactly the graph tube around the face's
  selected lift.
- For two compact zero-bit face covers, compactness now gives a positive common graph-tube radius
  below any supplied parent cap on every compact shared projected tile that avoids the common
  face. Specializing to the critical word `11…110` yields disjoint pre-blueprints there and the
  stronger collar form: any overlap projects within the chosen distance of an actual point on the
  shared lower face.
- Lean 4.34 compiled the geometry source and the fresh dependency chain through
  `GlobalAttractorTheorem.lean`. New geometry lemmas audit to only standard Lean axioms; the exact
  `Network.complexBalanced_genuinePermanent` audit still contains `sorryAx`.
- This supplies the equal-projection critical-facet separation clause of §7.3 with an explicit
  interface for passing residual overlap to the lower face. The recursive face filler, coherent
  global surface, and target consumer remain unproved.
- Strengthened the collar to an ambient metric statement: for every `epsilon > 0`, the critical
  width can be chosen below `epsilon / 3` so every overlap point is within `epsilon` of an actual
  point on the shared face. This uses compact uniform continuity of one graph section and the
  proved agreement of the two sections along the common face; it still does not construct the
  recursive filler itself.
- Consumed that estimate against any open neighborhood containing the compact common face: the two
  pre-blueprints can be scaled so their full intersection lies inside the inherited neighborhood.
  This makes the residual-overlap-to-lower-face handoff an explicit theorem, conditional only on
  the lower-face neighborhood already having been constructed.

## Continuation checkpoint — one critical-facet scale for a finite face family

- Added `CompactZeroBitFiberPatchCover.exists_common_criticalFacet_scale`. For each distinct face
  pair, it uses the open inherited-neighborhood theorem when the projected common face is
  nonempty; otherwise it separates the two graph tubes over their compact common projected base.
  It then takes the minimum of the finite pair scales and proves every pairwise constraint at
  that single width.
- Direct Lean 4.34 compilation succeeded for `ZeroSeparatingInduction.lean`. A fresh temporary
  dependency chain also compiled `FanRefinement.lean`, `ToricUniformWallMargin.lean`,
  `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean`.
- Added a Tietze extension theorem for each compact zero-bit center graph, then consumed the common
  scale in `exists_common_scale_and_oneBit_fills`: for each supplied directed one-bit boundary pair,
  it constructs the compact band between the extended center graphs, proves both restricted face
  pieces lie in that band, crosses the two inherited projected tile covers, and returns a
  `CompactOneBitFiberPatchCover` with exact coverage, compact pieces, interior disjointness, and
  seam identities at the selected scale. This is a graph-level fill only; the full thickened
  inherited pre-blueprints are not yet shown to bound the filled region.
- The extension theorem, finite scale selector, and one-bit fill consumer each audit to
  `[propext, Classical.choice, Quot.sound]`. The exact target audit remains
  `[propext, sorryAx, Classical.choice, Quot.sound]`; the theorem still has its original hole.
  The remaining construction must derive the directed boundary-pair/order data from the actual
  projected face lattice, incorporate the thickened inherited neighborhoods in the Case 1.2 fill,
  and recursively assemble these local fills into the faithful blueprint.

## Continuation checkpoint — binary-chain factor consumed by one-bit fill

- Added `CompactZeroBitFiberPatchCover.exists_common_scale_and_oneBit_fills_along_binary_chains`.
  It obtains the common strict factor from the full coherent binary-word chain theorem at depth
  `n + 1`, chooses a positive lower bound for the finite family of inherited graph radii, and
  invokes the existing Case 1.2 graph fill with cap `rho * scale`. The returned radius is below
  `rho * faceRadius i` for every face. For each directed face pair, the returned refinement now
  states directly that every equal strip width is strictly below `rho` times both incident face
  radii, using the tiling's `fiber_width_le` invariant.
- `ZeroSeparatingInduction.lean` compiled directly. A fresh module chain compiled
  `FanRefinement.lean`, `ToricUniformWallMargin.lean`,
  `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean`. The new fill theorem
  audits to `[propext, Classical.choice, Quot.sound]`; the exact target still audits to
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
- This supplies one actual Case 1.2 fill with a cross-chain refinement bound. The face-word-specific
  thickened neighborhood containment, recursive assembly across the face lattice, global surface,
  and target consumer remain open.

## Continuation checkpoint — arbitrary zero-ending profiles feed Case 1.1/1.2

- Proved a compact-set thickening lemma and used it to extend equal-projection overlap separation
  from the critical facet word to any pair of binary words. Every valid Craciun prefix box lies in
  a `2q` ambient thickening, so one compactness scale confines the full pre-blueprint overlap to
  the inherited open neighborhood.
- Added `exists_common_craciunRatio_scale`, which takes the minimum of the finite pair scales and
  preserves all arbitrary-word overlap constraints at one ratio. Added a ratio monotonicity lemma
  whose profile depth is independent of the ambient face dimension, since this construction uses
  a profile of depth `n + 1` on faces in dimension `n + 1`.
- Added `exists_common_scale_and_oneBit_fills_for_craciun_words`. For a finite family of
  zero-ending words, it selects a positive minimum profile width and caps the Case 1.2 graph-fill
  radius by both that width and the shared binary-chain face scale. It proves each Case 1.1 graph
  tube lies in its full Craciun pre-blueprint, carries pairwise overlap containment through to
  those tubes, and returns the same-scale Case 1.2 strip subdivision with strict incident-face
  width bounds.
- Direct Lean 4.34 compilation succeeded for `ZeroSeparatingInduction.lean`. A fresh dependency
  chain compiled `FanRefinement.lean`, `ToricUniformWallMargin.lean`,
  `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean`. The ratio selector
  and integrated fill theorem audit to `[propext, Classical.choice, Quot.sound]`; the exact target
  audit remains `[propext, sorryAx, Classical.choice, Quot.sound]`.
- This gives the finite Case 1.1/1.2 consumer the full inherited profile and one compatible scale.
  The actual face-indexed recursive order, filling from all proper-face boundary data, global
  faithful blueprint/ZSH assembly, and target consumer remain open.

## Continuation checkpoint — Step 2 profile-width bounds on every fill strip

- Strengthened `exists_common_scale_and_oneBit_fills_for_craciun_words` so the same subdivision
  certifies each strip width is strictly below the full Craciun profile width assigned to both
  incident zero-ending words, in addition to the two face-radius bounds. This is the explicit
  Step 2 inequality needed when the strip data is carried into the next blueprint stage.
- Lean 4.34 compiled `ZeroSeparatingInduction.lean` directly, then freshly rebuilt
  `FanRefinement.lean`, `ToricUniformWallMargin.lean`,
  `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean` against that source
  artifact. The new selector/fill theorem audit to `[propext, Classical.choice, Quot.sound]`.
- The exact target still audits to `[propext, sorryAx, Classical.choice, Quot.sound]`. This
  checkpoint supplies the missing per-word Step 2 bound only; recursive face-family construction,
  global faithful blueprint/ZSH assembly, and the target consumer remain the active goal.

## Continuation checkpoint — one-ending interpolated profile carried by each fill

- Added a positivity proof for every in-range one-ending interpolated tile scale, including the
  all-ones chain whose interpolation starts at zero.
- Strengthened `exists_common_scale_and_oneBit_fills_for_craciun_words` to take the finite family
  of one-ending words assigned to boundary pairs. It chooses the common ratio first, derives the
  uniform binary-chain factor at that ratio, caps the shared fill radius by the positive minimum
  of all supplied interpolated scales, and returns both a radius bound and a strict bound on each
  resulting strip by its assigned `tilde epsilon` profile.
- Fresh Lean 4.34 compilation succeeded for `ZeroSeparatingInduction.lean`, then
  `FanRefinement.lean`, `ToricUniformWallMargin.lean`,
  `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean` against that fresh
  source artifact. The positivity lemma and integrated fill theorem audit to
  `[propext, Classical.choice, Quot.sound]`.
- The exact target still audits to `[propext, sorryAx, Classical.choice, Quot.sound]`. This is a
  Step 2 profile-scale bridge; the actual face-lattice caller, recursive faithful blueprint,
  global zero-separating surface, and target consumer remain unfinished.

## Continuation checkpoint — outward Case 1.2 fill from inherited tubes

- Re-read Craciun v3 §7.4.3 Step 1 and Case 1.2. The face fill is delimited by already-built face neighborhoods, whereas the previous Lean band used only the selected center graphs.
- Changed the finite one-bit fill to use the shifted endpoints `extension i - radius` and `extension j + radius`. On the common projected base, the resulting band contains both selected radius-tubes around the inherited boundary graphs; it still contains the two boundary face pieces.
- Propagated the shifted endpoint functions and both tube-containment proofs through the binary-chain and full Craciun-profile consumers. The common strip-width bounds remain tied to the same selected radius.
- Fresh Lean 4.34 source compilation succeeded for `ZeroSeparatingInduction.lean`, `FanRefinement.lean`, `ToricUniformWallMargin.lean`, `ComplexBalanceStoichFanInclusion.lean`, and `GlobalAttractorTheorem.lean`. Axiom audits of the three changed fill theorems contain only standard axioms; the exact target audit still contains `sorryAx`.
- This closes the selected-neighborhood containment clause for this local Case 1.2 fill. It does not construct the face-lattice caller, recursively assemble the faithful blueprint, build the global zero-separating surface, or remove the target `sorry`.
