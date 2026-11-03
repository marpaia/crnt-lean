# Hole A, reframed (round 1 — with the P1 correction)

> **SUPERSEDED IN PART.** F-1/F-2/F-4 stand. **F-3 is FALSE and is retracted below.**
> The fan exists. Theorem 4.3 is proved. The wiring is the gap.

**Read this file, not `BRIEF-A.md`, when planning Hole A work.**

## F-1. Hole A is **not** Craciun's Theorem B — STANDS

Craciun's Theorem B concerns an **exhaustive family of zero-separating hypersurfaces** (ZSH) and
has **no proof anywhere in the paper** — one sentence on p. 8, discharged by a *plan* in §4
(p. 17: "Steps 2 and 3 are very much interconnected, and most of our effort will focus on these two
steps"). The only place exhaustiveness is argued is §8 Step 2, and there it is
"we just choose eps_0 < x_0^i … **it is easy to see** that …". Step 4 is called "a relatively quick
corollary" and was never written. The exhaustive half of Theorem B is itself a hand-wave.

The hole's statement carries a critical-siphon-face apparatus — `hcodim`, `hmaxExact`, `hzcard`,
`hrank` — that Craciun never mentions: no siphons, no zero sets, no ω-points, no codimension.
Theorem B is **a sufficient means**, not the statement.

## F-2. The hole's conclusion is strictly **weaker** than a ZSH — STANDS

The hole wants **one interior ω-point**. ZSH Definition 4.6 clauses **4.6(i)** (η-separation) and
**4.6(ii)** (meeting every toric ray exactly once) can both be **dropped**.

This is why the route has failed for months: it is **over-attempted, not under-attempted**. It
compounds entry **A-1** — the `oneBit*` recursors prove a *different* statement *and* the right
statement is weaker than their target.

A transcriber's further point, which strengthens this: the weakest sufficient hypothesis may be
reachable **directly in stoichiometric coordinates without a fan ever being named**. That is a live
route, not a fallback.

## ~~F-3. The hole's hypotheses do not supply the fan~~ — **RETRACTED, IT WAS FALSE**

I told twelve researchers in round 1 that the fan had to be built from scratch and that
`ToricEmbeddingWR.lean` was the highest-value asset in the tree. **Both were wrong.**

**The fan exists, unconditionally.**
`CRNT/Dynamics/ComplexBalanceStoichFan.lean`:

* `relativeSourceOrderStoichFan` (:98) is built from `N.stoichSubspace` and `N.R` alone — **no δ,
  no extra hypothesis, not one reference to `hxs`/`hcb`**;
* `relativeSourceOrderStoichFan_isPolyhedralFan` (:330) proves `CRNT.IsPolyhedralFan`;
* `exists_relativeSourceOrderConeInStoich_mem` (:305) proves covering;
* `relativeSourceOrderStoichFan_inter_mem` (:140) and `_faces_mem` (:250) give intersection and
  face closure;
* `relativeSourceOrderNegativeStoichFan` (:357) is likewise complete (:362, :377);
* `relativeSourceOrderNegativeStoichFan_hasDualFGCells` (`ComplexBalanceStoichFanInclusion.lean`:33)
  and `relativeSourceOrderNegativeConeFamily_hasExposedCommonFaces` (:802) supply the dual-FG-cell
  and exposed-common-face axioms.

**Theorem 4.3 is already proved.**
`CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean`:

* `isInclusionSolution_massAction_relativeSourceOrder` (:539) and
  `isInclusionSolutionOn_massAction_relativeSourceOrder` (:560) take **exactly the hole's
  hypotheses** — `hxs : xstar.Positive`, `hcb : N.IsComplexBalanced κ xstar`, `hδ : 0 < δ`, orbit
  positivity, and the genuine-derivative clause `hderiv`/`hsol` — and conclude the trajectory solves
  the toric differential inclusion `relativeSourceOrderToricInclusionField xstar δ`.
* Supporting layer complete: `massActionVectorField_mem_relativeSourceOrderToricInclusionField`
  (:492), `velocity_mem_stoichSubspace_of_mem_…` (:520),
  `exists_coordinate_refinement_of_relativeSourceOrderNegativeStoichFan` (:51),
  `toricField_relativeSourceOrderNegativeStoichFan_subset_commonRefinement` (:206),
  `massActionVectorField_inner_pos_of_mem_interior_sourceOrderNegativeCone` (:419).

**The wiring is the gap.** `CRNT/Dynamics/GlobalAttractorTheorem.lean` imports
`CRNT.Dynamics.ComplexBalanceStoichFan` at line 2 — and a grep for
`relativeSourceOrderStoichFan|stoichFan|_isPolyhedralFan` over all 1789 lines returns **ZERO
matches**. The complete fan is compiled into the hole's dependency cone and **never used**.

**And `ToricEmbeddingWR.lean` is the weaker path, partially dead.**
`multiCycle_velocity_mem_polarCone` (:136) and `NetworkCycleDecomposition.velocity_mem_polarCone`
(:232) are real, but both take a `CycleDecomposition` structure (:93, :160) that **nothing in the
tree builds**; the `mono` field is refuted by `CRNT/Examples/CycleRateNonMonotone.lean`
(`tri_no_monotone_rotation`, :89), and `cmin` has no supplier
(`Graph/CycleCover.lean:35-38`: "Not constructed here"). **Use the StoichFan path.**


## F-5. The residual blocker is the absence of any **δ** — STANDS, NEW IN ROUND 1

The fan exists; the embedding exists; the δ does not.

Every selector theorem consumes a δ: `massActionVectorField_mem_toricField_…`
(`ComplexBalanceStoichFanInclusion.lean:373`) takes `{δ : ℝ} (hδ : 0 < δ)`. The hole's hypothesis
list supplies `hxs`, `hcb`, `hsol` — matching the selector's complex-balance premises exactly — but
supplies **no δ** and no interior trajectory point to read the state from.

And per **A-12** a slack δ may **not** be manufactured ad hoc: Lemma 9.7's conclusion is non-strict
and its only quantification is an existential threshold `‖log P‖ ≥ max_C M_C`. So "just pick a δ" is
exactly the unproved strengthening A-12 forbids. **Where δ legitimately comes from — `hK`/`hmaps`
compactness, the `B` in `faceRelevantCones P δ B`, or the track record of the orbit — is the open
 question and is the sharpest remaining Hole A question.**

Note also (from `FormFanfaceCore.EmbeddingAudit`): `CRNT.Fan E` is an axiom-free `abbrev` for
`Finset (ProperCone ℝ E)` (`CRNT/Geometry/ToricFan.lean:50`), so `toricField` needs no predicate at
all; and the ambient cone family is
`relativeSourceOrderNegativeConeFamily` (`CRNT/Dynamics/ComplexBalanceCycleDecomposition.lean:2311`).

`ToricEmbeddingWR` is dead for a stronger reason than "nothing builds the decomposition":
`multiCycle_velocity_mem_polarCone` (:136) and `NetworkCycleDecomposition.velocity_mem_polarCone`
(:232) conclude about `D.totalVelocity`, and **no theorem in the file equates `D.totalVelocity`
with `N.massActionVectorField κ x`**. That path does not even reach the mass-action field.

## F-6. The landing site — FOUND

`CRNT/Dynamics/FaceDirectionCone.lean` is already parameterised by the hole's own data:

* `faceDirectionCone P` (:92) takes a `Finset S` face `P`; **the hole's `Pmax` is exactly such a `P`**;
* `faceLogPart` (:204) / `offFaceLogPart` (:210);
* `faceRelevantCones P δ B` (:317) — near-cones of the fan within `δ + B` of `faceDirectionCone P`;
* `faceRelevantCore` (:333), `faceRelevantCore_mem` (:337), `mem_of_mem_faceRelevantCore` (:342);
* terminal criteria `exists_positive_omegaPoint_of_tiled_faceCores` (:367) and
  **`exists_positive_omegaPoint_of_faceRelevantCore` (:417)**.

And inside the hole's own file, `CRNT/Dynamics/HighCodimensionSiphonFace.lean:1596` holds
`exists_positive_omegaPoint_of_upperRegion`, whose **only two unbuilt inputs are `hfloor` and the
non-crossing `hsplit`**.

`GlobalAttractorTheorem.lean` imports `ComplexBalanceStoichFan` (line 2),
`ComplexBalanceStoichFanInclusion` and `FaceDirectionCone`, and references **none** of them in 1789
lines. **Hole A is, at this point, a wiring problem.**

Note for the adversary tier: the `C ⊆ interior K` requirement is load-bearing at **five** sites in
`CRNT/Geometry/CraciunZSH.lean` — `exists_eventual_tube_subset_of_cone_interior` (:32) and
`exists_uniform_eventual_tube_subset_of_finite_properCone_pairs` (:222, hypothesis literally named
`hinterior`), propagating transitively to :186, :311, :346, :378. Whether
`FaceDirectionCone.lean` routes *around* `CraciunZSH` or *through* it determines whether the
shortest path to closing Hole A avoids A-11 entirely.
## What to attempt now, in priority order

1. **Wire the fan in.** `form-barrier` is the natural owner. The gap is concrete and small: the
   hole's context has a genuine mass-action trajectory with a complex-balanced positive equilibrium;
   `isInclusionSolution_massAction_relativeSourceOrder` consumes exactly that. Determine the precise
   statement that fails to close — the trajectory in the hole is an ω-limit-set one with extra
   properties (`hmaps`, `hK`, `hωnn`, `hgenω`, `hωaff`), so establish what *additional* hypothesis
   the inclusion theorem needs and whether it is derivable.
2. **Attack the weakened target** (F-2), now with a real fan and a real embedding behind it. One
   interior ω-point, not a ZSH.
3. Only then the blueprint induction, and only with an **ambient-rank-decreasing** recursor.

## Evidence grades

F-1, F-2, and the F-3 retraction are all `[V]`: the transcriber read the complete 91-page PDF, and
the F-3 retraction was verified by the orchestrator against the tree (`grep` returns zero uses in
`GlobalAttractorTheorem.lean`; both modules elaborate). The priority ordering above is an
inference; `adv-refute` and `adv-audit` are asked to attack it in round 2.
