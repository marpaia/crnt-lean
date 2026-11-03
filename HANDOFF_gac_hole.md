# HANDOFF — GAC hole (Hole 2), session of 2026-09-27

Target: `CRNT.Network.complexBalanced_genuinePermanent` in
`CRNT/Dynamics/GlobalAttractorTheorem.lean`.

**Status: still open.**  `#print axioms CRNT.Network.complexBalanced_genuinePermanent` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`.  What changed is *where* the `sorryAx` lives,
*how much* of the case analysis is discharged, and *which* routes are now known to be dead.

---

## 1. Environment (reproduce before doing anything else)

Lean 4.34.0 + Mathlib v4.34.0, offline, no `lake`.

```
/home/claude/toolchain/lean-4.34.0-linux     # PATH
/home/claude/mathlib4                        # .lake/build/lib/lean has all oleans
/home/claude/crnt-cache/                     # symlink farm read by scripts/offline_build.py
  mathlib -> /home/claude/mathlib4
  aesop, batteries, Qq, plausible, proofwidgets, importGraph, LeanSearchClient, Cli
                                             #   -> /home/claude/mathlib4/.lake/packages/*
```

```sh
export PATH=/home/claude/toolchain/lean-4.34.0-linux/bin:$PATH
export CRNT_CACHE=/home/claude/crnt-cache
python3 scripts/offline_build.py CRNT.Dynamics.GlobalAttractorTheorem
```

`LEAN_PATH` for direct `lean` invocation is cached in `/home/claude/leanpath.txt`.

**Disk.** The quota is about 19 GB even though `df` reports 252 GB.  A full Lean + Mathlib
install does not fit unpruned.  What was removed, all of it safe for `lean` elaboration (verified
by re-running an import of `Mathlib.Analysis.ODE.Gronwall` after each removal):

* every `*.ilean` and `*.ilean.hash` in Mathlib and in the toolchain (language-server only);
* `lib/lean/*.a` in the toolchain (static archives, needed only to link executables);
* `lib/libclang-cpp.so.22.1`, `lib/libLLVM.so.22.1`, `libcrypto.a`, `libssl.a`;
* Mathlib's `docs/ Archive/ MathlibTest/ Counterexamples/ Wanted/ DownstreamTest/ widget/ Cache/ scripts/`.

Do **not** remove `*.olean.private` (3.5 GB), `*.olean.server`, or `*.ir`; the loader needs them.
Extract Mathlib source with `--exclude='*.ilean' --exclude='._*'` and delete AppleDouble `._*`
files afterwards — the bundle is a macOS tar and they waste inodes and confuse `find`.

Bash calls here are capped at 300 s.  The 184-module closure of the target takes about six
chunks; `offline_build.py` is incremental, so just re-invoke it under `timeout 280`.

---

## 2. Where the hole is now

**Before:** one `sorry` inside `complexBalanced_genuinePermanent`, in the branch where the
Anderson–Shiu facet count fails.

**After:** `complexBalanced_genuinePermanent` has no `sorry` of its own.  Its last branch closes by
applying

```
CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
    -- CRNT/Dynamics/HighCodimensionSiphonFace.lean
```

which is the sole remaining obligation and carries the `sorry`.  Repo-wide `dump_sorries.py`
reports **2** sorries total: this one and the pre-existing True-SR hole
(`stronglyConcordant_fullyOpen_of_trueSRCriterion`).  No new trust gap was introduced.

`HighCodimensionSiphonFace` is on `scripts/unverified_modules.txt` (ledger at 40, baseline 73) and
in `CRNTFrontier.lean`; `check_exclusions.py` passes all four invariants, in particular that the
verified core does not reach it.

---

## 3. What was proved

### `CRNT/Dynamics/FaceCodimension.lean` — the facet count fails only in codimension ≥ 2

Audits `[propext, Classical.choice, Quot.sound]`.

| theorem | content |
| --- | --- |
| `map_projOn_eq_bot_of_ker_finrank_eq` | a full-dimensional kernel makes the `W`-projection of the subspace trivial |
| `eq_zero_of_mem_of_ker_finrank_eq` | pointwise form: every stoichiometric displacement vanishes on `W` |
| `one_le_finrank_map_projOn` | one nonvanishing coordinate ⇒ the projection is at least a line |
| `finrank_map_projOn_singleton_le_one` | a one-species face projects to at most a line |
| `facet_of_singleton_witness` | hence a one-species face **always** satisfies the facet count |
| `stoich_witness_of_face_point` | `w - x₀` is the witness: it equals `-x₀ s ≠ 0` on the face |
| `highCodimension_of_not_facet` | the packaged dichotomy (below) |
| `ker_finrank_ne_of_face_point` | contrapositive: codimension zero is impossible |

`highCodimension_of_not_facet`: if `W` is a nonempty coordinate face met by a point `w`
stoichiometrically compatible with a positive `x₀`, and the facet count fails for `W`, then

```
2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn W))   ∧   2 ≤ W.card.
```

Two cases are thereby removed from the old `sorry`.  Codimension zero: every stoichiometric
displacement would vanish on `W`, forcing `w s = x₀ s > 0` against `w s = 0`.  Single species: the
projection of a positive-to-boundary displacement onto one coordinate is exactly one-dimensional,
so the facet count holds and the Anderson–Shiu branch already applies.

### `CRNT/Geometry/PolyhedralBarrier.lean` — the trapping engine, convex and non-convex

Audits `[propext, Classical.choice, Quot.sound]`.

* `le_of_dini_slope_nonpos_at_level` — abstract fencing.  A continuous `u` with `u 0 ≤ R` whose
  right Dini slope is nonpositive *at times where `u` has already reached `R`* never exceeds `R`.
  Proved by fencing the truncation `max u R` against `R + ε·t` with
  `image_le_of_liminf_slope_right_le_deriv_boundary`.  Truncating is what removes the need for the
  usual `sSup`-of-last-crossing-time construction: below the level the truncation is locally
  constant, so the Dini hypothesis is not needed there at all.
* `barrier L b x = max i (L i x - b i)`, with `le_barrier`, `exists_active`, `barrier_le_iff`,
  `barrier_lt_iff`, `continuous_barrier`, `isClosed_sublevel`.
* `eventually_barrier_lt_of_active_descent` — the Dini estimate for a barrier: inactive pieces stay
  below by continuity, active ones by their own derivative.
* `barrier_le_of_local_descent` — the convex trapping theorem.
* `minMaxBarrier L b x = min k (max i (L k i x - b k i))`, with
  `minMaxBarrier_le`, `exists_min_branch`, `continuous_minMaxBarrier`, `isClosed_minMaxSublevel`,
  `minMaxBarrier_le_of_local_descent`, `forwardInvariant_minMaxSublevel`,
  `dist_ge_of_minMax_local_descent`.
* `forwardInvariant_barrierSublevel`, `forwardInvariant_of_cone_descent`,
  `forwardInvariant_of_polar_descent`, `dist_ge_of_local_descent`.

**Why this was missing.**  `SmoothBarrierGluing.smoothWallList` is a log-sum-exp, so every wall
stays weakly active everywhere; consequently
`Network.WeaklyReversible.zeroSeparatingSurfaceExists_toric_activeWallList_of_compact_band` needs

```
hinward : ∀ m ∈ n :: ns.map Prod.fst, ∀ r : N.R, 0 ≤ ⟪toEuclid m, toEuclid (N.reactionVector r)⟫_ℝ
```

— one normal direction inward for **every** reaction simultaneously.  No such direction exists for
a general fan: which reaction dominates depends on which cone `log x` lies in.  A genuine maximum
localises, and a minimum of maxima localises *and* drops convexity.  For the min-max form only one
branch — any branch attaining the minimum — has to descend; the other branches and the inactive
pieces of the chosen branch are unconstrained.  That is exactly a tile-by-tile surface.

Note also that `DifferentialInclusion.ZeroSeparatingSurfaceExists` demands a `C¹` defining
function (`∀ y, HasFDerivAt g (g' y) y`), so a polyhedral barrier cannot be fed into it.  The new
module therefore ships its own wiring lemmas (`dist_ge_of_local_descent`,
`dist_ge_of_minMax_local_descent`) delivering the same `∃ r > 0, ∀ t ≥ 0, r ≤ dist (γ t) p`
conclusion that `ZeroSeparatingSurfaceExists.away_from_origin` provides.

### `CRNT/Geometry/FanFaceLattice.lean` — fan axioms, the δ-core, and the descent bridge

Audits `[propext, Classical.choice, Quot.sound]`.

**Correction to an earlier assumption.**  Two things I had recorded as missing were already
present.  `CRNT/Geometry/ConeFace.lean` defines `CRNT.IsPolyhedralFan` with exactly the three
axioms of Craciun v3 Definition 4.1 (closure under exposed faces, pairwise intersections again
cones of the family, covering), and
`Network.relativeSourceOrderNegativeStoichFan_isPolyhedralFan` **proves** them for the fan the
complex-balanced embedding uses.  Mathlib 4.34 also has `PointedCone.IsFaceOf` and a cone face
lattice under `Mathlib/Geometry/Convex/Cone/Face/`, so the comment at `ToricFan.lean:47–51` about
missing polytope face theory is out of date.  I first wrote a duplicate `IsFan` record and then
deleted it; do not reintroduce one.

| theorem | content |
| --- | --- |
| `IsPolyhedralFan.inf_mem` | a fan is closed under lattice `⊓` (the axiom gives a cone with carrier `C ∩ D`, and a proper cone is determined by its carrier) |
| `IsPolyhedralFan.exists_mem` | completeness in usable form: every point lies in some cone |
| `nearCones F δ X` | the cones of `F` within `δ` of `X` — exactly those whose polars generate the toric field at `X` |
| `nearCones_nonempty` | nonempty, since the cone containing `X` is at distance `0` |
| `deltaCore F δ X h` | their intersection: the cone Remark 4.5 forces the ZSH normal into |
| `deltaCore_mem` | the δ-core is again a cone of the fan |
| `mem_of_mem_deltaCore` | anything in the δ-core lies in every nearby cone |
| `inner_nonneg_of_mem_toricField` | **the descent bridge (Remark 4.5)**: a vector in every cone within `δ` of `X` pairs nonnegatively with the entire toric field at `X` |
| `forwardInvariant_barrier_toricInclusion` | barrier whose normals lie in the nearby cones ⇒ the sublevel set is forward invariant for `toricInclusionField` |

**The mass-action specialisation** (this is the part that closes the second item of the old §5
task list).  The embedding, Craciun v3 Theorem 3.1, is already proved in
`CRNT/Dynamics/ComplexBalanceStoichFanInclusion.lean` as
`massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan`; it was only hard to
find because its statement inlines two subtype terms behind `let` binders.  Those are now named:

* `Network.euclideanMassActionField κ x` — the mass-action velocity transported into
  `N.euclideanStoichSubspace`;
* `Network.relativeLogFanState xstar x` — minus the stoichiometric projection of
  `log x - log x*`, the point at which the fan is read;
* `Network.euclideanMassActionField_mem_toricField` — the embedding, restated in those terms;
* `Network.deltaCore_mem` — the δ-core of the source-order fan is a cone of it;
* `Network.inner_euclideanMassActionField_nonneg` — **the descent inequality for complex-balanced
  mass action**: if `n` lies in every cone of the source-order fan within `δ` of the relative-log
  state of `x`, then `0 ≤ ⟪n, euclideanMassActionField κ x⟫`, i.e. `-n` is a valid barrier normal
  there;
* `Network.inner_euclideanMassActionField_nonneg_of_mem_deltaCore` — the δ-core form, which needs
  no choice of `n` beyond membership in a canonical cone of the fan.

### `CRNT/Dynamics/ToricBarrierTrapping.lean` — the analytic half, end to end

Audits `[propext, Classical.choice, Quot.sound]`.  This module joins the descent inequality to the
trapping engine and carries the reduction all the way to the residual's own conclusion.

*Coordinates.*  A mass-action trajectory lives in `Concentration S`; the fan and the barrier live
in `N.euclideanStoichSubspace`.

| theorem | content |
| --- | --- |
| `Network.euclideanStoichState x` | the state transported by orthogonal projection of `toEuclid x` |
| `Network.euclideanStoichStateL` | the same as a continuous linear map |
| `Network.euclideanStoichStateL_massActionVectorField` | the transport fixes the mass-action velocity (it is already in the stoichiometric subspace), so it lands on `euclideanMassActionField` |
| `Network.hasDerivAt_euclideanStoichState` | **the transport lemma**: the transported trajectory solves the transported ODE |
| `Network.continuous_euclideanStoichState_comp` | continuity of the transported trajectory |

*Trapping.*

| theorem | content |
| --- | --- |
| `Network.barrier_le_of_toric_descent` | convex form: one normal per piece, active normals in the nearby fan cones ⇒ the barrier never exceeds `R` |
| `Network.minMaxBarrier_le_of_toric_descent` | **non-convex form**, one branch per tile; this is the one a blueprint should feed |
| `Network.dist_ge_of_toric_descent` | a hard distance bound in the transported space |
| `Network.coordinate_lower_bounds_of_toric_barrier` | uniform positive floors on every coordinate of the trajectory, from the separation clause |
| `Network.exists_positive_omegaPoint_of_coordinate_floors` | compact orbit + floors ⇒ a positive ω-point (duplicates the same statement in the ledgered `GlobalAttractorTheorem.lean`, which cannot be imported into the core) |
| `Network.exists_positive_omegaPoint_of_toric_blueprint` | **the reduction** |
| `Network.exists_positive_omegaPoint_of_toric_halfspace` | the one-tile, one-piece instance: a single affine halfspace, which is the conservative / strongly-endotactic mechanism expressed inside the toric framework |

`exists_positive_omegaPoint_of_toric_blueprint` takes the blueprint data — tiles `ι'`, pieces `ι`,
fan vectors `n`, levels `b`, level `R`, band `δ > 0` — plus three clauses:

* `hstart`: the orbit starts inside the guarded region;
* `hnear`: on each tile the active normals lie in every fan cone within `δ` of the relative-log
  state (v3 Lemma 9.5 with the Lemma 9.7 slack);
* `hsep`: the guarded region, inside the positive compatibility class, is bounded away from every
  coordinate hyperplane (v3 Definition 4.6(i));

and concludes `∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive` — **exactly** the conclusion of the one
remaining `sorry`.  The orbit hypotheses are the usual ones plus
`hclass : ∀ t ≥ 0, N.StoichCompatible (γ x₀ 0) (γ x₀ t)`, taken as a hypothesis rather than proved
(it is a standard property of mass-action flows and the caller has it).

`PolyhedralBarrier.barrier_unique` and `minMaxBarrier_unique` evaluate a one-piece / one-branch
barrier, which is what makes the halfspace instance short.  That instance is not strong enough in
general — a single tile is impossible in dimension `≥ 3` by `ConvexBarrierObstruction` — but it
exhibits the blueprint interface at its simplest and confirms the three clauses are inhabitable.

I deliberately did **not** rewrite the `sorry` to assert blueprint existence.  Doing so would make
the open statement dynamics-free, but if my rendering of the blueprint were subtly unsatisfiable
the `sorry` would become a false statement and the difficulty would be hidden rather than reduced.
The implication is machine-checked instead, and the `sorry` keeps its faithful form.

### `CRNT/Geometry/ConvexBarrierObstruction.lean` — the convex route is dead

Audits `[propext, Classical.choice, Quot.sound]`.

* `not_exists_weights_gram`, `not_exists_weights_vector` — three unit vectors with all pairwise
  inner products equal to `c > 1/2` admit **no** positive weights `w` making every zonotope vertex
  `v_σ(w) = ∑_j w_j σ_j a_j` lie in its own normal cone.
* `witness_gram_posDef` — `c = 3/5` is admissible and the Gram matrix minors are `1, 16/25, 44/125`,
  all positive, so such a triple exists in `ℝ³` and is a basis.

---

### `CRNT/Dynamics/FaceDirectionCone.lean` — which fan cones can matter

Audits `[propext, Classical.choice, Quot.sound]`.  A blueprint builder needs to know *which* cones
of the fan can possibly be near the relative-log state when `x` is near a coordinate face.  This
answers that, and it is the content of v3 §6.1.3 ("outside the unit cube the toric field at `P`
will not depend on `C`, but on the intersection between `C` and `∂₁D^H₂`").

| theorem | content |
| --- | --- |
| `Network.relativeLogFanState_eq` | the relative-log state is exactly `euclideanStoichStateL (log x* − log x)` — a transport, so linear algebra applies to it |
| `Network.euclideanStoichUnit s` | the projected coordinate direction of a species |
| `Network.faceDirectionCone P` | `PointedCone.hull ℝ (euclideanStoichUnit '' P)` — the asymptotic direction cone of the `P`-face, depending on `P` and the network only |
| `Network.sum_smul_mem_faceDirectionCone` | nonnegative combinations of `P`-directions lie in it |
| `Network.euclideanStoichStateL_indicator` | the `P`-restriction of a coefficient vector expands over the `P`-directions |
| `Network.relativeLogFanState_eq_add` | **the splitting**: relative-log state = (`P`-part, in the cone) + (transport of the off-`P` data) |
| `Network.exists_mem_faceDirectionCone_dist_eq` | witness form: an explicit cone point at distance exactly `‖off-P part‖` |
| `Network.infDist_relativeLogFanState_faceDirectionCone_le` | **face localization**: the relative-log state lies within `‖off-P part‖` of `faceDirectionCone P` |
| `Network.exists_dist_lt_faceDirectionCone_of_infDist_lt` | **the usable form**: any fan cone within `δ` of the relative-log state comes within `δ + ‖off-P part‖` of `faceDirectionCone P` |
| `Network.faceLogPart` / `offFaceLogPart` | the two summands of the relative-log state, and `relativeLogFanState_eq_faceLogPart_add` |
| `Network.dist_relativeLogFanState_faceLogPart` | the distance between the state and its face part is exactly `‖off-face part‖` |
| `Network.relevantCones σ δ B` | the cones an **angular tile** `σ` must accommodate: those within `δ + B` of `σ` |
| `Network.relevantCore σ δ B` | their intersection — one normal legal for all of them |
| `Network.relevantCore_mem` | the core is itself a cone of the fan |
| `Network.relevantCones_subset_of_subset`, `relevantCore_le_of_subset` | **subdividing enlarges the core**: a smaller tile accommodates fewer cones |
| `Network.mem_relevantCones_of_infDist_lt` | localization to a tile: if the face part is in `σ` and the off-face part is `≤ B`, every cone within `δ` of the state is one `σ` must accommodate |
| `Network.faceRelevantCones` / `faceRelevantCore` | the one-tile case, `σ = faceDirectionCone P` |
| `Network.exists_positive_omegaPoint_of_tiled_faceCores` | **the multi-tile criterion** (below) |
| `Network.exists_positive_omegaPoint_of_faceRelevantCore` | its one-tile specialization, as a single halfspace |

`CRNT.subfanCore` in `FanFaceLattice` was factored out of `deltaCore` for this: the intersection of
any nonempty finite subfamily of a fan is again a cone of the fan (`subfanCore_mem`), and both the
δ-core and the face-relevant core are instances.  `deltaCore_eq_subfanCore` records that they agree
by `rfl`, so the old API is untouched.

`exists_positive_omegaPoint_of_tiled_faceCores` is the payoff.  Its blueprint data is a finite
family of angular tiles `σ : ι' → Set`, one normal `m k ∈ relevantCore (σ k) δ B` per tile, and one
level `b k`; the guarded region is the min over tiles of the halfspaces `⟪-m k, ·⟫ ≤ b k + R`.
Every cone condition in it is a condition on the fan, the tiles and the two scalars `δ`, `B` —
**no orbit times appear inside them**.

The orbit supplies only `hassign`: whenever the level is reached, some tile `k` attains the minimum,
the point is in the near-`P` regime (below `xstar` on `P`, off-face part bounded by `B`), **and**
its face part lies in that tile's `σ k`.  That last conjunct is the log-to-linear coupling — the
tile winning the minimum in state space must be the one containing the face part of the
relative-log state — and it is the one place where Craciun's `Ψ` correspondence (§6.1.2, Lemmas
9.9–9.10) is still needed.

`relevantCore_le_of_subset` says refining the tiles only ever helps on the cone side, so a
sufficiently fine subdivision always has nonzero cores.  The difficulty is entirely in making the
refinement compatible with `hassign`.


The `P`-part coefficients are `log (xstar s) − log (x s)`, nonnegative exactly when `x s ≤ xstar s`
— which is the hypothesis, and is what "near the face" means.  On a tile where the off-`P`
coordinates range over a compact set, `‖off-P part‖` is uniformly bounded, so the cone family a
tile must accommodate is determined by `P` alone.  Note the coherence with §3: if *every* projected
direction `euclideanStoichUnit s`, `s ∈ P`, were zero the cone would be trivial — and that is
exactly the codimension-zero case already excluded by `ker_finrank_ne_of_face_point`.

### `CRNT/Dynamics/ToricBarrierExplicit.lean` — the clauses as concentration inequalities

Audits `[propext, Classical.choice, Quot.sound]`.  The multi-tile criterion states its clauses in
terms of `euclideanStoichState`, `faceLogPart` and `minMaxBarrier`.  For *constructing* a blueprint
one wants them as inequalities in the concentrations; this module translates.

The key identity is `inner_euclideanStoichStateL_eq_sum`:

```
⟪m, euclideanStoichStateL z⟫ = ∑ s, (m : EuclideanSpace ℝ S) s * z s.
```

The orthogonal projection moves onto `m` (`Submodule.inner_starProjection_left_eq_right`), where it
is the identity because `m` already lies in the subspace — so the inner product never sees the
projection.  Consequences:

| theorem | content |
| --- | --- |
| `Network.inner_euclideanStoichState_eq_sum` | pairing with the transported state is `∑ s, m s * x s` |
| `Network.inner_faceLogPart_eq_sum` | the tile condition is a weighted sum of log-deviations over the face |
| `Network.inner_offFaceLogPart_eq_sum` | the off-face bound is a weighted sum off the face |
| `PolyhedralBarrier.minMaxBarrier_le_iff` | a min-max barrier is below a level iff some branch is |
| `Network.minMaxBarrier_euclideanStoichState_le_iff` | **the guarded region is a union of halfspaces**: `∃ k, -(∑ s, m k s * x s) - b k ≤ R` |
| `Network.coordinate_floor_of_tilewise` | **reduces `hsep`** to finitely many elementary statements, one per (species, tile): does one linear inequality plus positivity plus compatibility force `x s ≥ ε`? |

A structural fact that falls out of this form and is worth recording: a single halfspace
`∑ u, a u * x u ≥ η` with `a ≥ 0` bounds a *combination* of coordinates from below, never an
individual one.  So for a **union** of halfspaces (`minMaxBarrier`) *every* piece would have to
force *every* coordinate's floor, because a point of the region satisfies only one of them.

### Correction: the natural region is convex

Looking again at v3 Figure 3(d), the zero-separating curve is convex toward the origin, and the
region above a convex decreasing staircase is the **intersection** of the halfspaces above its
faces — a `barrier` (max of affine), not a `minMaxBarrier`.  That is much better for separation: a
point of an intersection satisfies *every* halfspace, so **one** halfspace per species suffices.

This does not conflict with `ConvexBarrierObstruction`, which rules out a *globally homogeneous*
convex barrier over the arrangement fan in dimension `≥ 3`.  Craciun's surface lives in a bounded
window of log-coordinates and is not homogeneous, which is exactly the escape already noted in §4.
Both engines are available: `barrier_le_of_toric_descent` for the convex case that the construction
actually uses, `minMaxBarrier_le_of_toric_descent` as the fallback generality.

| theorem | content |
| --- | --- |
| `Network.barrier_euclideanStoichState_le_iff` | the convex region, explicitly: `∀ k, -(∑ s, m k s * x s) - b k ≤ R` |
| `Network.le_of_halfspace_of_dominant` | **a halfspace with a dominant coefficient forces a coordinate floor**: if `a s > 0` and `η > M * ∑_{u ≠ s} |a u|` with all coordinates in `[0, M]`, then `η ≤ ∑ u, a u * x u` pins `x s` away from zero |
| `Network.coordinate_floor_of_dominant_barrier` | **separation discharged**: give each species one piece with positive coefficient there and a high enough level, and the convex region keeps every coordinate off zero |

`coordinate_floor_of_dominant_barrier`'s hypotheses are elementary inequalities in the
coefficients — no cones, projections or logarithms.  Together with `barrier_le_of_toric_descent`
this **closes the separation clause** of a blueprint.

### Eliminating the tile-assignment clause

| theorem | content |
| --- | --- |
| `Network.exists_positive_omegaPoint_of_convex_tiles` | the convex multi-piece criterion, proved directly from `barrier_le_of_toric_descent` and `exists_positive_omegaPoint_of_coordinate_floors` |
| `Network.activeFaceImage P xstar m b R B i` | the relative-log face parts actually reachable where piece `i` is active and the regime holds |
| `Network.faceLogPart_mem_activeFaceImage` | membership, by construction |
| `Network.exists_positive_omegaPoint_of_selfConsistent_normals` | **`hassign` eliminated** |
| `Network.exists_positive_omegaPoint_of_blueprintData` | **the sharpest form of what remains** (below) |

Take each angular tile to be `activeFaceImage`.  Then the tile-assignment clause — the
log-to-linear coupling, the one place Craciun still needs his `Ψ` correspondence — holds *by
construction*, and what remains is a **self-consistency condition on finitely many vectors and
scalars**:

> each `m i` lies in `relevantCore (activeFaceImage … i) δ B`.

No tiles have to be chosen and no correspondence between log-space and state-space regions has to
be established.  The blueprint problem is now: find `m : ι' → euclideanStoichSubspace`,
`b : ι' → ℝ` and scalars `R`, `B` with that `hm`, plus `hstart` (the orbit starts inside),
`hregime` (the region sits in the near-face regime) and `hsep` (already discharged by
`coordinate_floor_of_dominant_barrier`).

`hm` is self-referential: shrinking the region shrinks the active images, which *enlarges* their
cores by `relevantCore_le_of_subset`.  So it is a fixed-point problem with monotonicity in the
helpful direction, which is what the `ε(α)` scale hierarchy of v3 §7.4.3 is for.

Note the cone clause is stated **directly** — `∀ C ∈ relevantCones (σ i) δ B, m i ∈ C` — rather than
through `relevantCore`.  That drops the spurious `Finset.inf'` nonemptiness side-condition and makes
the clause vacuous exactly when a piece is never active in the regime.  `relevantCore` plus
`mem_of_mem_relevantCore` remains the canonical way to *produce* such an `m i`.

### The sharpest form of what remains

`exists_positive_omegaPoint_of_blueprintData` takes an arbitrary finite piece index `ι'` together
with a map `piece : S → ι'` assigning each species *some* piece that is positive at it with a high
enough level.  `piece` is not assumed injective or surjective, deliberately: the construction is
expected to need **more** pieces than species (Craciun's blueprint has one face per tile, and the
tiles refine far past one per coordinate direction), while separation needs only one dominant piece
per species.

An earlier version of this theorem indexed the pieces by the species themselves.  That was a
mistake — it forces exactly `|S|` pieces, and with so few pieces each active image is large, which
makes `hm` unsatisfiable for the reason given below.  Do not reintroduce it.

With that data, `hsep` is discharged internally by `coordinate_floor_of_dominant_barrier`,
`hassign` internally by `activeFaceImage`, and descent/trapping/transport by the verified chain.
What is left is exactly `hm`, `hstart` and `hregime`:

> Find a finite family of stoichiometric vectors `m i` and levels `b i`, with each species covered
> by some `m i` positive at it, such that every `m i` lies in **every** cone of
> `N.relativeSourceOrderNegativeStoichFan` coming within `δ + B` of the set of relative-log face
> parts reachable where `m i` is the active piece.

No dynamics, no analysis, no log-to-linear correspondence.

Why refinement is the only lever: a vector lying in a *proper* intersection of two maximal cones can
be forced to `0`, which contradicts `hpos`.  So a coarse family cannot work.  More pieces and higher
levels shrink each active image, which enlarges the cone intersection each normal must sit in
(`relevantCore_le_of_subset`).  That monotonicity is the whole point of the `ε(α)` scale hierarchy
of v3 §7.4.3.

The hypothesis `hMclass` — the positive compatibility class is bounded by `M` — is automatic for
conservative networks.  In general it must be replaced by a level set of the Horn--Jackson Lyapunov
function, which is what `CRNT.Geometry.ZeroSeparatingSurface`'s compact-band machinery is for.  So
this template does **not** yet cover every network; it covers the conservative case cleanly and
marks exactly where the extra work goes.

## 3b. Regression guard

`test/ToricBarrierAudit.lean` is a runnable axiom-cleanliness guard for everything added here:
seventy-seven `#print axioms` checks pinned with `#guard_msgs (whitespace := lax)`, each demanding
`[propext, Classical.choice, Quot.sound]`.  It imports only the new modules, so it builds in
seconds:

```sh
python3 scripts/offline_build.py test.ToricBarrierAudit
```

It passes.  `test/AxiomAudit.lean` imports all of `CRNT` and takes hours, so I did not extend it —
adding entries I could not execute would be worse than not adding them.  Extend it when a full
core build is affordable.

**The full verified core now builds.**  `python3 scripts/offline_build.py CRNT` completes all
**700** modules with **zero failures**, so the standing caveat about only building the affected
closure is retired.  A name-collision scan over the 123 declarations added this session found none
(the scan compared bare names across the whole tree, so it over-reports rather than
under-reports).

`test/AxiomAudit.lean`, the repo's own acceptance test, also passes now that the core is built —
**after one correction**.  It was failing on a *stale pinned expectation*, independent of this
session's work:

```
- info: 'CRNT.Network.numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Quot.sound]
+ info: 'CRNT.Network.numDiagonalDriveSpecies_eq_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That declaration lives in `CRNT/Decision/InjectivityMargin.lean`, whose 36-module import closure
contains **none** of the modules added this session, so its axiom dependence cannot have been
changed here — the expectation was simply out of date.  The actual axiom set is the standard clean
one; I corrected the docstring to match, and the whole audit then passes.

### The frontier also builds, and its acceptance test is stale wholesale

`python3 scripts/offline_build.py CRNTFrontier` completes all **473** modules with **zero
failures**.  This contradicts the docstring of `test/FrontierAudit.lean`, which says
`CRNTFrontier` "does not elaborate yet" because three Floquet constructions are referenced but
never declared.  Those three names —
`constructTransverseFloquetSectionData`, `constructParameterizedPoincarePersistence`,
`massActionFloquetData_of_branchMonodromy` — now have **zero** references anywhere in `CRNT/`, so
that gap has been closed since the docstring was written.  `scripts/frontier_gaps.txt` is likewise
out of date on this point.

`test/FrontierAudit.lean` still cannot be run against this snapshot, but for a different reason:
**every declaration it audits is absent.**  All of `completeOscillationKernelBundle_of_tube`,
`planarKernelBundle_proved`, `vassenaKernelBundle_proved`,
`parameterRichCoreKernelBundle_proved`, `stabilityInheritanceKernelBundle_of_tube`,
`recipeZeroKernelBundle_proved`, `nondegenerateDependentReactionPersistence_proved` and
`stableDependentReactionPersistence_proved` have zero references in `CRNT/`.  The file belongs to a
different snapshot than the source tree.

I deliberately **did not** "fix" it.  Deleting the eight failing checks would silently weaken an
acceptance test; the single stale *expectation* in `AxiomAudit.lean` was safe to correct because the
declaration exists and its true axiom set is clean, whereas here the targets themselves are
missing.  Someone who knows which snapshot the oscillation bundle lives in should reconcile the two,
and `test.FrontierAudit` should stay in `UNVERIFIED_TESTS` until then.

Instead I added **`test/FrontierAuditCurrent.lean`**, a gating audit that does match the tree.  It
is in the `test` library (not excluded), it passes, and it pins:

* the five incomplete endpoints **with** their `sorryAx` — the two holes and their downstream
  consumers;
* the clean frontier endpoint `floquetOrbitalStability_of_tube`;
* seven links of the GAC reduction chain, which must stay clean.

Pinning the *incomplete* results is the point: a test that only pins clean results cannot notice a
new hole.  If a third incomplete endpoint appears, or if one of these is closed, this file fails and
forces the ledger and handoffs to be updated in the same commit.

### `scripts/frontier_gaps.txt` refreshed

`python3 scripts/check_undefined_names.py --write-gaps` reports the three Floquet obligations
**closed** and rewrites the list.  The character of the list has changed: all four remaining entries
live in *test* files, so **no module under `CRNT/` references an undeclared identifier any more**.

```
completeOscillationKernelBundle_of_tube            test/FrontierAudit.lean
noDrainableSiphonOmega_of_minimalDichotomy         test/GlobalPersistenceSmoke.lean
nondegenerateDependentReactionPersistence_proved   test/FrontierAudit.lean
stableDependentReactionPersistence_proved          test/FrontierAudit.lean
```

Three of those four are the stale `FrontierAudit.lean` references, i.e. artifacts of the snapshot
mismatch rather than proof obligations.  They will disappear when that file is reconciled.

The fourth, `noDrainableSiphonOmega_of_minimalDichotomy` in `test/GlobalPersistenceSmoke.lean`, is
also a stale `#check` and should **not** be satisfied by writing a declaration with that name.  The
only sensible reading of the name would be

```
theorem noDrainableSiphonOmega_of_minimalDichotomy (N : Network S)
    (hreal : N.FluxSignRealizable) (hcons : N.IsConsistent)
    (hdich : N.MinimalCriticalSiphonDichotomy)
    (hnd : N.HasNoDrainableSiphon) : N.StructurallyOmegaPersistent
```

— composing `hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy`
(`CRNT/Dynamics/SiphonAutocatalysis.lean:640`) with the persistence consequence.  But
`Network.noDrainableSiphonOmegaPersistence` (`CRNT/Dynamics/GlobalPersistenceFrontier.lean:104`)
already proves `HasNoDrainableSiphon → StructurallyOmegaPersistent` with **no** dichotomy
hypothesis at all, so any such theorem would be strictly weaker and redundant.  Adding a redundant
declaration purely to make a `#check` succeed is the wrong trade: it makes the gap list shorter
while making the library worse.  Delete the stale `#check` instead, once someone confirms it is not
tracking an intended stronger statement.

## 4. The reduction that produced the obstruction (read this before trying a convex barrier)

Craciun's requirement, Lemma 9.5 plus the `δ`-slack of Lemma 9.7: at a smooth point `X` of the
zero-separating hypersurface the outer normal must lie in **every** fan cone within distance `δ` of
`X`, hence in the smallest one.  Near a wall that is a *low-dimensional* cone, so the surface must
be flat on a slab of width at least `δ` around each cone, with that flat piece's normal in that
cone.  A smooth surface cannot do this: the sphere satisfies the `δ = 0` condition of Lemma 9.5
exactly (its normal at `X` is `X`, which lies in the cone containing `X`) and fails Lemma 9.7.

For a **convex** barrier `g X = max i (⟪n i, X⟫ - b i)` the max structure additionally forces
`⟪n_C, X⟫ ≥ ⟪n_{C'}, X⟫` for `X ∈ C`; constant offsets cannot repair a violation because the
deficit grows linearly along `C`.  So `{n_C}` must be the face points of a polytope whose normal
fan refines the fan, each inside its own normal cone.

Two further steps pin this down for a hyperplane-generated fan (v3 §3), normals `a_1..a_m`:

1. *Matching across a wall forces the zonotope.*  Let `C`, `C'` be adjacent maximal cones sharing
   the wall `W_j ⊆ h_j = {⟪a_j, X⟫ = 0}`.  Every point of the `δ`-slab around `W_j` is within `δ`
   of `W_j`, so the slab's normals lie in `W_j ⊆ h_j`.  For the ridge separating a slab piece
   (normal `m`) from a `C` piece (normal `n`) to stay at distance `≥ δ` from `span W_j` along all
   of `W_j`, the ridge hyperplane `{⟪m - n, X⟫ = β}` must contain the directions of `W_j`, i.e.
   `m - n ⊥ h_j`, i.e. `m - n ∈ ℝ a_j`.  Hence `n_{W_j} = P_{h_j}(n_C)` and
   `n_C - n_{C'} ∈ ℝ a_j` — the zonotope edge structure.  So `n_{C_σ} = v_σ(w) = ∑_j w_j σ_j a_j`
   for some weights `w > 0`, and the arrangement fan is the normal fan of `∑_j w_j [-a_j, a_j]` for
   any such `w`.
2. *The weight problem is a linear program.*  `v_σ(w) ∈ C_σ` reads
   `0 ≤ σ_k ∑_j w_j σ_j ⟪a_k, a_j⟫` for every `k`, which is linear in `w`.

`scripts/probe_zonotope_cone_selection.py` solves that LP.  Findings:

* `w = 1` already fails: 11 normals at `0°..10°` plus one at `178°` makes the all-positive sign
  vector realizable while `⟪a_{178°}, ∑_j a_j⟫ ≈ -9.90`.
* In **dimension 2** the weighted LP is always strictly feasible over the random sample.
* In **dimension ≥ 3** it was infeasible in every random trial (dims 3 and 4, `m` from 3 to 7).
* The exact reason, formalized in `ConvexBarrierObstruction`: three unit vectors pairwise at inner
  product `c` are a basis when `c < 1`, so **all eight** sign vectors are realizable, and the
  constraints collapse to strict diagonal dominance `w_k ≥ c(w_i + w_j)` for each `k`.  Summing
  gives `W ≥ 2cW` with `W > 0`, hence `c ≤ 1/2`.  For `c = 3/5` this is a contradiction, and the
  LP cross-check returns margin exactly `-0.2`.

**Conclusion.**  A globally homogeneous convex polyhedral barrier over the arrangement fan is
impossible in dimension `≥ 3`.  This is why `minMaxBarrier` exists.  Note carefully what the
obstruction does *not* say: Craciun's construction is confined to a bounded window of
log-coordinates (§6.1.3 works inside `[0, M]^n`, so `log` coordinates are bounded below by
`log ε₀` and above by `log M`), which is precisely how the paper escapes step 1 above — the
"out to infinity" argument that forces the zonotope does not apply on a bounded window.  That is
also why the paper needs the `ε(α)` scale hierarchy of §7 rather than a single `δ`.

---

## 5. What remains

The obligation is `exists_positive_omegaPoint_of_highCodimension_siphonFace`.

Every analytic and dynamical ingredient is now in place and verified:

* the **descent inequality** — `Network.inner_euclideanMassActionField_nonneg`;
* the **trapping engine** — `PolyhedralBarrier.minMaxBarrier_le_of_local_descent`;
* the **coordinate transport** — `Network.hasDerivAt_euclideanStoichState`;
* the **reduction** — `Network.exists_positive_omegaPoint_of_toric_blueprint`, which derives the
  residual's exact conclusion from the blueprint data.

So one thing is left, and it is purely geometric:

> **Produce the blueprint.**  For the fan `N.relativeSourceOrderNegativeStoichFan`, a band
> `δ > 0`, and a positive start `x₀`: finite index types `ι'` (tiles) and `ι` (pieces), vectors
> `n : ι' → ι → N.euclideanStoichSubspace`, levels `b`, and a level `R`, satisfying `hstart`,
> `hnear` and `hsep` of `exists_positive_omegaPoint_of_toric_blueprint`.

Two things now make that target concrete rather than open-ended:

* `Network.deltaCore_mem` supplies the canonical cone each normal may be drawn from — the δ-core of
  a point is itself a cone of the fan;
* `Network.exists_dist_lt_faceDirectionCone_of_infDist_lt` bounds *which* cones a tile has to
  accommodate: only those coming within `δ + ‖off-P part‖` of `faceDirectionCone P`, a cone fixed
  by the face alone — collected as the `Finset` `Network.faceRelevantCones P δ B`;
* `Network.exists_positive_omegaPoint_of_tiled_faceCores` closes the whole descent side for an
  arbitrary finite family of angular tiles, and `relevantCore_le_of_subset` shows refining tiles
  only helps.  So the genuinely open part is **just** `hassign` plus `hsep`: choose the tiles,
  normals and levels so that the tile winning the min-max in state space is the one containing the
  face part of the relative-log state, and so that the guarded region stays off the boundary.
  Both clauses are now available in explicit concentration form
  (`barrier_euclideanStoichState_le_iff`, `minMaxBarrier_euclideanStoichState_le_iff`,
  `inner_faceLogPart_eq_sum`), so no further translation work is needed before attacking them.

Moreover `hsep` is **done** in the convex case (`coordinate_floor_of_dominant_barrier`), and
`hassign` has been **eliminated** rather than proved: with `activeFaceImage` as the tiles it holds by
construction (`exists_positive_omegaPoint_of_selfConsistent_normals`).  What is left is the single
self-consistency clause `hm`, a fixed-point problem about finitely many vectors `m i` and scalars
`b i`, `R`, `B`, with `relevantCore_le_of_subset` giving monotonicity in the helpful direction.
That, plus `hstart` and `hregime`, is the whole remaining content of v3 §7–§8.

What is left is the combinatorial choice of tiles, normals inside their δ-cores, and levels that fit
together: the `ε(α)` scale hierarchy of v3 §7.4.3 (Case 1.1 lifting, Case 1.2 filling, Step 2
refinement), then §8 Steps 1–4 for exhaustiveness in `x₀`.

At least two tiles are required in general: a single-tile (convex) blueprint is impossible in
dimension `≥ 3` by `ConvexBarrierObstruction.not_exists_weights_vector`.

`CRNT/Geometry/FanRefinement.lean` and `CRNT/Geometry/ToricUniformWallMargin.lean` already carry the
arrangement atlas, seam certificates, common-face incidence and the well-founded recursion index
(`oneBitFanFaceDependency` and its recursor), all auditing clean — but no caller uses the recursor
to emit geometric data.  **That caller is the single next task**, and its target is now a completely
specified Lean signature: the three clauses above.

## 5b. Gap analysis: three bridges I had not counted

`docs/gac-bridge-gap-analysis.lean` (runnable, not part of the build; see the accompanying `.md`)
attempts to derive the residual obligation from `exists_positive_omegaPoint_of_blueprintData` and
leaves a `sorry` for each fact the residual's context does not supply.  It elaborates with **exactly
three** `sorry`s and no errors, so the composition is machine-checked and the remaining plumbing is
precisely:

| bridge | statement | status |
| --- | --- | --- |
| 1 | `ContinuousOn (γ x₀) (Set.Ici 0)` | **DISCHARGED** — Dini lemmas weakened to `ContinuousOn · (Ici 0)`; immediate from `hsol` |
| 2 | `∀ t ≥ 0, (γ x₀ t).Positive` | **DISCHARGED** — `Network.orbit_pos_forward` in `CRNT/Dynamics/OrbitRegularity.lean`, ceiling from `hK`/`hmaps` |
| 3 | `∀ t ≥ 0, N.StoichCompatible (γ x₀ 0) (γ x₀ t)` | **DISCHARGED** — `Network.stoichCompatible_of_forward_solution` in `CRNT/Dynamics/OrbitRegularity.lean`, from `hsol` alone |

**Correction.**  Earlier sections of this document said the blueprint criterion yields "exactly the
conclusion" of the residual and that only `hm`, `hstart`, `hregime` remained.  The *conclusion* does
match on the nose, but the *hypotheses* do not — these three bridges are additional obligations.

Bridge 1 is mine: `PositiveOmegaPointForRates` gives `hsol` only for `t ≥ 0`, while
`PolyhedralBarrier.le_of_dini_slope_nonpos_at_level` and `eventually_barrier_lt_of_active_descent`
ask for global `Continuous`.  Weakening both to `ContinuousOn · (Set.Ici 0)` works — the inactive
piece step becomes `ContinuousWithinAt … (Ici 0) t` plus `nhdsWithin_mono` (valid because `0 ≤ t`
gives `Ioi t ⊆ Ici 0`) — and then has to be propagated through about fourteen signatures.  The
`forwardInvariant_…` lemmas are unaffected.  A shortcut that does **not** work: reparametrising as
`fun t => γ x₀ (max t 0)` to force global continuity, since that curve has no two-sided derivative
at `0`.

Bridges 2 and 3 are both proved in `CRNT/Dynamics/OrbitRegularity.lean`, and the gap-analysis file
now elaborates with exactly **one** `sorry` — bridge 1.

Bridge 3 is a three-line corollary of `Network.sub_mem_stoichSubspace_of_solution`, which already
existed in `AsymptoticStability.lean`.  My first attempt reproved it from scratch; **search
`AsymptoticStability.lean` before proving anything about mass-action solutions** — it also holds
`orbit_pos`, `exists_field_lower_bound` and `ge_mul_exp_of_forward_deriv_ge`.

Bridge 2 is `Network.orbit_pos_forward`, the unclamped forward-time analogue of `orbit_pos`.  The
Gronwall input comes from `exists_field_lower_bound`, so no `L` or `hbound` is in the signature;
continuity only on `Ici 0` forces `IsClosed.isClosed_le` relative to `Ici 0` and `le_on_closure`
for the limit step.

Bridge 1 is also done: the Dini lemmas now take `ContinuousOn · (Set.Ici 0)` (note
`ContinuousOn.sup`, not `ContinuousOn.max`, and `.mono Set.Icc_subset_Ici_self` for the fencing
step), propagated through the chain plus a new `Network.continuousOn_euclideanStoichState_comp`.

**All three bridges are discharged, and `docs/gac-bridge-gap-analysis.lean` now elaborates with no
`sorry` and no errors.**  The residual obligation follows from the blueprint data alone — nothing
about the orbit is missing.  What is left is exactly `hm`, `hstart`, `hregime` and the coefficient
conditions `hMclass`, `hpos`, `hlevel`.

## 5c. CORRECTION: the tile definition was vacuous, and is repaired

This is the most important entry in this document.  The version of
`Network.activeFaceImage` I first wrote quantified over **every** positive `x` satisfying the
regime bound, not over the trajectory.  That makes the self-consistency clause `hm`
**unsatisfiable**, so `exists_positive_omegaPoint_of_blueprintData` was vacuously true and the
"reduction" I was reporting was worth nothing.

The mechanism is now machine-checked, in `CRNT/Dynamics/ToricBarrierExplicit.lean`:

* `Network.relevantCones_eq_fan_of_small` — if an angular tile contains **any** point of norm
  `< δ + B`, then *every* cone of the fan is relevant to it, because `0` lies in every cone;
* `Network.mem_all_cones_of_hm` — `hm` then forces the piece's normal into every cone of the fan
  at once, which is incompatible with `0 < (m i) s` from `hpos`.

And a tile quantified over all `x` does contain such points: take `x` with `x s ≈ xstar s` for
`s ∈ P`, which makes `faceLogPart` arbitrarily small while leaving the off-face bound satisfied,
and nothing in the hypotheses stops the barrier from reaching its level there.

**Repair.**  `activeFaceImage` now quantifies over the trajectory:

```
activeFaceImage P xstar Γ m b R i
  = {X | ∃ t ≥ 0, level reached at Γ t ∧ piece i active at Γ t ∧ X = faceLogPart P xstar (Γ t)}
```

That is all the criterion ever used, and it is what Craciun's condition actually asks: the cone
condition is imposed on the surface *where it sits near the face*, not on the whole positive
orthant.  Note the `B` parameter dropped out of the tile — it is still used for the localization
bound, but no longer gates tile membership.

Both consumers and `docs/gac-bridge-gap-analysis.lean` were updated; everything still builds and
the gap analysis is still `sorry`-free.

**The repair does not by itself prove `hm` is now satisfiable.**  The tile is smaller, and small-norm
points now require the *orbit* to sit near `xstar` on `P` while the barrier level is reached — which
is what the trapping argument is supposed to preclude — so the clause is at least no longer
self-defeating.

### The prophylactic, made checkable

Rather than leave that as a hope, the guard is now in the library:

| theorem | content |
| --- | --- |
| `Network.norm_ge_of_mem_activeFaceImage` | every tile point inherits a depth bound `ρ` from the orbit |
| `Network.not_small_of_mem_activeFaceImage` | **the trap cannot fire**: with `δ + B < ρ`, no tile point is small enough for `relevantCones_eq_fan_of_small` to apply |

Both take

```
hdeep : ∀ t ≥ 0, level reached at Γ t → ρ ≤ ‖faceLogPart P xstar (Γ t)‖
```

`hdeep` is a **tuning condition on the level `R`**, not a consequence of the coefficient
conditions.  I checked this rather than assuming it: `hpos` and `hlevel` only pin `η j` into the
window `(M ∑_{u ≠ s} |m j u|, M ∑_u |m j u|]` — the two are consistent, with slack `M |m j s|` —
and they give coordinate floors *inside* the region, saying nothing about how deep the boundary
sits.  Reaching the level gives only `(m j) s · x s ≤ η j + M ∑_{u ≠ s} |m j u| < 2 η j`, an upper
bound on `x s`, not smallness.  So `hdeep` says "the guarded region's boundary sits near the face",
which is exactly what choosing `R` is for, and it has to be established, not derived.

So the blueprint problem now reads: choose `m`, `b`, `R`, `B`, `ρ` with the coefficient conditions,
`hdeep` for non-triviality, and `hm`.  `not_small_of_mem_activeFaceImage` certifies that the
combination is not self-defeating; satisfiability of `hm` itself is still open.

## 5d. SECOND CORRECTION: `hregime` was required outside the region

Running the same adversarial check on the next clause turned up a second structural defect, this
time not vacuity but circularity.

`hregime` is consumed in `exists_positive_omegaPoint_of_convex_tiles` at times where
`hlevel : R ≤ barrier …` holds — that is, at points **at or outside** the guarded region.  There
the coordinate floors of `coordinate_floor_of_dominant_barrier`, which need `barrier ≤ R`, are
unavailable.  Since `hregime` bounds `‖offFaceLogPart‖`, and that needs the off-face coordinates
bounded *below* as well as above, establishing it from the barrier's own floors would be circular:
the floors are what trapping gives, and trapping is what `hregime` is being used to prove.

Nor is there an easy alternative source.  Compactness of `K` supplies upper bounds only.  The
ω-limit structure does not obviously supply lower bounds either: maximality of `Pmax` says no
ω-point has a strictly *larger* zero set, which leaves ω-points whose zero sets are incomparable
with `Pmax`, so off-`Pmax` coordinates may still vanish somewhere on ω.

### The repair: band the hypothesis

| theorem | content |
| --- | --- |
| `PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le` | the fencing lemma with its Dini hypothesis localized to `[0, T)` |
| `PolyhedralBarrier.le_of_dini_slope_nonpos_in_band` | **band form**: the Dini bound is needed only where `u ∈ [R, R']`, and the conclusion is still `u ≤ R` |
| `PolyhedralBarrier.barrier_le_of_local_descent_in_band` | band form of the trapping theorem |
| `Network.barrier_le_of_toric_descent_in_band` | band form for complex-balanced mass action |

The band lemma is a two-step bootstrap.  First `u` never reaches `R'`: otherwise take the first such
time `t₁` (the set `{t ≥ 0 | R' ≤ u t}` is closed by `IsClosed.isClosed_le`), note `u < R'` on
`[0, t₁)` so the band hypothesis applies throughout, and the localized fencing lemma gives
`u t₁ ≤ R < R'`.  With `u < R'` everywhere the band hypothesis becomes unconditional and the global
form finishes.  Localizing the fencing hypothesis to `[0, T)` was the enabling step; the earlier
global form could not be used inside the bootstrap.

This breaks the circularity: with the band form, `hregime` and the coordinate floors need only hold
on `{barrier ≤ R'}`, which is inside the region for a level tuned to `R'` rather than `R`.

**Propagated.**  `exists_positive_omegaPoint_of_convex_tiles`,
`…_of_selfConsistent_normals` and `…_of_blueprintData` now all take `R < R'` and route through
`barrier_le_of_toric_descent_in_band`, so `hassign`, `hregime` and the tile all carry the band
premise `barrier ≤ R'`.  **The circularity is gone from the criterion statements.**

`activeFaceImage` gained the band premise too, which makes the tile strictly smaller — a second
benefit, since a smaller tile means fewer relevant cones and a weaker `hm` (`relevantCore_le_of_subset`).
The guard lemmas `norm_ge_of_mem_activeFaceImage` and `not_small_of_mem_activeFaceImage` were
threaded along, so their `hdeep` hypothesis is likewise only needed on the band.

`docs/gac-bridge-gap-analysis.lean` was updated to the new signature and still elaborates with no
`sorry` and no errors, so the residual still follows from the blueprint data alone — now with the
weaker, non-circular hypotheses.

## 5e. THIRD CORRECTION: the floor condition was too crude, and killed the conservative case

The one clause I had not adversarially tested was `hstart`.  Testing it found the sharpest defect
yet, and the fix improves the library.

Take any network carrying the **all-ones conservation law**, so every `m` in the stoichiometric
subspace has `∑_u m_u = 0`.  That is exactly the class for which `hMclass` (bounded positive
compatibility class) is automatic — the class the template was built for.  On the box `(0, M]`,

```
⟨m, x⟩ = ∑_u m_u (x_u - M) ≤ ∑_{m_u < 0} |m_u| (M - x_u) ≤ M ∑_{m_u < 0} |m_u| = (M/2) ∑_u |m_u|
```

(positive part equals negative part).  Combining with the old `hlevel`,
`η > M ∑_{u ≠ s} |m_u|`, and `hstart`, `⟨m, x₀⟩ ≥ η`, gives `m_s > ∑_{u ≠ s} |m_u|`.  But
`∑_{u ≠ s} |m_u| ≥ |∑_{u ≠ s} m_u| = m_s`.  So `m_s > m_s`: **jointly unsatisfiable**, and the
criterion was vacuous on precisely the networks it was meant for.

### Fix: positive parts, not absolute values

The error was in `le_of_halfspace_of_dominant`, where I bounded
`∑_{u ≠ s} a_u x_u ≤ M ∑_{u ≠ s} |a_u|`.  Since `x` is **nonnegative**, only the positive
coefficients can push the sum up, so the correct bound is

```
∑_{u ≠ s} a_u x_u ≤ M ∑_{u ≠ s} max (a_u) 0.
```

With that, the same comparison becomes `M p ≥ ⟨m, x₀⟩ ≥ η > M (p - m_s)` where
`p = ∑_u max (m_u) 0`, i.e. just `m_s > 0` — which is exactly `hpos`.  **Satisfiable.**

`le_of_halfspace_of_dominant`, `coordinate_floor_of_dominant_barrier` and the `hlevel` clause of
`exists_positive_omegaPoint_of_blueprintData` now all use `max (·) 0`.  This is strictly weaker than
before, so it is a strengthening of every consumer.  `docs/gac-bridge-gap-analysis.lean` was updated
and still elaborates with no `sorry` and no errors.

### The finding is now a verified regression guard

The argument above is no longer a note in a document; it is proved in
`CRNT/Dynamics/ToricBarrierExplicit.lean`:

| theorem | content |
| --- | --- |
| `Network.sum_posPart_le_erase_abs` | on a coordinate-sum-zero vector with `0 < a s`, the positive part is at most `∑_{u ≠ s} |a u|` |
| `Network.inner_le_erase_abs_of_sum_zero` | hence `⟨a, x⟩ ≤ M ∑_{u ≠ s} |a u|` for **every** `x` in the box |
| `Network.not_level_abs_and_start` | so the absolute-value floor condition and the start condition are contradictory: `False` |

If anyone reverts the sharpening, the tree will contain a machine-checked proof that the criterion
is vacuous.  That is the guard I would want against this class of mistake, since the mistake itself
was invisible to the kernel.

### Score on the adversarial pass

Three clauses tested, three defects found, all three repaired:

| clause | defect | repair |
| --- | --- | --- |
| `hm` | vacuous (tile over all `x` admits small-norm points, collapsing the cone condition) | tile restricted to the trajectory and to the band; guard lemmas added |
| `hregime` | circular (required outside the region, where the floors it needs are unavailable) | band form of the fencing and trapping theorems |
| `hstart` | unsatisfiable against `hlevel` on conservative networks | floor condition sharpened to positive parts |

None of these was visible to the kernel: every version typechecked.  **Check what would satisfy a
clause before trusting a reduction that consumes it.**

## 5f. PROGRESS ON `hm`: it reduces to a separation condition

Reading `CRNT/Dynamics/ComplexBalanceStoichFan.lean` closely settles what the fan actually is, and
that makes the self-consistency clause far more tractable than it looked.

`relativeSourceOrderNegativeStoichFan = negatedFan relativeSourceOrderStoichFan`, whose cones are
`relativeSourceOrderConeInStoich w` — cut out by the half-spaces of the `sourceOrderNormal`s, i.e.
the projections `proj_V (toEuclid y_{r₂} - toEuclid y_{r₁})` of **source-complex differences**.  So
the fan is the **arrangement fan** of those hyperplanes in `V`, sign-reversed: exactly Craciun's
hyperplane-generated fan of v3 §3.  Its cones are the chambers and faces of that arrangement.

Consequence: `relevantCones σ δ B` collects the cones coming within `δ + B` of the tile.  If a tile
sits inside **one** chamber and is `δ + B`-separated from every other cone of the fan, that family
is that single chamber, and `hm` collapses to "pick any `m i` in it".

| theorem | content |
| --- | --- |
| `Network.hm_of_single_chamber` | tiles in one chamber each, `δ + B`-separated from all other cones ⇒ `hm` holds for any `m i` in that chamber |
| `Network.hm_of_single_chamber_activeFaceImage` | the same for the trajectory-and-band tiles that `blueprintData` consumes |

**So `hm` — the last open clause — is now implied by a separation condition on the tiles.**  That is
precisely what a scale hierarchy is for: subdivide until each piece's active image lies in one
chamber, well away from the walls.  Two further levers make this easier than it first appears:

* `δ` may be taken arbitrarily small.  `Network.euclideanMassActionField_mem_toricField` holds for
  **every** `δ > 0`, and `toricField` is monotone in `δ`, so the separation only has to beat `B`
  plus an arbitrarily small margin.
* the band and trajectory restrictions already shrink each tile, and `relevantCore_le_of_subset`
  says shrinking only helps.

### Normal existence: settled

`hm_of_single_chamber` left two things to arrange — tiles separating into single chambers, and the
chosen `m i` being positive at the species it dominates (`hpos`).  **The second is now settled
outright, for every network.**

| theorem | content |
| --- | --- |
| `Network.coord_euclideanStoichUnit_self` | `(euclideanStoichUnit s) s = ‖euclideanStoichUnit s‖ ^ 2` |
| `Network.euclideanStoichUnit_ne_zero` | nonzero as soon as some stoichiometric vector has a nonzero `s`-component |
| `Network.pos_coord_euclideanStoichUnit` | hence its own coordinate is strictly positive |
| `Network.exists_chamber_coord_pos` | **some chamber of the fan contains a vector positive at `s`** — the one containing `euclideanStoichUnit s` |

The identity is the crux: pairing `euclideanStoichUnit s` against `Pi.single s 1` through
`inner_euclideanStoichStateL_eq_sum` collapses the sum to the single `s`-term, while the left side
is `‖·‖²`.  The nonvanishing hypothesis is exactly the negation of the degenerate case already
excluded by `Network.ker_finrank_ne_of_face_point`, so it is free in the residual's context.

**So suitable normals always exist, and the whole remaining difficulty is the separation
condition**: choose the pieces so each active image lands in a single chamber of the
source-complex-difference arrangement at distance `> δ + B` from the others.

### The separation condition is now checkable by inequalities

Metric statements about cones are awkward; signed evaluations against the arrangement's normals are
not.  Cauchy--Schwarz converts one into the other.

| theorem | content |
| --- | --- |
| `Network.dist_ge_of_separating_margin` | a normal nonpositive on `y` with margin `‖a‖ * μ` on `X` forces `μ ≤ dist X y` |
| `Network.hm_of_separating_margins` | supplying such a normal per (piece, other cone) pair yields `hfar`, hence `hm` |

Combined with `inner_faceLogPart_eq_sum`,

```
⟪a, faceLogPart P xstar x⟫ = ∑ s ∈ P, (a) s * (log (xstar s) - log (x s)),
```

the margin becomes an **explicit linear inequality in the log-deviations** with coefficients read
off the arrangement normals.  So the remaining task is fully concrete: choose pieces and levels so
that, for every piece `i` and every chamber `D` other than its own, some arrangement normal is
nonpositive on `D` and bounded below by `‖a‖ (δ + B)` on the log-deviation profile of the orbit
wherever piece `i` is active in the band.

### Depth buys margin: the mechanism of the hierarchy, formalized

The two-species case shows what the tiles look like.  With `P = {1,2}` and
`w_s = log (xstar s) - log (x s)`, the arrangement lines meet the face cone where
`(a) 1 · w 1 + (a) 2 · w 2 = 0`, i.e. at fixed *ratios* `w 2 / w 1`.  A blueprint piece's
halfspace `∑_s (m) s · x s = η` has, in `w`-coordinates, the shape of an `L`: nearly
`w 1 = const` when `w 1 ≪ w 2` and nearly `w 2 = const` when `w 2 ≪ w 1`, with the corner on a
diagonal `w 2 - w 1 = const`.  Each arm therefore concentrates, as it goes deep, on one of the
extreme directions `u 1`, `u 2` — and the corner region on the diagonal.  That is why different
pieces can be made to land in different single chambers: **depth in one coordinate pins the
direction.**

Formalized:

| theorem | content |
| --- | --- |
| `Network.inner_euclideanStoichUnit` | `⟪m, euclideanStoichUnit s⟫ = (m) s` — pairing reads off a coordinate |
| `Network.inner_faceLogPart_ge_of_depth` | one coordinate deep (`ρ ≤ w s₀`), the rest shallow (`w s ≤ κ`) ⇒ `(a) s₀ · ρ - κ ∑_{s ≠ s₀} |(a) s| ≤ ⟪a, faceLogPart⟫` |
| `Network.margin_of_depth` | the same in the form `hm_of_separating_margins` consumes |
| `Network.exists_depth_for_margin` | **the trade always closes**: any target margin `μ` is achieved by taking `ρ` large enough |

So the margin grows linearly in the depth while the shallow coordinates contribute only a fixed
penalty, and `exists_depth_for_margin` shows a large enough depth achieves any prescribed margin.
Chaining `margin_of_depth → hm_of_separating_margins → hm_of_single_chamber` turns depth-and-shallow
tile shapes directly into the self-consistency clause.

### Why the pieces must be indexed by scale orderings, not species

Working out what a piece's active region looks like in `w`-coordinates settles the indexing
question.  Near the face, `⟨m, x⟩ ≈ ∑_s (m) s · xstar s · exp (-w s)`, so the sum is dominated by
the coordinate with the **smallest** `w`.  On the region's boundary that dominant term is pinned:
`min_s w s ≈ log ((m) s · xstar s / η)`, a constant, with the other coordinates deeper.  So the
surface is a **staircase whose step is "the shallowest face coordinate hits a threshold"**.

One piece per species is therefore *not* enough: on the active region of such a piece the shallowest
coordinate is pinned but the remaining ones range over everything deeper, so the direction still
sweeps many chambers.  Pinning the direction needs the *next* coordinate pinned too, and so on —
pieces indexed by orderings of `P`, i.e. by flags.  That is exactly why v3 §7 indexes everything by
binary words `α ∈ {0,1}^n`: the word records the flag, and `ε(α)` records the scale at that level.

`Network.margin_of_scale_ratio` is that condition in operative form.  With the `s₀` coordinate deep
and all others bounded by the *next* scale `κ ≥ 1`, the margin `μ` follows as soon as

```
κ * ((‖a‖ * μ + ∑_{s ∈ P.erase s₀} |(a) s|) / (a) s₀)  ≤  log (xstar s₀) - log (x s₀),
```

a **ratio threshold between consecutive scales**, one per arrangement normal.  That is the shape of
Craciun's `ε(α) ≫ ε(α')` chain.

**What is left.**  The chain now runs: scale-separated tile shape ⇒ margin (`margin_of_scale_ratio`)
⇒ separation (`hm_of_cone_family_margins`) ⇒ `hm` ⇒ the residual.  The open
step is the *shape* claim: that pieces indexed by flags of `P`, with levels set by a scale chain,
make the orbit's active image at each piece scale-separated in that flag's order, simultaneously
with `hstart`, `hregime` and `hdeep`.  That is the remaining content of v3 §7.4.3, and it is now a
statement about log-deviation profiles along the orbit rather than about cones.

## 5g. FOURTH CORRECTION: the separation condition was too strong for wall tiles

`hm_of_single_chamber` asks each tile to be `δ + B`-separated from every cone **other than** its own
`C i`.  Thinking about which tiles a blueprint actually needs shows that is unsatisfiable for the
most important ones.

A tile sitting on a **wall** — a lower-dimensional cone `C` of the arrangement, which is exactly
where the normal is forced to live when the `δ`-slack reaches across a face — lies inside every
chamber `D` adjacent to that wall, because `C ⊆ D`.  So `dist(tile, D) = 0` and no separation from
`D` is possible.  But none is needed: `m i ∈ C ⊆ D` already.

### Fix

| theorem | content |
| --- | --- |
| `Network.hm_of_cone_family` | separation only from cones that do **not** contain `C i` ⇒ `hm` |
| `Network.hm_of_cone_family_margins` | the signed-margin form of the same |

`hm_of_single_chamber` remains valid — it is the special case where every relevant cone *is* `C i` —
but `hm_of_cone_family` is the one to build against, since it is the only one satisfiable on walls.

This is the fourth defect found by asking what would satisfy a clause, and the second of the
"hypothesis too strong to be met" kind rather than the "vacuous" kind.  Both are invisible to the
kernel.

## 5h. A concrete instance: the monomolecular 3-cycle

`scripts/probe_three_cycle_blueprint.py` instantiates the whole geometric side on a real network,
which is a different kind of check from the clause-by-clause reading and validates my
understanding of the objects rather than the logic between them.

**Network.**  `A → B → C → A` on `{A, B, C}`.  Weakly reversible, deficiency zero — hence complex
balanced for *every* rate vector — and conservative, so `hMclass` is automatic.  The stoichiometric
subspace is `V = {v : ∑ v = 0}` (dimension 2), the source complexes are the three single-species
complexes, and the source-complex differences `e_B - e_A`, `e_C - e_B`, `e_A - e_C` already lie in
`V`.

**The fan is Figure 3(a).**  The arrangement of their orthogonal complements inside the 2-plane `V`
is three distinct lines through the origin: the script confirms **6 chambers + 6 rays + origin = 13
cones**, which is exactly the fan Craciun draws in v3 Figure 3(a).  So the repo's
`relativeSourceOrderNegativeStoichFan` reproduces the paper's running example.

**Checks that passed.**

* `coord_euclideanStoichUnit_self`: `(u_s)_s = ‖u_s‖² = 2/3` for each species.
* `inner_euclideanStoichUnit`: `⟪a, u_s⟫ = (a) s` for all 9 normal/species pairs.
* For the codimension-2 face `P = {A, B}` (the class is `{∑ x = T}`, the face is the single point
  `(0,0,T)`), the evaluations are `⟪a₁, X⟫ = μ - λ`, `⟪a₂, X⟫ = -μ`, `⟪a₃, X⟫ = λ` on
  `X = λ u_A + μ u_B`.  So `K_P` meets exactly **two** chambers, separated by the wall `λ = μ`.
* The wall direction is `u_A + u_B = (1, 1, -2)/3`, whose `A`- and `B`-coordinates are both `+1/3`.
  **One piece with this normal satisfies `hpos` for both face species**, and it lies in the wall, so
  it lies in both adjacent chambers.
* Along the wall, `⟪a₁, ·⟫ ≡ 0` while `⟪a₂, ·⟫` and `⟪a₃, ·⟫` grow linearly in the depth.  The two
  nonvanishing normals separate the tile from every cone not containing the wall; the vanishing one
  is precisely why the normal must be taken **in** the wall — `hm_of_cone_family`, not
  `hm_of_single_chamber` (§5g).
* Separation from the origin cone `{0}` is `‖X(ρ)‖ = ρ`, i.e. exactly the depth condition
  `ρ > δ + B` of `not_small_of_mem_activeFaceImage`.  One scale parameter meets all three
  requirements at once.

**What this does and does not establish.**  It confirms the objects behave as the Lean statements
say, that the fan is the paper's, and that on this example the geometric clauses are jointly
satisfiable with a very small number of pieces.  It does **not** exhibit a full blueprint: the
orbit-dependent clauses `hstart`, `hregime`, `hdeep` were not checked, which would need integrating
the ODE, and `{A, B}` is not a siphon of this network, so this instance validates the geometry
rather than the residual case.

A note on method: the first version of the script sampled directions to count cones and reported
9 instead of 13, because angular sampling essentially never lands exactly on a line.  The rays are
now computed exactly from each normal.  Worth remembering when validating a discrete count
numerically.

## 5i. An instance of the residual case itself: A + B ⇌ 2B, A + C ⇌ 2C

`scripts/probe_residual_case_blueprint.py`.  Unlike the 3-cycle of §5h, this network satisfies
**every network-side hypothesis of the branch the hole sits in**, so the branch is a real branch of
the case analysis and not dead code.

* weakly reversible (two reversible pairs);
* deficiency zero — complexes `{A+B, 2B, A+C, 2C}` give `n = 4`, linkage classes `{A+B,2B}` and
  `{A+C,2C}` give `l = 2`, rank `s = 2`, so `n - l - s = 0` — hence **complex balanced for every
  rate vector**;
* conservative: every reaction preserves total count, so `(1,1,1)` is a conservation law, the
  positive class is bounded, and `hMclass` is automatic;
* `P = {B, C}` is a **siphon**: the only reactions producing `B` are `A+B → 2B` and `2B → A+B`,
  both consuming `B`; symmetrically for `C`; nothing makes `B` or `C` from `A` alone;
* `P` is **critical**: the conservation laws are multiples of `(1,1,1)`, supported on all three
  species, so none is supported inside `P`;
* the face has **codimension 2**: the class `{x_A + x_B + x_C = T}` has dimension 2 and
  `{x_B = x_C = 0}` meets it in the single point `(T,0,0)`.  Equivalently
  `finrank (stoichSubspace.map (projOn P)) = 2`, so `hcodim` holds, and `hcard = 2`,
  `stoichRank = 2 ≠ 1`.

### The geometry, fully explicit

The source-order arrangement has **5 distinct hyperplanes** in the 2-plane `V`, hence
`10 + 10 + 1 = 21` cones.  On `X = λ u_B + μ u_C` the evaluations are `λ`, `μ - λ`, `2μ - λ`,
`μ - 2λ`, `μ`, so the face direction cone is cut at the ratios `r = μ/λ ∈ {1/2, 1, 2}`: **four
sectors, three interior walls**.

| wall `r` | direction | `(·) B` | `(·) C` |
| --- | --- | --- | --- |
| `1/2` | `(-1/2, 1/2, 0)` | `+1/2` | `0` |
| `1` | `(-2/3, 1/3, 1/3)` | `+1/3` | `+1/3` |
| `2` | `(-1, 0, 1)` | `0` | `+1` |

So the middle wall is **strictly positive at both face species**: a single piece with that normal
meets `hpos` for `B` and `C` at once.  On each wall exactly one of the five normals vanishes — the
one defining it — and the other four have `|slope| ≥ 0.707`, so the separation margin grows
linearly in the depth, as `margin_of_scale_ratio` requires.  That the *defining* normal vanishes is
independent confirmation of §5g: the normal has to be taken **in** the wall, so
`hm_of_cone_family` is the usable form.

### What this settles, and what it does not

It settles that the residual branch is reachable on the network side, that the fan and the
`⟪a, u_s⟫ = (a) s` identity behave as the Lean statements say on a codimension-2 critical siphon,
and that on this instance the geometric clauses are jointly satisfiable with a handful of pieces.

It does **not** produce a blueprint.  The orbit clauses `hstart`, `hregime`, `hdeep` need the ODE
integrated and were not checked.  And note the orbit-side hypotheses of the residual — an ω-point
whose zero set is exactly `P` — are precisely what GAC denies, so they are *expected* to be
unsatisfiable for this network; the residual reads "if that configuration occurred there would also
be a positive ω-point", and proving it is what excludes the configuration.

## 5j. FIFTH CORRECTION: positive parts were necessary but not sufficient

Integrating the instance network's ODE and checking the orbit clauses against the class geometry
turned up a fifth defect, in the very condition I had "fixed" in §5e.

On `A + B ⇌ 2B, A + C ⇌ 2C` with unit rates, the complex-balanced equilibrium is
`x_A = x_B = x_C = T/3`, and since `ẋ_B = x_B (x_A - x_B)` and `ẋ_C = x_C (x_A - x_C)`, the boundary
equilibrium `(T,0,0)` is repelling: positive orbits converge to the interior point.  So GAC holds
here, as it must — but checking `hlevel` against `hstart` *inside the class* is revealing.

`hlevel` bounds the other coordinates' contribution by `M * ∑_{u ≠ s} max (a u) 0` with `M` the
coordinate ceiling.  That **double-counts**: inside a conservative class `∑_u c u x u = T` the
coordinates cannot all sit at the ceiling at once, and the achievable value of `⟪a, x⟫` is only
about `T * max_u (a u / c u)`.  Numerically, for `P = {B, C}`:

| normal | `s` | `hlevel` needs | class allows | |
| --- | --- | --- | --- | --- |
| `(-2/3, 1/3, 1/3)` (middle wall) | `B` | `η > T/3` | `η ≤ T/3` | **infeasible** |
| `(-2/3, 1/3, 1/3)` | `C` | `η > T/3` | `η ≤ T/3` | **infeasible** |
| `(-1/2, 1/2, 0)` (outer wall) | `B` | `η > 0` | `η ≤ T/2` | feasible |
| `(-1, 0, 1)` (outer wall) | `C` | `η > 0` | `η ≤ T` | feasible |

So the convenient middle wall — the one positive at *both* face species, which §5i flagged as
letting one piece cover both — is exactly the one `hlevel` rejects.  **A blueprint for this network
must use the two outer walls, one per species.**  That is a concrete design constraint I would have
got wrong.

### Fix: a ratio bound, not a sum

| theorem | content |
| --- | --- |
| `Network.le_of_halfspace_of_dominant_class` | inside a conservative class, if `a u ≤ β * c u` for all `u ≠ s` then the other coordinates contribute at most `β * T`, giving the floor `(η - β T) / a s ≤ x s` |
| `Network.coordinate_floor_of_dominant_class_barrier` | the barrier form: one dominant piece per species with the class-aware level condition `β T < η` |

The penalty is now a **single term** `β T` with `β` a coefficient-ratio bound, instead of a sum over
coordinates.  On the outer walls `β = 0`, so the condition is just `η > 0`.

This is the fifth defect found by asking what would satisfy a clause, and the second in the *same*
clause — the §5e sharpening from `|a u|` to `max (a u) 0` was a real improvement but stopped one
step short.  Both the old and new forms remain in the tree; the class-aware one is the one to build
against when the network is conservative, which is when `hMclass` is available at all.

## 5k. SIXTH FINDING: `hsep` must not be routed through per-species dominant halfspaces

`scripts/probe_hsep_dominant_obstruction.py`.  This one is not a bug in a theorem — both
`coordinate_floor_of_dominant_barrier` and its class-aware sharpening are true — it is a proof that
the **route** is inadequate.  On a conservative network, the species attaining the minimum of the
complex-balanced equilibrium `x*` admits **no admissible normal at all**, so the family of pieces
those theorems require does not exist.

**Why.**  The region must contain the whole forward orbit, whose closure contains `x*`, so
`η ≤ ⟪m, x*⟫`.  Take the best case `β = 0`, i.e. `m u ≤ 0` for every `u ≠ s`.  Mass conservation puts
`m` in `{∑ m = 0}`, so `∑_{u ≠ s} |m u| = m s`, and `⟪m, x*⟫ > 0` reads

```
m s * x*_s  >  ∑_{u ≠ s} |m u| * x*_u ,
```

i.e. `x*_s` strictly exceeds a **convex combination** of the other `x*_u`.  Impossible exactly when
`x*_s` is the minimum.  Allowing a positive entry elsewhere only raises `β`, which hurts.

Checked numerically over four rate choices; in every case the species attaining `min x*` fails and
the others succeed:

| `x*` | min at | failing species |
| --- | --- | --- |
| `(1,2,1)/4` | `A, C` | `A` and `C` |
| `(1,3,2)/6` | `A` | `A` |
| `(2,5,1)/8` | `C` | `C` |
| `(3,1,2)/6` | `B` | `B` |

There is also a degenerate trap worth knowing: with **all rates equal**, `x*` is proportional to the
conservation vector `c`, and then `⟪m, x*⟫ = 0` for *every* `m` in the stoichiometric subspace, so no
halfspace with `η > 0` contains `x*` and **all** species fail.  Generic rates are needed even to see
the real obstruction — my first pass used unit rates and drew the wrong conclusion from it.

**Consequence.**  The coordinate floors must come from the *global* geometry of the guarded region —
the staircase — not from one dominant halfspace per species.  That is what Craciun's surface does:
it bounds the coordinates below by *being* the surface, not by a per-coordinate inequality.  So
`exists_positive_omegaPoint_of_blueprintData`, which bakes in `piece : S → ι'`, `hpos` and `hlevel`,
is the wrong packaging; `exists_positive_omegaPoint_of_convex_tiles` and
`…_of_selfConsistent_normals`, which take `hsep` abstractly, are the ones to build against.

## 6. Retracted and dead ends (do not re-explore)

* Butler–McGehee is vacuous in this setting (recorded in earlier sessions).
* The quadratic `∑_{s ∈ W} x s ^ 2` is **not** monotone near the face once
  `finrank (stoichSubspace.map (projOn W)) ≥ 2`.  Leading order in the small face coordinates its
  derivative is a quadratic form in the approach direction `u ≥ 0` whose sign varies with `u`;
  already for a reversible pair inside the face with equal rate constants it is `-c(u_A - u_B)²`.
  So `no_omegaLimit_meets_locally_repelling_face` cannot be used in the residual branch, and no
  strengthening of `facet_repelling_near_facet_point` will cover it.
* Choosing `W = {s}` a singleton to make the facet count hold does not help: the estimate needs
  `z` positive off `W`, which fails once the maximal zero set has two or more species.  That is
  now recorded positively as `facet_of_singleton_witness` plus `two_le_card_of_not_facet`.
* Globally homogeneous convex polyhedral barriers: dead in dimension ≥ 3, §4 above, formalized.
* Unweighted zonotope vertices: dead even in dimension 2, §4 above.
* Writing a fresh fan-axioms record: `CRNT.IsPolyhedralFan` already exists in
  `CRNT/Geometry/ConeFace.lean` and is already proved for the source-order fan.  I wrote a
  duplicate and deleted it; check `ConeFace.lean` first.
* Assuming Craciun Theorem 3.1 is missing: it is proved, as
  `massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan`.  Its statement
  inlines subtype terms behind `let` binders, which is why grep for it fails; the named
  restatement is `Network.euclideanMassActionField_mem_toricField`.
