# Persistence and the global attractor conjecture

This area concerns the behavior of mass-action trajectories *in the large*: whether species avoid
extinction (**persistence**) and whether every positive trajectory of a complex-balanced network
converges to its unique positive equilibrium (the **global attractor conjecture**, Horn 1974). It
builds on the relative-entropy Lyapunov function and the forward semiflow described in
[`dynamics.md`](dynamics.md), and on the complex-balanced equilibrium theory in
[`deficiency.md`](deficiency.md).

The global attractor conjecture is open in general. This document records what is **proven here**,
what is **gated on explicit hypotheses**, and where the formalization stops. Where a step is
missing it enters as a named hypothesis (a `Prop`, a structure, or a supplied argument) whenever
that is possible, so the great majority of what follows is `sorry`-free. Exactly two `sorry`s
remain in the whole tree: `Dynamics/HighCodimensionSiphonFace.lean`, the residual
higher-codimension critical-siphon obligation of the Global Attractor chain, and
`Multistationarity/TrueChemistrySRCriterion.lean`, the ear-decomposition step of the
Shinar–Feinberg true-SR criterion. A successful build does not close either of them.

## The reduction: GAC ⟺ persistence

For a complex-balanced (toric) mass-action system, the relative entropy `relEntropy x* ·` is a
strict Lyapunov function whose dissipation vanishes exactly at complex-balanced equilibria (Horn &
Jackson, *General mass action kinetics*, 1972). LaSalle's invariance principle then forces
convergence to the equilibrium `{x*}` **unless** the ω-limit set of the trajectory touches the
boundary of the nonnegative orthant. So for complex-balanced systems, the global attractor
conjecture is equivalent to **persistence**: no positive trajectory has an ω-limit point on the
boundary.

This reduction is fully formalized:

- `omegaLimit_eq_singleton_of_persistent` (`Dynamics/GlobalStability.lean`): for a weakly reversible
  network with positive complex-balanced reference `x*`, given a compact set `K₀` in the open
  orthant that absorbs the cutoff orbit, the ω-limit set is `{x*}`. The persistence content enters as
  the absorbing-set hypothesis.
- `gac_of_genuine_persistence` (`Dynamics/PersistenceGAC.lean`): the same conclusion from a
  genuine-field persistence certificate `hgen` — every genuine integral curve from `x₀` stays in a
  fixed compact `K₀ ⊆` the open orthant.
- `gac_of_persistent` (`Dynamics/SingleLinkageGAC.lean`): the conjecture's conclusion against the
  bundled certificate `Network.PersistentFrom κ x₀`, which packages exactly the compact positive
  absorbing set `gac_of_genuine_persistence` consumes.
- `omegaLimit_eq_singleton_of_mem_positive` (`Dynamics/GACOmegaPositive.lean`), the sharp form: if
  the ω-limit set contains **even one** strictly positive point, it equals `{x*}`. Persistence is
  therefore needed only to place a single ω-point in the interior. The LaSalle facts the proof uses
  (ω-orbits solve the genuine field, the relative entropy is constant on the ω-limit set, ω-points
  are nonnegative and affinely invariant) are supplied as arguments and discharged inside the
  no-critical-siphon assembly below.

## The separating-confinement predicate, constructed

For weakly reversible complex-balanced networks the whole conjecture collapses, through the chain
`surface → region → confinement → persistence → GAC`, onto one geometric predicate
`Network.SeparatingConfinement κ x₀` (`Dynamics/GACSeparatingCapstone.lean`): the genuine orbit
through `x₀` is forward-invariant in a bounded region held a fixed positive distance above every
species facet. `gac_of_separatingConfinement` discharges everything from that predicate to the
`{x*}` conclusion. The predicate is the mass-action form of Craciun's zero-separating surface
(*Toric differential inclusions and a proof of the global attractor conjecture*).

That predicate is **exactly persistence**, and it is **realized** rather than assumed
(`Dynamics/GACSeparatingWitness.lean`):

- `persistentFrom_of_separatingConfinement` / `separatingConfinement_of_persistentFrom`: the
  predicate is logically equivalent to the absorbing certificate `Network.PersistentFrom` (the
  reverse for a positive start). Closing a separating region into the open orthant gives a compact
  positive absorbing set; adjoining the start to such a set gives a separating region. The
  geometric reduction target and the persistence certificate consumed elsewhere are the same content.
- `separatingConfinement_of_local`: when the start's relative entropy lies below every reference
  coordinate, the relative-entropy sublevel set is a compact region inside the open orthant that the
  genuine orbit never leaves, and compactness gives the uniform per-facet floor. The predicate holds
  outright near equilibrium.
- `separatingConfinement_of_hasNoCriticalSiphon`: on the decidable no-critical-siphon class the
  predicate holds for every positive start, with the orbit free to approach a facet at finite times
  — only its closure is held off, since the ω-limit set is interior.

The genuine-orbit inputs these constructions rest on are proven once, for the genuine (unclamped)
field, in `Dynamics/GenuineConfinement.lean`: `genuineOrbit_pos` (a positive start stays positive,
the box bound recovered from compactness on each finite interval), `genuineOrbit_relEntropy_le` (the
relative entropy never rises — Horn & Jackson, *General mass action kinetics*), and
`genuineOrbit_unique_of_box` (uniqueness inside a box, via Mathlib's interval ODE-uniqueness on the
Lipschitz cutoff). They are the genuine-field counterparts of the cutoff-orbit `orbit_pos` /
`orbit_relEntropy_le`, and they discharge the genuine-confinement hypotheses of
`gac_of_genuine_persistence` and `gac_of_confinement` directly.

The construction is uniform in its input: beyond the standing positivity and complex-balance data
(`x*` positive and complex-balanced, `x₀` positive), `persistentFrom_of_omegaLimit_singleton`
depends only on the genuine semiflow and the conclusion that its ω-limit set is `{x*}` — it is
agnostic to how that ω-limit was obtained — and returns `PersistentFrom`.
Read against `gac_of_separatingConfinement`, the reduction is therefore **tight** — for weakly
reversible complex-balanced networks `SeparatingConfinement`, `PersistentFrom`, and the
ω-limit-is-`{x*}` conclusion are mutually equivalent. The geometric predicate is neither weaker nor
stronger than the conjecture's own conclusion, so the reduction loses no generality.
`persistentFrom_of_hasNoCriticalSiphon` is the corollary that feeds `gac_of_hasNoCriticalSiphon`'s
ω-limit into this lemma, exposing the absorbing certificate the no-critical-siphon assembly does not
itself surface. What stays open is unchanged: *constructing* any of the three for the curved
mass-action case past critical siphons, refereed only up to stoichiometric dimension three.

## Siphons and the boundary (Angeli–De Leenheer–Sontag)

The combinatorial control on boundary ω-limit points is the **Petri-net siphon**. Following Angeli,
De Leenheer & Sontag (*A Petri-net approach to persistence analysis*, 2007), the zero set of a
boundary ω-limit point is a siphon, and a network with no *critical* (drainable) siphon is
persistent. This chain is proven:

- `omegaLimit_negInvariant` (`Dynamics/NegativeInvariance.lean`): backward (negative) invariance of
  the ω-limit set of a precompact `Flow ℝ≥0` orbit in a Hausdorff space. This is general
  dynamical-systems content absent from Mathlib, and a prerequisite for the boundary analysis.
- `massActionVectorField_pos_of_not_isSiphon` (`Dynamics/StrictInflow.lean`): at a nonnegative point
  whose zero set is **not** a siphon, the field has strictly positive inflow at a depleted species.
- `isSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/BoundaryOmegaSiphon.lean`): the zero set of a
  boundary ω-limit point is a siphon.
- `isCriticalSiphon_zeroSet_of_mem_omegaLimit` (`Dynamics/CriticalSiphonOmega.lean`): for a positive
  start it is moreover a *critical* siphon, by the mass-conservation argument (affine invariance of
  the ω-limit set).
- `omegaLimit_positive_of_hasNoCriticalSiphon` (`Dynamics/NoCriticalSiphonPersistence.lean`): under
  `HasNoCriticalSiphon`, every ω-limit point is strictly positive.
- **`gac_of_hasNoCriticalSiphon`** (`Dynamics/GACNoCriticalSiphon.lean`): **unconditional global
  attractor convergence for the no-critical-siphon class of complex-balanced networks**, with no
  persistence or closeness hypothesis — `HasNoCriticalSiphon` supplies it. This is the strongest
  global-convergence theorem proven here. Its arguments are weak reversibility, a positive
  complex-balanced reference, and a positive start in that reference's compatibility class.

Siphons themselves are defined in `Dynamics/Siphon.lean`: `IsSiphon` (every reaction producing a
species in the set also consumes one), `IsCriticalSiphon` (a nonempty siphon whose face carries no
conserved positive vector), and `HasNoCriticalSiphon`. `IsSiphon` is decidable (`decidableIsSiphon`,
checkable by `decide`); `IsCriticalSiphon` and `HasNoCriticalSiphon` are decidable too
(`decidableIsCriticalSiphon`, `decidableHasNoCriticalSiphon` in `Decision/CriticalSiphonDecide.lean`),
since criticality is a sign-restricted kernel-feasibility question settled constructively by
Fourier–Motzkin elimination. Forward invariance of siphon faces and
the supporting confinement, conservation, and descent results are in `Dynamics/{Persistence,
PersistenceTheorem,PersistenceConfined,ConfinedInvariance,BoundaryDescent,ConservationLaw,
SiphonConservation}.lean`.

The general dynamical-systems scaffolding for boundary-repulsion arguments is also formalized,
independent of reaction networks: the **Butler–McGehee escape principle** (`Dynamics/ButlerMcGehee.lean`,
after Butler & Waltman and Hale, *Asymptotic Behavior of Dissipative Systems*) — two-sided
invariance of the ω-limit set and the escaping-point geometry for an isolated invariant set;
**isolated invariant sets and isolating neighborhoods** (`Dynamics/IsolatedInvariant.lean`); and
**minimal compact invariant sets** by a Zorn descent (`exists_minimal_compact_invariant_subset`,
`Dynamics/MinimalInvariant.lean`). `Dynamics/EscapeSiphonFace.lean` fuses these: for a precompact
positive trajectory the forward limit of an escaping ω-point carries a critical siphon on its zero
set, so under `HasNoCriticalSiphon` no isolated boundary set can trap the ω-limit set.

## Toric differential inclusions (Craciun)

A second, geometric approach to persistence, independent of siphons, embeds the toric dynamical
system into a **toric differential inclusion** `ẋ ∈ F_{F,δ}(log x)`, whose right-hand side is read
off the polyhedral fan of the reaction vectors, and constructs **zero-separating surfaces** bounding
an invariant region that stays a fixed distance from the boundary. This is the approach of Craciun,
*Toric differential inclusions and a proof of the global attractor conjecture*. The general proof is
an unrefereed preprint; the formalization here machine-checks its architecture, and distinguishes
which steps are theorems and which are interfaces awaiting a construction.

Built and proven:

- **Differential inclusions** (`Dynamics/DifferentialInclusion.lean`): the set-valued `Field`,
  inclusion solutions, the embedding of an ODE solution into any inclusion that selects it, and
  forward-invariant regions. `Dynamics/ToricInclusion.lean` shows the mass-action velocity lies in
  the constant reaction-cone inclusion, so a nonnegative mass-action curve solves it.
- **The polyhedral-fan field** (`Geometry/{PolyhedralFan,ToricFan,ConeFace}.lean`): the polar cone
  (`coneDual`) with the bipolar theorem (`cone_dual_dual`) and Farkas separation
  (`exists_mem_coneDual_of_notMem`); the δ-uncertainty field `F_{F,δ}(X)` (`toricField`, monotone in
  δ by `toricField_mono_delta`) and the inclusion `ẋ ∈ F_{F,δ}(logCoords x)`. A `Fan` is bare cone
  data (`Finset (ProperCone ℝ E)`); the full fan axioms are the separate hypothesis
  `IsPolyhedralFan` (closure under exposed faces, pairwise intersection a common face, covering), and
  `Geometry/ConeFace.lean` supplies the exposed-face and supporting-hyperplane fragments
  (`exposedFace`, `IsExposedFaceOf`).
- **The embedding** (`Dynamics/{ToricEmbedding,ToricEmbeddingOrder,ToricEmbeddingWR}.lean`): a single
  cycle's velocity lies in the polar cone (`cycle_velocity_mem_polarCone`), by ordering complexes
  along an interior direction and summing consecutive differences (Abel summation) against
  `C`-minimality. The assembly over a weakly-reversible network is conditional on a cycle cover:
  `NetworkCycleDecomposition` packages the per-cycle reaction sequences and the ordering data
  (`mono`, `cmin`), and `velocity_mem_polarCone` derives the total-velocity membership from it.
- **The cycle-cover boundary** (`Graph/CycleCover.lean`): weak reversibility is defined through
  `Relation.ReflTransGen` reachability (`Graph/{Reachability,WeakReversibility}.lean`). At that
  reachability level the cover *is* proven: `WeaklyReversible.onDirectedCycle` shows every reaction
  lies on a directed cycle, and `WeaklyReversible.reaches_comm` gives strong connectivity of each
  component. What is **not** constructed is extracting a concrete closed walk (a `List N.R`) from the
  propositional reachability witness and assembling the full `NetworkCycleDecomposition` with its
  `mono`/`cmin` projection-ordering data; that structure is consumed as input by the multi-cycle
  embedding rather than derived from `WeaklyReversible`.
- **Zero-separating surfaces** (`Dynamics/ZeroSeparating.lean`,
  `Geometry/{ZeroSeparatingCurve2D,ZeroSeparatingSurface,ZeroSeparatingInduction,FaithfulCurve,
  FaithfulCurve2D,FaithfulCurve2DFan,FaithfulCurveExistence,FaithfulCurveGeneral,FanRefinement,
  ToricFieldPolar,ToricFieldPolarMulti}.lean`,
  `Dynamics/{PolyRegionInvariant,PolyRegionStrictInvariant,SupportDiniBridge,ThmBGenuine}.lean`):
  - the one-dimensional case is proven outright (`zeroSeparatingRegion_Ici`);
  - the invariance engine for a polygonal region is `polyRegion_invariant_of_strictSupport`: forward
    invariance from *boundary-local* strict subtangency (`IsStrictSupportField`), checked only at the
    active faces at a curve's actual position, so distinct (even conflicting) edge normals
    are handled;
  - in two dimensions the faithful curve is constructed by **angular chaining**: edge normals are
    unit vectors at the fan-wall angles and rotate monotonically, so within a sector of width less
    than π one direction lies strictly inside every face at once (`exists_strict_interior`), giving a
    nonempty zero-separating region that excludes a ball about the origin
    (`exists_faithful_separating_region`), and these normals are genuine attracting directions of an
    actual fan (`toricField_subset_wall_halfPlane`);
  - the higher-dimensional induction sweeps a lower-dimensional surface along a ruling direction
    (`ruledSet`), with separation and subtangency transferring to the sweep; a surface normal on a
    ruled patch must be orthogonal to its active directions, which is feasible below the ambient
    dimension and over-determined once those directions span. This is the elementary linear-algebra
    fact behind the difficulty in dimension four. Refining the fan keeps each patch below that
    threshold and transfers admissibility to the coarser fan (`Geometry/FanRefinement.lean`), so the
    dimension-four over-determination is a feature of the naive construction, not an obstruction.
    Supporting hyperplanes and exposed faces also preserve finite half-space representations.
    The same module now proves that images of a covering fan under a surjective linear map cover
    the target, and that finitely generated cone images are exact. For any split surjection whose
    kernel is spanned by one supplied direction, Fourier--Motzkin elimination proves that the closed
    image of each cone with a finite half-space representation again has a finite half-space
    representation and admits a complete polyhedral fan refinement; final-coordinate deletion in
    Euclidean coordinates is a proved instance. The module also constructs a complete central
    hyperplane arrangement fan for any supplied finite
    normal set. The arrangement of the finite dual normals refines any covering cone family with
    finite dual representations, and every arrangement cell has a finite dual representation.
    Therefore it supplies a complete polyhedral fan refinement of these projected image families.
    This does not show that the raw projected image family itself is a fan, nor does it cover
    projections with higher-dimensional kernels. The higher-dimensional surface construction and its
    analytic interfaces remain open.
- **Viability** (`Dynamics/{Viability,FirstExit,SublevelInvariant,SublevelNagumo,ClosedSetNagumo,
  ThmBGenuine}.lean`): for the genuine (Lipschitz) dynamics, solution existence is free
  (Picard–Lindelöf), so only invariance must be shown. The single-valued Nagumo step is proven: given
  a sublevel surface with a neighborhood-descent band and ball-separation, the genuine trajectory
  stays a fixed distance from the origin (`genuine_away_from_origin`,
  `massAction_genuine_away_from_origin`). That surface is supplied as input. The set-valued Nagumo
  theorem (subtangency implies invariance for a set-valued field) is itself taken as a hypothesis.

What is **not** verified are the analytic and geometric steps the proof rests on. Each is carried as
an explicit hypothesis, never a `sorry`:

1. **Set-valued viability / Nagumo.** Subtangency implies forward invariance for a set-valued field.
   `Dynamics/Viability.lean` defines the subtangency predicates (`Subtangent`, `PosSubtangent`) and
   proves the easy direction (invariance ⇒ subtangency along a solution); the general converse needs
   Filippov selection and Peano existence on a moving constraint, which Mathlib lacks, so it is not
   attempted.
2. **The n-dimensional surface construction.** The decomposition of a neighborhood into ruled patches
   and the simplicial gluing is the predicate `InductionStepHypothesis`
   (`Geometry/ZeroSeparatingSurface.lean`); `inductionStep_of_ruledBuild`
   (`Geometry/ZeroSeparatingInduction.lean`) returns its assumed witness unchanged. The descent band
   and ball-separation feeding `genuine_away_from_origin` are likewise supplied. A zero-bit geometric
   subcase is now kernel-checked: `exists_compact_separated_zeroBitGraphTube` turns a compact face
   with a zero-bit projection into a continuous graph section and a compact tube that contains the
   face, projects exactly onto the base, and retains a positive origin-avoidance margin when the
   tube radius is smaller than the face margin. `exists_compact_separated_zeroBitGraphTube_over_tile`
   restricts this construction to each compact projected tile while preserving exact projection,
   face containment, and separation; `projectionFiberTube_eq_iUnion_of_base_cover` proves that a
   finite cover of the base lifts to an exact cover by those tile tubes. This is still set-level
   tube geometry. `compactZeroBitFiberPatchCover_of_compactBaseCover` packages that lift for a
   finite compact cover of the projected face whose tile interiors are pairwise disjoint, with a
   shared continuous center, compact tile tubes, exact tile projections, the inherited separation
   margin, exact overlaps along common projected bases, and disjoint ambient interiors. These are
   set-level seams only. On the one-bit side,
   compactProjectionFiberTiling_of_compactBase now supplies
   finitely many compact strips with exact coverage, full base projection, width bounds, and
   continuous center graphs. Distinct strips have disjoint ordinary ambient interiors in the full
   product space, proved by showing that any ambient interior point lies strictly between its
   fiber endpoints. Adjacent closed strips intersect exactly in the graph of their shared
   endpoint, which is continuous and compact over a compact base. This records set-level seam
   topology; the piecewise-smooth separating surface, descent estimates, and differential seam
   conditions remain open. `compactOneBitFiberBlueprintRefinement_of_compactBand` takes a compact
   face patch already contained in the band and derives an exact finite cover by compact
   face-tile intersections. The continuous boundary graphs and face-in-band containment remain
   explicit inputs. `compactOneBitFiberPatchCover_of_compactBand` lifts a finite compact cover of
   the projected base whose tile interiors are pairwise disjoint, allowing different subdivision
   counts on each base tile, and packages compact face pieces with pairwise-disjoint ambient
   interiors. The cross-base case follows from openness of coordinate projection and exact tile
   projections; the same-base case uses the equal-strip interior-separation theorem. The
   zero-bit pre-blueprint rule from Craciun v3, §7.3, is now encoded set-theoretically by
   `zeroBitPreBlueprintNeighborhood`: a face is thickened by the coordinate box whose radii come
   from its binary-word prefixes, then intersected with the pullback of the lower-dimensional
   neighborhood. `forgetLastCoordinate_image_zeroBitPreBlueprintNeighborhood` proves the exact
   projection recursion; compactness and face containment follow when compactness and projected
   containment are supplied. A prefix ending in `1` has a zero-width coordinate via
   `binaryWordFiberBox_lastCoordinate_eq_zero`. The depth-indexed function
   `craciunBinaryWordEpsilon` assigns the padded lower-endpoint scale to a zero-ending prefix and
   zero to a one-ending prefix, with `craciunBinaryWordEpsilon_pos_iff` characterizing positive
   widths exactly as valid zero-ending prefixes. `coherentBinaryWordTileScale_eq_craciunBinaryWordEpsilon_of_zero`
   identifies that width with the first scale on its last-zero refinement chain. The construction
   keeps its ambient depth fixed while projecting to lower coordinate dimensions. The code proves
   every prefix width is at most `q`, and `zeroBitPreBlueprintNeighborhood_craciunSeparated`
   specializes the earlier avoidance estimate: a face with margin greater than `q` retains the
   reduced margin `margin - q`. If every box width is at most `r`,
   `zeroBitPreBlueprintNeighborhood_separated` shows that a face outside the margin-`m` ball yields
   a neighborhood outside the ball of radius `m - r`, with that reduced margin positive when
   `r < m`. These are pre-blueprint set facts, not the smooth hypersurface or normal-condition
   construction. See [Craciun v3, §7.3](https://arxiv.org/html/1501.02860v3).
   The smooth gluing layer now also
   proves, via exists_fderiv_smoothMaxList_le and
   exists_fderiv_smoothMaxF_nonpos_of_value_gap, that finite smooth maxima preserve a shared
   directional-derivative upper bound and that a strictly descending chart remains nonincreasing
   after gluing a competitor whose outward derivative is bounded and whose barrier value is
   sufficiently lower. The new `zeroSeparatingSurfaceExists_smoothWallList_of_dominantHead_band`
   wires this estimate into the ZSH interface when one fixed head chart is inward throughout the
   barrier band and the aggregated tail stays below it by the required gap. This remains a
   chart-local conditional result: selecting such dominant charts across all blueprint tiles and
   proving the full piecewise-smooth surface and seam conditions remain open. Separately, the
   log-projective chart compatibility result currently
   proves pointwise overlap when neighboring face weights
   balance on each tied-coordinate fiber. A separate first-moment condition aligns directional
   derivatives of the scalar level equations; the two-species example in
   `Geometry/LogProjectiveFaceCompatibility.lean` shows that fiber balance alone need not align
   transverse section derivatives, so it rules out inferring C¹ gluing from pointwise overlap. The
   [Craciun v3 ZSH definition](https://arxiv.org/html/1501.02860v3) requires a piecewise-smooth
   surface and tests non-crossing at smooth points (Definition 4.6), so this derivative mismatch is
   not itself an obstruction to the stated construction. The blueprint's pointwise seam
   compatibility, seam topology, and normal condition on smooth pieces remain to be proved.
3. **The weak-reversibility cycle cover and its ordering data.** The reachability-level cover is
   proven (`WeaklyReversible.onDirectedCycle`), but `NetworkCycleDecomposition` still assumes the
   concrete cycle lists and ordering data needed to assemble the network velocity. Its original
   `mono`/`cmin` interface is problematic in graph order: `Examples/CycleRateNonMonotone.lean`
   exhibits the strongly connected triangle `A → B → A + B → A` at `x = (1/2, 4)`, where the rates
   are `1/2, 4, 2` and no rotation is monotone. Reordering steps by rate fixes `mono`, but changes
   the vertices to partial sums of reaction vectors.

   The cycle-level partial-sum argument is now formalized. `ToricCycleSortedBase.lean` proves that
   the prefixes obtained by sorting coefficients have nonnegative partial sums in one direction;
   `ToricCycleOrderLimits.lean` lifts this to a cone condition `OrderRefines C y a` and proves
   `cycle_velocity_mem_polarCone_of_orderRefines`. It also defines the coefficient-dependent
   `OrderChamber y a`, giving an unconditional cycle-level polar-cone result relative to that
   chamber. This repairs the sorted-walk `C`-minimality step under the stated order condition, but
   does not construct the network-level cycle decomposition or show that the required chambers and
   fan slack assemble for general rate constants. With a common positive rate constant, `log x`
   belongs to each cycle's order chamber. With non-uniform constants, the ordering is shifted by
   `log κ`; `massAction_cycle_inner_le_kappaCorrection` and `massAction_cycle_inner_le_kappaSpread`
   quantify the resulting term when adjacent log-rate differences are bounded. The separate
   `CycleSignCompatible` Abel condition does not bypass the ordering issue: under strict
   `C`-minimality it forces coefficient monotonicity at the separating indices.
4. **The polyhedral-fan axioms and common refinements.** `IsPolyhedralFan` (closure under exposed
   faces, pairwise intersection a common face, covering) remains a requirement on input fans.
   `Geometry/FanRefinement.lean` now constructs finite iterated intersections of supplied
   polyhedral fans with dual-finitely-generated cells and proves the fan and refinement properties
   persist. `Dynamics/ComplexBalanceStoichFanInclusion.lean` also proves the toric field inclusion
   survives successive intersections with covering fans. The subdivision fans and tiles required by
   the zero-separating construction are still not constructed.
5. **Arbitrary-fan faithful-curve existence.** The global slope-interval chaining is the
   `ChainingData` interface (`Geometry/FaithfulCurveGeneral.lean`); the two-dimensional results assume
   a sector bound and strict subtangency (`IsStrictSupportField`), discharged only for worked
   instances such as the first-quadrant `crossFan`.
6. **The support-to-`infDist` bridge.** For a Lipschitz polygonal boundary the per-half-plane Dini
   monotonicity is proven (`infDist_halfPlane_antitoneOn_of_support`, `Dynamics/SupportDiniBridge.lean`),
   and the per-face slack lower-bounds the region distance. The matching upper control — the
   convex-intersection projection identity that turns per-face support into antitonicity of the
   *region* distance — enters as the hypothesis `hanti`.

No theorem assembles these into a conclusion of persistence or the global attractor conjecture for
the toric-inclusion approach. Its persistence-style results are the one-dimensional base case
(unconditional) and genuine-flow distance bounds conditional on a supplied surface. The architecture
is formalized and the dimension-four over-determination is understood, but the conjecture is not
closed here.

## Additional candidate reductions from the supplied handoff

Pantea's paper proves that all bounded trajectories of weakly reversible mass-action systems with
two-dimensional stoichiometric subspace are persistent, and proves the Global Attractor Conjecture
for complex-balanced systems with three-dimensional stoichiometric subspace ([Pantea,
*On the persistence and global stability of mass-action systems* (2012)](https://arxiv.org/abs/1103.0603)).
Neither result is formalized here. They are candidate dimension-specific proof branches, subject to
an important interface check: the current `GenuinePermanentForRates` target asks for a class-uniform
eventual compact set, so a formalization must prove that the paper's persistence or convergence result
supplies this stronger API before counting either branch as closed.

Anderson and Shiu give another candidate rank-2 branch: Theorem 4.6 proves GAC when every
semilocking face is a facet, vertex, or empty, and Corollary 4.7 applies this to two-dimensional
compatibility classes ([paper, Theorem 4.6 and Corollary 4.7](https://people.math.wisc.edu/~dfanderson/papers/AndShiuFacetsSIAM.pdf)).
The local critical-siphon facet inequality is now formalized conditionally, but the finite-cover and
vertex arguments are not assembled into Lean, and the result still needs to feed the
class-uniform `GenuinePermanentForRates` interface.

The handoff's rate-realization observation is also present in
`Dynamics/ToricCycleOrderLimits.lean`: `not_exists_realizing_of_relation` shows that a translation
realizing `log κ` must satisfy every linear relation among the cycle complexes, while
`massAction_cycle_inner_le_kappaSpread` bounds the residual when no such translation exists. This
limits the translated-cycle route for arbitrary rate constants; it does not refute the Global
Attractor Conjecture or close the critical-siphon case.

## The permanence route (Gopalkrishnan–Miller–Shiu)

A third route to the conjecture runs through **permanence**: `StronglyEndotactic ⇒ permanent ⇒ GAC`,
the geometric approach of Gopalkrishnan, Miller & Shiu (*A geometric approach to the global attractor
conjecture*, 2014), with low-dimensional predecessors in Craciun, Nazarov & Pantea (2013) and Pantea
(2012). `Endotactic` and `StronglyEndotactic` are defined in `Geometry/Endotactic.lean`. The
**permanence ⇒ convergence** bridge is constructed (`Dynamics/EndotacticPermanence.lean`):
`Permanent` is the eventual-confinement predicate (the forward orbit is eventually inside a fixed
compact set of strictly positive concentrations), `omegaLimit_meets_positive_of_permanent` places an
ω-point in the interior, and `gac_of_permanent` then yields `ω = {x*}` via the sharp positive-ω-point
form. The sign content of strong endotacticity along the relative-entropy dissipation is proven
(`stronglyEndotactic_strict_dissipation_direction`). What this route does **not** supply is the step
`StronglyEndotactic ⇒ permanent`, which is the unproven analytic core.

## What is complete, and what is open

- **Complete:** the Lyapunov/LaSalle reduction; GAC ⟺ persistence; unconditional global convergence
  for the no-critical-siphon class; the sharp "one positive ω-point ⇒ convergence" reduction; the
  siphon → critical-siphon → ω-positivity chain; backward invariance of ω-limit sets; the
  Butler–McGehee escape geometry, isolated and minimal invariant sets; the reachability-level cycle
  cover of a weakly-reversible network; the differential-inclusion, polar-cone, embedding, one- and
  two-dimensional zero-separating, and single-valued-Nagumo machinery above; the permanence ⇒
  convergence bridge. In `Dynamics/GlobalAttractorTheorem.lean`, `PositiveOmegaPointForRates` now
  requires the initial curve to solve the mass-action ODE, and the zero-dimensional and rank-one
  cases are proved. Also complete, in `Dynamics/GlobalAttractorTheorem.lean`:
  `exists_relEntropy_const_on_omegaLimit`, which *derives* the LaSalle constant
  `∀ z ∈ ω, relEntropy x* z = c` for an arbitrary supplied semiflow rather than assuming it (every
  theorem in `Dynamics/GACOmegaPositive.lean` takes that constant as a hypothesis, while
  `PositiveOmegaPointForRates` does not supply it);
  `positiveOmega_or_criticalSiphonFaceEquilibrium`, the resulting dichotomy — either a positive
  ω-point, or a boundary equilibrium whose zero set is a critical siphon *meeting the compatibility
  class*, with strictly smaller face rank;
  `positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium`, which also removes the case where
  the orbit reaches an equilibrium; and
  `positiveOmegaPointForRates_of_criticalSiphonFaces_miss_classes`, a sufficient condition for the
  omega-interior certificate strictly weaker than `HasNoCriticalSiphon` (critical siphons are
  allowed, provided none of their coordinate faces meets a positive compatibility class), together
  with `positiveOmegaPointForRates_of_no_boundary_equilibrium_in_classes`. Finally
  `omegaLimit_fixed_of_complexBalanced` and `omegaLimit_singleton_of_mem_omegaLimit`: every ω-point
  of a bounded positive genuine orbit is a *fixed point* of the semiflow and is its own forward
  limit, which shows the Butler–McGehee stack of `Dynamics/EscapeSiphonFace.lean` is vacuous on
  such ω-limit sets and cannot supply a siphon-dimension descent. In
  `Dynamics/SiphonFaceWeakReversibility.lean`, the avoiding-reaction subnetwork and its filled face
  equilibrium are formalized. `Dynamics/ToricCycleSortedBase.lean` and
  `Dynamics/ToricCycleOrderLimits.lean` prove sorted partial-sum and polar-cone results, and
  `Examples/CycleRateNonMonotone.lean` verifies that no cyclic rotation of a particular weakly
  reversible triangle has monotone mass-action rates.
- **Open:** persistence in general — the remaining gap is that interior orbits must be repelled from
  *critical*-siphon faces. The codimension-1 non-siphon facet case is proven
  (`Dynamics/FacetRepulsion.lean`, via `massActionVectorField_pos_of_not_isSiphon` and Butler–McGehee:
  a non-siphon facet is strictly repelling and traps no ω-point). For critical-siphon facets,
  `Dynamics/FacetRepulsionAndersonShiu.lean` formalizes the one-sign facet direction and a
  conditional version of Anderson–Shiu Theorem 3.2: `facet_repelling_of_data` derives the repulsion
  inequality when the facet direction, a nonnegative reaction contribution, and quantitative
  monomial-domination bounds are supplied. `exists_positiveReaction_below_of_negativeReaction`
  now derives, for each negative reaction, a positive reaction in its weakly reversible component
  whose source is strictly smaller on every facet species. The witness may vary by reaction, so
  the proof does not assume a global ordering across disconnected linkage classes.
  `facet_repelling_of_reactionwise_data` now assembles this shape of estimate when each negative
  term is controlled by the full nonnegative contribution. `facet_repelling_of_local_monomial_bounds`
  combines the cycle witnesses, exponent comparison, complementary-factor bounds, coefficient
  ratios, and sum estimate into local repulsion. `exists_uniform_complement_monomial_bounds`,
  `exists_uniform_reaction_coefficient_bound`, and `exists_small_facet_parameters` now derive the
  required constants uniformly on a neighborhood. `facet_repelling_near_facet_point` packages
  these choices, while `facet_repelling_near_facet_point_of_facet` also derives the signed facet
  direction from the codimension-one projection-rank condition and a compatible positive point.
  In `Dynamics/GlobalAttractorTheorem.lean` the maximal boundary zero face is chosen by
  `exists_maximal_zeroSet_omegaPoint`; when its codimension is one the orbit is contradicted by
  `no_omegaLimit_meets_locally_repelling_face` applied through
  `facet_repelling_near_facet_point_of_facet`. When the maximal boundary face is not a facet,
  `highCodimension_of_not_facet` rules out the degenerate zero-projection case and also returns
  `2 ≤ Pmax.card`, and the branch is discharged by
  `exists_positive_omegaPoint_of_highCodimension_siphonFace` in `Dynamics/HighCodimensionSiphonFace.lean`.
  That theorem is where the one remaining GAC `sorry` lives, so `complexBalanced_genuinePermanent`
  inherits it from exactly one place instead of from an open branch of the main argument. The
  supporting face-codimension and barrier machinery added alongside it — `Dynamics/FaceCodimension.lean`,
  `Dynamics/FaceDirectionCone.lean`, `Dynamics/OrbitRegularity.lean`,
  `Dynamics/ToricBarrierTrapping.lean`, `Dynamics/ToricBarrierExplicit.lean`,
  `Geometry/PolyhedralBarrier.lean`, `Geometry/ConvexBarrierObstruction.lean` and
  `Geometry/FanFaceLattice.lean` — is `sorry`-free, and `test/ToricBarrierAudit.lean` pins the
  axiom set of each entry point so none of them can silently acquire `sorryAx`.
  Anderson's single-linkage tier argument is also not
  formalized. Also open: in the toric-inclusion approach, the six explicit hypotheses
  enumerated above, none assembled into a persistence or GAC conclusion; and, in the permanence route,
  `StronglyEndotactic ⇒ permanent`.

## Modules

`Dynamics/`: `Siphon`, `SiphonConservation`, `ConservationLaw`, `Persistence`, `PersistenceTheorem`,
`PersistenceConfined`, `ConfinedInvariance`, `BoundaryDescent`, `GlobalStability`, `PersistenceGAC`,
`ForwardInvariance`, `StrictInflow`, `NegativeInvariance`, `BoundaryOmegaSiphon`, `CriticalSiphonOmega`,
`NoCriticalSiphonPersistence`, `GACNoCriticalSiphon`, `GACOmegaPositive`, `SingleLinkageGAC`,
`GACConfinement`, `GACSeparatingRegion`, `GACSeparatingRegionNagumo`, `GACSeparatingCapstone`,
`GenuineConfinement`, `GACSeparatingWitness`, `SiphonFaceWeakReversibility`,
`IsolatedInvariant`, `MinimalInvariant`, `ButlerMcGehee`, `EscapeSiphonFace`, `FacetRepulsion`,
`EndotacticPermanence`, `DifferentialInclusion`, `ToricInclusion`, `ToricEmbedding`,
`ToricEmbeddingOrder`, `ToricEmbeddingWR`, `ToricCycleSortedBase`, `ToricCycleOrderLimits`,
`ZeroSeparating`, `Viability`, `FirstExit`, `FaceCodimension`, `FaceDirectionCone`,
`HighCodimensionSiphonFace`, `OrbitRegularity`, `ToricBarrierTrapping`, `ToricBarrierExplicit`,
`SublevelInvariant`, `SublevelNagumo`, `ClosedSetNagumo`, `SupportDiniBridge`, `PolyRegionInvariant`,
`PolyRegionStrictInvariant`, `ThmBGenuine`, `DissipationBound`, `FacetRepulsionAndersonShiu`.
`Geometry/`: `PolyhedralFan`, `Endotactic`, `ToricFan`, `ConeFace`, `ZeroSeparatingSurface`,
`ZeroSeparatingCurve2D`, `ZeroSeparatingInduction`, `FanRefinement`, `ToricFieldPolar`,
`ToricFieldPolarMulti`, `FaithfulCurve`, `FaithfulCurveExistence`, `FaithfulCurveGeneral`,
`FaithfulCurve2D`, `FaithfulCurve2DFan`, `PolyhedralBarrier`, `ConvexBarrierObstruction`,
`FanFaceLattice`.
`Graph/`: `Reachability`, `WeakReversibility`, `CycleCover`.
`Examples/`: `CycleRateNonMonotone`.

Related: [`architecture.md`](architecture.md), [`dynamics.md`](dynamics.md),
[`deficiency.md`](deficiency.md).
