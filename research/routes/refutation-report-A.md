# Refutation report A — `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`

**Agent:** `adv-refute` · **Branch:** `research/adv-refute` · **Round 1**

**Verdict: the STATEMENT of Hole A is not refutable. It is TRUE, and in fact every packaged
criterion that was proposed to prove it is DEAD — machine-checked, and now consolidated on
`infra-scaffold-crnt`'s general template.**

Two independent results, both compiled:

| # | Result | Machine-checked at |
|---|---|---|
| **V1** | `exists_positive_omegaPoint_of_upperRegion`'s hypothesis list is **INCONSISTENT** with Hole A's boundary-ω-point hypotheses: together they give `False` | `CRNT/Dynamics/UpperRegionObstruction.lean`, theorem `upperRegion_inconsistent_with_boundaryOmegaPoint` — now a **thin corollary** of `infra-scaffold-crnt`'s general template `Network.universalPositive_omegaLimit_of_closedPositiveConfine` (`UpperRegionFloorRefutation.lean:256`), per orchestrator Decision 1 |
| **V2** | A systematic computational + exact search of small networks finds **no** counterexample to Hole A | `research/scripts/holeA_refute_search.py`, phases 1 and 2 |

`#print axioms` on `upperRegion_inconsistent_with_boundaryOmegaPoint` reports exactly
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. The refutation is not resting on the
hole.

---

## V1 — the decisive negative result (settles the round-1 fork)

### The dispute

* `form-barrier`: `hfloor` is an *unbuilt* input — a floor on a **region**, not along the orbit.
* `papers-craciun`: `hfloor` is not unbuilt but **inconsistent**; `ω ⊆ K` is forced, and `hKpos`
  forces `wmax.Positive`, contradicting `hzeroMax`.

### The verdict: `papers-craciun` is right. Compiled.

```lean
theorem upperRegion_inconsistent_with_boundaryOmegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s)
    {wmax} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    False
```

`hsplit hx₀Z hfloor hε hopenLow hopenUp hdisj` are **exactly** the six surface hypotheses of
`exists_positive_omegaPoint_of_upperRegion` (`:1596`). `hwmax hPmaxne hzeroMax` are **exactly** the
three boundary-ω-point hypotheses of Hole A that mention the face.

### Proof, in four lines of mathematics

`exists_positive_omegaPoint_of_upperRegion`'s **own proof** establishes

* `horbit : ∀ t : ℝ≥0, ϕ t x₀ ∈ K` (its line 1646), where
  `K = closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀}`, and
* `hKpos : ∀ y ∈ K, y.Positive` (its line 1641), from `hfloor` plus closedness of the floor set.

`K` is **closed** and absorbs the forward image, so by `omegaLimit_subset_closure_image2`,
`ω ⊆ K`. Then `hwmax ⟹ wmax ∈ K ⟹ wmax.Positive`, so `wmax s > 0` for every `s`. But `hzeroMax`
gives `wmax s = 0` for every `s ∈ Pmax`, and `hPmaxne` supplies such an `s`. Contradiction.

The refutation uses **only** these ingredients, all already in the tree:
`orbit_stays_in_upperRegion` (`HighCodimensionSiphonFace.lean:1508`),
`genuineOrbit_pos` and `genuineOrbit_relEntropy_le` (`GenuineConfinement.lean:53`, `:141`),
`relEntropy_continuous` and `isCompact_relEntropy_sublevel` (`AsymptoticStability.lean:95`, `:142`),
`omegaLimit_subset_closure_image2` (Mathlib).

It uses **none** of: `hmaxExact`, `hzcard`, `hcodim`, `hcard`, `hrank`, `hωaff`, `hK`/`hmaps`,
`hωnn`, `hgenω`, the fan, a barrier, `hsep`, or any blueprint data. Two supporting closedness
lemmas were added because the criterion's proof needed them and they were not stated separately:
`isClosed_floorSet` and `isClosed_relEntropy_sublevel_nonneg`.

### Why `form-barrier`'s counter-argument fails

`form-barrier`'s position is that a *region* floor escapes the segment/closure refutations that kill
the `hsep` family. That is correct about `hsep` — and irrelevant here. The mechanism above is
different and does not use convexity, segments, or `hsep` at all:

> `closure Zupper` is closed, the floor set is closed, and **closed sets are closed**. A floor on a
> region passes through the closure automatically. That is the whole argument.

`form-barrier`'s "region floor, not orbit floor" distinction is real but does not rescue
`_of_upperRegion`: the region floor becomes an *orbit* floor the moment the orbit is confined to
`Zupper`, and `hsplit` + `hx₀Z` confine it, via `orbit_stays_in_upperRegion`, to `closure Zupper`.

### What this means for Hole A

**`_of_upperRegion` is a dead target**, and so is every other rung that routes through
`exists_positive_omegaPoint_of_coordinate_floors` with `T = S`: `blueprintData`,
`selfConsistent_normals`, `convex_tiles`, `tiled_faceCores`, `faceRelevantCore`, `toric_blueprint`,
`toric_halfspace`. Supplying `hm`, `hstart`, `hface`, `hcore` to any of them buys `False`, not the
conclusion. **Do not build those inputs.**

**This does not refute Hole A.** Hole A never supplies `hfloor`. The surface
`Zlow ∪ Zupper` with a uniform floor is exactly the unbuilt Craciun v3 §4/§7–§9 data, and V1 says
such a surface **cannot exist** for an orbit whose ω-limit set meets the boundary. That is a genuine
mathematical consequence of complex balance — it is the content of the Global Attractor Conjecture,
not a defect of the theorem. V1 is best read as: *Craciun's Step-4 certificate is the entire
difficulty of Hole A, and it is not approximable by any of the packaged criteria.*

---

## V2 — systematic counterexample search for Hole A's statement

### Hypothesis set searched

`hxs hcb hsol hϕγ hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hwmax hzeroMax hmaxExact hzcard hcodim
hcard hrank` with conclusion `∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive`.

A counterexample requires, in the Python encoding: a network with a **certified strictly positive
complex-balanced point**, and a positive start point whose genuine mass-action trajectory has
ω-limit set equal to a nonnegative `w` with `|zero(w)| ≥ 2` and
`rank(proj_{zero(w)} stoichSubspace) ≥ 2`. When the trajectory converges to a single point,
`hmaxExact` and `hzcard` hold automatically (ω is a singleton) and `hzeroMax` holds with
`Pmax := zero(w)`.

### Method — and the certification discipline

* **Complex balance is never accepted from a floating-point residual.** Candidates are snapped to
  `fractions.Fraction` and the complex-balance equations are re-verified **exactly**. A necessary
  pre-filter is applied first (the source-complex set must equal the target-complex set).
* **Weakly reversible networks are searched too**, not skipped. They are complex balanced by
  Craciun's theorem, and the Global Attractor Conjecture is open precisely there. An earlier
  revision of this script skipped them; that was wrong and is fixed.
* `stoichRank ≥ 2` is required up front, since `hcodim` forces it.
* Boundedness of the forward orbit (`hK`, `hmaps`) is checked on the integrated trajectory.

### PHASE 1 — exact, exhaustive: all first-order networks

For unimolecular networks the mass-action ODE is `x' = M x`, so complex balance is decided exactly
by linear algebra (`ker M` contains a strictly positive vector), and trajectories are obtained from
the linear system. Enumerated **all** such networks on `n = 2, 3, 4` species with `≤ 4` distinct
ordered reactions `i → j`.

```
python3 research/scripts/holeA_refute_search.py 1
```

**Result: no hits.**

```
phase1 {'nets': 852, 'rank_ok': 822, 'cb': 31, 'traj': 62} hits 0
```

852 first-order networks enumerated, 822 with `stoichRank ≥ 2`, **31 with a certified strictly
positive complex-balanced point**, 62 trajectories integrated, **0 hits**.

**A methodological trap worth recording.** My first run of this phase reported `cb = 0` on *every*
network, and I nearly filed "no counterexample found" on that basis. It was wrong: the test looked
for a positive kernel vector in the **range of `Mᵀ`** instead of in **`ker M`**. The `cb = 0` was an
artefact, not a result. Complex balance for a first-order network is exactly `M x = 0` for some
`x > 0` — species `b` gains `Σ_{r: target = b} x_{sole reactant} − Σ_{r: source = b} x_{sole
reactant}`, the `b`-th component of `M x` — so the decision belongs on `ker M`. Fixed to an SVD
nullspace computation with exact `Fraction` certification before a network is counted. This is the
same failure mode as the false positive in phase 2: **a "no counterexample" result is only as
trustworthy as its certification.**

### PHASE 2 — random general networks, exact CB certification

Random networks on `n ∈ {2,3,4}` species, 2–5 reactions, complexes of size `≤ 2`, rate constants
from `{0.5, 1, 2, 3}`, initial points from `[0.4, 2.5]`, integrated with LSODA to `T = 400` at
`rtol = 1e-11`.

```
python3 research/scripts/holeA_refute_search.py 2 <seed> <iters>
```

**Result: no hits**, seeds 0–3 at 1500 iterations each:

```
seed=0 nets=1500 rank_ok=1460 srcset_ok=93  cb_certified=93  cb_wr=93  traj=558 hits=0
seed=1 nets=1500 rank_ok=1463 srcset_ok=100 cb_certified=100 cb_wr=100 traj=600 hits=0
seed=2 nets=1500 rank_ok=1465 srcset_ok=100 cb_certified=100 cb_wr=100 traj=600 hits=0
seed=3 nets=1500 rank_ok=1466 srcset_ok=135 cb_certified=135 cb_wr=135 traj=810 hits=0
```

**An honest limitation, and it materially narrows what phase 2 covers.** In every seed
`cb_certified == cb_wr`: **every** network that passed was accepted by weak reversibility
(Craciun's theorem), and the numerical-plus-exact-rational path never fired once. Two filters
explain it:

* `balanced_source_set` keeps only networks whose source-complex set equals its target-complex set
  — a *necessary* condition for complex balance at a strictly positive point — and this rejects
  ~93% of random networks (`srcset_ok` ≈ 100 of 1500);
* among survivors, the `least_squares` + `Fraction` certification almost never converges to an
  exact rational certificate, because generic real CB solutions are not rational and snapping to
  `10⁻⁶…10⁻¹⁰` denominators destroys the equality.

So phase 2 as implemented covers **weakly reversible networks well and non-weakly-reversible
complex-balanced networks essentially not at all.** The latter is where an exotic counterexample
would most plausibly hide, so this is a real gap in the search, not a formality. A phase 3 that
enumerates structured non-WR families (Craciun's canonical examples, deficiency-one chains with a
catalyst, weakly-reversible networks with one reaction reversed) and certifies complex balance by
*exact symbolic* means — `sympy` solving the polynomial balance equations, then exact
verification — is the obvious next step and is not done.

### The one search hit that was discarded, and why it matters

An early, loosely-certified run reported a hit on a 4-species network. It was a **false positive of
the complex-balance test**, caught by the exact re-verification: the network was not complex
balanced at all. This is the single most important methodological point in this report —

> **A refutation of Hole A found by floating-point means is worthless and dangerous.** The
> hypothesis `hcb` is a strictly-positive complex-balanced point, and the search space is dense in
> networks that merely *look* complex balanced. Any adversarial claim about Hole A must come with
> exact certification.

The final script never accepts a `CB` claim on float evidence.

### What was searched, precisely

| Axis | Coverage |
|---|---|
| Species | 2, 3, 4 |
| Reaction order | phase 1: all order-1 (exhaustive, `≤4` reactions). phase 2: mixed order ≤ 2 |
| Network count | phase 1: all 852 order-1 nets on `n≤4`, `≤4` reactions (31 complex balanced). phase 2: 6000 random nets over 4 seeds (428 complex balanced, **all weakly reversible** — see the limitation above) |
| Rate constants | phase 1: all `κ ≡ 1` (mass-action is homogeneous, so rates are a rescaling of the trajectory shape together with `x₀`). phase 2: `{0.5,1,2,3}` |
| Start points | phase 1: `(1,1,…)` and `linspace(0.7,2.1,n)`. phase 2: 6 random per network |
| Horizon | `T = 400` |
| Weak reversibility | searched, **not** skipped — the GAC is open precisely there |

**Not covered, and this bounds the result:** `n ≥ 5`; complexes of size `≥ 3`; network topologies
requiring `≥ 5` reactions on 4 species; **non-weakly-reversible complex-balanced networks** (phase 2
reached none — see above); and — most importantly — this is a *numerical* search with exact
certification only of the complex-balance condition, not of the trajectory. A genuine counterexample
would be a counterexample to the Global Attractor Conjecture, which is believed true.

---

## Formulation-gap audit of the Lean statement

Each hypothesis compared against the classical Anderson–Shiu / Craciun–Fiebig–Singleton GAC
statement. **Conclusion: no exploitable gap.** The statement is faithful; where it looks weak, the
weakness is genuine mathematics rather than a missing hypothesis.

| Item | Finding |
|---|---|
| `Concentration S = S → ℝ` (plain reals, not `ℝ≥0^S`) | `CRNT/Kinetics/Concentration.lean:19`. Nonnegativity is the separate predicate `Nonnegative` (`:26`), carried by `hωnn` and `hKpos`. **Not exploitable**: every use of a concentration as an order-theoretic object is guarded by `hωnn` / `hΓpos` / `hxs` / `hx₀`. |
| `Flow` has only `cont'`, `map_add'`, `map_zero'` | Mathlib. No injectivity, no monotonicity, no dissipativity. **Not exploitable**, because `hϕγ` + `hsol` pin the flow to the genuine mass-action solution. |
| `StoichCompatible` uses the linear `Submodule`, not the stoichiometric *cone* | `CRNT/Equilibria/CompatibilityClass.lean:25`. Displacements leaving the positive orthant are admitted. **Not exploitable**: `hsep_fails_of_boundaryPoint_mem_sublevel` and the `floor`-based obstructions all use positivity as a *premise*, which the linear relaxation cannot fake. |
| `projOn Pmax` is a coordinate projection, not a projection onto a face of the stoichiometric subspace | `CRNT/Dynamics/FacetRepulsionAndersonShiu.lean:316`. Ignores stoichiometric structure. **Not exploitable**: it is used only in the codimension hypothesis `hcodim`, where the classical statement likewise asks for the rank of the coordinate restriction. It is a *narrower* (more conservative) condition, so it cannot admit a counterexample the classical statement excludes. |
| `omegaLimit` is Mathlib's, `Filter.atTop` | Standard. `hmaps`+`hK` give precompactness, so `isClosed_omegaLimit` and `nonempty_omegaLimit_of_isCompact_absorbing` apply. |
| `hxs`/`hcb` — `xstar` unrelated to `x₀` | `IsComplexBalanced` is a property of the network+rates, so any positive CB point certifies it. Classical GAC likewise assumes a complex-balanced *network*, not a relation to the start point. **Not a gap.** |
| `hmaxExact` / `hzcard` / `hzeroMax` — the "critical siphon face" apparatus | Craciun never states this. It is the repo's own encoding of "the ω-limit set meets a face of codimension ≥ 2 in the compatibility class". Faithful to the *intended* statement (per `HOLEA-FRAMING.md` F-1), and **stricter** than Theorem B, which has no such apparatus. |

**The single real weakness** is the one the orchestrator identified as F-3 and V1 confirms: the
hypotheses do not supply the fan, and every packaged criterion that would bridge to them
(`faceRelevantCore`, `tiled_faceCores`, `toric_blueprint`, `toric_halfspace`, `upperRegion`) demands
a separation clause or a coordinate floor that Hole A's data **cannot** supply. That is the theorem.

---

## A correction I owe the ledger

`form-barrier`'s defence of `_of_upperRegion` — that a *region* floor escapes the segment and
closure refutations that kill the `hsep` family — is **wrong**, and four of us came close to
shipping it. The distinction is real but irrelevant here: `hfloor` is consumed through
`closure_minimal`, i.e. as a fact about `closure Zupper`, and ω-limit points lie in the closure of
the orbit image. A floor on a region becomes a floor on the orbit. I recorded that reasoning in
this report's V1 section while still holding the opposing view, which is why it is worth keeping
verbatim: it is the mistake, not just its resolution.

## Recommendation

1. **Record V1 in `research/DEAD-ENDS.md`** as the resolution of the fork: `papers-craciun` correct,
   `form-barrier` conceded. Per orchestrator Decision 1 the canonical citation is now
   `universalPositive_omegaLimit_of_closedPositiveConfine` (A-28), **not** `Permanent` — `Permanent`
   is a hypothesis Hole A never assumes, so it cannot be what refutes it; it merely discharges
   A-28's template.
2. **Do not build** `hm`, `hstart`, `hface`, `hcore`, or any blueprint data. They feed dead criteria.
3. **Do not spend budget on further counterexample search.** V2 found nothing over an exact,
   documented space, and a hit would refute the Global Attractor Conjecture.
4. **Do not run phase 3 of the search.** A counterexample to Hole A is a counterexample to the GAC;
   the search space I can reach is a tiny corner of it, and phase 2 demonstrably misses the
   non-weakly-reversible case entirely. The budget is better spent on Hole B.
5. Per the orchestrator's round-1 close, the live residue is
   `ComparableGrowthDescent.descend` (`SiphonDimensionDescent.lean:125-132`) with
   `eq_zero_on_pmax_of_conservation_eq` (`:569`) as the missing half. Note `adv-audit`'s
   `comparableGrowthDescent_is_not_a_weaker_route` shows it is *equivalent* to the goal, so it is
   not a cheaper route — it is the same difficulty stated as a dynamical estimate.

## Reproducing

```sh
cd <worktree>
research/scripts/checkmod.sh CRNT/Dynamics/UpperRegionObstruction.lean   # → OK, 0 sorry-warnings
python3 research/scripts/holeA_refute_search.py 1                        # phase 1, exhaustive, exact
python3 research/scripts/holeA_refute_search.py 2 0 4000                 # phase 2, seeded, deterministic
```