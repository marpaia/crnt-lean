# The consumer chain below hole A — verified link by link

**Scope.** Everything that must hold for
`CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:111`) to be *used* by the Global Attractor chain.
Hole A's own statement is untouched by this document.

**Bottom line.**

* The chain is **complete**: every link elaborates, and `#print axioms` on each of them reports
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx` anywhere below hole A.
* **Yes**, closing hole A closes `complexBalanced_genuinePermanent` (and hence
  `complexBalanced_permanent` and `complexBalanced_globalAttractor`). There is exactly one
  unproven branch, and it is hole A.
* But the chain as written is a **dead route**, and I proved that machine-checked rather than in
  prose. See §3.

---

## 1. Verified facts

### 1.1 `docs/gac-bridge-gap-analysis.lean` is clean

Command (from the worktree root):

```sh
LEAN_PATH=/Users/akutuva/Documents/Proofs/crnt-lean/.lake/build/lib/lean \
  lake env lean docs/gac-bridge-gap-analysis.lean
```

Exact output:

```
$ ls docs/
analyze-contract.md  architecture.md  decidability.md  deficiency.md  design.md  dynamics.md
foundations.md  gac-bridge-gap-analysis.lean  gac-bridge-gap-analysis.md  gac-v3-face-fill-plan.md
generated-certificates.md  global-persistence.md  multistationarity-robustness.md  oscillation.md
persistence-gac.md  stochastic.md
=== RUN ===

real	9m7.360s
user	1m47.248s
sys	4m51.838s
```

i.e. **empty stdout/stderr**. No errors, no warnings, no `sorry`, no `declaration uses 'sorry'`.
The claim in the file's docstring holds.

### 1.2 The axiom audit

`#print axioms` on the whole chain (run against the shared build cache):

| declaration | axioms |
| --- | --- |
| `Network.complexBalanced_genuinePermanent` | `[propext, **sorryAx**, Classical.choice, Quot.sound]` |
| `Network.complexBalanced_permanent` | `[propext, **sorryAx**, Classical.choice, Quot.sound]` |
| `Network.complexBalanced_globalAttractor` | `[propext, **sorryAx**, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` | `[propext, **sorryAx**, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_blueprintData` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_selfConsistent_normals` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_convex_tiles` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_toric_blueprint` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_tiled_faceCores` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_faceRelevantCore` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_toric_halfspace` | `[propext, Classical.choice, Quot.sound]` |
| `Network.hsep_fails_of_boundaryPoint_mem_sublevel` | `[propext, Classical.choice, Quot.sound]` |
| `Network.barrier_le_of_mem_omegaLimit` | `[propext, Classical.choice, Quot.sound]` |
| `Network.exists_positive_omegaPoint_of_coordinate_floors` | `[propext, Classical.choice, Quot.sound]` |
| `Network.coordinate_lower_bounds_of_toric_barrier` | `[propext, Classical.choice, Quot.sound]` |
| `Network.barrier_le_of_toric_descent_in_band` | `[propext, Classical.choice, Quot.sound]` |

### 1.3 There is no second `sorry` under the GAC chain

A transitive-import closure computation over `CRNT/` from `CRNT.Dynamics.GlobalAttractorTheorem`
gives **326 modules**. The only executable `sorry` in that closure is
`CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`. In particular
`CRNT.Multistationarity.TrueChemistrySRCriterion` (hole B) is **not** in the GAC closure, so the
two holes are independent.

---

## 2. The chain, one row per link, with exact signatures

Read bottom-up. "Feeds" = the hypothesis each link asks for and where it comes from.

| # | declaration | file:line | exact hypothesis list (abbreviating `hxc`-prefixed names) |
| --- | --- | --- | --- |
| 0 | hole A `exists_positive_omegaPoint_of_highCodimension_siphonFace` | `Dynamics/HighCodimensionSiphonFace.lean:111` | `(N) (κ) {xstar} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {ϕ} {γ} {x₀} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t) (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) {K} (hK : IsCompact K) (hmaps : ∀ t, ϕ t x₀ ∈ K) (hωnn : ∀ y ∈ omegaLimit, Nonnegative y) (hgenω : ∀ y ∈ omegaLimit, ∀ t ≥ 0, HasDerivAt (γ y) (field κ (γ y t)) t) (hωaff : ∀ z ∈ omegaLimit, (z - x₀) ∈ N.stoichSubspace) (hx₀ : x₀.Positive) {Pmax} (hPmaxne : Pmax.Nonempty) {wmax} (hwmax : wmax ∈ omegaLimit) (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) (hmaxExact : ∀ z ∈ omegaLimit, (∀ s ∈ Pmax, z s = 0) → ∀ s, z s = 0 ↔ s ∈ Pmax) (hzcard : ∀ z ∈ omegaLimit, card (univ.filter (· s = 0)) ≤ Pmax.card) (hcodim : 2 ≤ finrank ℝ (N.stoichSubspace.map (projOn Pmax))) (hcard : 2 ≤ Pmax.card) (hrank : N.stoichRank ≠ 1)` ⟹ `∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive` |
| 1 | `exists_positive_omegaPoint_of_tiled_faceCores` | `Dynamics/FaceDirectionCone.lean:367` | `0`'s `hxs hcb hϕγ hK hmaps` **+** `(hΓcont : ContinuousOn (γ x₀) (Ici 0)) (hΓpos : ∀ t ≥ 0, (γ x₀ t).Positive) (hΓd : ∀ t ≥ 0, HasDerivAt (γ x₀) (field κ (γ x₀ t)) t) (hclass : ∀ t ≥ 0, N.StoichCompatible (γ x₀ 0) (γ x₀ t)) (hδ : 0 < δ) {P} {B R} {ι'} [Fintype ι'] [Nonempty ι'] {σ : ι' → Set _} (hσne : ∀ k, (N.relevantCones (σ k) δ B).Nonempty) {m} (hm : ∀ k, m k ∈ N.relevantCore (σ k) δ B (hσne k)) {b : ι' → ℝ} (hstart : minMaxBarrier (fun k _ => ⟪-m k, ·⟫) (fun k _ => b k) (state (γ x₀ 0)) ≤ R) (hassign : ∀ t ≥ 0, R ≤ minMaxBarrier … → ∃ k, barrier (fun _ => ⟪-m k,·⟫) (fun _ => b k) (state (γ x₀ t)) = minMaxBarrier … ∧ (∀ s ∈ P, γ x₀ t s ≤ xstar s) ∧ ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B ∧ N.faceLogPart P xstar (γ x₀ t) ∈ σ k) (hsep : ∀ s, ∃ ε > 0, ∀ x, x.Positive → N.StoichCompatible (γ x₀ 0) x → minMaxBarrier … (state x) ≤ R → ε ≤ x s)` |
| 2 | `exists_positive_omegaPoint_of_faceRelevantCore` | `Dynamics/FaceDirectionCone.lean:417` | `0`'s orbit hypotheses + `hclass` + `hδ {P} {B c} (hcore : (N.faceRelevantCones P δ B).Nonempty) {m} (hm : m ∈ N.faceRelevantCore P δ B hcore) (hstart : ⟪-m, state (γ x₀ 0)⟫ ≤ c) (hface : ∀ t ≥ 0, c ≤ ⟪-m, state (γ x₀ t)⟫ → (∀ s ∈ P, γ x₀ t s ≤ xstar s) ∧ ‖offFaceLogPart‖ ≤ B) (hsep : ∀ s, ∃ ε > 0, ∀ x, Positive → Compatible → ⟪-m, state x⟫ ≤ c → ε ≤ x s)` |
| 3 | `exists_positive_omegaPoint_of_toric_blueprint` | `Dynamics/ToricBarrierTrapping.lean:422` | `hxs hcb hϕγ hK hmaps hΓcont hΓpos hΓd hclass (hδ) {n : ι' → ι → _} {b} {R} (hstart : minMaxBarrier (fun k i => ⟪-n k i, ·⟫) b (state (γ x₀ 0)) ≤ R) (hnear : ∀ t ≥ 0, R ≤ minMaxBarrier … → ∃ k, barrier (fun i => ⟪-n k i,·⟫) (b k) (state (γ x₀ t)) = minMaxBarrier … ∧ ∀ i, ⟪-n k i, state (γ x₀ t)⟫ - b k i = barrier … → ∀ C ∈ N.relativeSourceOrderNegativeStoichFan, infDist (N.relativeLogFanState xstar (γ x₀ t)) C < δ → n k i ∈ C) (hsep : ∀ s, ∃ ε > 0, ∀ x, Positive → Compatible → minMaxBarrier … (state x) ≤ R → ε ≤ x s)` |
| 4a | `exists_positive_omegaPoint_of_convex_tiles` | `Dynamics/ToricBarrierExplicit.lean:347` | orbit hyp + `hclass` + `hδ {P} {B R R'} (hRR' : R < R') {σ} {m} (hm : ∀ i, ∀ C ∈ N.relevantCones (σ i) δ B, m i ∈ C) {b} (hstart : barrier (fun i => ⟪-m i,·⟫) b (state (γ x₀ 0)) ≤ R) (hassign : ∀ t ≥ 0, R ≤ barrier … → barrier … ≤ R' → ∀ i, ⟪-m i, state (γ x₀ t)⟫ - b i = barrier … → N.faceLogPart P xstar (γ x₀ t) ∈ σ i) (hregime : ∀ t ≥ 0, R ≤ barrier … → barrier … ≤ R' → ‖offFaceLogPart P xstar (γ x₀ t)‖ ≤ B) (hsep : ∀ s, ∃ ε > 0, ∀ x, Positive → Compatible → barrier … (state x) ≤ R → ε ≤ x s)` |
| 4b | `exists_positive_omegaPoint_of_selfConsistent_normals` | `Dynamics/ToricBarrierExplicit.lean:502` | orbit hyp + `hclass` + `hδ {P} {B R R'} (hRR') {m} {b} (hm : ∀ i, ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B, m i ∈ C) (hstart) (hregime) (hsep)` — i.e. 4a with `σ i := activeFaceImage … i`, so `hassign` is discharged by `N.faceLogPart_mem_activeFaceImage` |
| 5 | `exists_positive_omegaPoint_of_blueprintData` | `Dynamics/ToricBarrierExplicit.lean:578` | orbit hyp + `hclass` + `hδ {P} {B R R' M} (hRR') (hMclass : ∀ x, x.Positive → N.StoichCompatible (γ x₀ 0) x → ∀ u, x u ≤ M) {m} {b} (piece : S → ι') (hpos : ∀ s, 0 < ((m (piece s) : EuclideanSpace ℝ S) s)) (hlevel : ∀ s, M * (∑ u ∈ univ.erase s, max (m (piece s) u) 0) < -(R + b (piece s))) (hm) (hstart) (hregime)` — `hsep` is discharged internally by `N.coordinate_floor_of_dominant_barrier` from `hMclass`/`hpos`/`hlevel` |
| 6 | `exists_positive_omegaPoint_of_coordinate_floors` | `Dynamics/ToricBarrierTrapping.lean:366` | `(hϕγ) {K} (hK : IsCompact K) (hmaps) (hlower : ∀ s, ∃ ε > 0, ∀ t ≥ 0, ε ≤ γ x₀ t s)` ⟹ `∃ p ∈ omegaLimit, p.Positive` — **no `N`, no `κ` at all** |
| 7 | `coordinate_lower_bounds_of_toric_barrier` | `Dynamics/ToricBarrierTrapping.lean:308` | `(N κ hxs hcb hδ) {n} {b} {R} {Γ} (hΓcont) (hΓpos) (hΓd) (hclass) (hstart : minMaxBarrier … (state (Γ 0)) ≤ R) (hnear) (hsep)` ⟹ `∀ s, ∃ ε > 0, ∀ t ≥ 0, ε ≤ Γ t s` |
| 8 | `barrier_le_of_toric_descent_in_band` | `Dynamics/ToricBarrierTrapping.lean:165` | `(N κ hxs hcb hδ) {n} {b} {R R'} (hRR' : R < R') {Γ} (hΓcont) (hΓpos) (hΓd) (hstart : barrier (fun i => ⟪-n i,·⟫) b (state (Γ 0)) ≤ R) (hnear)` ⟹ `∀ t ≥ 0, barrier … (state (Γ t)) ≤ R` |

Edges:

```
1 ─┐                                              ┌─ 6  exists_positive_omegaPoint_of_coordinate_floors
2 ─┤                                              │        ▲
3 ─┤  all ── 8 (trapping) ───────────────────────┤        │ 7 (coordinate_lower_bounds_of_toric_barrier)
4a─┼── 4a ── 8 ──────────────────────────────────┤        │
4b─┤── 4b ── 8 ──────────────────────────────────┤        │
5 ─┘  5 ── 8 ────────────────────────────────────┘        │
└──────────────────────▶ hole A (needs a *different* final step; none exists)
```

Note the shape: 1→3→4a/4b→5 all *conclude* hole A's conclusion, they do not *feed* it. The chain is a
ladder of successively packaged sufficient criteria; each rung consumes the rung below plus one
more hypothesis. Nothing on the ladder is a hypothesis of hole A.

### 2.1 The three orbit bridges `docs/gac-bridge-gap-analysis.lean` discharges

| bridge | source lemma | signature |
| --- | --- | --- |
| continuity | `Network.orbit_pos_forward`'s companion, direct | `(hsol t ht).continuousAt` on `Ici 0` |
| forward positivity | `CRNT.Dynamics.OrbitRegularity.lean:66` | `(N κ) {B} {Γ} (hΓ0 : (Γ 0).Positive) (hΓbdd : ∀ t ≥ 0, ∀ s, Γ t s ≤ B) (hΓd) : ∀ t ≥ 0, (Γ t).Positive` — needs a **uniform ceiling** `B`, obtained from `hK`/`hmaps` via `hK.exists_isMaxOn` |
| class invariance | `CRNT.Dynamics.OrbitRegularity.lean:53` | `(N κ) {Γ} (hΓd) : ∀ t ≥ 0, N.StoichCompatible (Γ 0) (Γ t)` |

So all four orbit-side hypotheses (`hΓcont`, `hΓpos`, `hΓd`, `hclass`) of rows 1–5 are already
derivable from `0`'s own `hsol`, `hx₀`, `hK`, `hmaps`. That part of the chain is genuinely closed.

### 2.2 The two lemmas after line 140

`CRNT/Dynamics/HighCodimensionSiphonFace.lean:184` and `:272`:

```
theorem hsep_fails_of_boundaryPoint_mem_sublevel {ι'} [Fintype ι'] [Nonempty ι']
    (N : Network S) (m : ι' → N.euclideanStoichSubspace) (b : ι' → ℝ) (R : ℝ)
    {x₀ wmax : Concentration S} {s : S}
    (hx₀ : x₀.Positive) (hwnn : Concentration.Nonnegative wmax)
    (hcompat : N.StoichCompatible x₀ wmax) (hsw : wmax s = 0)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R)
    (hwmax : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState wmax) ≤ R) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive → N.StoichCompatible x₀ x →
        PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
          (N.euclideanStoichState x) ≤ R → ε ≤ x s
```

```
theorem barrier_le_of_mem_omegaLimit {ι'} [Fintype ι'] [Nonempty ι']
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ wmax : Concentration S} (N : Network S) (m : ι' → N.euclideanStoichSubspace)
    (b : ι' → ℝ) (R : ℝ)
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (htrap : ∀ t : ℝ, 0 ≤ t → PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R)
    (hw : wmax ∈ omegaLimit atTop ϕ {x₀}) :
    PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState wmax) ≤ R
```

Both audit clean (`[propext, Classical.choice, Quot.sound]`).

---

## 3. The gap I found and closed: the wiring was prose, not Lean

`HighCodimensionSiphonFace.lean:170-171` says of these two lemmas:

> "The two lemmas below are the machine-checked core of this analysis; **the wiring to each
> criterion's hypotheses is the paragraph above**."

That paragraph is not a proof. It claims the packaged route is dead but never *demonstrates* that
the criteria's own hypotheses can be fed and contradicted. I wrote that wiring.

### New module `CRNT/Dynamics/BlueprintRouteRefutation.lean` (hole-free)

Three theorems, weakest first.

**(a) Barrier-free obstruction.**

```
theorem floor_on_omegaLimit_of_floor_along_orbit
    {ϕ} {γ} {x₀} (hϕγ) {K} (hK : IsCompact K) (hmaps)
    {ε} (hε : 0 < ε) {s} (hfloor : ∀ t, 0 ≤ t → ε ≤ γ x₀ t s)
    (z) (hz : z ∈ omegaLimit atTop ϕ {x₀}) : ε ≤ z s

theorem no_uniform_floor_along_orbit_of_boundaryOmegaPoint
    {ϕ} {γ} {x₀} (hϕγ) {K} (hK : IsCompact K) (hmaps)
    {w} {s} (hw : w ∈ omegaLimit atTop ϕ {x₀}) (hsw : w s = 0) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s
```

(a) is a general fact, proved from `omegaLimit_subset_closure_image2` + closedness of `Ici.preimage
(continuous_apply s)`: the orbit lies in `{y | ε ≤ y s}`, that set is closed, every ω-limit point is
in the closure of the orbit, so it carries the floor too.

This is strictly stronger than the packaged obstruction: it uses **no barrier, no polyhedron, no
fan, no `N` and no `κ`**. Consequence: `exists_positive_omegaPoint_of_coordinate_floors` (row 6),
`coordinate_lower_bounds_of_toric_barrier` (row 7) and
`exists_positive_omegaPoint_of_uniform_coordinate_lower_bounds`
(`Dynamics/GlobalAttractorTheorem.lean:288`) can never be applied to an orbit whose ω-limit set
meets a boundary face. Any route to hole A through a **uniform coordinate floor** is dead —
including ones not yet written.

**(b) The barrier wiring.**

```
theorem not_separationClause_of_boundaryOmegaPoint
    {ϕ} {γ} {x₀ wmax} (hϕγ) (N : Network S) (m : ι' → N.euclideanStoichSubspace)
    (b : ι' → ℝ) (R : ℝ)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R)
    (htrap : ∀ t, 0 ≤ t → PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R)
    (hx₀ : x₀.Positive) (hwnn : Concentration.Nonnegative wmax)
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀}) (hcompat : N.StoichCompatible x₀ wmax)
    {s : S} (hsw : wmax s = 0) :
    ¬ ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
        N.StoichCompatible x₀ x →
        PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
          (N.euclideanStoichState x) ≤ R → ε ≤ x s
```

i.e. `hsep` is refuted from `hstart` + trapping + one boundary ω-point. This is exactly the
"paragraph above", now a theorem.

**(c) The full refutation — the headline result.**

```
theorem blueprintData_inconsistent_with_highCodimension
    (N : Network S) (κ : N.RateConstants)
    {xstar} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ} {γ} {x₀}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' M : ℝ} (hRR' : R < R')
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} (piece : S → ι')
    (hMclass : ∀ x : Concentration S, x.Positive → N.StoichCompatible (γ x₀ 0) x →
      ∀ u, x u ≤ M)
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hlevel : ∀ s : S,
      M * (∑ u ∈ Finset.univ.erase s, max ((m (piece s) : EuclideanSpace ℝ S) u) 0)
        < -(R + b (piece s)))
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B,
      m i ∈ C)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B) :
    False
```

Proof (all verified steps):

1. `hγ0 : γ x₀ 0 = x₀` from `hϕγ x₀ 0`.
2. Uniform ceiling `Bx` on the compact `K` via `hK.exists_isMaxOn`, hence on the orbit.
3. The three bridges: `hΓcont` (differentiability), `hΓpos` (`N.orbit_pos_forward κ`),
   `hclass` (`N.stoichCompatible_of_forward_solution κ`) — identical to the bridge file.
4. `hnear` assembled from `hm`, `N.faceLogPart_mem_activeFaceImage`, `hregime` and
   `N.mem_relevantCones_of_infDist_lt` — the same assembly as inside row 4a.
5. `htrap` from `N.barrier_le_of_toric_descent_in_band`.
6. `hstart0` (at `x₀` rather than `γ x₀ 0`) by rewriting `hγ0`.
7. `hsep` reconstructed exactly as row 5 does it, from `N.coordinate_floor_of_dominant_barrier`
   + `hMclass`.
8. `hwcompat` from `hωaff`; pick `s₀ ∈ Pmax` and get `wmax s₀ = 0` from `hzeroMax`.
9. `not_separationClause_of_boundaryOmegaPoint` applied to that `hsep`.

Note which hole A hypotheses are *not* used: `hgenω`, `hmaxExact`, `hzcard`, `hcodim`, `hcard`,
`hrank`, and the `Pmax`-maximality content. The refutation needs only "the ω-limit set is
nonnegative, is compatible with `x₀`, and contains a point vanishing at some coordinate".

**Interpretation.** Rows 1–5 of the ladder are *consistent* criteria — you can satisfy all of their
hypotheses for a network whose ω-limit set is entirely interior. But the moment you *also* assume
hole A's ω-limit hypotheses, they become unsatisfiable. So instantiating a packaged criterion to
prove hole A does not produce hole A's conclusion; it produces `False` from an inconsistent
premise. Any proof of hole A that routes through row 5 is therefore a proof of `False`, i.e. a
proof of the *stronger* claim "no complex-balanced ω-limit set ever meets a coordinate face" —
which is a strictly stronger statement than the GAC needs and is refuted by
`CRNT.Examples.CodimTwoFaceModel`.

---

## 3b. THE FORK IS SETTLED BY COMPILATION — every pre-packaged criterion is refuted

`CRNT/Dynamics/BlueprintRouteRefutation.lean`, all eight theorems auditing to
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`), `checkmod.sh` = `OK`, 0 sorry-warnings.

| criterion | refuted by | mechanism |
| --- | --- | --- |
| `…_of_blueprintData` | `blueprintData_inconsistent_with_highCodimension` (`:False`) | full hypothesis set + hole A's ω-hypotheses ⟹ `False` |
| `…_of_selfConsistent_normals`, `…_of_convex_tiles` | `not_separationClause_of_boundaryOmegaPoint` | same `hsep` shape |
| `…_of_tiled_faceCores`, `…_of_faceRelevantCore` | `no_uniform_floor_along_orbit_of_boundaryOmegaPoint` | barrier-free; covers the `minMaxBarrier` rungs too |
| `…_of_toric_blueprint`, `…_of_toric_halfspace` | same | they route through `exists_positive_omegaPoint_of_coordinate_floors` with `T = S` |
| `…_of_upperRegion` (:1596) | `upperRegion_criterion_inconsistent_with_boundaryOmegaPoint` (`:False`) | see below |

### Why `_of_upperRegion` dies — the disputed point, resolved

The objection was: the criterion builds `K := closure Zupper ∩ {relEntropy ≤ relEntropy x₀}`, a
**closed** set containing the whole orbit image (`himgs`, :1655), so `ω ⊆ K` is forced; `hKpos`
(:1629) is **universal** (`∀ y ∈ K, y.Positive`); hence `wmax ∈ ω ⊆ K` is forced strictly positive,
contradicting `hzeroMax` + `hPmaxne`.

**That is correct, and it is now compiled.** The exact argument:

```
hstay      : ∀ t ≥ 0, γ x₀ t ∈ Zupper        -- orbit_stays_in_upperRegion, from hsplit + hx₀Z
hfloorC    : closure Zupper ⊆ {y | ∀ s, ε ≤ y s}
⇒ orbit ⊆ closure Zupper
⇒ orbit image ⊆ K
⇒ ω ⊆ K                                   -- omegaLimit_subset_closure_image2, K closed
⇒ wmax ∈ K ⟹ ∀ s, ε ≤ wmax s             -- hKpos
⇒ ε ≤ wmax s₀ = 0                         -- hzeroMax, hPmaxne
```

Convexity of the barrier sublevel is **irrelevant** here, which is why the convexity-based
argument of §3 does not cover this criterion and why the region-vs-orbit distinction does not save
it: the containment `orbit image ⊆ closure Zupper` is direct.

So `hfloor` is not an unbuilt input to that criterion; it is an *inconsistent* one. This is the
same obstruction as `Network.not_persistentFrom_of_mem_omegaLimit_notPositive`
(`HighCodimensionSiphonFace.lean:407`).

### The general principle, now machine-checked

**Canonical statement (consolidated by `infra-scaffold-crnt`, branch `research/infrascaffold`):**

```lean
CRNT.Network.universalPositive_omegaLimit_of_closedPositiveConfine
  (hKc : IsClosed K) (hKpos : ∀ y ∈ K, y.Positive) (hv : v ∈ atTop)
  (hvK : closure (Set.image2 ϕ v {x₀}) ⊆ K) : ∀ y ∈ omegaLimit atTop ϕ {x₀}, y.Positive
```

`sorryAx`-free, and stated with no floor, no `ε`, no concentration structure and no reaction
network — a bare set-theoretic condition. This is the template that retires the family at once.
`floor_on_omegaLimit_of_floor_along_orbit` and `floor_on_omegaLimit_of_floor_on_region` in my
module are the floor-shaped instances of it; **`infra-scaffold-crnt`'s statement is the one to
cite**, and mine should be read as corollaries.

Note that `upperRegion_criterion_inconsistent_with_boundaryOmegaPoint` is *not* a corollary of
the template and does not reduce to it: the template takes the closed confinement as a hypothesis,
whereas this one takes `_of_upperRegion`'s actual hypothesis set (`hsplit`, `hopenLow`,
`hopenUp`, `hdisj`, `hx₀Z`, `hfloor`) and *derives* the confinement via
`Network.orbit_stays_in_upperRegion`. That is the statement that answers "are the packaged
criterion's own hypotheses satisfiable under the hole's?", which is what retires the criterion.

In words:

> Any certificate that traps the orbit image in a set floored away from the coordinate boundary
> also traps the **whole ω-limit set** there, hence is incompatible with a boundary ω-point.

This is a statement about the proof architecture of the whole tree, not about one criterion: every
`PersistentFrom` certificate, every `barrier` sublevel criterion, and every `Zupper` region
criterion falls under it. A proof of hole A cannot be a *confinement* argument. This is why
`CodimTwoFaceModel` shows the hypotheses are satisfiable with a false conclusion.

### What remains

`Network.omegaLimit_positive_of_descend` / `Network.ComparableGrowthDescent`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:124`, `:137`) — the Anderson-style descent named in the
hole's own docstring at :167–175. It is the only packaged route not of the confinement shape. Its
residual is branch (I): a carried critical siphon `Q` with `Q.card < Pmax.card`, which `hzcard` does
not refute. `descendStep_iff_omegaPointPositive_of_cardMinimal` shows the iteration bottoms out at
the goal itself, so the descent hypothesis is equivalent to hole A's conclusion, not weaker.

The weakened, satisfiable statement proved here as a starting point for any future route is
`exists_positive_omegaPoint_of_relInteriorFace`: floors off `P` give an ω-limit point in the
relative interior of the `P`-face.

## 4. Does closing hole A close the GAC chain?

**Yes — unconditionally, with no other unproven branch.**

`complexBalanced_genuinePermanent` (`Dynamics/GlobalAttractorTheorem.lean:1490`) is a `by` block
whose branches are:

| branch | discharged by | status |
| --- | --- | --- |
| `N.HasNoCriticalSiphon` | `positiveOmegaPointForRates_of_boundaryOmegaExcluded ∘ boundaryOmegaExcluded_of_hasNoCriticalSiphon` | proved |
| `N.stoichSubspace = ⊥` | `positiveOmegaPointForRates_of_trivialStoichSubspace` | proved |
| `N.stoichRank = 1` | `positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one` | proved |
| residual orbit already has a positive ω-point | `positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium`, first disjunct | proved |
| `Pmax` is a facet | `False.elim ∘ no_omegaLimit_meets_locally_repelling_face ∘ facet_repelling_near_facet_point_of_facet` | proved |
| `Pmax` is not a facet | `exists_positive_omegaPoint_of_highCodimension_siphonFace` at line 1555 | **hole A** |

The last row is the only `sorryAx` in the 326-module import closure (§1.3), and the axiom audit
(§1.2) confirms `complexBalanced_genuinePermanent`, `complexBalanced_permanent` and
`complexBalanced_globalAttractor` each report exactly one `sorryAx`, which is hole A's.

`complexBalanced_permanent` (`:1561`) and `complexBalanced_globalAttractor` (`:1624`) are thin
wrappers over `complexBalanced_genuinePermanent`, so they close with it.

So the dependency is exactly one edge wide. **Replace the `sorry` at
`HighCodimensionSiphonFace.lean:135` with any proof and `measure.py` reports `holes = 1`.**

---

## 5. What hole A must actually supply

Not a blueprint. Per §3, a uniform-floor blueprint is *refutable*. Hole A must supply one of:

1. **An Anderson-style descent.** `Network.omegaLimit_positive_of_descend`
   (`CRNT/Dynamics/SiphonDimensionDescent.lean:137`) already closes
   `ComparableGrowthDescent ϕ x₀` + `hP₀crit` ⟹ positive ω-point. What is missing is deriving
   `N.ComparableGrowthDescent ϕ x₀` from hole A's hypotheses. The `SiphonDimensionDescent`
   module docstring (line 248) identifies branch (I) as the residue: a carried critical siphon
   `Q` with `Q.card < Pmax.card`, which `hzcard` does not refute.
2. **A local-persistence argument on `wmax`.** The codimension `≥ 2` and `hcard ≥ 2` hypotheses
   are precisely the Anderson–Shiu side conditions; `facet_repelling_near_facet_point_of_facet`
   already handles codimension `1`. A codimension-`≥ 2` analogue of that theorem
   (`hcodim` unused today, other than being passed to hole A) is the missing analytic ingredient.

`hcodim` is the sharpest unused hypothesis: nothing in the whole tree consumes
`2 ≤ finrank ℝ (N.stoichSubspace.map (projOn Pmax))` except the `exists ⟨hcodim, hcard⟩` destructuring
at `GlobalAttractorTheorem.lean:1553`. Whatever closes hole A will have to be the first consumer of
it.

## 6. Dead ends (machine-checked)

* **Instantiate `…_of_blueprintData` (row 5) inside hole A.** Refuted:
  `blueprintData_inconsistent_with_highCodimension`.
* **Instantiate `…_of_selfConsistent_normals` / `…_of_convex_tiles` (row 4).** Refuted: row 4's
  `hsep` is `row 5`'s `hsep`, so the same argument applies with `hMclass`/`hpos`/`hlevel` deleted
  from the input. Formally: `not_separationClause_of_boundaryOmegaPoint` is stated for exactly
  row 4's `hsep` shape.
* **Instantiate `…_of_toric_blueprint` (row 3) or `…_of_tiled_faceCores` (row 1).** Same `hsep`
  shape modulo `minMaxBarrier` vs `barrier`; the min-max form is *stronger* (it implies the convex
  `barrier` form by `Network.minMaxBarrier_le_of_toric_descent`), so the convex refutation covers
  it after one rewriting step. **Not yet formalised** — flagged as residual, see §7.
* **Any route producing uniform coordinate floors on the orbit.** Refuted, barrier-free:
  `no_uniform_floor_along_orbit_of_boundaryOmegaPoint`. This kills
  `exists_positive_omegaPoint_of_uniform_coordinate_lower_bounds` for hole A too.

## 7. Residual work

* Formalise the `minMaxBarrier` variant: `¬ hsep_minmax` given `hstart` (min-max),
  `barrier_le_of_toric_descent` and a boundary ω-point. One `minMaxBarrier ≤ barrier` rewriting
  step away from (b); not done.
* Import `CRNT/Dynamics/BlueprintRouteRefutation` into `CRNT.lean` once the orchestrator's build
  runs (not done here — no `lake build` from a researcher).
---

## 8. A-11 (relint-chamber fix for `CraciunZSH.hinterior`) — attempted, NOT landed

I wrote `CRNT/Geometry/CraciunRelintChamber.lean` with four theorems
(`exists_eventual_tube_subset_of_relint_chamber`, `…_closed`, the finite-family form, and
`exists_uniform_logCube_toricField_support_of_faithful_normals_relint`). **It did not come to
green within my budget and I deleted it rather than commit non-compiling code.** Two concrete
blockers, both useful to whoever picks it up:

1. **`Set.affineSpan` does not exist in this Mathlib** (`lean.unknownIdentifier`). The correct
   name is `Module.affineSpan ℝ s` or `AffineSpan ℝ s`. Consistent with the orchestrator's warning
   not to use it: the relative hypothesis I finally wanted was just
   `∀ x ∈ C ∩ sphere 0 1, ∃ ρ > 0, ball x ρ x ⊆ K`, with no `∩ affineSpan` at all, which is both
   sufficient (the proof only ever consumes the `⊆ K` component) and not stronger.
2. With that removed, `Metric.ball x ρ x` in a binder type was reported to elaborate as `Prop`
   rather than `Set E`, in every one of the three places the hypothesis is stated. This is a
   `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` instance-availability question
   at binder-elaboration time, not a statement problem: the sibling `CraciunZSH.lean` uses the same
   variables and the same `Metric.ball`, so the fix is to state the hypothesis after a
   `let _ : PseudoMetricSpace E := inferInstance` or to move `E` out of `variable` into explicit
   binders with `[ProperSpace E]` / `[PseudoMetricSpace E]`.

A third site, line ~288 of that file, is a plain parse error
(`by by_cases h : ∃ y ∈ (C i : Set _), y ≠ 0` — `Set _` cannot be inferred there; it needs
`∃ y ∈ (C i : Set (EuclideanSpace ℝ (Fin n))), y ≠ 0`).

A-11 is a cleanup, not a blocker: `CRNT/Dynamics/FaceDirectionCone.lean` imports only
`ToricBarrierTrapping` and never reaches `CraciunZSH`, and `hm` in the ladder is a *hypothesis*
(a `Finset.inf'` intersection), never a geometric consequence needing a δ-tube.
