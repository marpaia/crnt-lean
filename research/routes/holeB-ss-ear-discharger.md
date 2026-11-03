# The missing discharger at `TrueChemistrySRCriterion.lean:8607`: a species-to-species ear

**Status: target statement established; the S→S builder obstacle is CLEARED; the true blocker is
evenness of the glued cycle, which is a sum-versus-term gap in the σ-sign data. The proof is not
written.** All `file:line` citations were read in the tree at commit `5f4160a` (branch
`research/holeb-earcase-port`, PR #36).

## 1. Why this is the exact remaining gap

The `sorry` sits at the end of a `by_cases hvr` inside the `v`-is-a-species branch of the `hspan`
proof, where an `exfalso` has made the goal `False`. Read the three ear dischargers the file
already contains and compare their endpoint types:

| discharger | line | `hstart` endpoint | `hlast` endpoint | shape |
|---|---|---|---|---|
| `no_clean_directed_species_reaction_ear_of_trueSRCriterion` | 5299 | `Sum.inl s` | `Sum.inr ρ` | S → R |
| `no_species_reaction_ear_of_trueSRCriterion` | 5688 | `Sum.inl s` | `Sum.inr ρ` | S → R |
| `no_reaction_species_ear_of_trueSRCriterion` | 5735 | `Sum.inr ρ` | `Sum.inl s` | R → S |

**All three require an on-cycle *reaction* at one end.** The in-scope data at `:8607` has an
on-cycle **species** at *both* ends. No discharger in the tree has that shape. That is the
"A.6 Case-2 source-block datum" the in-file comment at `:8600-8607` names, and it is why
`research/DEAD-ENDS.md` B-6 and B-10 record that the ear route is "a different proof": the Case-2
dischargers of `CRNT/Multistationarity/TrueSREarCase2.lean` are stated for `TrueSRPathRR` /
`TrueSRSSPath` **on a stage cycle built inside a source block**, which is not what this proof
constructs.

## 2. The data actually in scope

From `Q0 := CRNT.exists_minimal_relPath … ` and `exists_minimal_escape` (`:7585`):

- `Q0 : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m`, `0 < m`,
  `hQ0inj : Function.Injective Q0.vertex`;
- `hv0 : Q0.vertex ⟨0,_⟩ = Sum.inl s0` with `hs0C : C.HasSpecies s0.1`;
- `hqm : Q0.vertex ⟨m,_⟩ = Sum.inr q`, `hqT : Sum.inr q ∈ T`;
- `hQ0late : ∀ i, i.1 ≠ 0 → ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (Q0.vertex i))`;
- `W : (CRNT.relationGraphOn … T).Walk … (Sum.inr q) (Sum.inr v)` with `hvOn : C.HasVertex … v`
  where `v` is `Sum.inl`, i.e. an on-cycle species; `W.IsPath`; `hWoff : ∀ i, i < W.length,
  ¬ C.HasVertex …`; `hWpos : 0 < W.length`;
- `hm1s : ¬ (m = 1 ∧ s0 = s)`;
- `¬ hnc`, `hopp`, `hcausal`, `hsep`, `hCeven`, `hSR`, `hscc`, `hsource`.

### The concatenation is the ear, and its parity is forced

The causal-edge case table (`:4691-4699`) is

```
| Sum.inl s, Sum.inr ρ => (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1 < 0
| Sum.inr ρ, Sum.inl s => 0 < (N.trueInternalClassFlux α ρ.1 s.1) * σ s.1
| Sum.inl _, Sum.inl _ => False
| Sum.inr _, Sum.inr _ => False
```

so consecutive vertices alternate species/reaction, and:

- `Q0.vertex 0 = Sum.inl s0` (species) and `Q0.vertex m = Sum.inr q` (reaction) force **`m` odd**;
- `W` starts at the reaction `q` and ends at the species `v`, so **`W.length` is odd**;
- hence `Q0 ++ W` has **even** total length and is species at both ends: the shape of
  `N.TrueSRSSPath (2 * j + 2)`, **not** `TrueSRPathRR`.

Consequently the applicable glue is `SSGluable` / `ssGlueCycle`
(`TrueSRSpeciesPath.lean:392`, `:548`), with evenness from `ssGlueCycle_numCPairs`
(`TrueSRSSGlueCPairs.lean:107`) and `ssGlueCycle_even_of_partner` (in the Case-2 port) — **not**
`rrGluedCycle`. Step 0 of `Q0` forces `Q0.vertex 1 = Sum.inr ρ₁` with
`N.trueInternalClassFlux α ρ₁.1 s0.1 * σ s0.1 < 0` and `ρ₁` off-cycle, which is exactly the
`no_offCycle_negFlux` refutation recorded by PR #20 and is why `no_escape_from_cycleSpecies` cannot
be used.

## 3. Target statement

To be stated inside `TrueChemistrySRCriterion.lean` (the three ingredients
`trueSREdge_endpoint_eq_of_same_class_and_species` `:1806`,
`exists_trueSREdge_of_nonzero_trueInternalClassFlux` `:4781` and
`nonAdjacent_cycleClassFlux_eq_zero` `:6979` are all `private` to that file, so nothing usable
lives outside it):

```lean
private theorem no_species_species_ear_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
    (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
    (hinj : Function.Injective P.vertex) (hk : 4 ≤ k)
    {s₀ s₁ : AggregateActiveSpecies σ}
    (hstart : P.vertex ⟨0, by omega⟩ = Sum.inl s₀)
    (hlast  : P.vertex ⟨k, by omega⟩ = Sum.inl s₁)
    (hs₀C : C.HasSpecies s₀.1) (hs₁C : C.HasSpecies s₁.1)
    (hne : s₀ ≠ s₁)
    (hinterior : ∀ i : Fin (k + 1), i.1 ≠ 0 → i.1 ≠ k →
      ¬ C.HasVertex (N.aggregateVertexToTrueSRVertex (P.vertex i))) : False
```

with `k` even forced by the case table, so `hk : 4 ≤ k` (rather than `3 ≤ k` as in the S → R
versions, which have odd length).

## 4. What the proof must do

Convert `P` to a `TrueSRSSPath` (both ends species ⇒ even length), obtain the two cycle arcs between
`s₀` and `s₁`, and exhibit one of the six arrangements of Fig. 8 as in the header table of
`TrueSREarCase2.lean`, then feed `lemmaA6_case2_interleaved` / `lemmaA6_case2_twoComponents`.
Three obstacles, in order of difficulty:

1. ~~**`P` is a `RelPath`, not a `TrueSRSSPath`.**~~ **CLEARED.** The S → S builder exists:
   `relPathToTrueSRSSPath` at **`TrueChemistrySRCriterion.lean:5475`**,

   ```lean
   private noncomputable def relPathToTrueSRSSPath (N : Network S)
       {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
       (T : Finset (N.TrueInternalAggregateVertex α σ)) {k : ℕ}
       (P : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T k)
       (hinj : Function.Injective P.vertex) (hk : 0 < k)
       {s s' : AggregateActiveSpecies σ}
       (h0 : P.vertex ⟨0, by omega⟩ = Sum.inl s)
       (hlast : P.vertex ⟨k, by omega⟩ = Sum.inl s') : N.TrueSRSSPath k
   ```

   It is `private`, hence in-file, and takes **species at both ends** — exactly the composite's
   shape. Every argument is available at the residue: `P` = the concatenation of `Q0` with the
   `RelPath` form of `W`; `hinj` from `hQ0inj` together with `W.IsPath`; `hk` from the parity
   argument above (composite length even and `> 0`); `h0 = hv0`; `hlast` from `hvOn` with `v` the
   species. Sibling builders `relPathToTrueSRPath` (`:5217`, S → R) and `relPathToTrueSRPathRev`
   (`:5584`, R → S) sit at the same level.
   **So the route does not stop at step 1.** Two obstacles remain.
2. **`harr`, the arrangement datum.** `CE/QE/PE/VE` appear nowhere above `:8607`
   (`DEAD-ENDS.md` B-10, confirmed by grep: zero hits for `harr`, `hdecX`, `hdecY` in the file).
   `research/routes/pr10-verification.md` §5 records that `harr` has no producer and that the
   reason is not merely a missing glue instance. The arrangement is the
   cut-the-cycle-at-four-attachments computation.
3. **Evenness of the glued cycle — THE REAL BLOCKER.** `hC : C.Even` is given for `C` only. The
   glued cycle's evenness comes from `TrueSRCycle.even_of_signDirected` (Case-2 port `:147`),
   which needs

   ```lean
   def TrueSRCycle.SignDirected {n : ℕ} (C : N.TrueSRCycle n) (σ : S → ℝ) : Prop :=
     (∀ i, σ (C.species i) ≠ 0) ∧
       (∀ i, C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0)
   ```

   The ear's interior species are **off-cycle**, and the residue's hypotheses pin σ there in no way:

   - `hcausal`/`hopp` pin the class flux at *cycle* classes only (`DEAD-ENDS.md` B-5: "already
     sharp", no slack).
   - `hlocal` (`:6077-6080`) is a **sum** positivity,
     `0 < ∑_ρ (N.trueInternalClassFlux α ρ s.1) * σ s.1` over
     `N.trueInternalAggregateSourceClasses α σ T`. It bounds the *total* at each species and forces
     nothing about any individual term, hence nothing about an individual off-cycle σ-sign.
   - every other `σ s ≠ 0` in the file (`:1272`, `:1408`, `:1957`) occurs as a **precondition**
     `hs : σ s ≠ 0`, never as something derivable.

   So `SignDirected σ` on any cycle containing ear species is **not provable from the residue's
   hypotheses**. This is a sum-versus-term gap, the same species of obstruction as Hole A's
   A-64/A-68 — an analytic estimate nobody has made, not a missing lemma.

**Prioritisation.** Obstacles 1 and 2 are finite combinatorics over `C` and the ear's shape, and both
are writable now. But even if both succeed, `lemmaA6_case2_*` cannot be applied without evenness. **The
true target is therefore not `harr` but a new estimate relating the σ-sign pattern to the flux-sign
pattern on off-cycle species** — of the shape "the aggregate causal degree of an off-cycle species is
bounded, or its class flux is σ-sign-definite". Nothing in the tree, the 21 landed declarations, or
the research ledger supplies it. `harr` is the tractable second-order problem.

Corollary: `no_offCycle_negFlux` (landed, PR #20) is **refuted** at the residue, so any strategy
assuming it is dead; and a strategy needing σ-sign-definiteness for an off-cycle class asks for
something the hypotheses equally do not give.

## 5. Dead ends already excluded (do not re-walk)

- `no_spanning_path_of_trueSRCriterion` cannot be applied to `Q0`: `hqm` puts `q` at index `m` and
  `hQ0late` + `hmpos` force every index `≠ 0` off-cycle, so `Q0` is half-spanning (B-7).
- `hnd` in the `hspan` witness is unsatisfiable: every SR edge joining a cycle species to a cycle
  reaction is itself a cycle edge (B-1). Do not try to rebuild `hspan` in this branch.
- `hopp` does **not** force the first hop to be length 1 (B-8); the in-file comment at `:8600-8607`
  is wrong, and PR #20's `classFlux_trichotomy` machine-checks the correction.
- `hrest` is not in scope at `:8607` and its natural instance is refuted by `hattachment` (B-3).
- `hSR.2` is vacuous on a degree-two cycle (B-25), so degree-two isolation cannot be discharged
  through it.

## 6. Cited sources

- G. Shinar and E. D. Feinberg, *Sign-causality and concavity in chemical reaction networks*,
  arXiv:1203.6560, Appendix A.3, Lemma A.6 (Case 1 = S → R ear, Case 2 = S → S ear) and
  Appendix A.2 (parity transfer). Case 1 is formalised in
  `CRNT/Multistationarity/TrueSREarCase1.lean`; Case 2's discharge lemmas are in
  `CRNT/Multistationarity/TrueSREarCase2.lean`.
- The six arrangements and the `CE/QE/PE/VE` notation: header table of
  `CRNT/Multistationarity/TrueSREarCase2.lean`.

## 5b. SUPERSEDED ordering — read `holeB-literature.md` first

This note's §4 prioritised `harr` as obstacle 2 and named the σ-sign estimate as the true
blocker (§4b). **Both were superseded** by the primary-source work recorded in
`research/routes/holeB-literature.md`:

| this note said | the source says | status |
|---|---|---|
| blocker is a sum-versus-term σ gap (§4b) | Prop. 5.11 (`:869`) gives evenness of **every cycle in the source** under `hSR.2`, with **no σ-sign hypothesis at all** | §4b **wrong**; the paper never asks for a σ-sign estimate |
| build `no_species_species_ear_of_trueSRCriterion` | the target is a port of **Prop. 5.11** over the block decomposition | §3 target **mis-aimed** |
| `harr` is a real obstacle | `harr` is real but **second-order**: it only matters once evenness is in hand, and evenness is free under Prop. 5.11 | §4 ordering **wrong** |
| "Lemma A.6" | no such lemma; the content is **Prop. 5.8** (App. A.3) + **App. A.2** | citation wrong throughout |

What survives from this note and is still correct:

1. **The residue's ear is species→species.** The three existing dischargers (`:5299`, `:5688`,
   `:5735`) all need an on-cycle reaction at one end; the in-scope data has an on-cycle species at
   both ends (`Q0 : s0 ⇝ q`, then `W : q ⇝ v`). Verified, and unchanged by the literature work.
2. **The parity forcing.** `m` odd, `W.length` odd, composite even and species-terminated, so the
   applicable glue is `SSGluable`/`ssGlueCycle` rather than `rrGluedCycle`. Verified from the case
   table at `:4691-4699`.
3. **`relPathToTrueSRSSPath` exists** at `:5475` and takes species at both ends — obstacle 1
   cleared. Verified.
4. **The dead-end list in §5.** All still valid; B-8 in particular is now machine-checked by
   `classFlux_trichotomy` (landed in PR #36), which confirms the in-file comment at `:8600-8607`
   is wrong.
5. **`v ≠ s`** is already proved in the file: the `hsNotIn` argument at `:8306-8316` shows
   `⟨Sum.inl s, hsT⟩ ∉ W.support`, and it is branch-independent. **`v = s0` is neither forced nor
   excluded** — nothing in `:8572-8609` relates them, so a `by_cases` on it is required.

Corrected dependency order for whoever attempts this next:

1. `Walk → RelPath` lift + a whole-path `append` (`RelPath.concat` extends by ONE vertex only —
   verified at `CRNT/Graph/RelPath.lean:189-190`, so `Q0 ++ W` needs a new operation). In progress
   in `CRNT/Graph/RelPathWalk.lean`.
2. `relPathToTrueSRSSPath` on the composite; `by_cases` on `v = s0`.
3. **Port the weakest useful form of Prop. 5.11** — see `holeB-literature.md` §7-8 for why the block
   structure may be avoidable, and §11 for the full cost if it is not.
4. Only then `harr` / the six arrangements of `SixCases.eps` (recoverable — the tarball ships it).

## 6. The S→S `hSR.2` route is REFUTED in-tree (machine-checked, commit `d82ca85`)

This is the most consequential negative result so far, and it is *proved*, not argued.

Glue the residue's ear `P : TrueSRSSPath (m + 1)` to `Crot.speciesArc` and `Crot.speciesArcBwd`
via `SSGluable.ss_gluable_arcs` (`TrueSRSpeciesPath.lean:902`). That yields three cycles —
`C`, `P ∪ Q₁`, `P ∪ Q₂`. Every **pairwise** common subgraph is then a single simple path with
**species at both ends**:

| pair | common path | endpoints |
|---|---|---|
| `C`, `P ∪ Q₁` | `Q₁` | species, species |
| `C`, `P ∪ Q₂` | `Q₂` | species, species |
| `P ∪ Q₁`, `P ∪ Q₂` | `P` | species, species |

And `CRNT.Network.no_sToRIntersection_of_speciesSpecies_common`
(`CRNT/Multistationarity/TrueSRSSGlueCPairs.lean:233`) proves that exactly this configuration admits
no `SToRIntersection`: its hypotheses are a covered, vertex-injective connected common subgraph with
`hstart : ∃ s, vertex 0 = Sum.inl s` and `hend : ∃ s, vertex (Fin.last K) = Sum.inl s`.

Its docstring states the consequence in plain words:

> "…so `SToRIntersection` is never available. That is why a species-to-species chord is invisible to
> `TrueSRStrongCriterion`."

**Consequence.** `hSR.2` is not merely hard to apply at the residue — it is *provably inapplicable to
any species-to-species ear*, whatever its length, parity, signs, or gluability. This confirms
DEAD-ENDS B-6 and B-10 from a direction the ledger did not record, and it kills §4b's suggestion that
`harr` plus the Case-2 arrangement machinery could discharge via `hSR.2`. **The six arrangements of
`SixCases.eps` exist for a stage cycle inside a source block whose cycles are *directed*; the residue's
ear produces only species-to-species common subgraphs, which is the configuration the packaged
dischargers explicitly cannot see.**

**What survives.** The ear is still the right object — it is now landed as
`aggregateEar_TrueSRSSPath` (`TrueChemistrySRCriterion.lean:8041`) with its off-cycle interior proved
by `aggregateEar_interior` (`:8089`). What is refuted is only the route from that ear to `False`
via `hSR.2`. The remaining options are:

1. `hSR.1` — show the ear-containing cycle is even and **not** an s-cycle. `SCycle` is
   `∏ leftEdge coeffs = ∏ rightEdge coeffs` (`TrueChemistrySRCriterion.lean:169`), so a strict
   gain on the ear's edges would break the product identity. This needs no `SToRIntersection`.
2. The block-level evenness of Prop. 5.10/5.11 (`holeB-literature.md` §7-8), which then feeds
   `hSR.2` in the *other* direction — the paper extracts an S-to-R intersection between two cycles
   that are each **directed** in the stage-block sense, which the residue's cycle is not.

Option 1 has not been attempted and does not require the block decomposition. It is the cheapest
untried route.

## 7. The `hSR.1` route is blocked too — a second, structural obstruction

§6 killed `hSR.2`. The obvious alternative is `hSR.1 : ∀ C, C.Even → C.SCycle`, discharged by a
strict multiplicative gain on the ear's edge coefficients. **That is blocked as well**, for a
different reason, and the reason is a mismatch of quantities rather than a missing lemma.

`TrueSRCycle.SCycle` (`TrueChemistrySRCriterion.lean:169`) is

```lean
def TrueSRCycle.SCycle (C : N.TrueSRCycle n) : Prop :=
  (∏ i : Fin n, (C.leftEdge i).coeff) = (∏ i : Fin n, (C.rightEdge i).coeff)
```

and `TrueSREdge.coeff` (`TrueChemistrySRGraph.lean:120-127`) is

```lean
def TrueSREdge.coeff (e : N.TrueSREdge) : ℕ := e.endpoint e.species
theorem TrueSREdge.coeff_pos (e : N.TrueSREdge) : 0 < e.coeff := Nat.pos_of_ne_zero e.occurs
```

with `occurs : endpoint species ≠ 0` a **field of the structure** (`:119`). So every coefficient is
a **positive natural**, unconditionally. Two consequences:

1. **No factor can vanish or be negative.** The product identity cannot break via a degenerate or
   sign-changing factor; it requires a genuinely strict comparison between two products.
2. **No in-scope hypothesis supplies that comparison.** Every strict inequality available at the
   residue — `hopp`, `hcausal`, `hattachment`, the step-0 negativity on `ρ₁` — is an inequality on
   `N.trueInternalClassFlux α ρ s * σ s`, i.e. on **monomial ratios of concentrations**. `coeff` is an
   **integer stoichiometric label**, `endpoint e.species`. These are different quantities.
   `netCoeff` (`:185`) is `|target s − source s|`, and `edge_coeff_eq_abs_reactionVector` identifies
   the two labels under `hsep` — but that is an identification of *which* integer, not a bound on
   its *size*.

Verified by grep, no hits:

```
grep -rn "trueInternalClassFlux.*coeff|coeff.*trueInternalClassFlux|netCoeff.*[Ff]lux|[Ff]lux.*netCoeff" \
     CRNT/ --include=*.lean
→ (no output)
```

**So there is no bridge in the tree between the flux inequalities the residue has and the integer
labels `SCycle` constrains.**

### Net status of the residue

Both halves of `hSR` are now closed off at the residue, for *different* structural reasons:

| clause | obstruction | nature |
|---|---|---|
| `hSR.2` (no S-to-R intersection) | `no_sToRIntersection_of_speciesSpecies_common` (`TrueSRSSGlueCPairs.lean:233`) — proved: the ear's common subgraphs are species-to-species | proved refutation |
| `hSR.1` (every even cycle is an s-cycle) | the available inequalities are on `flux·σ`; `SCycle` constrains positive-integer labels; no bridge exists | proved absence |

This is the sharpest available characterisation of what remains, and it is consistent with the
Shinar–Feinberg reading in `holeB-literature.md` §2: the paper proves Prop. 5.8/5.10 using
**inequalities on the source's stoichiometric coefficients** (`eq:SourceInequalitySystem`, paper
§5.4), not on monomial ratios. The in-tree residue has flux inequalities but no coefficient
inequalities — which is precisely the missing input, and it is an *input*, not a tactic.

**Therefore the residue needs a source-level coefficient inequality system**, the paper's §5.4
object. That is a substantial new input, related to but distinct from the block decomposition of
§11. It is not something the six arrangements or the ear machinery can supply.

## 8. RETRACTION of §7 — the flux↔SCycle bridge EXISTS (commit `fbb1361`)

§7 claimed, on the strength of a name-adjacency grep, that no theorem relates `trueInternalClassFlux`
to `coeff`/`netCoeff`, and that `hSR.1` was therefore structurally blocked by a quantity mismatch.
**That was wrong.** The grep looked for names next to each other, not for mathematics.

`sCycleNet_eq_fluxMagnitude_product` (`TrueChemistrySRCriterion.lean:8132`, axiom-clean):

```lean
private theorem sCycleNet_eq_fluxMagnitude_product (N : Network S)
    {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} {n : ℕ} [NeZero n]
    (C : N.TrueSRCycle n) (β : Fin n → ℝ)
    (hrep : ∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative)
    (hbeta : ∀ i t, N.trueInternalClassFlux α (C.reaction i) t =
      β i * N.reactionVector (C.rightEdge i).representative t)
    (hβne : ∀ i, β i ≠ 0) :
    C.SCycleNet ↔
      (∏ i : Fin n, |N.trueInternalClassFlux α (C.reaction i) (C.species i)|)
        = ∏ i : Fin n,
          |N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i))|
```

Each edge's `netCoeff` is `|flux| · (|β i|)⁻¹`, and since **both products run over the same index
set**, the `∏ |β i|⁻¹` factor appears on both sides and cancels. So `SCycle` *does* constrain products
of the magnitudes of exactly the fluxes that `hopp`/`hcausal`/`hattachment` bound strictly.

**§7's "quantity mismatch" is retracted.** The remaining obstruction in the `hSR.1` route is narrower:
a magnitude *comparison* between two fluxes at two cycle species — not a bridge.

### The single remaining obligation, stated

Also new in `fbb1361`: `aggregateEar_ssGluable_arcs` (:8196) proves **both** ear-containing true-SR
cycles genuinely exist (edge-disjointness is free via `TrueSRSSPath.ss_edges_off_cycle`), so existence
is no longer open. `CRNT/Multistationarity/TrueSRSSArcEven.lean` (297 lines, 18 declarations) proves
`ssNumCPairsH_speciesArcs_add`: the cycle's c-pairs **partition** across its two species-arcs —
the statement DEAD-ENDS B-10 listed as missing.

Since `ssGlueCycle_numCPairs` (`TrueSRSSGlueCPairs.lean:107`) has **no seam term**, the obligation

```
(TrueSRSSPath.ssGlueCycle P (Crot.speciesArc k) h₁).Even
```

reduces, with the partition identity, to exactly one proposition:

```
P.ssNumCPairs % 2 = ssNumCPairs (Crot.speciesArcBwd k) % 2
```

— the **parity of the ear's own c-pair count**. That is the last open datum, confirmed absent by
exhaustive grep:

- no theorem computes the parity of `ssNumCPairs` for a species-to-species path, nor relates it to
  the path's length; its only two consumers (`ssGlueCycle_numCPairs`,
  `ssGlueCycle_even_iff_even`) treat it as an opaque unknown that cancels mod 2;
- `TrueSRSSPath` carries **no σ data at all**, so no sign characterisation of `ssCPairAt` exists for
  paths;
- `TrueSRPathCPairs.lean` is 63 lines of pure edge-index combinatorics with no σ;
- the only edge-level c-pair↔sign lemma in the tree is
  `trueInternalCausalEdges_cPair_iff_signChange` (:2459), about the two canonically constructed
  causal edges of the witness flow, **not** arbitrary path edges.

What makes `C.Even` computable is precisely the **cycle-level** analogue
`C.isCPair i ↔ σ (C.species i) * σ (C.species (finRotate n i)) < 0`, proved at `:6736`. **That statement
has no species-path counterpart.** It is the missing input for the residue, and it is an input rather
than a tactic.

### Corrected standing of the two obstructions

| clause | status |
|---|---|
| `hSR.2` | **proved refutation** — `no_sToRIntersection_of_speciesSpecies_common` (§6). Unchanged and final. |
| `hSR.1` | bridge **found** (`sCycleNet_eq_fluxMagnitude_product`); obstacle narrowed to the ear's c-pair parity |

## 9. FINAL characterization of the residue (commit `a6b78db`)

Everything below is machine-checked. This supersedes §§6-8 as the standing account.

### The reduction is proved, not asserted

`ssGlueCycle_even_iff_parity_of_cycleEven` (`TrueChemistrySRCriterion.lean:8273`):

```lean
(ssGlueCycle P (C.speciesArc (k+1) hk _) h₁).Even
  ↔ ssNumCPairs P % 2 = ssNumCPairsH (C.speciesArcBwd (k+1) hk _) % 2
```

from `ssGlueCycle_numCPairs` (no seam term), `ssNumCPairs_speciesArc_succ`,
`ssNumCPairsH_speciesArcBwd_eq_cPairsAbove` (:302), `cPairsBelow_card_add`, and `C.Even`.

### The path-level sign lemma EXISTS

`ear_cPair_iff_signChange` (:8380) — the species-path analogue of the cycle-level `:6736`:

```lean
ssCPairAt P r ↔ σ (P.speciesAt ⟨2*r⟩) * σ (P.speciesAt ⟨2*r+2⟩) < 0
```

Its edge-level core is `cPair_of_twoClassEdges_iff_signChange` (:8323). **This contradicts §7's
claim that "TrueSRSSPath carries no σ data at all"** — the σ *statement* now exists; what is missing
is the two hypotheses it needs.

### Two blockers, independent of each other

**Blocker 1 — the two missing hypotheses are about representative channels, not σ.**

| hypothesis | content | why unobtainable |
|---|---|---|
| `hcommon` | a common non-flow representative at each ear reaction vertex | `relPathToTrueSRSSPath` picks every edge **independently** by `Classical.choose` (`relationGraphOn` adjacency → `aggregateSourceAdj_has_trueSREdge` → `exists_trueSREdge_of_nonzero_trueInternalClassFlux`), so the two edges at one class may carry **different** representative channels; `TrueSRSSPath` has **no field** recording representatives. For a cycle this is free — `leftEdge i` and `rightEdge i` are both `trueSREdgeOfReactionVectorNe (rep i)`. For an ear it is not. |
| `hβ` | `flux(·,t) = β * reactionVector R t` at that class | `trueInternalClassFlux` is a **sum** over the class's channels, so `hβ` says the sum has a single contributing pattern. |

**The mismatch is structural, not a missing lemma.** A c-pair compares *endpoint complexes*, which is
a **per-channel** condition (the two species sit on the same side of the representative's
source/target); `flux·σ < 0` is a **sum** condition on the class flux. With two or more contributing
channels these are independent, so the equivalence is **genuinely false**. Closing it needs either
(a) that each ear reaction class has exactly one contributing non-flow channel, or (b) a signed-flux
decomposition per class rather than the raw class flux. Neither follows from
`hopp`/`hcausal`/`hlocal`/`¬hnc` — `hlocal` is a total `0 < ∑_ρ flux·σ` and pins no single term.

**Blocker 2 — a proved parity would not close the branch anyway.**
`ssGlueCycle_even_iff_even` (`TrueSRSSGlueCPairs.lean:200-205`) demands

```lean
(hQ : (ssNumCPairs Q₁ + ssNumCPairs Q₂) % 2 = 0)
```

which constrains only the two **arcs** and never mentions `P`. Supplying
`hQ := (ssNumCPairs P + ssNumCPairs arcB) % 2 = 0` is rejected by the elaborator ("expected
`(arcF.ssNumCPairs + arcB.ssNumCPairs) % 2 = 0`"). **So that lemma can make the two ear-containing
cycles agree in parity, never make either even.**

### Also dead, with reason

The route-A length/involution formula is dead: `ssCPairAt P r` compares the `endpoint` complexes of
two arbitrary edges, and `TrueSREdge.endpoint : Complex S` is a free field constrained only by
`endpoint_is_source_or_target` and `occurs`. No formula `ssNumCPairs P % 2 = f (P.length)` can hold.

### The one piece of pure bookkeeping left

`signChanges_mod_two` and its corollary `ssNumCPairs P % 2 = (if σ(start)·σ(end) < 0 then 1 else 0)`
were **not** landed: the XOR algebra was discharged, but the `Finset` plumbing (`card_bij` over
`Fin (K+1)`) failed repeatedly. Given Blocker 1 this would not close the residue by itself, but it is
the last purely combinatorial step of the sign route and is worth landing for reuse.

### Bottom line

The residue is not a missing tactic. It is blocked by **(i)** a per-channel vs per-sum information
loss that no in-scope hypothesis repairs, and **(ii)** a parity-transfer lemma that provably cannot
force evenness. Both are machine-checked. This is consistent with the paper's own route, which
supplies evenness *ambiently* through Prop. 5.11 at the level of blocks — a structure
`CRNT/Graph/SourceBlocks.lean` defers by name (§11).
