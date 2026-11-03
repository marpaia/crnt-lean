# Route: landing the `form-sr-deg2a` Hole-B modules on `holes`

**Agent:** `HoleBPort20` · **status: landed (21 machine-checked declarations, axiom-clean)**

Two modules ported from `origin/research/form-sr-deg2a` into the working tree:

| file | declarations |
| --- | --- |
| `CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean` | 12 |
| `CRNT/Multistationarity/TrueSREarRRGluable.lean` | 9 |

Source route docs (on that branch, **not** ported here): `research/routes/cycle-species-degree-two.md`,
`research/routes/rr-reaction-arc.md`.

---

## 1. Final import lines

`TrueSREarRRGluable.lean` — **unchanged from the branch**, and it is already cycle-free:

```lean
import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRCycleSplit
import CRNT.Multistationarity.TrueSRRotate
```

`TrueSRCycleSpeciesDegree.lean` — **unchanged from the branch**:

```lean
import CRNT.Multistationarity.TrueChemistrySRCriterion
```

### Why the `TrueChemistrySRCriterion` import was kept

The brief offered three repairs, in preference order (i) drop the import, (ii) re-prove a `private`
prerequisite, (iii) split the file. **None of the three is available here**, and the reason is
structural rather than incidental: the module's *statements*, not merely its proofs, are phrased in
terms of names that `TrueChemistrySRCriterion.lean` is the sole definer of.

`N.trueInternalClassFlux` occurs **27 times in `TrueSRCycleSpeciesDegree.lean`, and 27 of those are
in declaration statements** (all ten sign-carrying declarations quantify over it). Its sole
definition is `TrueChemistrySRCriterion.lean:4421`. Five more TSC-internal names appear in
statements:

| name | sole definition |
| --- | --- |
| `N.trueInternalClassFlux` | `TrueChemistrySRCriterion.lean:4421` |
| `N.nonflowOriginalChannels` (used by `:4421` itself) | `TrueChemistrySRCriterion.lean:1588` |
| `N.ActiveAggregateTrueReaction` | `TrueChemistrySRCriterion.lean:4678` |
| `AggregateActiveSpecies` | `TrueChemistrySRCriterion.lean:4683` |
| `N.TrueInternalAggregateVertex` | `TrueChemistrySRCriterion.lean:4685` |
| `N.TrueInternalAggregateCausalEdge` | `TrueChemistrySRCriterion.lean:4691` |

Consequences:

* **Route (i) is impossible, not merely inconvenient.** Dropping the import does not "supply a
  handful of missing prerequisites"; it requires *re-defining the flux itself*, which is the
  mathematical content of the theorem. The brief's premise — that `classFlux_eq_zero_of_nonNeighbour`
  is "the sole declaration that reaches outside `TrueSRCycle`" — is true at the level of *proofs* but
  false at the level of *statements*: every one of the ten declarations reaches outside via its type.
* **Route (ii) is impossible** for the same reason, and doubly so: the two ingredients of
  `nonAdjacent_cycleClassFlux_eq_zero` (`trueSREdge_endpoint_eq_of_same_class_and_species` at
  `:1806` and `exists_trueSREdge_of_nonzero_trueInternalClassFlux` at `:4781`) are indeed `private`,
  but re-proving them yields a lemma *stated in TSC-internal vocabulary*, which cannot then be used
  by declarations that are themselves stated in TSC-internal vocabulary without the import anyway.
* **Route (iii) does not help.** Splitting off "the `TrueChemistrySRCriterion`-free part" leaves an
  empty module: `finRotate_val` is the only declaration whose statement is TSC-free, and it is a
  two-line arithmetic fact with no Hole-B content.

The honest description is that **this module is by construction a consumer of
`TrueChemistrySRCriterion`, not a provider to it.** It cannot become importable *by* that file
without moving `trueInternalClassFlux` and its five siblings down into a separate
hole-free module — a large, invasive refactor of a 8641-line file, explicitly out of scope here.

**No cycle exists today.** `grep -rn "TrueSRCycleSpeciesDegree\|TrueSREarRRGluable" CRNT/ --include=*.lean | grep import`
returns nothing: nothing in the tree imports either module, so the single edge
`TrueSRCycleSpeciesDegree → TrueChemistrySRCriterion` is acyclic. The cycle is latent, arising only
if someone later adds `import CRNT.Multistationarity.TrueSRCycleSpeciesDegree` to
`TrueChemistrySRCriterion.lean`. That is the one thing the Hole-B closer must not do naively; see §4.

## 2. `sorryAx` does not leak — the import is axiom-safe

This is the substantive result, and it is the reason keeping the import is acceptable. `#print axioms`
on **all 21** declarations reports exactly `[propext, Classical.choice, Quot.sound]`. See §5 for the
probe.

The reason is positional, not lucky: the `sorry` is at `TrueChemistrySRCriterion.lean:8003`, inside
`stronglyConcordant_fullyOpen_of_trueSRCriterion`. Everything this module reaches into TSC for is
defined **before** line 8003 — `trueInternalClassFlux` (4421), the vertex/edge vocabulary
(4678–4691), and `nonAdjacent_cycleClassFlux_eq_zero` (6979). A `sorry` at 8003 can only contaminate
declarations that depend on it, i.e. those at 8003 and below. This module depends on none of those.

The `classFlux_eq_zero_of_nonNeighbour` route that Main identified is therefore **unnecessary**: it
reaches a lemma at line 6979 that is itself axiom-clean, so there is nothing to re-prove. Had it
been needed, the two `private` ingredients (`:1806`, `:4781`) would have needed re-proving; the
branch route doc's §3 already cites the public replacements `containsEdge_iff_cycleNeighbour`
(`TrueSRCPairThirdEdge.lean:183`) and `no_single_edge_chord_of_trueSRCriterion`
(`TrueSRChordExtraction.lean:42`).

## 3. Declarations now available

### `TrueSRCycleSpeciesDegree.lean` — namespace `CRNT.Network.TrueSRCycle`

`finRotate_val`, `hoppAt`, `hcausalAt`, `classFlux_eq_zero_of_nonNeighbour`, `negFlux_eq_leftEdge`,
`posFlux_eq_rightEdge`, `classFlux_trichotomy`, `no_offCycle_negFlux` (a `def`),
`negCausalStep_from_cycleSpecies`, `aggregateVertexOnCycle` (a `def`), `no_escape_from_cycleSpecies`,
`exists_offCycle_negFlux_class`.

(The branch route doc says "ten machine-checked declarations"; the file actually exports **twelve** —
the two `def`s `no_offCycle_negFlux` and `aggregateVertexOnCycle` are counted there only as prose.
All twelve are kept. Nothing was dropped or renamed.)

### `TrueSREarRRGluable.lean` — namespace `CRNT.Network.TrueSRCycle`

`reactionArcFwd` (a `noncomputable def`), `reactionArcFwd_startReaction`,
`reactionArcFwd_endReaction`, `reactionArcFwd_edge_cases`, `reactionArcFwd_edge_on_cycle`,
`reactionArcFwd_vertex_cases`, `reactionArcFwd_species`, `reactionArcFwd_reaction`,
`rrGluable_reactionArcFwd`.

Nothing was dropped, renamed, or re-proved.

## 4. The one fix that was needed

`no_escape_from_cycleSpecies` did not compile as branched — **two** errors, both in the same
tactic block (`CRNT/Multistationarity/TrueSRCycleSpeciesDegree.lean:265`, `:277`). The branch wrote:

```lean
have hlate1 : ¬ aggregateVertexOnCycle α σ C (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) := by
  rw [hv1]
  show C.HasReaction ρ1.1
  rw [hρ]
  exact hlate (⟨1, by omega⟩ : Fin (m + 1)) (by show (1 : ℕ) ≠ 0; omega)
```

`rw [hv1]` rewrites the goal to `¬ aggregateVertexOnCycle α σ C (Sum.inr ρ1)`, and `show C.HasReaction ρ1.1`
then fails to typecheck against the *negated* goal — the branch author elided the `Not`. The final
`exact` is wrong for a second, independent reason: `hlate` produces a statement about `Q.vertex …`,
whereas by that point the goal has been rewritten to a statement about `C.reaction b`. The two are
never in the same form, so no tactic closes it. Repaired by keeping both sides in the same form:

```lean
have hlate1 : ¬ aggregateVertexOnCycle α σ C
    (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) :=
  hlate (⟨1, by omega⟩ : Fin (m + 1)) (by show (1 : ℕ) ≠ 0; omega)
refine hlate1 (hv1 ▸ ?_)
show C.HasReaction ρ1.1
rw [hρ]
exact ⟨b, rfl⟩
```

This is the only edit to either file. Two warnings remain and are benign (a `simpa`-vs-`simp`
hint at `:68`, and `hcausal` unreferenced at `:132` in `classFlux_trichotomy`, where it is genuinely
redundant given the two sharper lemmas — it is retained because the branch statement exposes it and
downstream callers pass it).

## 5. Axiom footprint

Probe at `/tmp/holeB_port20_ax.lean` (outside the repo), run with `lake env lean`. All 21 public
declarations, verbatim:

```
'CRNT.Network.TrueSRCycle.finRotate_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.hoppAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.hcausalAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.classFlux_eq_zero_of_nonNeighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.negFlux_eq_leftEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.posFlux_eq_rightEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.classFlux_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.no_offCycle_negFlux' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.negCausalStep_from_cycleSpecies' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.aggregateVertexOnCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.no_escape_from_cycleSpecies' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.exists_offCycle_negFlux_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_startReaction' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_endReaction' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_edge_on_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_vertex_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_species' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.reactionArcFwd_reaction' depends on axioms: [propext, Classical.choice, Quot.sound]
'CRNT.Network.TrueSRCycle.rrGluable_reactionArcFwd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere.

## 6. Warnings for the Hole-B closer

1. **Do not import `TrueSRCycleSpeciesDegree` into `TrueChemistrySRCriterion`** — that is the latent
   cycle of §1. The trichotomy is the right *diagnostic* (`no_offCycle_negFlux` is unprovable in
   scope, DEAD-ENDS B-3), and `exists_offCycle_negFlux_class` states the ear's off-cycle end, but
   the discharge of the residue needs a formulation that does not depend on the hole-owning file.
   The only clean fix is to extract `trueInternalClassFlux` and its five siblings (TSC lines 1588,
   4421, 4678–4691) into a new hole-free module; that is a separate, invasive change and was
   deliberately not attempted here.
2. **`TrueSREarRRGluable` has no such problem.** Its three imports are all hole-free, so
   `rrGluable_reactionArcFwd` and `rrGluedCycle` *can* be consumed by `TrueChemistrySRCriterion`
   directly. This is the half of the port that is actually usable at the residue today.
3. **`no_escape_from_cycleSpecies` is conditional** and discharges nothing on its own: it needs
   `no_offCycle_negFlux`, which DEAD-ENDS B-3 shows is false (refuted by `hattachment`). Its value
   is that it converts the residue into the single named proposition `no_offCycle_negFlux`, and
   `exists_offCycle_negFlux_class` turns the failure of that proposition into concrete off-cycle
   data. Per the branch route doc §4, pairing that with `hattachment` gives the two off-cycle
   endpoints `TrueSREarRRGluable`'s `rrGluable_reactionArcFwd` consumes.