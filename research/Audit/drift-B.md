# Statement-drift audit — chain B: `CRNT/Multistationarity/TrueChemistrySRCriterion.lean`

28 theorems checked against their docstrings, plus a full trace of every predicate the hypotheses
quantify over. The module's single `sorry` (line 8607) is the known hole and is **not** reported as
drift.

Read for the vacuity trace: `TrueChemistrySRGraph.lean` (`TrueSRCycle` :137, `Even` :164, `SCycle`
:169, `netCoeff`/`SCycleNet` :185/:190, `SToRIntersection` :236, `TrueSRStrongCriterion` :271),
`StrongConcordance.lean:26-67`, `Augmentation.lean:39-49`, `TrueSRChordExtraction.lean:42`/:124,
`TrueSRReactionInteriorPath.lean:110`, `TrueSRCycleChord.lean:255`, `TrueSRSingleSharedEdge.lean:72`,
`GainPotential.lean:331`/:424, `Examples/TrueSRCounterexample.lean:74`,
`Examples/TrueSRNetCoeffCounterexample.lean:87`/:170`/:637`/:666`/:704`/:707`/:712`.

## Predicate non-vacuity trace — the most important check

| predicate | definition | inhabited / non-vacuous? |
|---|---|---|
| `TrueSRCycle n` | `TrueChemistrySRGraph.lean:137-151`: `nontrivial : 2 ≤ n`, `species`/`reaction : Fin n → _`, `species_injective`, `reaction_injective` | **Inhabited** — `netN.TrueSRCycle 2` (`TrueSRNetCoeffCounterexample.lean:666`). No `Decidable`/`Nonempty` filler: the structure has no such field. |
| `TrueSRCycle.Even` | `_root_.Even C.numCPairs` | **Satisfiable** — `netN_has_even_cycle` (`:704`). |
| `TrueSRCycle.SCycle` | `∏ leftEdge.coeff = ∏ rightEdge.coeff` | **Satisfiable** — `netN_cycle_sCycle` (`:707`). |
| `TrueSRCycle.SCycleNet` | same with `netCoeff = \|target − source\|` | **Satisfiable under `hsep`** via the proved bridge `sCycleNet_iff_sCycle_of_separated` (:2092), used at :8026. `netN_cycle_not_sCycleNet` (`:712`) shows they genuinely differ *without* separation. |
| `SToRIntersection` | certificate structure, :236-268 | **Non-vacuous** — `componentCount_pos` forces ≥1 component; `components_separated` applies only *between distinct* components, so a single shared path is a legitimate inhabitant. |
| `TrueSRStrongCriterion` | :271-274 | **Non-vacuous** — proved of `flowN` (`TrueSRCounterexample.lean:74`) and non-trivially of `netN` (`TrueSRNetCoeffCounterexample.lean:637`). |
| `ReactantProductSeparated` | `StrongConcordance.lean:26-28` | **Inhabited**, and provably **necessary** (`netN_not_reactantProductSeparated`, `:87`). |
| `ZeroComplexReactionsAreFlows` | `TrueChemistrySRCriterion.lean:366-369` | **Inhabited**, but a **genuine extra restriction** — see finding #1. |
| `fullyOpen` | `Augmentation.lean:49`, `R := N.R ⊕ S ⊕ S` | Well-defined; `StronglyConcordant` of it is **refutable** (`netN_fullyOpen_not_stronglyConcordant`, `:170`), so the goal is not vacuous. |

**Conclusion: no hypothesis in the file is a vacuity device.** No `True`-style hypothesis, no unused
`Decidable`/`Nonempty` instance doing load-bearing work, no `Prop` the surrounding definitions make
trivially true. That class of drift — the most serious one — is **absent here**.

## The Shinar–Feinberg content in the hypotheses immediately upstream of the hole: present

All three documented items are carried by exact Lean binder name:

1. **Reactant/product separation** → `hsep : N.ReactantProductSeparated`.
2. **Every e-cycle is an s-cycle** → `hSR.1 : ∀ {n} (C : N.TrueSRCycle n), C.Even → C.SCycle`,
   instantiated at :8024 as `hSCycle : C.SCycle := hSR.1 C hCeven`.
3. **No two e-cycles share an S-to-R intersection** → `hSR.2 : ∀ {m n} (C) (D), C.Even → D.Even →
   ¬ Nonempty (C.SToRIntersection D)`, consumed transitively by every chord obstruction
   (`no_nonneighbor_chord` :7306 via `no_close_arc_chord_of_trueSRCriterion` :7473;
   `nonAdjacent_cycleClassFlux_eq_zero` :6979 via `no_single_edge_chord_of_trueSRCriterion` :6998).

The theorem `TrueSRCycle.sCycleNet_iff_sCycle_of_separated` (:2092) is **proved**, not assumed, so
there is **no undisclosed weakening**. `sharpened_source_inequality_at_cycle_separator` (:7100) takes
`hsep` but **no** `hSR` — correct, since it is a within-block inequality lemma, not a criterion
consumer.

## Findings, ranked by severity

1. **DRIFT — the flagship theorem's documentation understates its hypotheses (:8003).** The module
   docstring (:24-32) says: "For a reactant/product-separated network, if every e-cycle is an
   s-cycle and no two e-cycles have an S-to-R intersection, then its fully open extension is
   strongly concordant." The theorem requires a **third side condition**,
   `hflow : N.ZeroComplexReactionsAreFlows` (:8005, defined :366) — every reaction incident to the
   zero complex is literally one of the singleton `inflowReaction`/`outflowReaction` channels added
   by `fullyOpen`. It is **not** implied by `hsep` or `hSR`, and its own definition's docstring
   (:362-365) calls it a "side condition repairing the true-chemistry SR criterion". The theorem
   docstring (:7997-8002) discusses *only* why `hsep` is necessary. **The module docstring's theorem
   statement is literally untrue as written.**
2. **DRIFT — `cyclic_gain_no_strict` (:3577) and `cyclic_gain_no_strict'` (:3598) state a strictly
   weaker theorem than what is proved.** The first takes `(_hf : ∀ i, 0 < f i)`, the second
   `(_he : ∀ i, 0 < e i)`. Inspection of both proofs confirms each uses only the *other* family's
   positivity, so the marked hypothesis is provably unnecessary. These are the algebraic kernel of
   the S-block contradiction (fed at :4412 and :4639 via `no_strict_gain_net'`), so the weakening
   propagates into the load-bearing path.
3. **OVERSTATED — three docstrings point at Lean API that does not exist.** `SrBlocks` is cited at
   :4016 and :7093; `SrProp510` at :4069. A repository-wide grep for `SrBlocks|SrProp510|Prop510`
   returns **only these three occurrences** — neither declaration exists. The statements themselves
   are honest; the narrative points a reader at non-existent API.
4. **OVERSTATED — `no_nonneighbor_chord` (:7306) silently restricts the chord species to index 0.**
   Binders include `(i0 : Fin n) (hi0 : i0.1 = 0)`. The rotation at the call site (:8201) justifies
   it, but the docstring reads as more general than it is.
5. **OVERSTATED — `no_clean_predecessor_chord_of_trueSRCriterion` (:7478): "any length" vs
   `hlarge : 2 ≤ L`.** Substantively correct (a 1-edge chord from `C.species (finRotate n i)` to
   `C.reaction i` *is* the cycle right edge), but the phrase overstates.
6. **MATCH with a note — instance side conditions omitted from narrative.**
   `weighted_source_inequalities_infeasible_of_unit_graph` (:4235) and
   `source_inequalities_survive_leaf_block_of_simple` (:4071) both need `[Nonempty Sp] [Nonempty Rx]`.
   Legitimate (they rule out degenerate empty-block vacuity); statements otherwise faithful.

## Table — 28 theorems

| # | name | file:line | verdict |
|---|---|---|---|
| 1 | `stronglyConcordant_fullyOpen_of_trueSRCriterion` | 8003 | SKIPPED (known hole) — see finding #1 |
| 2 | `stronglyConcordant_of_trueSRCriterion_of_weaklyNormal` | 8616 | MATCH — "for weakly normal/nondegenerate networks, the same SR condition implies strong concordance" is exactly `hsep + hwn + hflow + hSR → N.StronglyConcordant` |
| 3 | `stronglyConcordant_of_trueSRCriterion_of_weaklyReversible` | 8624 | MATCH — "in particular this applies to every weakly reversible network"; `hwr` used only via `weaklyNormal_of_weaklyReversible` |
| 4 | `injective_of_trueSRCriterion` | 8632 | MATCH — faithful application of `injective_of_twoWayWeaklyMonotonic` |
| 5 | `nonAdjacent_cycleClassFlux_eq_zero` | 6979 | MATCH — stronger than needed (equality, no `σ`); the "one-edge test" paragraph is a true corollary at :8547 |
| 6 | `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest` | 7019 | MATCH — *discloses* that `hrestOff` is undischargeable at the frontier. Model of honest scoping. |
| 7 | `sharpened_source_inequality_at_cycle_separator` | 7100 | MATCH — conclusion is exactly (40) over `F ∖ {…}`; `hrest` scoped to `i ≠ i₀` as documented |
| 8 | `no_nonneighbor_chord` (private) | 7306 | **OVERSTATED** — finding #4 |
| 9 | `no_clean_predecessor_chord_of_trueSRCriterion` (private) | 7478 | **OVERSTATED** — finding #5 |
| 10 | `exists_simple_directed_cycle_in_trueInternalAggregateSource` | 6169 | MATCH — supplies `hp2`, `hpeven` consumed at :8020-8023 |
| 11 | `exists_trueInternalAggregateCausalSource_data` | 6039 | MATCH — statement far *stronger* than the docstring; understated, the safe direction |
| 12 | `trueInternalAggregateSource_flux_pos` | 5994 | MATCH — direct; `Nonempty` derived from `W.sigma_ne`, not assumed |
| 13 | `exists_positive_off_cycle_aggregate_class` | 4644 | MATCH — `ρ ≠ C.reaction i ∧ ρ ≠ C.reaction (finRotate n i)` genuinely excludes both cycle reactions |
| 14 | `no_degree_two_aggregate_causal_cycle` | 4520 | MATCH — `hrep`/`hbeta` named in the docstring |
| 15 | `no_degree_two_causal_cycle` | 4314 | MATCH — carries **no** `hsep` and the docstring *correctly announces the absence*. Honest, not drift. |
| 16 | `TrueSRCycle.no_strict_gain_net'` | 3696 | MATCH — both extra hypotheses disclosed and actually discharged at :4391/:4597/:7180 |
| 17 | `TrueSRCycle.sCycleNet_iff_sCycle_of_separated` | 2092 | MATCH — the bridge the criterion depends on; **proved**, not assumed |
| 18 | `fullyOpen_trueSRCriterion_iff` | 1029 | MATCH — the lift/lower machinery (:370-905) is genuinely pointwise |
| 19 | `cyclic_gain_reverse_at_of_rest` | 3628 | MATCH — exactly (33); the `≤` bridge at `i₀` is the documented `cyclic_gain_no_strict'` refutation |
| 20 | `cyclic_gain_no_strict` | 3577 | **DRIFT** — finding #2 |
| 21 | `cyclic_gain_no_strict'` | 3598 | **DRIFT** — finding #2 |
| 22 | `multiplier_chain` | 3719 | MATCH — exactly the chained bound; candid that the naive ear route fails |
| 23 | `exists_cycle_multipliers` | 3763 | MATCH — honest self-limitation to the single-cycle case, with a correct pointer to `GainPotential.lean` |
| 24 | `weighted_source_inequalities_infeasible` | 4178 | MATCH — direct transposition-and-sum argument |
| 25 | `weighted_source_inequalities_infeasible_of_unit_graph` | 4235 | MATCH — "parallel units retained" borne out by the `max 0 (sup' …)` construction at :4247 |
| 26 | `source_inequalities_survive_leaf_block` | 3836 | MATCH — exactly §5.9 leaf step; no hidden extra premise |
| 27 | `source_inequalities_survive_leaf_SBlock` | 4019 | MATCH — `hseparator` correctly attributed to `sharpened_source_inequality_at_cycle_separator` |
| 28 | `source_inequalities_survive_leaf_block_of_simple` | 4071 | **OVERSTATED** — finding #3 (`SrProp510` does not exist) |

## Load-bearing positives (statements that are *stronger* than claimed)

- `exists_trueInternalAggregateCausalSource_data` (:6039) — understated.
- `massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses` (chain A, :742) — takes fewer
  hypotheses than the module's own orbit data.
- `relEntropy_le_of_mem_omegaLimit` / `sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint` (chain A,
  :957/:996) — need no boundedness though the docstrings say "bounded".
- `no_degree_two_causal_cycle` (:4314) and `no_degree_two_aggregate_causal_cycle_of_offCycle_hrest`
  (:7019) — both *announce* their own limitation. The single best-documented region of the file.
