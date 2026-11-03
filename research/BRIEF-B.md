> **CLOSED.** `stronglyConcordant_fullyOpen_of_trueSRCriterion` is proved, statement unchanged, by
> the Banaji--Craciun determinant argument in `CRNT/Multistationarity/BC*.lean`; see
> `HANDOFF_trueSR_closed.md`.  The material below documents the abandoned sign-causality route.

# BRIEF B — Shinar–Feinberg true-SR graph criterion ⟹ strong concordance

## B.1 The target

`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` — the `sorry` sits at the end of the
long graph-to-sign-causality proof of

```lean
theorem Network.stronglyConcordant_fullyOpen_of_trueSRCriterion
    (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.ZeroComplexReactionsAreFlows)
    (hSR : N.TrueSRStrongCriterion) :
    N.fullyOpen.StronglyConcordant
```

`TrueSRStrongCriterion` is defined in `CRNT/Multistationarity/TrueChemistrySRGraph.lean:271`:
for a reactant/product-separated network, *every e-cycle is an s-cycle* and *no two e-cycles have
an S-to-R intersection*.

Downstream: `stronglyConcordant_of_trueSRCriterion_of_weaklyNormal`,
`stronglyConcordant_of_trueSRCriterion_of_nonDegenerate`. The separation hypothesis `hsep` is
**necessary** and is not removable: see `CRNT/Examples/TrueSRNetCoeffCounterexample.lean`, where
dropping it makes the statement false.

## B.2 Where the residue actually sits

The `sorry` is *not* at the top of the theorem. It is the terminal case of the chain

```
stronglyConcordant_fullyOpen_of_trueSRCriterion
  └─ no_spanning_path_of_trueSRCriterion                     (proved up to the residue)
       └─ residue: `cases hv0 : Q0.vertex ⟨0, _⟩` with `inl s0`
            ├─ m = 1 ∧ s0 = s   → closed by aggregateCausalEdge_not_both_directions
            └─ residual: vertex0 = s0 on the cycle, no non-neighbour cycle flux,
                         (m ≠ 1 ∨ s0 ≠ s)                          ← THIS IS THE SORRY
```

Read the source comment at that point verbatim:

> A shortest species-to-reaction route from `s0` is then the single causal leftEdge step
> `s0 → C.reaction(pos s0)` (k = 1 is forced by `hopp`), the `leftEdge-final` residue; it is
> consistent with every hypothesis in scope and awaits the **A.6 Case-2 source-block datum** or
> **`hrest` degree-two isolation**.

So the residue is a *named, already-identified combinatorial obligation*: rule out a spanning
species→reaction path whose first hop is a leftEdge and whose rest has length 1. Two escape routes
are named in the repo itself:

* **the A.6 Case-2 source-block datum** — the missing hypothesis fed in from the case analysis one
  level up in the Shinar–Feinberg proof (see `CRNT/Examples` and the `A.6` references in the file);
* **`hrest` degree-two isolation** — isolate the degree-two case and discharge it separately.

## B.3 What is already proved

* `no_single_edge_chord_of_trueSRCriterion`, `no_spanning_path_of_trueSRCriterion` (modulo residue),
* `TrueSREdgePath`, `TrueSRSpeciesPath`, `TrueSRReactionInteriorPath`, `TrueSRChordExtraction`,
  `TrueSRChordParity`, `TrueSRParityRR`, `TrueSRGlueCPairs`, `TrueSRSSGlueCPairs`,
  `TrueSRCPairThirdEdge`, `TrueSRDegreeTwoNoSToR`, `TrueSRNoArcChord`, `TrueSRMinimalChord`,
  `TrueSRCycleChord`, `TrueSRCycleReverse`, `TrueSRSingleSharedEdge`, `TrueChemistrySRGraph`,
* `N.trueInternalClassFlux`, `N.exists_trueSREdge_of_nonzero_trueInternalClassFlux`,
  `N.trueSREdge_endpoint_eq_of_same_class_and_species`, `N.aggregateCausalEdge_not_both_directions`,
* `stronglyConcordant_of_fullyOpen_of_weaklyNormal` (already proved, needs only `hsep` + `hwn`).

`hSR` also transfers across the fully open extension
(`TrueChemistrySRCriterion.lean:1030`: `N.fullyOpen.TrueSRStrongCriterion ↔ N.TrueSRStrongCriterion`).

## B.4 Where the real difficulty is, ranked

1. **Recovering the A.6 Case-2 datum.** Find where in the case analysis above the residue the
   Case-2 source-block hypothesis is produced, determine its exact Lean statement, and check whether
   it is actually in scope at the residue. If it is in scope, the residue is a short combinatorial
   lemma. If it is *not* in scope, the fix is a restructuring of the case split — a real Lean task,
   not a math task.
2. **The `hopp` argument** forcing `k = 1`. Establish precisely which hypothesis `hopp` is and why it
   forces the first hop of a shortest path to be the sole step.
3. **Degree-two isolation via `hrest`.** If `hrest` is a hypothesis about degree-two vertices in the
   cycle class, isolating it needs a genuine case split on the local graph, and each case needs its
   own parity/chord lemma. This is the most robust route if (1) fails, because it does not depend
   on the case analysis's shape.

## B.5 Known dead ends

* Removing `hsep`. Provably false; a counterexample module already exists. Do not attempt.
* Treating this as "just add more sign/causality lemmas" without first pinning the exact residual
  combinatorial statement. The residue was left because the *hypotheses in scope were verified
  consistent with it* — i.e. the route is blocked upstream, not downstream.

## B.6 What a completed Hole B looks like

* no `sorry` in `CRNT/Multistationarity/TrueChemistrySRCriterion.lean`;
* `python3 scripts/dump_sorries.py` reports 1 hole (A only);
* `#print axioms Network.stronglyConcordant_fullyOpen_of_trueSRCriterion` reports only
  `[propext, Classical.choice, Quot.sound]`;
* the module still elaborates (it is 8641 lines; a careless `by_cases` restructuring will not).