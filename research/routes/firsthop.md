# Route `firsthop` — what `hopp` actually forces at the `leftEdge-final` residue

Target: `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` (Hole B residue),
inside `stronglyConcordant_fullyOpen_of_trueSRCriterion`.

Deliverable module: **`CRNT/Multistationarity/TrueSRFirstHop.lean`** (hole-free, elaborates).
Route document written before the module's final elaboration pass; the Lean sources in §3 are
the authoritative record of what is proved.

---

## 1. `hopp`: exact statement and source

Introduced at `TrueChemistrySRCriterion.lean:8039-8043`:

```lean
have hopp : ∀ i,
    (N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i))) * σ (C.species (finRotate n i)) < 0 := by
  intro i
  exact hneg (finRotate n i)
```

* Binder name `hopp`, line **8039**. Origin: `hneg`, the negative-flux output of
  `N.trueSRCycle_of_simple_aggregate_cycle` (line 8023, destructured at 8021-8022).
* It is the same binder used in `no_degree_two_aggregate_causal_cycle` (line **4534**) and
  `sharpened_source_inequality_at_cycle_separator` (line **7114**).
* Its only *use* at the residue is line **8497** (`hopp ((finRotate n).symm k)`), to close the
  "final edge rides `ρ0`'s own cycle left edge" case by contradiction with `hpos0`.

Sign convention (`Network.TrueInternalAggregateCausalEdge`,
`TrueChemistrySRCriterion.lean:4691`):

| direction | condition |
| --- | --- |
| `Sum.inl s → Sum.inr ρ` | `trueInternalClassFlux α ρ s * σ s < 0` |
| `Sum.inr ρ → Sum.inl s` | `0 < trueInternalClassFlux α ρ s * σ s` |

So `hopp i` reads: **the cycle's left incidence at index `finRotate n i` is a
species-to-reaction aggregate causal edge `C.species (finRotate n i) → C.reaction (finRotate n i)`.**
`C.leftEdge j` has species `C.species j` and reaction `C.reaction j`
(`TrueChemistrySRGraph.lean:141-144`), so this is literally "the leftEdge is a causal edge".

## 2. Other hypotheses genuinely in scope at the residue

| binder | line | statement |
| --- | --- | --- |
| `hcausal` | 8036 | `∀ i, 0 < φ i (finRotate n i) * σs (finRotate n i)` |
| `hopp` | 8039 | `∀ i, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0` |
| `hCeven` | 8021 | `C.Even` |
| `hnc` (negated, line 8537) | 8537 | `¬ ∃ a b, a ≠ b → b ≠ (a+1)%n → φ a b * σs b ≠ 0`, i.e. `∀ a b, … → φ a b * σs b = 0`. This is `nonAdjacent_cycleClassFlux_eq_zero` (`TrueChemistrySRCriterion.lean:6979`), obtained via `exists_trueSREdge_of_nonzero_trueInternalClassFlux` + `no_single_edge_chord_of_trueSRCriterion`. |
| `hSR` | 8006 | `TrueSRStrongCriterion` |
| `hsep` | 8004 | `ReactantProductSeparated` |

with `φ a b := N.trueInternalClassFlux α (C.reaction a) (C.species b)` and
`σs b := σ (C.species b)`.

**`hopp` contains no path data whatsoever.** It is a pointwise sign condition.

## 3. Machine-checked statements (all in `CRNT/Multistationarity/TrueSRFirstHop.lean`)

The module has **no `CRNT` import** (pure `Fin n`/real combinatorics), so it can be imported by
`TrueChemistrySRCriterion.lean` itself without an import cycle.

```lean
theorem val_finRotate (i : Fin n) : (finRotate n i).1 = (i.1 + 1) % n
theorem finRotate_ne_self (hn2 : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i

theorem hopp_at {φ σs} (hopp : ∀ i : Fin n, φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0)
    (j : Fin n) : φ j j * σs j < 0

theorem hopp_of_hopp_at {φ σs} (hd : ∀ j : Fin n, φ j j * σs j < 0) (i : Fin n) :
    φ (finRotate n i) (finRotate n i) * σs (finRotate n i) < 0

theorem firstHopZero_of_hnc {φ σs}
    (hnc : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b ≠ 0)
    (a b : Fin n) (h1 : a.1 ≠ b.1) (h2 : b.1 ≠ (a.1 + 1) % n) : φ a b * σs b = 0

-- THE forcing lemma. hopp is deliberately unused.
theorem firstHop_forced_leftEdge {φ σs}
    (hz : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n → φ a b * σs b = 0)
    (hcausal : ∀ i : Fin n, 0 < φ i (finRotate n i) * σs (finRotate n i))
    (j a : Fin n) (h : φ a j * σs j < 0) : a = j

theorem hop_backward_forced {φ σs}
    (hz : …) (hopp : …) (j a : Fin n) (h : 0 < φ a j * σs j) : a = (finRotate n).symm j

theorem two_hop_onCycle {φ σs} (hz) (hcausal) (hopp)
    (j a b : Fin n) (h1 : φ a j * σs j < 0) (h2 : 0 < φ a b * σs b) :
    a = j ∧ b = finRotate n j

theorem no_hop_to_cycle_predecessor {φ σs} (hz) (hcausal) (hn2 : 2 ≤ n) (j : Fin n) :
    ¬ (φ ((finRotate n).symm j) j * σs j < 0)

theorem shortest_hop_is_leftEdge {φ σs} (hz) (hcausal) (hopp) (j : Fin n) :
    (∃ a : Fin n, φ a j * σs j < 0) ∧ (∀ a : Fin n, φ a j * σs j < 0 → a = j)

def badFlux (a b : Fin 3) : ℝ :=
  if a.1 = b.1 then -1 else if a.1 = 1 ∧ b.1 = 2 then -1 else 0

theorem hopp_alone_insufficient_diag :
    ∃ (φ : Fin 3 → Fin 3 → ℝ) (σs : Fin 3 → ℝ),
      (∀ j : Fin 3, φ j j * σs j < 0) ∧ ¬ (∀ a j : Fin 3, φ a j * σs j < 0 → a = j)

theorem hopp_alone_insufficient :
    ∃ (φ : Fin 3 → Fin 3 → ℝ) (σs : Fin 3 → ℝ),
      (∀ i : Fin 3, φ (finRotate 3 i) (finRotate 3 i) * σs (finRotate 3 i) < 0) ∧
        ¬ (∀ a j : Fin 3, φ a j * σs j < 0 → a = j)
```

### 3b. CRNT-level restatement — `CRNT/Multistationarity/TrueSRFirstHopCycle.lean`

A CRNT-level restatement is in `CRNT/Multistationarity/TrueSRFirstHopCycle.lean`, elaborating and
`sorryAx`-free (`#print axioms` on all six declarations reports exactly
`[propext, Classical.choice, Quot.sound]`):

```lean
theorem Network.nonneighbour_cycleClassFlux_eq_zero (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (a b : Fin n) (h1 : a.1 ≠ b.1) (h2 : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0

theorem Network.cycleReaction_active_at_cycleSpecies (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    ∃ s : S, σ s ≠ 0 ∧ N.trueInternalClassFlux α (C.reaction j) s ≠ 0

-- THE residue-level statement.
theorem Network.oneStep_fromCycleSpecies_eq_leftEdge (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (C : N.TrueSRCycle n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (j : Fin n) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    {ρ : N.ActiveAggregateTrueReaction α σ} (hρC : C.HasReaction ρ.1)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) :
    ρ.1 = C.reaction j

theorem Network.leftEdge_step_exists (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (C : N.TrueSRCycle n)
    (hopp : …) (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    N.TrueInternalAggregateCausalEdge
      (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
      (Sum.inr ⟨C.reaction j, cycleReaction_active_at_cycleSpecies N C hopp j hσ⟩)

theorem Network.onCycle_out_neighbour_leftEdge (N : Network S) … :
    (∀ {ρ : N.ActiveAggregateTrueReaction α σ}, C.HasReaction ρ.1 →
        N.TrueInternalAggregateCausalEdge
          (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ)) (Sum.inr ρ) →
        ρ.1 = C.reaction j) ∧
      N.TrueInternalAggregateCausalEdge
        (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
        (Sum.inr ⟨C.reaction j, …⟩)

theorem Network.no_oneStep_to_pos_of_cycleSpecies (N : Network S)
    {n : ℕ} {α} {σ} (C : N.TrueSRCycle n) (hn2 : 2 ≤ n) (hzero) (hcausal)
    (j : Fin n) {ρ : N.ActiveAggregateTrueReaction α σ}
    (hρpos : ρ.1 = C.reaction ((finRotate n).symm j))
    (hρC : C.HasReaction ρ.1) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) : False
```

This module **does** import `TrueChemistrySRCriterion` (necessarily: the statements are in its
vocabulary). It nonetheless audits to `[propext, Classical.choice, Quot.sound]` — the criterion's
`sorry` is not on the path of any of these six declarations. The axiom-clean core is the separate
CRNT-free `TrueSRFirstHop.lean`.

## 4. Proof sketches

*`firstHop_forced_leftEdge`.* Suppose `a ≠ j` and `φ a j * σs j < 0`.
If `j.1 ≠ (a.1+1) % n` then `hz a j` forces the product to be `0` — contradiction.
If `j.1 = (a.1+1) % n` then `finRotate n a = j`, so `hcausal a` reads
`0 < φ a j * σs j` — contradiction.
No use of `hopp`. **This is Shinar–Feinberg's local orientation lemma**: on the cycle, at a
species `s_j` the *only* cycle class whose aggregate flux opposes `σ(s_j)` is its own
leftEdge partner `r_j`; the rightEdge predecessor is causal-positive by `hcausal`, and
non-neighbouring cycle classes vanish by the no-single-edge-chord condition.

*`hop_backward_forced`.* Mirror. The one place `hopp` is needed: to exclude `a = j`, i.e. the
cycle's leftEdge reaction `r_j` cannot send a *positive* (reaction→species) causal edge into
`s_j`, because `hopp_at j` says the sign there is negative.

*`two_hop_onCycle`.* Composition. The aggregate causal graph induced on the cycle vertices is
the **directed** cycle
`s_j → r_j → s_{finRotate j} → r_{finRotate j} → …`.
An on-cycle walk of length `2t` from `s_j` ends at `C.species (finRotate^[t] n j)`; of length
`2t+1` at `C.reaction (finRotate^[t] n j)`. (The walk-index statement is immediate by induction
from `two_hop_onCycle` and is left to the caller; it is not needed at the residue.)

*`no_hop_to_cycle_predecessor`.* `firstHop_forced_leftEdge` gives `(finRotate n).symm j = j`,
which by `rot_of_symm_apply` gives `finRotate n j = j`, contradicted by `finRotate_ne_self`
for `2 ≤ n`.

*`hopp_alone_insufficient`.* Exact counterexample on `Fin 3` with `σs ≡ 1` and flux matrix
```
       b=0  b=1  b=2
 a=0   -1    0    0
 a=1    0   -1   -1
 a=2    0    0   -1
```
`hopp` holds (all diagonal terms are `-1 < 0`), yet `badFlux 1 2 = -1 < 0` with `1 ≠ 2`.
Verified by `decide` + `norm_num`; no `native_decide`, no axioms.

## 5. Definitive answer about the informal `hopp` claim

The residue comment (`TrueChemistrySRCriterion.lean:8602-8604`) reads:

> A shortest species-to-reaction route from `s0` is then the single causal leftEdge step
> `s0 → C.reaction(pos s0)` (k = 1 is forced by `hopp`).

Three findings, two of them machine-checked:

1. **`hopp` does not force `k = 1`.** Machine-checked: `hopp_alone_insufficient`. The forcing of
   the first hop comes from `hcausal` + the non-neighbour vanishing `nonAdjacent_cycleClassFlux_eq_zero`
   (`firstHop_forced_leftEdge`), hypotheses the comment does not mention; `hopp` contributes only
   *existence* of the hop (`hopp_at`) and the backward orientation (`hop_backward_forced`).
   **This independently confirms orchestrator ledger entry B-8** and sharpens it: B-8 says
   "`hopp`/`hcausal`/`¬hnc` constrain only CYCLE classes"; `firstHop_forced_leftEdge` shows that on
   cycle classes those three hypotheses *do* force the target uniquely, and `hopp` is not among
   the two load-bearing ones for the forward direction.

2. **The claimed target is wrong (off by one rotation).** The residue's own `pos` convention is
   fixed by `s₀ = C.species (finRotate n i)` (line 8052) with path endpoint `qC.1 = C.reaction i`
   (line 8219), i.e. `pos s₀ = (finRotate n).symm (index of s₀)`. Machine-checked:
   `no_hop_to_cycle_predecessor` — there is **no** aggregate causal hop
   `C.species j → C.reaction ((finRotate n).symm j)`. The genuine one-hop target is
   `C.reaction j`, i.e. `C.leftEdge j`. So the sentence should read
   "`s₀ → C.leftEdge j = C.reaction j`", not "`C.reaction (pos s₀)`".
   (Under the *other* possible reading of `pos`, `pos s₀ = j`, the step is correct but is **not**
   the path's endpoint `qC.1 = C.reaction i` for `n ≥ 2` — so under either reading the comment
   misidentifies the endpoint of `Q0`.)

3. **Consequence for the residue.** By (2), the first hop of `Q0` out of the on-cycle species `s₀`
   can only be `C.reaction j`, which is itself an on-cycle vertex; but `hQ0late`
   (`TrueChemistrySRCriterion.lean:8359`) forbids on-cycle vertices at every interior position.
   Hence **the first hop of `Q0` must land on an off-cycle class**. Where it lands is *not*
   determined by `hopp` and requires the missing A.6 Case-2 source-block datum (per B-9, that
   datum is not in `holes`; it lives on `backup-fig8` and must be ported).
   Note also that `m = 1` is already excluded outright by `hQ0late` (vertex `⟨1⟩ = qC` is on the
   cycle), so `m` is odd and `m ≥ 3` — which makes the existing `m = 1 ∧ s₀ = s` case split at
   lines 8587-8599 **redundant**.

## 6. Dependency order for consuming these lemmas at the residue

1. `nonneighbour_cycleClassFlux_eq_zero` — turn the negated `hnc` (line 8537) into the
   flux-times-`σ` vanishing form `hzero` (via `nonAdjacent_cycleClassFlux_eq_zero`, line 6979).
2. `Network.oneStep_fromCycleSpecies_eq_leftEdge` with `j` the index with `C.species j = s₀.1`,
   applied to the first hop of `Q0` out of `s₀`.
3. Combine with `hQ0late` to obtain: `Q0.vertex ⟨1⟩` is an off-cycle class.
4. Then the ported A.6 datum is required to finish. `hopp` cannot help beyond step 2.

## 7. Dead ends and environment notes

* **`hopp` as the k = 1 forcing hypothesis** — refuted above (`hopp_alone_insufficient`,
  `no_hop_to_cycle_predecessor`). Do not re-walk.
* **Trying to make `firstHop_forced_leftEdge` use `hopp`.** Impossible and unnecessary; the proof
  term does not mention it.
* **Asserting "no on-cycle path from `C.species (finRotate i)` to `C.reaction i`".** False:
  the on-cycle route has length `2n − 1` (all hops forward), consistent with `two_hop_onCycle`.
* **The residue's `m = 1 ∧ s0 = s` case (lines 8587-8599).** Redundant: `hQ0late` already
  excludes `m = 1` for every `s₀`.
* **Environment — RESOLVED.** `checkmod.sh` originally failed on any `CRNT.*` import because
  `lake env` prepends to `LEAN_PATH` and put the worktree-local build dir ahead of the shared
  cache. `infra-build` fixed this (PR #7 on `research/infra-build`): shared root first, `lean`
  called directly. Until that merges I worked around it by rsyncing the shared `CRNT` oleans
  into this worktree's `.lake/build/lib/lean/CRNT`. Both my modules were re-verified after the
  workaround, so neither "does not elaborate" claim I made mid-round stands.
* **Import availability.** `Mathlib.Tactic.Omega` and `Mathlib.Data.Fin.Tuple.FinOps` have no
  `.olean` in the local Mathlib build; the umbrella `Mathlib.Tactic` does. `TrueSRFirstHop.lean`
  imports the umbrella.
* **Axiom footprint of `TrueSRFirstHopCycle.lean`.** It imports `TrueChemistrySRCriterion`, so it
  was a fair candidate for the `sorryAx` trap. It is clean: the criterion's `sorry` lies on no
  dependency path of any of the six declarations. Anyone re-checking should re-run
  `#print axioms` rather than assume.