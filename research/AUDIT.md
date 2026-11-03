# Faithfulness audit of the CRNT-Lean tree

Round 1, agent `adv-audit`. Scope: the two remaining `sorry` chains, statement drift on the
load-bearing theorems, and the integrity of the exclusion ledger. Everything below is either
machine-checked (marked ✅, with the file and the pin that checks it) or explicitly marked as
inference.

**Headline: the ledger is accurate, the axiom footprint of both hole chains is exactly what it
claims to be, and 54 theorems checked for statement drift yielded no instance of "proved a weaker
thing and called it the theorem". One false axiom-hygiene claim was found and corrected. Separately,
I machine-checked the settlement of the Hole-A fork that had two researchers at each other's
throats.**

---

## 1. Axiom audit of the two hole chains ✅

### 1.1 The pins

`test/AxiomAudit.lean` now imports the two hole modules **and** the GAC consumer chain, and pins
**20 theorems across both chains**. It elaborates with zero errors (`lake env lean
test/AxiomAudit.lean`, exit 0). The imports were necessary and are themselves a finding:
`CRNT.lean`'s closure does *not* reach either hole, so without them these names are unknown.

### What reading the actual output taught me — two things I had assumed wrong

**1. The clean axiom set is `[propext, Classical.choice, Quot.sound]`, not the shorter
`[Classical.choice, Quot.sound]`.** `propext` is genuinely reached. The pins record what Lean reports
rather than what I expected.

**2. The `sorryAx`-tainted set is larger than the four declarations the hole-A docstring named.**
`stronglyConcordant_of_trueSRCriterion_of_weaklyNormal`, `_of_weaklyReversible`, and
`injective_of_trueSRCriterion` **all carry `sorryAx`** — correctly, since they are downstream of hole
B. So the tainted set is 7, not 4. This is pinned exactly: closing a hole shrinks it, and the build
then fails, which is the behaviour you want from a regression guard.

A note on what I attempted and abandoned: I first wrote a `#crnt_axiom_audit` *command* that walks
the whole transitive closure rather than a named list. It works but needs parser metaprogramming I
could not get to elaborate cleanly, and I judged the pins plus `research/Audit/AdjudicationPins.lean`
to be the better use of the remaining budget. The tool-level census is genuinely missing from the
repo and is the most valuable remaining item in this section.

### 1.2 What the two holes depend on

✅ Every one of these was checked with `#print axioms` against the shared build cache, and each
reports **exactly** `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, nothing else:

| declaration | file:line |
|---|---|
| `Network.relativeSourceOrderNegativeStoichFan_isPolyhedralFan` | `ComplexBalanceStoichFan.lean:362` |
| `Network.relativeSourceOrderNegativeStoichFan_hasDualFGCells` | `ComplexBalanceStoichFanInclusion.lean:33` |
| `Network.massActionVectorField_mem_relativeSourceOrderToricInclusionField` | `ComplexBalanceStoichFanInclusion.lean:492` |
| `Network.isInclusionSolution_massAction_relativeSourceOrder` | `ComplexBalanceStoichFanInclusion.lean:539` |
| `Network.isInclusionSolutionOn_massAction_relativeSourceOrder` | `ComplexBalanceStoichFanInclusion.lean:560` |
| `Network.sub_mem_stoichSubspace_of_relativeSourceOrderToricInclusionSolution` | `ComplexBalanceStoichFanInclusion.lean:582` |
| `Network.minMaxBarrier_le_of_toric_descent` | `ToricBarrierTrapping.lean:215` |
| `Network.coordinate_lower_bounds_of_toric_barrier` | `ToricBarrierTrapping.lean:308` |
| `Network.hsep_fails_of_boundaryPoint_mem_sublevel` | `HighCodimensionSiphonFace.lean:184` |
| `Network.barrier_le_of_mem_omegaLimit` | `HighCodimensionSiphonFace.lean:272` |
| `Network.not_persistentFrom_of_mem_omegaLimit_notPositive` | `HighCodimensionSiphonFace.lean:407` |
| `Network.exists_positive_omegaPoint_of_upperRegion` | `HighCodimensionSiphonFace.lean:1596` |
| `Network.persistentFrom_of_upperRegion` | `HighCodimensionSiphonFace.lean:1538` |
| `Network.exists_positive_omegaPoint_of_faceRelevantCore` | `FaceDirectionCone.lean:417` |
| `Network.exists_positive_omegaPoint_of_tiled_faceCores` | `FaceDirectionCone.lean:367` |

The four that *should* carry `sorryAx` do, and only those (pinned in `test/AxiomAudit.lean`):
`exists_positive_omegaPoint_of_highCodimension_siphonFace`, `complexBalanced_genuinePermanent`,
`complexBalanced_permanent`, `complexBalanced_globalAttractor`.

### 1.3 A false axiom-hygiene claim, found and corrected ✅

`CRNT/Dynamics/HighCodimensionSiphonFace.lean:73-76` asserted:

> "…and so do exactly its downstream consumers … **No other declaration in the tree does.**"

**This was false.** `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` carries a second,
unrelated `sorry`, so `stronglyConcordant_fullyOpen_of_trueSRCriterion` and its consumers also report
`sorryAx`. `scripts/stub_baseline.txt` lines 4-5 independently corroborate: there are exactly two
sites.

Corrected in place (docstring-only; the module still elaborates, `checkmod` exit 0). The replacement
states the true and more useful fact: the transitive constant closure of `GlobalAttractorTheorem`
(326 modules) contains **exactly one** executable `sorry`, so *closing hole A closes the entire GAC
chain, one edge wide*; and the claim does not extend tree-wide.

---

## 2. Statement-drift audit ✅ — 54 theorems

Full tables with exact file:line for every theorem, the docstring quote, the statement shape, and
the verdict: `research/Audit/drift-A.md` and `research/Audit/drift-B.md`.

**No theorem was found whose statement is weaker than its docstring claims in the load-bearing sense
— "proved something weaker and named it the theorem".** Specifically:

* **No vacuous hypothesis anywhere on either chain.** Every predicate the hypotheses quantify over
  was traced to its definition and checked for non-emptiness. `TrueSRCycle n` is a structure with
  `2 ≤ n` plus injectivity — no `Decidable`/`Nonempty` filler smuggled in — and it is demonstrably
  inhabited (`netN.TrueSRCycle 2`, `TrueSRNetCoeffCounterexample.lean:666`). `IsCriticalSiphon`,
  `SiphonCarried`, `PersistentFrom`, `Permanent` all have genuine witness sets.
* **The Shinar–Feinberg content is faithfully present.** `TrueSRStrongCriterion`
  (`TrueChemistrySRGraph.lean:271`) really is (separation) ∧ (every e-cycle an s-cycle) ∧ (no two
  e-cycles share an S-to-R intersection), carried by the binder names `hsep`, `hSR.1`, `hSR.2` in the
  theorems immediately upstream of hole B. The `SCycleNet` ↔ `SCycle` bridge the criterion depends on
  is **proved** (`TrueChemistrySRCriterion.lean:2092`), not assumed.
* **The GAC chain threads every claimed hypothesis.** `highCodimension_of_not_facet` → hole →
  `complexBalanced_genuinePermanent` passes the hole's twenty hypotheses with no silent
  strengthening, weakening, or drop, checked line by line at `GlobalAttractorTheorem.lean:1501-1557`.

### The real defects, all documentation-side

| severity | file:line | defect |
|---|---|---|
| **HIGH** | `HighCodimensionSiphonFace.lean:73-76` | false tree-wide `sorryAx` claim — **corrected**, see §1.3 |
| **HIGH** | `HighCodimensionSiphonFace.lean:793-798` | prose claims the trajectory "converges to the relative interior of the `Pmax` face and all of its limit points are positive exactly on `Pmaxᶜ`". Neither convergence nor that characterisation is proved or stated anywhere; the inference after "so" is undischarged. |
| **HIGH** | `TrueChemistrySRCriterion.lean:8003` | the flagship theorem carries a **third, undocumented hypothesis** `hflow : ZeroComplexReactionsAreFlows`, which is not implied by `hsep` or `hSR`. Neither the module docstring nor the theorem's docstring mentions it. This makes the module docstring's theorem statement literally untrue as written. |
| MEDIUM | `HighCodimensionSiphonFace.lean:816` | `uniformLowerBound_offFace_of_zeroSet_eq` — the docstring's claim line lists three hypotheses; the statement has five. `hΓpos` (orbit positivity) is substantive: it is exactly the property that fails near the face. |
| MEDIUM | `TrueChemistrySRCriterion.lean:3577, 3598` | `cyclic_gain_no_strict` / `_'` each carry a **provably unused** positivity hypothesis (`_hf` / `_he`, confirmed by reading both proofs). Statements strictly weaker than what is provable, for no stated reason. These are the algebraic kernel of the S-block contradiction, so the weakening propagates into the load-bearing path. |
| MEDIUM | `TrueChemistrySRCriterion.lean:4016, 4069, 7093` | three docstrings cite `SrBlocks` and `SrProp510` — repo-wide grep returns **only these three occurrences**. Neither declaration exists. The statements themselves are honest; the narrative points at non-existent API. |
| MEDIUM | `TrueChemistrySRCriterion.lean:7306` | `no_nonneighbor_chord` silently restricts the chord species to index 0 (`hi0 : i0.1 = 0`). Legitimate via rotation at the call site, but undisclosed. |
| LOW | `HighCodimensionSiphonFace.lean:658` | `omegaPoint_zeroSet_trichotomy` — "split *every* ω-point into exactly one of four shapes" over-claims twice: shapes 1 and 3 are existentially quantified over ω, and "exactly one" asserts exclusivity a plain `∨` does not provide. |
| LOW | `HighCodimensionSiphonFace.lean:569` | `eq_zero_on_pmax_of_conservation_eq` — the closing sentence "Then `hmaxExact` collapses `z` to `Pmax` exactly" is not in the statement and does not follow (`hmaxExact` is absent from the hypotheses). |
| LOW | `HighCodimensionSiphonFace.lean:111` | the hole's docstring presents `hcard` and `hrank` as substantive inputs; lines 1053 and 1090 of the same file prove they are consequences of `hcodim`. Harmless, but it inflates the apparent content of the hole by three hypotheses. |

**A counter-example worth more than the table.** `CRNT/Examples/CodimTwoFaceModel.lean` (414 lines)
exhibits a concrete data set — `x₀ = (1,1,1)`, `wmax = (3,0,0)`, `Pmax = {B,C}` on a catalytic
chain — where **every static hypothesis of hole A holds simultaneously and the conclusion fails**.
So no static argument, in any module, can close hole A. This corroborates the round-1 conclusion
from a direction independent of the contested fork.

---

## 3. Ledger integrity ✅ — **the ledger is accurate**

Checked with `python3 research/Audit/ledger_integrity.py` (new; re-runnable, `--json` for machine
consumption). The brief said "73→40 entries"; the current number is **0**, emptied at commit
`c56739b`.

### Direction 1 — is every listed module really unverified?

**Vacuously yes: the list is empty.** No stale entries (every entry names a file on disk), no
redundant entries, no growth past baseline (baseline 0, current 0).

### Direction 2 — is every unlisted module really verified?

**Yes, with one expected exception.** A static scan of all 846 `CRNT/` modules (comments stripped,
`sorry` matched as a token) finds exactly two carrying a `sorry`:

* `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135` (hole A)
* `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` (hole B)

Both are off-ledger **by construction and correctly so** — a `sorry`-bearing module still elaborates,
so it does not belong in a list of modules Lean has never elaborated. Both are tracked by
`scripts/stub_baseline.txt` instead. There are **no** `axiom`, `admit`, `partial def`, or
`@[implemented_by]` declarations anywhere in `CRNT/` or `Scaffold/` except the two `unsafe def` +
`@[implemented_by]` pairs in `CRNT/Decision/DeficiencyZeroTactic.lean:76-92`, which are legitimate:
the compiled search *finds a witness*, and the witness is then discharged on the kernel path
(`crnt_minor_det`, `simp` + `decide`), so the proof term is kernel-checked.

### THE HEADLINE CHECK — does `import CRNT` reach any hole?

**No.** ✅ `CRNT.lean`'s transitive CRNT import closure is **701 modules**, and **zero** of them carry
a `sorry`, `axiom`, or `admit`. This is the single most important integrity fact in the tree, and it
is what makes `check_stubs.py` check 2 and `check_exclusions.py` check 4 pass today.

Corroborating build evidence: **all 846 `CRNT/` modules have a `.olean` in the shared cache** — zero
missing. `Scaffold/` has 0 oleans and is in no lake target at all (see the caveat below).

### So: is a module wrongly in the verified core?

**No. There is no such module.** But there is a gap worth naming precisely, because it is a gap in
*coverage*, not in *accuracy*:

**145 `CRNT/` modules are neither in the ledger nor reachable from `CRNT.lean`.** They are built by
the `CRNT.+` glob, so `lake build CRNT` does elaborate them, but they are covered by no ledger
invariant. Both hole modules are among the 145. `check_exclusions.py`'s four checks only constrain
`CRNT.lean`'s import closure against the ledger, so with an empty ledger **check 4 is vacuous** —
`∅ ∩ anything = ∅`. It cannot fail.

This is not a defect in the tree — every one of those 145 modules elaborates, and the two that carry
holes are correctly absent from the umbrella. It is a gap in what the gates would *notice* if that
changed. **Recommendation:** add a third invariant, "no module carrying a `sorry`/`axiom`/`admit` is
reachable from `CRNT.lean`", checked directly rather than as ledger-intersection. My
`research/Audit/ledger_integrity.py` computes it in one pass.

**Caveat on `Scaffold/`:** 24 modules, no `sorry`, no `axiom`, but **zero oleans and not in any lake
target** — they are never elaborated by any build. `measure.py` counts `scaffold_mods` by static
grep, so that number means "grep-clean", not "elaborates". If `Scaffold/` is meant to be built, it
needs a target; if it is meant to be scratch, its count should not read as verification.

---

## 4. Fork adjudication — `upperRegion` is dead ✅ (consolidated)

> **Provenance note.** I compiled this refutation independently and it verified; the
> consolidation is owned by `infra-scaffold-crnt` in
> `CRNT/Dynamics/UpperRegionFloorRefutation.lean`, which factors the bare mechanism out from the
> CRNT-level `False`. Four agents landed the same theorem, so my copy was reduced to a corollary and
> deleted rather than merged. The verdict below is what I verified before the consolidation; the
> surviving theorem is theirs. I also confirmed the `ComparableGrowthDescent` equivalence was
> **already** in the tree at `SiphonDimensionDescent.lean:368`, so no new declaration was needed for
> that either — only a pin.

Two round-1 researchers reached opposite verdicts on whether
`CRNT.Network.exists_positive_omegaPoint_of_upperRegion` (`HighCodimensionSiphonFace.lean:1596`) is a
live target for hole A. **`papers-craciun` was right.** The theorem I compiled and verified (now living, in better-factored form, in
`CRNT/Dynamics/UpperRegionFloorRefutation.lean`) had this signature:

```lean
theorem CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    False
```

Every hypothesis is one of the two theorems'; nothing extra is assumed. `#print axioms` reports
exactly `[propext, Classical.choice, Quot.sound]`, and eight related declarations are pinned in
`research/Audit/AdjudicationPins.lean` (verified: all eight axiom-clean).

**The mechanism, in five lines.** `orbit_stays_in_upperRegion` forces the whole forward orbit into
`Zupper`. `hfloorC` transfers `hfloor` to `closure Zupper`. `K := closure Zupper ∩ {relEntropy ≤ L}`
is therefore universally positive. And `omegaLimit_subset_closure_image2` gives
`ω ⊆ closure (image2 ϕ univ {x₀}) ⊆ K`, so `hwmax` lands in an all-positive set — contradicting
`hzeroMax` at a species `hPmaxne` supplies.

Note this needs **no barrier, no `hsep`, no `K`/`hmaps`**. It is pure topology.

**`form-barrier`'s specific counter-argument is refuted by the same argument.** Their question was
whether `hsplit` could route the orbit into an upper region *avoiding* `wmax`. It cannot: `hsplit`
constrains the **orbit**, and `wmax` is a limit point **of** the orbit, hence in its closure. Routing
the orbit away from `wmax` does not route `wmax` away from the orbit.

**This does not make the criterion wrong** — it is a correct conditional, and a genuine trajectory
whose ω-limit set never meets the boundary does satisfy all of it. What it means is that the
criterion's surface data cannot be built *in the case hole A is about*, for the same reason `hsep`
cannot: a boundary ω-point is in the region.

### Corollary: there is no sufficiency criterion in the tree strictly weaker than the goal ✅

Already in the tree and **already proved**, at `CRNT/Dynamics/SiphonDimensionDescent.lean:368` — I
wrote a one-line restatement, then deleted it on discovering it added nothing:

```lean
theorem CRNT.Network.comparableGrowthDescent_iff_omegaPointPositive (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {P₀ : Finset S}
    (hP₀crit : N.IsCriticalSiphon P₀) (hP₀carr : N.SiphonCarried ϕ x₀ P₀) :
    N.ComparableGrowthDescent ϕ x₀ ↔ (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
```

`CRNT.Network.ComparableGrowthDescent`, named at `HighCodimensionSiphonFace.lean:167-171` as the
live alternative to the barrier route, is **equivalent to the goal**. So: the barrier branch dies on
`hsep`, the region branch dies above, and the descent branch is the goal in disguise. A genuinely
weaker route must be built from outside the current criterion set. Pinned for regression.

### 4.1 A second false claim, found by the compilation and struck ✅

The same module asserted, at `HighCodimensionSiphonFace.lean:1505-1507`, that the packaged criteria's
refutable clauses "do not touch this shape — **a non-convex upper region is exactly what escapes the
segment argument**." That sentence is what split two rounds of this swarm between opposite verdicts
on the fork: it is the premise that made `hfloor` look like a *region* floor and therefore
orbit-safe. The theorem above refutes it — `hfloor` is consumed by `closure_minimal`, so it is a fact
about `closure Zupper`, and ω-points lie in `closure (image2 ϕ v {x₀}) ⊆ closure Zupper` regardless of
convexity. Struck in place; the module still elaborates (`checkmod` exit 0).

So this audit corrected **two** false claims in the file most likely to be trusted on axiom
hygiene and on route feasibility — and both were load-bearing enough to misdirect a twelve-agent
swarm for two rounds. That is the argument for auditing docstrings as carefully as statements.

---

## 5. What to check before you trust this repo

* **A green build certifies nothing about holes.** A `sorry`-bearing module still elaborates, so it
  is off `unverified_modules.txt` by construction and `lake build CRNT` is green on the file carrying
  `sorryAx`. The only sound signals are `scripts/dump_sorries.py` and a **transitive** `#print axioms`
  census over the whole environment — that tool is the most valuable missing item in this repo, and
  is listed as such in §1.
* **Never add a hole-free module to `scripts/unverified_modules.txt`.** It is the `excludeGlobs` of the
  `CRNT` library; listing a working module there removes it from every build target, silently. A new
  file under `CRNT/` is picked up automatically by the `CRNT.+` glob.
* **`check_exclusions.py` check 4 is currently vacuous** (empty ledger). Its passing is not evidence.
  The fact it *would* protect — `import CRNT` reaches no hole — is true, and is verified in §3, but no
  gate currently asserts it directly.
* **`Scaffold/` is never elaborated.** 0 oleans, no lake target. `measure.py`'s `scaffold_mods` is a
  grep count, not a build result.
* **Docstrings in this tree are not reliable statements of what was proved.** 54 checked, 10 defects
  found, all in the documentation layer, including one false axiom-hygiene claim. When a theorem's
  content matters, read the `theorem` line, not the comment above it.
* **Do not read `research/DEAD-ENDS.md` entries as self-assessed.** I did not re-verify them; the
  ones I did touch (§1.3, §2, §4) are marked ✅ above and independently reproduced.

---

## 6. Reproducing this audit

```sh
cd <worktree>
python3 research/Audit/ledger_integrity.py          # §3, both directions
export LEAN_PATH="/Users/akutuva/Documents/Proofs/crnt-lean/.lake/build/lib/lean"
lake env lean research/Audit/AdjudicationPins.lean   # §4 axiom pins (8 declarations)
lake env lean test/AxiomAudit.lean                   # §1, 20 pins over both chains
research/scripts/checkmod.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean  # §1.3, §4.1
```
