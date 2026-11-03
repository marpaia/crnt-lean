# `DEAD-ENDS.md` merge — the two-ledger crosswalk

**This file is generated.** Do not hand-edit it. Regenerate with

```sh
python3 research/scripts/gen_deadends_merge.py
```

It is a *crosswalk*, not a resolution. It says, for every entry on either side, what the
other side says about it and what has to happen to it — and it does **not** pick a winner.
Choosing which file is canonical is the human's merge (nobody may merge a PR; see
`research/README.md` §3).

## Sources

| | branch | entries parsed | grading | character |
| --- | --- | --- | --- | --- |
| **H** | `origin/holes` | 121 heading-entries (120 distinct ids) | `[V]` / `[H]` | orchestrator ledger, appended as broadcasts landed; chronological, uncorrected |
| **P** | `origin/research/adv-negative` (PR #13) | 105 heading-entries (105 distinct ids) | `[M]` / `[S]` / `[N]` | deduplicated across five prior handoff documents; has §0 grading, §4 maintenance protocol and `research/routes/negative-checklist.md` |

Line numbers below are **1-based line numbers in the file at that ref**, not in any working
tree, so they stay checkable after either branch moves.

## Why this cannot be a last-writer-wins

| | count |
| --- | --- |
| entries parsed on `holes` only | **93** |
| entries parsed on PR #13 only | **78** |
| entries whose id appears on **both** sides | 27 |
| of those, byte-identical text (keep one copy) | 26 |
| of those, same finding under a *different* id (keep both ids, one text) | 11 |
| of those, the two sides make **different claims** (keep both, dated) | 1 |
| `holes`-only entries that must be **ported** | **82** (74 curated + 8 auto-classified `PORT-AUTO`) |

A silent last-writer-wins drops 82 entries that exist nowhere on PR #13 — the
entire round-2 wave (`A-29` onward, `B-19` onward), the mining-scout TRAP/LEAD blocks, and
every API/OPS/ENV/VAC/AUDIT note.

## ⚠️ Three id hazards that a mechanical merge would hit

**Hazard 1 — the two schemes use the same numerals for different entries.** PR #13 §1/§2
number `A1`…`A30` and `B1`…`B18` *without* a hyphen, while §3b–§3d import the round-1
`A-1`…`A-15` / `B-1`…`B-12` *with* one. Normalising `A-16` and `A16` to the same key
matches unrelated findings:

| `holes` id | what it says | PR #13 id | what it says | title similarity |
| --- | --- | --- | --- | --- |
| `A-1` (13) | The `oneBit*` fan-face recursors prove the wrong statement | `A1` (52) | The three packaged barrier criteria cannot be instantiated: any `hsep` instant | 0.0 |
| `A-2` (30) | `binaryWordValue` is the wrong termination measure | `A2` (73) | The theorem's own conclusion is incompatible with `PersistentFrom` — the hole  | 0.0 |
| `A-3` (40) | §7.3 is not open — do not re-attack | `A3` (94) | A globally homogeneous convex polyhedral barrier (max-of-affine) is impossible | 0.0 |
| `A-4` (50) | The ε̃ scale system (Craciun eq. 19) is not open — do not re-attack | `A4` (115) | Anderson–Shiu quadratic face mass is not monotone at codimension ≥ 2 | 0.0 |
| `A-5` (61) | `Refines` is set-containment, not face-to-face equality | `A5` (135) | `hMclass` (bounded positive compatibility class) is not derivable — false off  | 0.0 |
| `A-6` (70) | "IsCompletePointedPolyhedralFan does not exist" — RETRACTED, the entry was WRO | `A6` (152) | The vacuous tile definition: `activeFaceImage` over all positive `x` makes `hm | 0.0 |
| `A-11` (87) | `CraciunZSH.hinterior` is not the paper's hypothesis, and the difference is fa | `A11` (263) | One piece per species is not enough — pieces must be indexed by scale ordering | 0.0 |
| `A-12` (100) | Lemma 9.7 has no quantitative bound on normal straying | `A12` (282) | The topological (two-closed-sets) method cannot fire on branch (I): a species  | 0.0 |
| `A-13` (109) | The n-dimensional upgrade of Lemma 9.7 is not in the paper | `A13` (301) | Descent-iteration route bottoms out at the goal itself | 0.0 |
| `A-14` (116) | The width-≥δ flatness claim needs a qualification the repo omits | `A14` (319) | `hface` of `uniformLowerBound_offFace_of_zeroSet_eq` does not cover the tie br | 0.0 |
| `A-15` (124) | Craciun v3 §7/§9 is reachable only via alphaxiv | `A15` (336) | Branch (4) (exact ties) is dead — ties cannot coexist with face points | 0.0 |
| `B-11` (132) | The `TrueSREarCase2.lean` port cannot be a file copy | `B11` (812) | `ConcordantWith (twoWayInfluenceSpecification) ↔ StronglyConcordant` was demot | 0.0 |

(of 48 hyphen-stripped id pairs, 48 have title similarity below 0.45, i.e. they are
**not** the same finding.) **Merge on content, never on id.**

**Hazard 2 — PR #13 reuses its own ids.** Its §3c numbering (`F-1`…`F-4`, the framing
revision) and its §3g numbering (`F-1`…`F-5`, the fork resolution) are different entries
with the same ids, at lines 1319–1364 and 1820–1870 respectively. Anyone citing "F-1"
without a line number is ambiguous. This table cites line numbers throughout for that
reason.

**Hazard 3 — `holes` itself has a duplicate id.** `A-40` is used twice, at lines 873 and
992, for two unrelated findings ("a strictly positive conservation law separates two class
points is FALSE" and "hole A's statement is NOT refutable"). Both must be ported and
renumbered on the way in.

Duplicate ids on `holes`: `A-40` ×2.

## The crosswalk

`H` column = `holes` id and line. `P` column = PR #13 id and line, or `—` for none.

| # | `holes` id | H line | PR #13 id | P line | action | what it is / what to do |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `A-1` | 13 | `A-1` | 1033 | **IDENTICAL** | oneBit* recursors rank the projected fan, not the ambient face |
| 2 | `API-1` | 848 | — | — | **PORT** | dot notation on Concentration S resolves in namespace Function |
| 3 | `AUDIT-1` | 1338 | — | — | **PORT** | a clean claim must name its evidence type (diff vs file-content) |
| 4 | `A-2` | 30 | `A-2` | 1053 | **IDENTICAL** | binaryWordValue is anti-monotone |
| 5 | `API-2` | 858 | — | — | **PORT** | StoichCompatible.refl is applied as StoichCompatible.refl N x |
| 6 | `A-3` | 40 | `A-3` | 1065 | **IDENTICAL** | §7.3 closed for a single chain |
| 7 | `API-3` | 865 | — | — | **PORT** | Concentration.zeroSet must be noncomputable |
| 8 | `A-4` | 50 | `A-4` | 1078 | **IDENTICAL** | epsilon-tilde scale system proved five times |
| 9 | `A-5` | 61 | `A-5` | 1092 | **IDENTICAL** | Refines is set containment |
| 10 | `A-6` | 70 | `A-6` | 1100 | **DIVERGES** | holes RETRACTS the claim (`IsPolyhedralFan` exists at ConeFace.lean:196); PR #13 §3b A-6 still states the claim and P4 bullet 2 repeats it. Port the retraction and delete the claim; do NOT merge the two into one 'entry'. |
| 11 | `A-7` | 152 | `A-7` | 1110 | **IDENTICAL** | Anderson arXiv:0903.0901, not 2006.02483 |
| 12 | `A-8` | 162 | `A-8` | 1122 | **IDENTICAL** | CNP has no entry-loss function |
| 13 | `A-9` | 166 | `A-9` | 1129 | **IDENTICAL** | Craciun v3 is arXiv:1501.02860 |
| 14 | `A-10` | 176 | `A-10` | 1141 | **IDENTICAL** | arXiv HTML truncates; use the PDF |
| 15 | `A-11` | 87 | `A-11` | 1394 | **IDENTICAL** | CraciunZSH.hinterior mistranscribes relint as interior |
| 16 | `A-12` | 100 | `A-12` | 1416 | **IDENTICAL** | Lemma 9.7 has no slack on the normal |
| 17 | `A-13` | 109 | `A-13` | 1429 | **IDENTICAL** | n-dimensional Lemma 9.7 is unwritten |
| 18 | `A-14` | 116 | `A-14` | 1440 | **IDENTICAL** | width>=delta flatness fails at vertices |
| 19 | `A-15` | 124 | `A-15` | 1453 | **IDENTICAL** | alphaxiv is the only complete HTML route |
| 20 | `A-16` | 341 | `F-1` | 1820 | **CROSSREF** | PR #13 files the same verdict as F-1 (of upperRegion dead) |
| 21 | `A-17` | 352 | `F-2` | 1834 | **CROSSREF** | PR #13 F-2: the refutation does not transfer to faceRelevantCore |
| 22 | `A-18` | 364 | — | — | **PORT** | the round-1 VERDICT that every terminal criterion is refuted or goal-equivalent; PR #13 §3h carries the same prose un-numbered |
| 23 | `A-19` | 418 | — | — | **PORT** | the unifying structural fact, Permanent-framed; superseded in substance by PR #13 H-4, but the Permanent framing is still quoted in the tree |
| 24 | `A-20` | 457 | `H-1` | 1960 | **CROSSREF** | PR #13 H-1: Lemma 9.7 does not construct the surfaces |
| 25 | `A-21` | 491 | — | — | **PORT** | frontier membership implies nothing about holes; pairs with F-5 |
| 26 | `A-22` | 516 | — | — | **PORT** | the real obstruction is the forall/exists mismatch, not Permanent |
| 27 | `A-23` | 531 | — | — | **PORT** | hole A reduces to ONE unproved descent estimate; read with A-33/A-34 |
| 28 | `A-24` | 561 | — | — | **PORT** | the false axiom-hygiene claim at HighCodimensionSiphonFace.lean:73-76 |
| 29 | `A-25` | 588 | `H-5` | 2068 | **CROSSREF** | PR #13 H-5: hm is vacuous, m := 0 |
| 30 | `A-26` | 635 | `H-3` | 1998 | **CROSSREF** | PR #13 H-3 carries the same compiled False-level refutation |
| 31 | `A-27` | 656 | — | — | **PORT** | 151 proved, hole-free modules in hole A's import closure with no caller |
| 32 | `A-28` | 667 | `H-4` | 2037 | **CROSSREF** | PR #13 H-4 carries the same general template |
| 33 | `A-29` | 689 | — | — | **PORT** | four copies of one False-level theorem; consolidation owner named |
| 34 | `A-30` | 707 | — | — | **PORT** | 'unused' != 'unavailable'; with A-35, the marking rule for the fan table |
| 35 | `A-31` | 719 | — | — | **PORT** | the template does NOT reach the hsep family; cite two different lemmas |
| 36 | `A-32` | 738 | — | — | **PORT** | hm-vacuity alone does not kill faceRelevantCore |
| 37 | `A-33` | 750 | — | — | **PORT** | 'three-line wrapper' is the wrong phrasing; correct file:line |
| 38 | `A-34` | 761 | — | — | **PORT** | descend is unproved as a whole; :569 is a separate open item |
| 39 | `A-35` | 772 | — | — | **PORT** | 'no live consumer' overstates it; ComplexBalanceStoichFanInclusion is live |
| 40 | `A-36` | 788 | — | — | **PORT** | do not re-land comparableGrowthDescent_is_not_a_weaker_route |
| 41 | `A-37` | 798 | — | — | **PORT** | the descent route is circular and the tree says so |
| 42 | `A-38` | 808 | — | — | **PORT** | closed-positive confinement is not impossible in general |
| 43 | `A-39` | 816 | — | — | **PORT** | orchestrator line citations were fabricated; SiphonDimensionDescent is 382 lines. Verified line list included |
| 44 | `A-40` | 873 | — | — | **PORT** | TWO entries share this id on holes. First: 'a strictly positive conservation law separates two class points' is FALSE. Second: hole A's statement is NOT refutable. Both must be ported and renumbered. |
| 45 | `A-40` | 992 | — | — | **PORT** | TWO entries share this id on holes. First: 'a strictly positive conservation law separates two class points' is FALSE. Second: hole A's statement is NOT refutable. Both must be ported and renumbered. |
| 46 | `A-41` | 1008 | — | — | **PORT** | two of adv-refute's own results were float/kernel artefacts |
| 47 | `A-42` | 1040 | — | — | **PORT** | the template is not a new obstruction; cite GlobalPersistence.lean:161 |
| 48 | `A-43` | 1050 | — | — | **PORT** | closed positive confines exist and are built; the sharp statement of what hole A needs |
| 49 | `A-44` | 1065 | — | — | **PORT** | the comment at HighCodimensionSiphonFace.lean:1493 was false and load-bearing for two rounds |
| 50 | `A-45` | 1076 | — | — | **PORT** | Concentration S is S -> R, plain reals |
| 51 | `A-46` | 1086 | — | — | **PORT** | hole A is not vacuous; it is genuinely the GAC boundary case |
| 52 | `A-47` | 1404 | — | — | **PORT** | two disjoint scopes missing the same half of the descent estimate |
| 53 | `A-48` | 1438 | — | — | **PORT** | LOAD-BEARING: hole A must consume hsol essentially; machine-checked |
| 54 | `A-49` | 1458 | — | — | **PORT** | the projOn bridge is NOT NEEDED; withdrawn |
| 55 | `A-50` | 1483 | — | — | **PORT** | the projOn bridge is structurally IMPOSSIBLE, not merely absent |
| 56 | `A-51` | 1514 | — | — | **PORT** | exists_maximal_zeroSetOf_card_le duplicates hmaxExact_of_zeroSet_card_le; cut it, keep exists_maximalCard_zeroSet |
| 57 | `A-52` | 1529 | — | — | **PORT** | SiphonCarried is discharged by the hole's own hwmax/hzeroMax [S] |
| 58 | `A-53` | 1549 | — | — | **PORT** | IsCriticalSiphon Pmax is FULLY discharged [M]; residue is exactly descend |
| 59 | `A-54` | 1603 | — | — | **PORT** | the descent is ATTRIBUTED to Anderson but he did not use it, and it is INAPPLICABLE at hole A's faces; the closing hypothesis is numLinkageClasses = 1 |
| 60 | `A-55` | 1643 | — | — | **PORT** | TierPersistence.lean is outside hole A's import closure (476 lines); TierStrictBelow has the OPPOSITE sign convention to Anderson Def 4.1(ii) |
| 61 | `A-56` | 1664 | — | — | **PORT** | two points that REDUCE the apparent residue: Anderson's condition 2 is one by_case here, and the projected time-dependent network is absent |
| 62 | `A-57` | 1674 | — | — | **PORT** | DO NOT FUND THE SINGLE-LINKAGE ROUTE -- closed, not underfunded (l=1 contradicts hwmax) |
| 63 | `A-58` | 1684 | — | — | **PORT** | the residue is pinned from three independent directions; the target is NOT what the file names |
| 64 | `A-59` | 1712 | — | — | **PORT** | 'omega finite => no strictly smaller carrier' is FALSE; spread enables the descent |
| 65 | `A-60` | 1720 | — | — | **PORT** | the exact target sentence, agreed by three routes: smaller_carried_siphon_iff_zeroSet_card_lt at :608 |
| 66 | `A-61` | 1737 | — | — | **PORT** | siphonCarried_of_escape cannot supply the cardinality estimate; it is a missing input, not a missing proof |
| 67 | `A-62` | 1748 | — | — | **PORT** | machine-checked: the strict-shrinking disjunct is false at singleton omega |
| 68 | `A-63` | 1756 | — | — | **PORT** | numLinkageClasses = 1 is CLOSED, not underfunded -- stated per request |
| 69 | `A-64` | 1765 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 70 | `A-65` | 1781 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 71 | `A-66` | 1794 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 72 | `A-67` | 1801 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 73 | `A-68` | 1819 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 74 | `A-69` | 1836 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 75 | `A-70` | 1847 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 76 | `B-1` | 199 | `B-1` | 1164 | **IDENTICAL** | the hspan witness is refuted |
| 77 | `B-2` | 215 | `B-2` | 1182 | **IDENTICAL** | degree splitting at the residue is degenerate |
| 78 | `B-3` | 224 | `B-3` | 1193 | **IDENTICAL** | hrest is not in scope at the residue |
| 79 | `B-4` | 233 | `B-4` | 1205 | **IDENTICAL** | no_sToRIntersection_of_degree_two unusable as a closer |
| 80 | `B-5` | 239 | `B-5` | 1214 | **IDENTICAL** | hopp/hcausal/hnc are already sharp |
| 81 | `B-6` | 246 | `B-6` | 1224 | **IDENTICAL** | species-interior analogue does not apply |
| 82 | `B-7` | 253 | `B-7` | 1233 | **IDENTICAL** | no_spanning_path_of_trueSRCriterion cannot apply to Q0 |
| 83 | `B-8` | 261 | `B-8` | 1242 | **IDENTICAL** | hopp does not force k=1 |
| 84 | `B-9` | 270 | `B-9` | 1254 | **IDENTICAL** | the residue's source comment is wrong about the tree |
| 85 | `B-10` | 281 | `B-10` | 1268 | **IDENTICAL** | no upstream case analysis to thread a datum from |
| 86 | `B-11` | 132 | `B-11` | 1464 | **IDENTICAL** | TrueSREarCase2.lean cannot be a file copy |
| 87 | `B-12` | 145 | `B-12` | 1479 | **IDENTICAL** | the ear closes in hSR.2, not hnd |
| 88 | `B-13` | 330 | `F-4` | 1870 | **CROSSREF** | PR #13 F-4: the RR arc builder is NOT needed |
| 89 | `B-14` | 468 | `H-2` | 1974 | **CROSSREF** | PR #13 H-2 repeats B-14 verbatim |
| 90 | `B-15` | 481 | `H-2` | 1974 | **CROSSREF** | PR #13 H-2 repeats B-15 verbatim |
| 91 | `B-16` | 571 | — | — | **PORT** | no privacy lift and no bespoke builder; TrueSRGlueInterface has no hole import |
| 92 | `B-17` | 598 | — | — | **PORT** | glueArc is NOT the RR arc builder; it takes both inputs |
| 93 | `B-18` | 899 | — | — | **PORT** | hopp is a sign condition with no path content |
| 94 | `B-19` | 912 | `B-9` | 1254 | **CROSSREF** | PR #13 B-9 (round-1) is the comment-is-wrong entry; holes B-19 is the machine-checked one-rotation correction. Both concern the residue's comment; different findings. |
| 95 | `B-20` | 921 | — | — | **PORT** | the on-cycle route has length 2n-1; module that imports the hole file and is still sorryAx-free |
| 96 | `B-21` | 937 | — | — | **PORT** | m=1 is excluded by hQ0late; the m=1 split is redundant |
| 97 | `B-22` | 952 | — | — | **PORT** | the hopp_alone_insufficient counterexample, explicit 3x3 flux matrix |
| 98 | `B-23` | 978 | — | — | **PORT** | firstHop_forced_leftEdge omits hopp; hopp is load-bearing backwards only |
| 99 | `B-24` | 1110 | — | — | **PORT** | the RRGluable INSTANCE is the blocker (rr_gluable_arcs) |
| 100 | `B-25` | 1127 | `B7` | 749 | **CROSSREF** | PR #13 B7 proves degree-two makes an S-to-R intersection impossible; holes B-25 adds that the shipped lemma takes NO hypotheses, so hSR.2 is vacuous there |
| 101 | `B-26` | 1149 | — | — | **PORT** | hole B has no witness: no network satisfies hsep and hflow and hSR |
| 102 | `B-27` | 1162 | — | — | **PORT** | rr_three_glued_even_of_two already exists at TrueSRParityRR.lean:775 |
| 103 | `B-28` | 1171 | — | — | **PORT** | the RR arc builder was written four times; reconcile before building |
| 104 | `B-29` | 1350 | — | — | **PORT** | the four TrueSRReactionArc.lean files are NOT identical; four disjoint APIs |
| 105 | `B-30` | 1391 | — | — | **PORT** | the k < n failure is a type error, so k+1 < n is necessary |
| 106 | `ENV-1` | 946 | — | — | **PORT** | Mathlib submodule imports have no local .olean; import umbrellas |
| 107 | `LEAD-1` | 1255 | — | — | **PORT** | KurtzScaling.lean touches the deterministic field; unassigned |
| 108 | `LEAD-2` | 1327 | — | — | **PORT** | the projOn / ProjectedFaceDimensionCode bridge does not exist |
| 109 | `OPS-1` | 1033 | — | — | **PORT** | push before `git reset --hard` on an unpushed branch |
| 110 | `OPS-2` | 1103 | — | — | **PORT** | root Scaffold/ is gitignored; use CRNT/Scaffold/ |
| 111 | `OPS-3` | 1269 | — | — | **PORT** | the prepend privacy lift is settled; audit by diff, never by message |
| 112 | `OPS-3b` | 1813 | — | — | **PORT-AUTO** | auto-classified: appended to `holes` after the crosswalk was built. PORT is correct by construction; the note is not curated. |
| 113 | `OPS-4` | 1314 | — | — | **PORT** | the four-way union risks namespace collision; elaborate to settle it |
| 114 | `OPS-5` | 1379 | — | — | **PORT** | checkmod.sh second bug: a stale shared-cache .olean causes a FALSE PASS |
| 115 | `OPS-6` | 1538 | — | — | **PORT** | land elaboration-friction API facts in the ledger BEFORE stalling on them |
| 116 | `SEQ-1` | 1223 | — | — | **PORT** | Hole B's safe dependency order: arc and glue are vacuity-safe, the ear is not |
| 117 | `TRAP-1` | 1199 | — | — | **PORT** | eight kernel modules are about ComplexIdx, not Concentration: the worst mis-citable surface in the tree for hmaxExact/Pmax |
| 118 | `TRAP-1b` | 1294 | — | — | **PORT** | concrete citations for TRAP-1 from a second disjoint scout; also the negative that the descent estimate is absent at that layer |
| 119 | `TRAP-2` | 1212 | — | — | **PORT** | kineticMap_complexMonomial_mem_deficiencySubspace assumes IsMassActionSteadyState, which the hole lacks for wmax |
| 120 | `TRAP-3` | 1234 | — | — | **PORT** | in CRNT/Stochastic the confused axis is count lattice vs concentration |
| 121 | `VAC-1` | 1136 | — | — | **PORT** | DifferentialInclusion.Field is vacuous when empty; blast radius = 4 PolyhedralBarrier ForwardInvariant conclusions |

**121 rows — every entry parsed on `origin/holes`.**

## PR #13-only entries

These have no `holes` counterpart. They stay; they are PR #13's main contribution
(deduplication, grading, the maintenance protocol). Listed so the merge is provably
complete, not so it can be reproduced from this file alone.

| PR #13 id | P line | disposition |
| --- | --- | --- |
| `A1` | 52 | KEEP — PR #13 §1, dashless id |
| `A2` | 73 | KEEP — PR #13 §1, dashless id |
| `A3` | 94 | KEEP — PR #13 §1, dashless id |
| `A4` | 115 | KEEP — PR #13 §1, dashless id |
| `A5` | 135 | KEEP — PR #13 §1, dashless id |
| `A6` | 152 | KEEP — PR #13 §1, dashless id |
| `A7` | 174 | KEEP — PR #13 §1, dashless id |
| `A8` | 192 | KEEP — PR #13 §1, dashless id |
| `A9` | 224 | KEEP — PR #13 §1, dashless id |
| `A10` | 245 | KEEP — PR #13 §1, dashless id |
| `A11` | 263 | KEEP — PR #13 §1, dashless id |
| `A12` | 282 | KEEP — PR #13 §1, dashless id |
| `A13` | 301 | KEEP — PR #13 §1, dashless id |
| `A14` | 319 | KEEP — PR #13 §1, dashless id |
| `A15` | 336 | KEEP — PR #13 §1, dashless id |
| `A16` | 350 | KEEP — PR #13 §1, dashless id |
| `A17` | 373 | KEEP — PR #13 §1, dashless id |
| `A18` | 393 | KEEP — PR #13 §1, dashless id |
| `A19` | 409 | KEEP — PR #13 §1, dashless id |
| `A20` | 421 | KEEP — PR #13 §1, dashless id |
| `A21` | 432 | KEEP — PR #13 §1, dashless id |
| `A22` | 452 | KEEP — PR #13 §1, dashless id |
| `A22b` | 470 | KEEP — PR #13 §1: do not misread A22 as refuting the no-critical-siphon route |
| `A23` | 481 | KEEP — PR #13 §1, dashless id |
| `A24` | 495 | KEEP — PR #13 §1, dashless id |
| `A25` | 508 | KEEP — PR #13 §1, dashless id |
| `A26` | 527 | KEEP — PR #13 §1, dashless id |
| `A27` | 546 | KEEP — PR #13 §1, dashless id |
| `A28` | 569 | KEEP — PR #13 §1, dashless id |
| `A29` | 582 | KEEP — PR #13 §1, dashless id |
| `A30` | 605 | KEEP — PR #13 §1, dashless id |
| `B1` | 624 | KEEP — PR #13 §2, dashless id |
| `B2` | 651 | KEEP — PR #13 §2, dashless id |
| `B3` | 670 | KEEP — PR #13 §2, dashless id |
| `B4` | 694 | KEEP — PR #13 §2, dashless id |
| `B5` | 713 | KEEP — PR #13 §2, dashless id |
| `B6` | 734 | KEEP — PR #13 §2, dashless id |
| `B7` | 749 | KEEP — PR #13 §2, dashless id |
| `B8` | 767 | KEEP — PR #13 §2, dashless id |
| `B9` | 783 | KEEP — PR #13 §2, dashless id |
| `B10` | 799 | KEEP — PR #13 §2, dashless id |
| `B11` | 812 | KEEP — PR #13 §2, dashless id |
| `B12` | 826 | KEEP — PR #13 §2, dashless id |
| `B13` | 847 | KEEP — PR #13 §2, dashless id |
| `B14` | 858 | KEEP — PR #13 §2, dashless id |
| `B15` | 878 | KEEP — PR #13 §2, dashless id |
| `B16` | 892 | KEEP — PR #13 §2, dashless id |
| `B17` | 905 | KEEP — PR #13 §2, dashless id |
| `B18` | 913 | KEEP — PR #13 §2, dashless id |
| `C-1` | 1726 | KEEP — PR #13 §3f fork-contest record |
| `C-2` | 1750 | KEEP — PR #13 §3f fork-contest record |
| `C-3` | 1770 | KEEP — PR #13 §3f fork-contest record |
| `C-4` | 1781 | KEEP — PR #13 §3f fork-contest record |
| `C-5` | 1798 | KEEP — PR #13 §3f fork-contest record |
| `F-1` | 1820 | KEEP — PR #13 §3g fork resolution |
| `F-2` | 1834 | KEEP — PR #13 §3g fork resolution |
| `F-3` | 1856 | KEEP — PR #13 §3g fork resolution |
| `F-4` | 1870 | KEEP — PR #13 §3g fork resolution |
| `F-5` | 1891 | KEEP — PR #13 §3g fork resolution |
| `H-1` | 1960 | KEEP — PR #13 §3h unified fact + corrections |
| `H-2` | 1974 | KEEP — PR #13 §3h unified fact + corrections |
| `H-3` | 1998 | KEEP — PR #13 §3h unified fact + corrections |
| `H-4` | 2037 | KEEP — PR #13 §3h unified fact + corrections |
| `H-5` | 2068 | KEEP — PR #13 §3h unified fact + corrections |
| `H-6` | 2080 | KEEP — PR #13 §3h unified fact + corrections |
| `P1` | 928 | KEEP — PR #13 §3 process finding |
| `P2` | 940 | KEEP — PR #13 §3 process finding |
| `P3` | 948 | KEEP — PR #13 §3 process finding |
| `P4` | 965 | KEEP — PR #13 §3 process finding |
| `P5` | 998 | KEEP — PR #13 §3 process finding |
| `R-1` | 1509 | KEEP — PR #13 §3e landing-site wave |
| `R-2` | 1546 | KEEP — PR #13 §3e landing-site wave |
| `R-3` | 1562 | KEEP — PR #13 §3e landing-site wave |
| `R-4` | 1586 | KEEP — PR #13 §3e landing-site wave |
| `R-5` | 1614 | KEEP — PR #13 §3e landing-site wave |
| `R-6` | 1629 | KEEP — PR #13 §3e landing-site wave |
| `R-7` | 1661 | KEEP — PR #13 §3e landing-site wave |
| `R-8` | 1678 | KEEP — PR #13 §3e landing-site wave |

Plus, on PR #13 and **not** an entry: §0 (grading table), the deduplication note, the ID
mapping table at §3b, `research/routes/negative-checklist.md`, and §4 (maintenance
protocol, six subsections). Those are structural and must survive any merge — they are the
reason PR #13's file is worth more than `holes`'s as an *artifact*, independent of which
entries win.

## Non-entry sections on `holes`

These are prose blocks, not IDed entries, and a diff-based merge will silently drop them:

* **"The Hole B route that survives round 1"** (line 290) — duplicated verbatim on PR #13
  at line 1289. Both copies are stale in the same way: step 1 says to port
  `TrueSRCycle.SignDirected`, which round 1 landed (`B-27`), and step 2 names
  `ss_three_glued_even_of_two`, the wrong flavour (`B-27`).
* **"Maintenance protocol"** (line 314) — the `[V]`/`[H]` protocol. Superseded in full by
  PR #13 §4, which is longer and grades honestly. Do not keep both.
* **"Durable Tier C work"** (line 615) — four unbuilt Tier C items. PORT; nothing on
  PR #13 carries them.
* **"WIP branch status"** (line 886) — a branch-status note, explicitly *not* a
  contribution. Do not port into the ledger; it belongs in the round's handoff.
* **"RULE (tier-wide, from A-41)"** (line 1021) — a negative result ships with its
  certification method. PORT; it is the sharpest process rule in either file and PR #13's
  P3 is its weaker sibling.

## Cross-reference: `adv-audit` (PR #14)

Three documentation defects `adv-audit` found are *ledger-relevant* and belong in the merged
file rather than only in `research/AUDIT.md`. All three re-verified here this session.

| claim | re-verified | where it belongs after the merge |
| --- | --- | --- |
| three docstrings cite `SrBlocks` / `SrProp510`, which exist nowhere | `grep -rn 'SrBlocks\|SrProp510' --include='*.lean' CRNT` → **3 hits, all prose**, at `TrueChemistrySRCriterion.lean:4016, 4069, 7093`; `grep -E '(theorem|lemma|def|structure|abbrev) (SrBlocks|SrProp510)'` → **0**. Matches PR #13 entry B18 verbatim. | merge with B18; the ledger entry is already right, the *docstrings* are what is broken |
| the Hole B flagship carries an undisclosed third hypothesis `hflow` | `stronglyConcordant_fullyOpen_of_trueSRCriterion` at `TrueChemistrySRCriterion.lean:8003-8006` takes `(hsep) (hflow : N.ZeroComplexReactionsAreFlows) (hSR)`; its docstring at `:7998-8002` names only reactant/product separation. | **this is the merge's most important single fact** — see below |
| `HighCodimensionSiphonFace.lean:73-76` makes a false axiom-hygiene claim | the block at `:73-77` asserts "No other declaration in the tree does"; `measure.py --no-gates` reports **2 executable `sorry`s** under `CRNT/`, one of them in the Hole B file, and `grep -rn '^\s*sorry\b' CRNT/` returns exactly those two `.lean` sites plus one hit in a non-Lean backup file (`CRNT/Equilibria/TreeConstants.lean.pre_matrix_tree_backup:140`, not a build target). The claim as written is false. | identical to `holes` **A-24**; port A-24 and let it carry the fix |

### Why `hflow` is the merge's load-bearing fact

Both ledgers describe Hole B's flagship as a two-hypothesis theorem (`hsep ∧ hSR`). It is
three. The third, `hflow`, is the reason `holes` **B-26** ("hole B has no witness") is a
statement about the *class* and not about a derivable side condition: PR #16's `flowN`
counterexample fails `hflow` and PR #16's `netN` fails `hsep`, so **no** network in the
tree satisfies `hsep ∧ hflow ∧ hSR`. Any merged ledger that describes the flagship as
`hsep ∧ hSR` will send the next researcher at a vacuous class without saying so.

Cross-referenced entries: `holes` **B-26** (PORT), **B-24** (`rr_gluable_arcs` — built for
the empty class, so it is vacuity-*safe*), **B-27**/**B-28** (arc builder, likewise), and
PR #13 **B17** (the superseded not-built claim) + **B18** (the phantom docstring names).

## Numbers in this file, and how to re-derive them

Everything below is emitted by the generator from `research/scripts/measure.py --no-gates`, so no count here is a hand-typed claim.

| metric | value | source |
| --- | --- | --- |
| executable `sorry`s under `CRNT/` | **2** | `measure.py --no-gates` |
| hole site | `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135` | `measure.py --no-gates` |
| hole site | `CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8607` | `measure.py --no-gates` |
| frontier modules | 844 | `measure.py --no-gates` |
| scaffold modules | 24 | `measure.py --no-gates` |
| Lean lines | 137502 | `measure.py --no-gates` |
| declared `axiom`s | 0 | `measure.py --no-gates` |

The two `hole_sites` are the frozen objective (`holes = 0`). They are listed here so a
reader of this file can see that the merge concerns the *record*, not the target.

## Recommended order of operations (for the human merge)

1. Take PR #13's `DEAD-ENDS.md` as the **base** — grading scheme, deduplication, §4
   protocol and `negative-checklist.md` are structural and exist nowhere else. This is a
   recommendation about *structure*, not about any entry; no entry is thereby resolved.
2. Port the **PORT** rows above, keeping their ids. **Renumber `A-40` (×2) on the way in**
   and preserve the distinction between `A-40a`/`A-40b`.
3. For each **CROSSREF** row, keep PR #13's text and add the `holes` id as an alias in the
   entry's `found-by` line. Do not paste both texts.
4. For **A-6** (the only `DIVERGES` among the round-1 entries): PR #13's §3b A-6 and its
   `P4` bullet 2 assert something `holes` **retracted**. Port the retraction, and delete the
   retracted claim rather than merging the two — a retracted false claim that survives in a
   new file is worse than the original error.
5. Keep `adv-negative`'s §3f (`C-1`…`C-5`) even though the dispute is settled: it is the only
   record of *why* the fork looked contested, and `H-3`'s `closure_minimal` subtlety is
   only legible against it.
6. Do **not** renumber the dashless `A1`…`A30` / `B1`…`B18`. Renumbering makes Hazard 1
   permanent instead of fixable.

---

Generated from `origin/holes:research/DEAD-ENDS.md` and `origin/research/adv-negative:research/DEAD-ENDS.md`.
Every `file:line` in this document was read in the generating session; the generator
refuses to emit if an id on either side has no row.
