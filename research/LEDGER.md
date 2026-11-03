# Swarm ledger

Objective: `research/scripts/measure.py` → `holes = 0`. Baseline at round 1:
`holes=2, frontier_mods=844, scaffold_mods=24, lean_lines=137502, score=-1301`.

Branch of record: `holes`. Swarm base: `research/swarm`. Worktrees:
`/Users/akutuva/Documents/Proofs/crnt-wt/<agent>`.

## Roster

### Tier A — Route Architects (own the mathematics)

| agent | slice | status |
| --- | --- | --- |
| `arch-fanface` | A: polytope / face-lattice architecture, weakest-satisfiable-hypothesis, witness construction | round 1 |
| `arch-fanfill` | A: recursive face fill, §7.4.3, well-foundedness | round 1 |
| `arch-delta` | A: δ-slack, Lemma 9.5/9.7, uniform-vs-combinatorial decay | round 1 |
| `arch-sr-case2` | B: A.6 Case-2 source-block datum, in-scope verdict | round 1 |
| `arch-sr-deg2` | B: degree-two isolation route, graph-theoretic statement | round 1 |
| `arch-alt` | both: alternative routes and legitimate restatement options | round 1 |

### Tier B — Formalization Engineers (own the proofs)

| agent | slice | status |
| --- | --- | --- |
| `form-fanface-core` | A: rational cones, faces, normal-cone construction | round 1 |
| `form-fan-incidence` | A: face lattice, common faces, strict rank decrease, ℝ/ℚ bridge | round 1 |
| `form-domination` | A: dominance ⇒ polarity; non-vacuous 2D witness | round 1 |
| `form-scales` | A: scale hierarchy arithmetic, uniform decay question | round 1 |
| `form-tiles` | A: tile covering, seam agreement, satisfiability verdict | round 1 |
| `form-barrier` | A: verify + complete the consumer chain; bridge-gap recheck | round 1 |
| `form-sr-hopp` | B: `hopp` / k=1 forcing lemma | round 1 |
| `form-sr-route` | B: species→reaction shortest-path machinery | round 1 |
| `form-sr-case2` | B: land the A.6 Case-2 datum with a derivation lemma | round 1 |
| `form-sr-deg2a` | B: degree-two case analysis, first half | round 1 |
| `form-sr-deg2b` | B: degree-two parity consequences | round 1 |
| `form-sr-parity` | B: general parity invariant + extension | round 1 |
| `form-scaffold` | both: three new CRNT concepts formalized | round 1 |
| `form-audit` | tooling: vacuity, statement-drift, axiom-scan, measure-diff | round 1 |

### Tier C — Infrastructure & Scaffolding (own the ground floor)

| agent | slice | status |
| --- | --- | --- |
| `infra-mathlib-poly` | A: empirical Mathlib convex-geometry survey + thin layer | round 1 |
| `infra-mathlib-fan` | A: pointed-fan API with constructed examples | round 1 |
| `infra-scaffold-crnt` | both: theorem index, glossary, duplication map, unformalized roadmap | round 1 |
| `infra-build` | both: transactional `close_hole.sh`, ledger reconciliation, `pr_score.py` | round 1 |
| `papers-craciun` | A: Craciun v3 full transcription with Lean notation map | round 1 |
| `papers-sf` | B+A: Shinar–Feinberg, Craciun–Fiebig–Singleton, Anderson–Shiu transcriptions | round 1 |

### Tier D — Adversaries & Verifiers (own honesty)

| agent | slice | status |
| --- | --- | --- |
| `adv-refute` | A: try to refute hole A's statement; small-instance search | round 1 |
| `adv-vacuity` | both: vacuous proofs, degenerate definitions, permanent non-vacuity tests | round 1 |
| `adv-negative` | both: dead-end ledger, evidence grading, negative checklist | round 1 |
| `adv-audit` | both: axiom audit of the two chains, statement-drift audit, ledger integrity | round 1 |

## Scoring (from `research/README.md` §5)

| event | points |
| --- | --- |
| a `sorry` eliminated, enclosing module elaborates | +100 |
| new machine-checked lemma on a route, used downstream | +25 |
| machine-checked refutation killing a route or statement | +30 |
| new machine-checked lemma on a route | +10 |
| route doc surviving adversary review | +12 |
| new consumable module, elaborating | +8 |
| lemma another researcher's PR builds on | +15 |
| no commit | 0 |
| introduced `sorry`/`axiom`/`admit` outside the holes | −60 |
| broke a static gate | −60 |
| silent hypothesis weakening | −200 |

Retirement rule: bottom 30% of the field at the end of each round is retired and re-seeded.

## Round log

### Round 1

Spawned all 30. Baseline `score=-1301`. Awaiting results.