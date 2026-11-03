# Tooling: certifying a closed hole

*(`infra-build`. Appended sections are marked with their author; do not overwrite a
section someone else has added — add yours at the bottom.)*

Closing one of the two holes is not one edit. It is a reconciliation of six things that
are only correct together, and every one of them used to be a manual step, in a specific
order, that nobody wrote down:

1. the affected modules elaborate, in dependency order;
2. the theorem's axiom set is a subset of `{propext, Classical.choice, Quot.sound}`;
3. `scripts/dump_sorries.py` agrees the hole is gone;
4. `scripts/unverified_modules.txt` no longer lists the module;
5. the *generated* files (`lakefile.toml`, `CRNTFrontier.lean`, `scripts/frontier_history.txt`)
   match the ledger, and the four static gates are green;
6. `lake build CRNT` is green.

Do them in the wrong order and the result is a tree that looks green locally and fails in
CI, or worse, one that drops a module out of a build target without anybody noticing. The
commands below make the whole sequence one command, and make the interesting cases fail
loudly.

---

## Ledger semantics — the trap that cost the round most

`scripts/unverified_modules.txt` is **not** a registry of interesting modules, of frontier
candidates, or of things you want built. It is a list of modules **Lean has never
successfully elaborated**, and it becomes `excludeGlobs` of the `CRNT` library.

So listing a hole-free module there *removes it from `lake build CRNT`*, and it stops being
elaborated by `CRNTFrontier` too. Nothing fails loudly: you have taken a working module out
of every build target in the tree and the build is still green. Two researchers proposed
exactly this edit during round 1 (to "keep a module in the frontier" and to "keep a
semantically-defective module in the build"), and both were wrong for the same reason.

What happens for free, with no ledger edit and no generator run:

* A new file under `CRNT/` is picked up automatically. The verified library's globs are
  `["CRNT", "CRNT.+"]` — pattern-based, not enumerated — so a new module is in
  `lake build CRNT` the moment it exists on disk.
* Not appearing in `CRNTFrontier.lean` is **not** lost coverage. That target is the set of
  modules that have ever failed to elaborate; it is a diagnostic, not a build.
* To reach the verified **umbrella**, add an `import` line to `CRNT.lean`. That is an
  import, not a ledger line.
* `scripts/gen_lakefile.py --add M` is correct in exactly one case: you added a module and
  `lake build` genuinely cannot elaborate it yet (a stub, or it depends on an unproved
  hole). It refuses to write if the entry would transitively hide anything.

Never hand-edit `lakefile.toml` or `CRNTFrontier.lean`. Run
`python3 scripts/gen_lakefile.py` and commit the result; `--check` is now a CI step.

### The corollary that matters more

**The ledger cannot detect holes.** A hole-bearing module still *elaborates* — it elaborates
*with* `sorryAx`. Both holes are off-ledger by construction, and have been all along.

Three consequences, all of which this tooling is built around:

1. **`lake build` green is not evidence of anything on this tree.** Every module
   elaborates; two of them carry `sorryAx`.
2. **Frontier membership is not evidence about elaboration either**, in either direction.
   "It's on the frontier, so it doesn't build" and "it's on the frontier, so it carries a
   `sorry`" are both invalid inferences. The frontier is "modules the `CRNTFrontier` target
   has ever covered", which is not the same question.
3. **The real signals are `scripts/dump_sorries.py` and the transitive `#print axioms`
   check.** `#print axioms` reports the whole axiom closure of a declaration, not just its
   own proof, so it is also the strong version of the hole check: it catches a module that
   is clean in isolation but imports something unverified. That is exactly the trap
   `CRNT.Multistationarity.TrueChemistrySRCriterion` sets for any file that must not import
   it (ledger entry B-11).

`close_hole.sh` treats `dump_sorries.py` as the primary signal and the ledger step as the
follow-up, for this reason.

---

## `scripts/close_hole.sh <Module.lean> <TheoremName>`

```sh
scripts/close_hole.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean \
    exists_positive_omegaPoint_of_highCodimension_siphonFace
```

Runs all seven steps and prints one PASS/FAIL summary. **Transactional**: it snapshots the
ledger, the growth baseline, the frontier history, `CRNT.lean`, `lakefile.toml` and
`CRNTFrontier.lean` up front and restores the snapshot on *any* failure, so a failed run
leaves the tree exactly as it found it. It never commits — review the diff and commit it.

| flag | effect |
| --- | --- |
| `--no-build` | skip step 7's full `lake build CRNT`. **Researchers must use this**: a full build from a worktree destroys the round for everyone. A run with `--no-build` reports that step as `SKIP` and says in its summary that it does not certify the full build. |
| `--all-deps` | re-elaborate the whole transitive CRNT import closure instead of only what is not already built. |

`MAX_REBUILD` (environment, default 32) caps step 1. When more modules than that need
elaborating, the shared build cache has fallen behind the branch and rebuilding is a *full
build* — the orchestrator's job, not this command's — so it refuses and says exactly that
instead of silently elaborating 162 modules.

Step 1 is incremental. A module is re-elaborated when

* it is the module under certification (always — step 2 has to import the *current*
  source, and a shared-cache `.olean` built from an older revision would certify a theorem
  that is not the one on disk);
* its source is modified or untracked relative to `HEAD` and some `.olean` for it predates
  the edit; or
* it, or anything below it in the import graph, has no `.olean` in the worktree or the
  shared cache. That last clause is what makes the command self-diagnosing when the cache
  lags: without it, a missing dependency surfaces as a bare `object file ... does not
  exist` for an unrelated module several steps down the graph.

Wall-clock mtimes alone are the wrong test — on a fresh checkout every source is newer than
every `.olean` in the cache, so an untouched tree looks entirely stale and the command would
re-elaborate hundreds of modules before checking anything. Git knows which sources actually
differ; that is the only thing that should force a rebuild.

Step 4 is the only place in the repository permitted to **lower**
`scripts/unverified_baseline.txt`, the high-water mark the growth guard compares against.
See "Why `promote.py` no longer lowers it" below.

### Runtime

Importing a CRNT module means loading its entire `.olean` closure. Budget **minutes**, not
seconds: on this tree the `#print axioms` probe alone took 6–10 minutes, dominated by I/O
(`sys` ≫ `user`). `scripts/check_axioms.py` invokes `lean` directly with a hand-assembled
`LEAN_PATH` rather than through `lake env`, because `lake env` re-resolves the workspace on
every call; `--lake-env` restores the `checkmod.sh` behaviour.

---

## `scripts/check_axioms.py <Module.lean> <TheoremName>`

The `#print axioms` check `test/AxiomAudit.lean` pins for the headline results, as a tool you
can point at any declaration:

```sh
python3 scripts/check_axioms.py CRNT/Dynamics/HighCodimensionSiphonFace.lean \
    exists_positive_omegaPoint_of_highCodimension_siphonFace
```

* Exit 0 only if the declaration resolved **and** its axiom list is a subset of
  `propext, Classical.choice, Quot.sound`.
* A `sorry` in the proof is **not** a special case: Lean reports `sorryAx`, which fails the
  subset test. An `axiom` declared in a dependency surfaces under its own name, likewise.
* Names may be bare or fully qualified; a bare name is resolved against the file's own
  `namespace` stack, because every declaration here worth certifying lives in a namespace
  and an `unknown identifier` failure would be misread as "the check is broken".
* "the module has no `.olean`" is reported as an *environment* problem with its own
  message, not as an axiom failure — the two send you to completely different places.

---

## `scripts/gen_lakefile.py`

Generates **both** `lakefile.toml` and `CRNTFrontier.lean` from
`scripts/unverified_modules.txt` (the ledger). Edit the ledger; never the generated files.

```sh
python3 scripts/gen_lakefile.py                 # regenerate
python3 scripts/gen_lakefile.py --check         # CI: exit 1 if stale, write nothing
python3 scripts/gen_lakefile.py --add MODULE    # record a module Lean has never checked
python3 scripts/gen_lakefile.py --remove MODULE # retire one out of the ledger
python3 scripts/gen_lakefile.py --print         # dump the frontier set
```

### What changed, and why

**The frontier is `ledger ∪ history`, not `ledger`.** There are now two lists.
`scripts/unverified_modules.txt` is the *active* frontier — modules Lean has never
elaborated. `scripts/frontier_history.txt` is append-only and records every module the
`CRNTFrontier` target has ever covered. `CRNTFrontier.lean` is generated from the union.

The old pipeline had a bug here that no gate could see: `scripts/promote.py` *deleted* a
promoted module's `import` from `CRNTFrontier.lean`. So the moment a module became verified,
it stopped being elaborated by `lake build CRNTFrontier` and stopped contributing to the
frontier error count that CI reports — the metric went quiet on exactly the modules that had
just improved. With the union, a module leaves the ledger and lands in the history instead,
and the count is monotone.

**A newly added `CRNT/` file can no longer be silently excluded.** Lake's globs are
hierarchical: `excludeGlobs = ["CRNT.Foo"]` drops every `CRNT.Foo.*` too. So listing
`CRNT.Foo` on the ledger removes a whole namespace from the verified `CRNT` target, and
because those submodules are not themselves on the ledger they are not in the frontier
globs either — they are in **no** build at all, and nothing fails. `gen_lakefile.py` now
refuses to write when a ledger entry transitively hides a file that is not itself listed,
and names the culprit for each:

```
::error::these CRNT/ files are excluded transitively by a ledger entry but are not on
the frontier target, so no build elaborates them -- list each one in
scripts/unverified_modules.txt (or narrow the entry): CRNT.Examples.CatalyticChain
(hidden by CRNT.Examples), ...
```

It also rejects duplicate ledger entries, ledger or history entries with no file on disk, and
— as a backstop — regenerates nothing at all if validation fails.

**`--check` writes nothing.** `scripts/check_exclusions.py` previously *regenerated* the
lakefile as a side effect of testing it, so a gate would silently repair a hand-edited
lakefile and then report `ok`; the drift was fixed locally, merged as a no-op, and the next
checkout broke again. The gate now calls `gen_lakefile.py --check` and is read-only.

### CI

`.github/workflows/ci.yml`'s static job runs, before the exclusion audit:

```yaml
- name: Generated files in sync with the ledger
  run: python3 scripts/gen_lakefile.py --check
```

---

## `scripts/pr_score.py <base-ref> <head-ref>`

```sh
python3 scripts/pr_score.py holes research/form-sr-deg2a
python3 scripts/pr_score.py holes HEAD --json
python3 scripts/pr_score.py holes HEAD --no-gates      # ~8s instead of ~30s
```

Exports both refs with `git archive` into a temp directory (no worktree, no checkout, no
interference with anything else running against the repo), runs `research/scripts/measure.py`
on each **in parallel**, diffs the metrics, and prints the `research/README.md` §5 scoring
table restricted to what a script can decide. The metric script comes from the head ref when
it has one — scoring two refs with two different metric scripts would confound the comparison
— and the choice is printed.

Three deliberate choices:

* **Holes are diffed by enclosing declaration, not by `(file, line)`.** Inserting a lemma
  above a hole shifts every line below it, and a line-based diff reports that as *one hole
  closed and one hole opened* — a mechanical false positive that gets a correct hole-closing
  PR thrown out. Declared names are namespace-qualified for the same reason. Verified on a
  fixture: a PR that only inserts a lemma above the hole now scores 0, not +40 net.
* **Hole statements are compared textually.** A PR that closes a hole by deleting a
  hypothesis moves `holes` and would otherwise look like the best submission of the round.
  Every declaration in a hole-carrying file is extracted and compared after whitespace
  normalisation; a change to the hole's *own* declaration scores the −200 rule, and a change
  to a neighbouring one is named at zero points, because adding a lemma next to a hole is
  normal work and silently editing one is not.
* **Judgement calls are left unscored.** "Survives adversary review", "used downstream" and
  friends are listed as `unscored` rather than guessed at, so the printed total is a floor
  and not a fiction. The `+100` per `sorry` eliminated is likewise labelled as needing
  `close_hole.sh` certification — `measure.py` cannot see whether the enclosing module still
  elaborates axiom-cleanly, and that is the whole content of the rule.

It also diffs counts of `admit`, `native_decide`, `@[implemented_by]` and declared
`axiom`/`constant` between the two trees, and applies the −60 rule to any increase.

---

## Why `scripts/promote.py` no longer lowers the baseline or edits the frontier

Two bugs in `promote.py`, both of which quietly destroyed a guard rail:

* it rewrote `scripts/unverified_baseline.txt` to the post-promotion ledger size. The
  baseline is the high-water mark the growth guard compares against, so auto-lowering it
  means a promotion can be undone by re-adding the same number of excluded modules, and
  `check_exclusions.py` reports `ok`. `promote.py` now leaves the baseline alone; only
  `close_hole.sh`, which additionally certifies the axioms and the build, lowers it.
* it deleted the promoted module's `import` from `CRNTFrontier.lean` (see above).
  `CRNTFrontier.lean` is generated now, and a graduating module moves to the history.

`promote.py` also no longer re-imports a module that `CRNT.lean` already reaches, which used
to produce a duplicate `import` line.

---

## Known limitation: `Scaffold/` is in no build target

`lakefile.toml` has no `lean_lib` for `Scaffold/`, so a module under `Scaffold/` is not
elaborated by any `lake build` target and cannot regress CI — but it also cannot be
*certified* by CI. "Elaborates" for a `Scaffold/` module means somebody ran
`research/scripts/checkmod.sh` on it by hand.

That is a deliberate gap, not an oversight to route around: several dozen `Scaffold/`
modules in flight this round do not elaborate, so adding `Scaffold` to `defaultTargets`
would turn CI red for reasons that have nothing to do with the holes. When the scaffolding
settles, the fix is one `[[lean_lib]]` stanza in `gen_lakefile.py` plus a decision about
whether it belongs in `defaultTargets`.

---

## What a merge should look like

```sh
scripts/close_hole.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean \
    exists_positive_omegaPoint_of_highCodimension_siphonFace
git --no-pager diff --stat
git add -A && git commit -m "close hole A"
python3 scripts/pr_score.py holes HEAD
```

Step 7 (`lake build CRNT`) is the orchestrator's or the human's, not a researcher's. A
researcher runs `close_hole.sh --no-build` and says so in their report.
