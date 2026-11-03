# Ledger coverage: closing the gap `adv-audit` found

*(`infra-promote`. Appended sections are marked with their author; do not overwrite a section
someone else has added — add yours at the bottom.)*

`adv-audit` (PR #14) established two things and left one open:

1. **No wrongly-verified module exists.** `CRNT.lean`'s transitive closure is 701 modules and
   none carries a `sorry`, an `axiom` or an `admit`. All 846 `CRNT/` modules have an
   `.olean`. Exactly two carry a `sorry`, and both are correctly off-ledger — because a
   module with a `sorry` *elaborates*, with `sorryAx`, and putting it on the ledger would
   exclude it from the build.

The open item was the **coverage gap**: `check_exclusions.py` check 4 is vacuous against an
empty ledger, and 145 `CRNT/` modules are neither in the ledger nor reachable from
`CRNT.lean` — both holes among them — so no ledger invariant covers them.

This document states what should happen to those 145 modules, proves that check 4's vacuity is
correct rather than a bug, supplies the invariant that is *not* vacuous, and adds the two
checks that were missing. All four numbers are reproduced by
`python3 research/Audit/ledger_coverage.py` on `origin/holes` @ `90bddfc`.

| class | count | meaning |
| --- | --- | --- |
| **core** | 701 | reachable from `CRNT.lean` by `import CRNT…` lines |
| **frontier** | 0 | named in `scripts/unverified_modules.txt`; `excludeGlobs` of `CRNT` |
| **orphan** | 145 | on disk, in neither |

---

## 1. The coverage gap, and what should happen to an orphan

### 1.1 An orphan is not an unverified module

The three classes are disjoint and exhaustive over the 846 modules on disk. The trap is that
the two "not in the core" classes mean opposite things:

* a **frontier** module is excluded from `lake build CRNT` — Lean has never elaborated it;
* an **orphan** is elaborated by the `CRNT.+` glob and has an `.olean` right now — it is
  simply not reachable from `CRNT.lean`.

So an orphan is *not* a candidate for the ledger. Adding one to
`scripts/unverified_modules.txt` would remove a working module from every build target in the
tree (`research/README.md` §7) — the exact edit two round-1 researchers proposed and both were
wrong to propose. `ledger_coverage.py` therefore never suggests it.

### 1.2 The disposition

An orphan is a module nobody has decided anything about, and that is the defect. The two
available decisions are:

* **import it** — add an `import` line to `CRNT.lean`. This is free, needs no ledger edit and
  no generator run, and it converts the module to *core*, where C3 then covers it. This is the
  right default for any module that is genuinely part of the library.
* **record why it stays out** — an orphan that is deliberately not in the umbrella (dead code,
  an example, a diagnostic) should be recorded, so that its later disappearance or its
  acquisition of a `sorry` is a decision rather than an accident.

`ledger_coverage.py` enforces only the *mechanical* half of this (C5): the orphan set may
shrink, never grow, against `research/Audit/orphan_baseline.txt` = 145. A module leaving the
umbrella closure with nobody recording the decision fails the check. It does **not** attempt to
decide the 145 individually — that is a judgement call per module, and an audit that guesses
at it is worse than one that reports it.

What the audit *does* decide is the part that is mechanical: **of the 145 orphans, exactly
three carry `sorryAx`**, and they are named in `research/Audit/known_holes.txt`. The other 142
are clean and belong in the umbrella or in a recorded decision.

### 1.3 The three sorryAx-carrying orphans

```
CRNT.Dynamics.HighCodimensionSiphonFace       declares sorry   (Hole A, :135)
CRNT.Multistationarity.TrueChemistrySRCriterion declares sorry  (Hole B, :8607)
CRNT.Dynamics.GlobalAttractorTheorem          USES Hole A's holed declaration
```

The third is new here and is the reason C4 exists in this form. `GlobalAttractorTheorem.lean`
contains **zero** `sorry` of its own (`grep -c sorry` → 0, read this session) and is 2000+
lines of proved mathematics — but at `:1555`, inside `complexBalanced_genuinePermanent`
(header `:1490`), it does:

```lean
exact N.exists_positive_omegaPoint_of_highCodimension_siphonFace κ hxs hcb
```

which is Hole A's `sorryAx`. A per-file syntactic scan cannot see this: the file is clean, and
so is every other module that merely *imports* Hole A. Seven other modules import one of the
two holes; of those, five use a holed declaration and three (`GlobalAttractorSpecialCases`,
`CodimTwoFaceModel`, `OmegaPointFakeFlow`) do not — they import the hole without depending on
the holed name, and are clean. Distinguishing those two cases requires tracking *which
declarations* are holed, not which files are.

---

## 2. Check 4 is vacuous, and that is correct

`check_exclusions.py` check 4 is:

```python
reachable = transitive_imports("CRNT.lean")
leaked = sorted(set(ledger) & reachable)
```

With `ledger = ∅` this computes `∅ ∩ reachable = ∅` for **every** tree. It cannot fail, so it
is not a check. Two questions follow: is the vacuity a bug, and what should replace it.

### 2.1 Why the vacuity is correct

The check encodes *"the verified core does not depend on unverified source"*, where
"unverified" is defined as **"named in the ledger"**. That definition is right for what the
ledger is: `scripts/unverified_modules.txt` is a list of modules Lean has never successfully
elaborated, it becomes `excludeGlobs`, and a module on it is excluded from the build.

But a hole-bearing module is not that. It **elaborates** — with `sorryAx` — which is why both
holes are correctly off-ledger and have been all along. So while the ledger is empty, its set
is empty, and "no core module is on it" is a tautology rather than evidence. The vacuity is
not a defect in check 4; it is the ledger answering a question about exclusions when the
question that actually matters is about holes. `research/tooling.md` (infra-build) already says
this — *"the ledger cannot detect holes, by construction"* — and the gap is that nothing
supplies the missing question.

Note the converse, which is the real hazard: adding Hole A's module to the ledger would make
check 4 *fire*, and would be a false positive — it would exclude a module that elaborates, and
drag 3 more modules out of `lake build CRNT` with it (`gen_lakefile.py`'s `validate()` refuses
exactly that transitive hiding).

### 2.2 The invariant that is not vacuous

C3 replaces it:

> **C3. No module reachable from `CRNT.lean` carries `sorryAx`, by declaration or
> transitively.**

Both operands are non-empty on `holes`: 701 core modules, 3 tainted modules, intersection 0.
It is strictly stronger than check 4 — it is check 4's question ("does the core depend on
something untrustworthy?") asked about the right set.

**When is C3 vacuous?** Exactly when nothing on disk carries `sorryAx`. Call that condition
`Z`. Then:

* `Z` ⇒ the tainted set is empty ⇒ `core ∩ tainted = ∅` for every `core`, so C3 is vacuous;
* `Z` ⇒ no module declares a `sorry`, `admit` or `axiom` (that is how the tainted set is
  seeded) ⇒ no module can *use* a holed declaration, because there are none (that is how it is
  propagated) ⇒ the tainted set is empty.

So **C3 is vacuous ⟺ no hole exists ⟺ the swarm's objective `holes = 0` is met.** Its
vacuity condition is the goal condition. That is the strongest statement available: C3 cannot
be vacuous while the work remains, and it stops mattering exactly when the work is done. Check
4's vacuity condition, by contrast, is "the ledger is empty", which is unrelated to the
objective and happened to arrive early.

### 2.3 The negative result is certified, not asserted

A check that has never failed is indistinguishable from a check that cannot fail.
`--selftest` proves C3 has teeth: it copies the tree to a temp directory, appends

```lean
theorem mutationTestOnly : 0 = 1 := by sorry
```

to a core module with zero CRNT importers, and requires C3 to report it. Observed:

```
baseline: core=701 tainted=3 problems=0
victim: CRNT.Algebra.PositiveTorusIdeals
mutated: core=701 tainted=4 problems=1
C3 fires on the injected module: True
```

So "no wrongly-verified module exists" is a **certified negative result**: search space = the
846 modules on disk; arithmetic = none (set membership on exact module names); unsearched =
anything requiring elaboration (`native_decide` over a non-`Decidable`, a `sorry` hidden in a
macro-generated declaration, a hole whose `sorryAx` is reached through a `Decidable` instance
rather than a name) — which is precisely the residue `#print axioms` covers and a text scan
does not.

---

## 3. The vacuous-by-empty-argument shape (`check_vacuity_shape.py`)

`adv-vacuity` (PR #16) found that `DifferentialInclusion.Field E := E → Set E`
(`CRNT/Dynamics/DifferentialInclusion.lean:43`, read this session) has **no nonemptiness
requirement**, so all four `ForwardInvariant` conclusions in `PolyhedralBarrier.lean` are
obtained for free by instantiating `F := fun _ => ∅`. Machine-checked there as
`forwardInvariant_vacuous_for_empty_field`.

That is a *semantic* finding. The tooling gap is that **nothing would have found it**, and
nothing will find the next instance. `check_vacuity_shape.py` screens for the shape statically,
with no `lean` and no `.olean`:

1. find **set-valued maps** — `def`/`abbrev` whose body is a function type ending in `Set`
   (the whole tree has exactly one: `Field`);
2. for each theorem/lemma mentioning one, find a **binder** over it (`{F : …Field E}`) and
   confirm the statement **quantifies over the map's values** (`∀ c ∈ F y, …`);
3. report those with **no emptiness guard** anywhere in the statement.

Observed on `holes`: 1 set-valued map, 7883 statements examined, 26 hits, 26 unguarded. The
four the brief names are all present, at the lines I read myself:

```
CRNT.Geometry.PolyhedralBarrier : 317  forwardInvariant_barrierSublevel
CRNT.Geometry.PolyhedralBarrier : 341  forwardInvariant_of_cone_descent
CRNT.Geometry.PolyhedralBarrier : 364  forwardInvariant_of_polar_descent
CRNT.Geometry.PolyhedralBarrier : 491  forwardInvariant_minMaxSublevel
```

**A bug worth recording.** The first version of this scan matched only the bare name `Field`
and consequently reported **19** hits and missed all four target theorems, because every one of
them writes the binder *fully qualified* (`{F : DifferentialInclusion.Field E}`,
`PolyhedralBarrier.lean:318`). A screen that misses the case it was written for is worse than
no screen, and it failed silently. Fixed by matching an optional dotted prefix; the number went
19 → 26 and the four appeared. This is the `adv-audit` lesson in miniature: the check was
written from the report, not from the source.

**This is a screen, not a verdict, and exits 0 by design.** A hit means "a reader must confirm
this is load-bearing" — `forwardInvariant_inter` and `IsInclusionSolution.mono` are *not*
defective, they are closure properties that genuinely hold for every field including `∅`.
Making them CI-red would train people to ignore it. What it does not decide is stated in its
own `--help`: whether a theorem is *actually* vacuous (needs an inhabitedness proof); maps
written with an inline `Set` binder rather than a synonym (not matched); obligations discharged
by `variable` or a section (invisible to text); and `Finset`/`List`/`Option`-valued maps (out
of scope by construction, though they have canonical empty values too).

---

## 4. `close_hole.sh` must catch a hole-free module that imports something unverified

Step 2 runs `#print axioms` on **one named theorem**. That is the right granularity for "is
this proof axiom-clean" and the wrong one for "is this module trustworthy": `#print axioms`
reports the axiom closure of the named declaration *only*. A module that imports a hole and
uses a holed declaration therefore reports **clean** for every theorem that does not happen to
touch that declaration — which, in a 2000-line module, is nearly all of them.

`CRNT.Dynamics.GlobalAttractorTheorem` is the live instance: hole-free in isolation, 1490-line
`complexBalanced_genuinePermanent` resting on Hole A's `sorryAx` at `:1555`. Closing Hole A and
running `close_hole.sh` on a *different* theorem of that module would pass step 2 and report
the hole closed.

**Step 2b**, added between step 2 and step 3:

```sh
step "2b. transitive sorryAx of $MODULE"
if "$PY" research/Audit/ledger_coverage.py --module "$MODULE_PATH"; then
  record "transitive-sorryAx" "PASS"
else
  fail "the module (not just $THEOREM) is sorryAx-contaminated -- see step 2b above" \
       "transitive-sorryAx"
fi
```

It is a pure source-graph query: no `lean`, no `.olean`, ~10 s. Observed both directions:

```
$ … --module CRNT/Dynamics/GlobalAttractorTheorem.lean
  FAIL: carries sorryAx
    uses CRNT.Dynamics.HighCodimensionSiphonFace.exists_positive_omegaPoint_of_highCodimension_siphonFace
$ echo $?
1
$ … --module CRNT/Dynamics/ZeroSeparating.lean
  ok: no sorryAx in this module or its transitive import closure (1 CRNT modules)
  in the CRNT.lean closure
$ echo $?
0
```

`research/Audit/close_hole_2b.diff` carries the patch against
`origin/research/infra-build:scripts/close_hole.sh`. **infra-build owns `close_hole.sh` and
the four gates, so this is a proposal for their branch, not a fork.** The new query is a
standalone script in `research/Audit/` and does not touch `gen_lakefile.py`, `check_exclusions.py`
or `lakefile.toml`; applying the diff is a one-line `git apply`.

---

## 5. Why this does not fork the tooling

`infra-build` owns the generator and the four gates. The division here:

* **untouched**: `scripts/gen_lakefile.py`, `scripts/check_exclusions.py`,
  `scripts/close_hole.sh`, `lakefile.toml`, `CRNTFrontier.lean`,
  `scripts/unverified_modules.txt`, `scripts/unverified_baseline.txt`.
* **new**: three files under `research/Audit/` (inert — no build target reads them) and two
  inert manifests beside them.
* **proposed**: one `git apply`-able diff adding a step to `close_hole.sh`.

The gate that *should* absorb C3 permanently is `check_exclusions.py`, which already owns the
ledger invariants; wiring C3 in there is infra-build's call, and the audit is written to be
importable (`ledger_coverage.audit()` returns a dict) for exactly that.

`research/Audit/known_holes.txt` is deliberately **not** `scripts/unverified_modules.txt` and
must never be made to be it. It is inert; the ledger is `excludeGlobs`. Listing
`GlobalAttractorTheorem` — which elaborates — on the ledger would remove three working modules
from every build target to hide a hole the ledger cannot represent.

---

## 6. Reproducing

```sh
python3 research/Audit/ledger_coverage.py              # classification + C2/C3/C4/C5
python3 research/Audit/ledger_coverage.py --selftest   # mutation test: C3 has teeth
python3 research/Audit/ledger_coverage.py --module CRNT/Dynamics/GlobalAttractorTheorem.lean
python3 research/Audit/check_vacuity_shape.py          # vacuous-by-empty-argument screen
python3 research/Audit/check_vacuity_shape.py --explain CRNT.Geometry.PolyhedralBarrier
python3 research/Audit/ledger_integrity.py             # adv-audit's original audit (PR #14)
```

Every number quoted above was produced by running these on `origin/holes` @ `90bddfc`. Nothing
here was run against a stale checkout, and no `lake build` was invoked.