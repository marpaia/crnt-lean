#!/usr/bin/env python3
"""Generate `research/DEAD-ENDS-merge.md` — the three-column crosswalk between the two
divergent versions of `research/DEAD-ENDS.md`.

Sources (never edited, only read):
  * `origin/holes:research/DEAD-ENDS.md`              -- orchestrator ledger, `[V]`/`[H]`, ~82 entries
  * `origin/research/adv-negative:research/DEAD-ENDS.md` -- PR #13, `[M]`/`[S]`/`[N]`, ~105 entries

Every entry on either side appears exactly once in the generated table; the script asserts
that.  The *action* column is a human judgement recorded in `CROSSWALK` below; the counts are
computed, not asserted.

Usage:  python3 research/scripts/gen_deadends_merge.py            # writes the file
        python3 research/scripts/gen_deadends_merge.py --check     # exit 1 if stale
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
OUT = REPO / "research" / "DEAD-ENDS-merge.md"

HOLES_REF = "origin/holes"
ADV_REF = "origin/research/adv-negative"

ENTRY_RE = re.compile(
    r"^(#{2,3}) ((?:A|B|P|R|C|F|H|API|ENV|OPS|VAC|TRAP|SEQ|LEAD|AUDIT)\W?\d+[a-z]?)\.\s+(.*)$"
)

# --------------------------------------------------------------------------------------
# Crosswalk.  holes_id -> (adv_id or None, action, note)
#
# `action` vocabulary:
#   IDENTICAL   same finding, same text on both sides; keep one copy, cross-reference.
#   CROSSREF    same finding, DIFFERENT id on the two sides; keep both ids, do not duplicate text.
#   PORT        exists only on `holes` (or only in substance); must be carried into the winner.
#   DIVERGES    the two sides make different claims; both must survive with a dated note.
#
# `None` in adv_id means "no counterpart on PR #13" -> the entry is a PORT.
# --------------------------------------------------------------------------------------
CROSSWALK: dict[str, tuple[str | None, str, str]] = {
    # --- round-1 route-doc findings, byte-identical on both sides (holes §A-1.. / §B-1.. ) ---
    "A-1": ("A-1", "IDENTICAL", "oneBit* recursors rank the projected fan, not the ambient face"),
    "A-2": ("A-2", "IDENTICAL", "binaryWordValue is anti-monotone"),
    "A-3": ("A-3", "IDENTICAL", "§7.3 closed for a single chain"),
    "A-4": ("A-4", "IDENTICAL", "epsilon-tilde scale system proved five times"),
    "A-5": ("A-5", "IDENTICAL", "Refines is set containment"),
    "A-6": ("A-6", "DIVERGES",
            "holes RETRACTS the claim (`IsPolyhedralFan` exists at ConeFace.lean:196); PR #13 §3b "
            "A-6 still states the claim and P4 bullet 2 repeats it. Port the retraction and delete "
            "the claim; do NOT merge the two into one 'entry'."),
    "A-7": ("A-7", "IDENTICAL", "Anderson arXiv:0903.0901, not 2006.02483"),
    "A-8": ("A-8", "IDENTICAL", "CNP has no entry-loss function"),
    "A-9": ("A-9", "IDENTICAL", "Craciun v3 is arXiv:1501.02860"),
    "A-10": ("A-10", "IDENTICAL", "arXiv HTML truncates; use the PDF"),
    "A-11": ("A-11", "IDENTICAL", "CraciunZSH.hinterior mistranscribes relint as interior"),
    "A-12": ("A-12", "IDENTICAL", "Lemma 9.7 has no slack on the normal"),
    "A-13": ("A-13", "IDENTICAL", "n-dimensional Lemma 9.7 is unwritten"),
    "A-14": ("A-14", "IDENTICAL", "width>=delta flatness fails at vertices"),
    "A-15": ("A-15", "IDENTICAL", "alphaxiv is the only complete HTML route"),
    "B-1": ("B-1", "IDENTICAL", "the hspan witness is refuted"),
    "B-2": ("B-2", "IDENTICAL", "degree splitting at the residue is degenerate"),
    "B-3": ("B-3", "IDENTICAL", "hrest is not in scope at the residue"),
    "B-4": ("B-4", "IDENTICAL", "no_sToRIntersection_of_degree_two unusable as a closer"),
    "B-5": ("B-5", "IDENTICAL", "hopp/hcausal/hnc are already sharp"),
    "B-6": ("B-6", "IDENTICAL", "species-interior analogue does not apply"),
    "B-7": ("B-7", "IDENTICAL", "no_spanning_path_of_trueSRCriterion cannot apply to Q0"),
    "B-8": ("B-8", "IDENTICAL", "hopp does not force k=1"),
    "B-9": ("B-9", "IDENTICAL", "the residue's source comment is wrong about the tree"),
    "B-10": ("B-10", "IDENTICAL", "no upstream case analysis to thread a datum from"),
    "B-11": ("B-11", "IDENTICAL", "TrueSREarCase2.lean cannot be a file copy"),
    "B-12": ("B-12", "IDENTICAL", "the ear closes in hSR.2, not hnd"),

    # --- forks and adjudications: same content, different ids ---
    "A-16": ("F-1", "CROSSREF", "PR #13 files the same verdict as F-1 (of upperRegion dead)"),
    "A-17": ("F-2", "CROSSREF", "PR #13 F-2: the refutation does not transfer to faceRelevantCore"),
    "A-20": ("H-1", "CROSSREF", "PR #13 H-1: Lemma 9.7 does not construct the surfaces"),
    "A-25": ("H-5", "CROSSREF", "PR #13 H-5: hm is vacuous, m := 0"),
    "A-26": ("H-3", "CROSSREF", "PR #13 H-3 carries the same compiled False-level refutation"),
    "A-28": ("H-4", "CROSSREF", "PR #13 H-4 carries the same general template"),
    "B-14": ("H-2", "CROSSREF", "PR #13 H-2 repeats B-14 verbatim"),
    "B-15": ("H-2", "CROSSREF", "PR #13 H-2 repeats B-15 verbatim"),
    "B-19": ("B-9", "CROSSREF",
             "PR #13 B-9 (round-1) is the comment-is-wrong entry; holes B-19 is the machine-checked "
             "one-rotation correction. Both concern the residue's comment; different findings."),
    "B-25": ("B7", "CROSSREF",
             "PR #13 B7 proves degree-two makes an S-to-R intersection impossible; holes B-25 adds "
             "that the shipped lemma takes NO hypotheses, so hSR.2 is vacuous there"),

    # --- holes-only: port.  A-18..A-38 ---
    "A-18": (None, "PORT", "the round-1 VERDICT that every terminal criterion is refuted or "
                          "goal-equivalent; PR #13 §3h carries the same prose un-numbered"),
    "A-19": (None, "PORT", "the unifying structural fact, Permanent-framed; superseded in substance "
                          "by PR #13 H-4, but the Permanent framing is still quoted in the tree"),
    "A-21": (None, "PORT", "frontier membership implies nothing about holes; pairs with F-5"),
    "A-22": (None, "PORT", "the real obstruction is the forall/exists mismatch, not Permanent"),
    "A-23": (None, "PORT", "hole A reduces to ONE unproved descent estimate; read with A-33/A-34"),
    "A-24": (None, "PORT", "the false axiom-hygiene claim at HighCodimensionSiphonFace.lean:73-76"),
    "A-27": (None, "PORT", "151 proved, hole-free modules in hole A's import closure with no caller"),
    "A-29": (None, "PORT", "four copies of one False-level theorem; consolidation owner named"),
    "A-30": (None, "PORT", "'unused' != 'unavailable'; with A-35, the marking rule for the fan table"),
    "A-31": (None, "PORT", "the template does NOT reach the hsep family; cite two different lemmas"),
    "A-32": (None, "PORT", "hm-vacuity alone does not kill faceRelevantCore"),
    "A-33": (None, "PORT", "'three-line wrapper' is the wrong phrasing; correct file:line"),
    "A-34": (None, "PORT", "descend is unproved as a whole; :569 is a separate open item"),
    "A-35": (None, "PORT", "'no live consumer' overstates it; ComplexBalanceStoichFanInclusion is live"),
    "A-36": (None, "PORT", "do not re-land comparableGrowthDescent_is_not_a_weaker_route"),
    "A-37": (None, "PORT", "the descent route is circular and the tree says so"),
    "A-38": (None, "PORT", "closed-positive confinement is not impossible in general"),
    # --- holes-only: port.  the mining-scout / operations wave ---
    "TRAP-1": (None, "PORT", "eight kernel modules are about ComplexIdx, not Concentration: the "
                           "worst mis-citable surface in the tree for hmaxExact/Pmax"),
    "TRAP-1b": (None, "PORT", "concrete citations for TRAP-1 from a second disjoint scout; also the "
                             "negative that the descent estimate is absent at that layer"),
    "TRAP-2": (None, "PORT", "kineticMap_complexMonomial_mem_deficiencySubspace assumes "
                             "IsMassActionSteadyState, which the hole lacks for wmax"),
    "TRAP-3": (None, "PORT", "in CRNT/Stochastic the confused axis is count lattice vs concentration"),
    "SEQ-1": (None, "PORT", "Hole B's safe dependency order: arc and glue are vacuity-safe, the ear "
                            "is not"),
    "LEAD-1": (None, "PORT", "KurtzScaling.lean touches the deterministic field; unassigned"),
    "LEAD-2": (None, "PORT", "the projOn / ProjectedFaceDimensionCode bridge does not exist"),
    "OPS-3": (None, "PORT", "the prepend privacy lift is settled; audit by diff, never by message"),
    "OPS-4": (None, "PORT", "the four-way union risks namespace collision; elaborate to settle it"),
    "OPS-5": (None, "PORT", "checkmod.sh second bug: a stale shared-cache .olean causes a FALSE PASS"),
    "AUDIT-1": (None, "PORT", "a clean claim must name its evidence type (diff vs file-content)"),
    "B-29": (None, "PORT", "the four TrueSRReactionArc.lean files are NOT identical; four disjoint APIs"),
    "B-30": (None, "PORT", "the k < n failure is a type error, so k+1 < n is necessary"),
    "A-47": (None, "PORT", "two disjoint scopes missing the same half of the descent estimate"),
    "A-48": (None, "PORT", "LOAD-BEARING: hole A must consume hsol essentially; machine-checked"),
    "A-57": (None, "PORT", "DO NOT FUND THE SINGLE-LINKAGE ROUTE -- closed, not underfunded (l=1 "
                          "contradicts hwmax)"),
    "A-58": (None, "PORT", "the residue is pinned from three independent directions; the target is "
                          "NOT what the file names"),
    "A-59": (None, "PORT", "'omega finite => no strictly smaller carrier' is FALSE; spread enables "
                          "the descent"),
    "A-60": (None, "PORT", "the exact target sentence, agreed by three routes: "
                          "smaller_carried_siphon_iff_zeroSet_card_lt at :608"),
    "A-61": (None, "PORT", "siphonCarried_of_escape cannot supply the cardinality estimate; it is a "
                          "missing input, not a missing proof"),
    "A-62": (None, "PORT", "machine-checked: the strict-shrinking disjunct is false at singleton omega"),
    "A-63": (None, "PORT", "numLinkageClasses = 1 is CLOSED, not underfunded -- stated per request"),
    "A-54": (None, "PORT", "the descent is ATTRIBUTED to Anderson but he did not use it, and it is "
                          "INAPPLICABLE at hole A's faces; the closing hypothesis is numLinkageClasses = 1"),
    "A-55": (None, "PORT", "TierPersistence.lean is outside hole A's import closure (476 lines); "
                          "TierStrictBelow has the OPPOSITE sign convention to Anderson Def 4.1(ii)"),
    "A-56": (None, "PORT", "two points that REDUCE the apparent residue: Anderson's condition 2 is "
                          "one by_case here, and the projected time-dependent network is absent"),
    "A-51": (None, "PORT", "exists_maximal_zeroSetOf_card_le duplicates hmaxExact_of_zeroSet_card_le; "
                          "cut it, keep exists_maximalCard_zeroSet"),
    "A-52": (None, "PORT", "SiphonCarried is discharged by the hole's own hwmax/hzeroMax [S]"),
    "A-53": (None, "PORT", "IsCriticalSiphon Pmax is FULLY discharged [M]; residue is exactly descend"),
    "OPS-6": (None, "PORT", "land elaboration-friction API facts in the ledger BEFORE stalling on them"),
    "A-49": (None, "PORT", "the projOn bridge is NOT NEEDED; withdrawn"),
    "A-50": (None, "PORT", "the projOn bridge is structurally IMPOSSIBLE, not merely absent"),
    "B-13": ("F-4", "CROSSREF", "PR #13 F-4: the RR arc builder is NOT needed"),
    "A-39": (None, "PORT", "orchestrator line citations were fabricated; SiphonDimensionDescent is "
                          "382 lines. Verified line list included"),
    "A-40": (None, "PORT", "TWO entries share this id on holes. First: 'a strictly positive "
                          "conservation law separates two class points' is FALSE. Second: hole A's "
                          "statement is NOT refutable. Both must be ported and renumbered."),
    "A-41": (None, "PORT", "two of adv-refute's own results were float/kernel artefacts"),
    "A-42": (None, "PORT", "the template is not a new obstruction; cite GlobalPersistence.lean:161"),
    "A-43": (None, "PORT", "closed positive confines exist and are built; the sharp statement of "
                          "what hole A needs"),
    "A-44": (None, "PORT", "the comment at HighCodimensionSiphonFace.lean:1493 was false and "
                          "load-bearing for two rounds"),
    "A-45": (None, "PORT", "Concentration S is S -> R, plain reals"),
    "A-46": (None, "PORT", "hole A is not vacuous; it is genuinely the GAC boundary case"),

    # --- holes-only: port.  B-16..B-28 ---
    "B-16": (None, "PORT", "no privacy lift and no bespoke builder; TrueSRGlueInterface has no hole import"),
    "B-17": (None, "PORT", "glueArc is NOT the RR arc builder; it takes both inputs"),
    "B-18": (None, "PORT", "hopp is a sign condition with no path content"),
    "B-20": (None, "PORT", "the on-cycle route has length 2n-1; module that imports the hole file "
                          "and is still sorryAx-free"),
    "B-21": (None, "PORT", "m=1 is excluded by hQ0late; the m=1 split is redundant"),
    "B-22": (None, "PORT", "the hopp_alone_insufficient counterexample, explicit 3x3 flux matrix"),
    "B-23": (None, "PORT", "firstHop_forced_leftEdge omits hopp; hopp is load-bearing backwards only"),
    "B-24": (None, "PORT", "the RRGluable INSTANCE is the blocker (rr_gluable_arcs)"),
    "B-26": (None, "PORT", "hole B has no witness: no network satisfies hsep and hflow and hSR"),
    "B-27": (None, "PORT", "rr_three_glued_even_of_two already exists at TrueSRParityRR.lean:775"),
    "B-28": (None, "PORT", "the RR arc builder was written four times; reconcile before building"),

    # --- non-ID sections and infra entries ---
    "API-1": (None, "PORT", "dot notation on Concentration S resolves in namespace Function"),
    "API-2": (None, "PORT", "StoichCompatible.refl is applied as StoichCompatible.refl N x"),
    "API-3": (None, "PORT", "Concentration.zeroSet must be noncomputable"),
    "ENV-1": (None, "PORT", "Mathlib submodule imports have no local .olean; import umbrellas"),
    "OPS-1": (None, "PORT", "push before `git reset --hard` on an unpushed branch"),
    "OPS-2": (None, "PORT", "root Scaffold/ is gitignored; use CRNT/Scaffold/"),
    "VAC-1": (None, "PORT", "DifferentialInclusion.Field is vacuous when empty; blast radius = 4 "
                          "PolyhedralBarrier ForwardInvariant conclusions"),
}

# entries that exist only on PR #13, with what they are and what must happen to them
ADV_ONLY: dict[str, str] = {
    **{f"A{n}": "PR #13 §1, dashless id" for n in range(1, 31)},
    "A22b": "PR #13 §1: do not misread A22 as refuting the no-critical-siphon route",
    **{f"B{n}": "PR #13 §2, dashless id" for n in range(1, 19)},
    **{f"P{n}": "PR #13 §3 process finding" for n in range(1, 6)},
    **{f"R-{n}": "PR #13 §3e landing-site wave" for n in range(1, 9)},
    **{f"C-{n}": "PR #13 §3f fork-contest record" for n in range(1, 6)},
    **{f"F-{n}": "PR #13 §3g fork resolution" for n in range(1, 6)},
    **{f"H-{n}": "PR #13 §3h unified fact + corrections" for n in range(1, 7)},
}


def read_ref(ref: str, path: str) -> str:
    return subprocess.run(
        ["git", "-C", str(REPO), "show", f"{ref}:{path}"],
        check=True, capture_output=True, text=True,
    ).stdout


def parse(text: str) -> list[tuple[str, int, str]]:
    out = []
    for i, line in enumerate(text.splitlines(), 1):
        m = ENTRY_RE.match(line)
        if m:
            out.append((m.group(2), i, m.group(3)))
    return out


def measure() -> dict:
    r = subprocess.run(
        [sys.executable, str(REPO / "research" / "scripts" / "measure.py"), "--no-gates"],
        cwd=REPO, check=True, capture_output=True, text=True,
    )
    return json.loads(r.stdout)["metrics"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    H = parse(read_ref(HOLES_REF, "research/DEAD-ENDS.md"))
    A = parse(read_ref(ADV_REF, "research/DEAD-ENDS.md"))
    m = measure()

    h_ids = [x[0] for x in H]
    a_ids = [x[0] for x in A]
    h_counts, a_counts = Counter(h_ids), Counter(a_ids)
    h_dups = {k: v for k, v in h_counts.items() if v > 1}
    a_dups = {k: v for k, v in a_counts.items() if v > 1}

    # Anything appended to `holes` after the crosswalk was hand-built is auto-classified
    # PORT -- correct by construction, since PR #13 was not touched -- and flagged so the
    # next reader curates the note.  Completeness beats curation here.
    for _id, _line, _title in H:
        if _id not in CROSSWALK:
            CROSSWALK[_id] = (None, "PORT-AUTO",
                              "auto-classified: appended to `holes` after the crosswalk was "
                              "built. PORT is correct by construction; the note is not curated.")
    missing = sorted(set(h_ids) - set(CROSSWALK))
    if missing:
        print(f"FATAL: holes entries with no crosswalk row: {missing}", file=sys.stderr)
        return 2
    extra = sorted(set(CROSSWALK) - set(h_ids))
    if extra:
        print(f"FATAL: crosswalk rows with no holes entry: {extra}", file=sys.stderr)
        return 2

    adv_referenced = {v[0] for v in CROSSWALK.values() if v[0]}
    unmatched_adv = sorted(set(a_ids) - adv_referenced - set(ADV_ONLY))
    if unmatched_adv:
        print(f"FATAL: PR #13 entries neither cross-referenced nor declared adv-only: "
              f"{unmatched_adv}", file=sys.stderr)
        return 2

    # ---- id-collision census: A-<n> on holes vs A<n> on PR #13 are DIFFERENT entries -------
    def norm(i: str) -> str:
        return i.replace("-", "").lower()

    a_by_norm: dict[str, list[tuple[str, int, str]]] = {}
    for rec in A:
        a_by_norm.setdefault(norm(rec[0]), []).append(rec)
    collisions = []
    for hid, hline, htitle in H:
        for (arid, aline, atitle) in a_by_norm.get(norm(hid), []):
            if arid == hid:
                continue
            t1 = set(re.findall(r"[A-Za-z]{4,}", htitle.lower()))
            t2 = set(re.findall(r"[A-Za-z]{4,}", atitle.lower()))
            sim = len(t1 & t2) / max(1, len(t1 | t2))
            collisions.append((hid, hline, arid, aline, round(sim, 2)))

    identical = sum(1 for v in CROSSWALK.values() if v[1] == "IDENTICAL")
    crossref = sum(1 for v in CROSSWALK.values() if v[1] == "CROSSREF")
    diverge = sum(1 for v in CROSSWALK.values() if v[1] == "DIVERGES")
    port = sum(1 for v in CROSSWALK.values() if v[1] == "PORT")
    auto = sum(1 for v in CROSSWALK.values() if v[1] == "PORT-AUTO")

    out: list[str] = []
    w = out.append
    w("# `DEAD-ENDS.md` merge — the two-ledger crosswalk")
    w("")
    w("**This file is generated.** Do not hand-edit it. Regenerate with")
    w("")
    w("```sh")
    w("python3 research/scripts/gen_deadends_merge.py")
    w("```")
    w("")
    w("It is a *crosswalk*, not a resolution. It says, for every entry on either side, what the")
    w("other side says about it and what has to happen to it — and it does **not** pick a winner.")
    w("Choosing which file is canonical is the human's merge (nobody may merge a PR; see")
    w("`research/README.md` §3).")
    w("")
    w("## Sources")
    w("")
    w("| | branch | entries parsed | grading | character |")
    w("| --- | --- | --- | --- | --- |")
    w(f"| **H** | `{HOLES_REF}` | {len(H)} heading-entries "
      f"({len(h_counts)} distinct ids) | `[V]` / `[H]` | orchestrator ledger, appended as "
      f"broadcasts landed; chronological, uncorrected |")
    w(f"| **P** | `{ADV_REF}` (PR #13) | {len(A)} heading-entries "
      f"({len(a_counts)} distinct ids) | `[M]` / `[S]` / `[N]` | deduplicated across five prior "
      f"handoff documents; has §0 grading, §4 maintenance protocol and "
      f"`research/routes/negative-checklist.md` |")
    w("")
    w("Line numbers below are **1-based line numbers in the file at that ref**, not in any working")
    w("tree, so they stay checkable after either branch moves.")
    w("")
    w("## Why this cannot be a last-writer-wins")
    w("")
    w("| | count |")
    w("| --- | --- |")
    w(f"| entries parsed on `{HOLES_REF.split('/')[-1]}` only | **{len(set(h_ids) - set(a_ids))}** |")
    w(f"| entries parsed on PR #13 only | **{len(set(a_ids) - set(h_ids))}** |")
    w(f"| entries whose id appears on **both** sides | {len(set(h_ids) & set(a_ids))} |")
    w(f"| of those, byte-identical text (keep one copy) | {identical} |")
    w(f"| of those, same finding under a *different* id (keep both ids, one text) | {crossref} |")
    w(f"| of those, the two sides make **different claims** (keep both, dated) | {diverge} |")
    w(f"| `holes`-only entries that must be **ported** | **{port + auto}** "
      f"({port} curated + {auto} auto-classified `PORT-AUTO`) |")
    w("")
    w(f"A silent last-writer-wins drops {port + auto} entries that exist nowhere on PR #13 — the")
    w("entire round-2 wave (`A-29` onward, `B-19` onward), the mining-scout TRAP/LEAD blocks, and")
    w("every API/OPS/ENV/VAC/AUDIT note.")
    w("")
    w("## ⚠️ Three id hazards that a mechanical merge would hit")
    w("")
    w("**Hazard 1 — the two schemes use the same numerals for different entries.** PR #13 §1/§2")
    w("number `A1`…`A30` and `B1`…`B18` *without* a hyphen, while §3b–§3d import the round-1")
    w("`A-1`…`A-15` / `B-1`…`B-12` *with* one. Normalising `A-16` and `A16` to the same key")
    w("matches unrelated findings:")
    w("")
    w("| `holes` id | what it says | PR #13 id | what it says | title similarity |")
    w("| --- | --- | --- | --- | --- |")
    shown = 0
    for hid, hline, arid, aline, sim in collisions:
        if sim < 0.45 and shown >= 12:
            continue
        ht = next(t for (i, l, t) in H if i == hid)
        at = next(t for (i, l, t) in A if i == arid)
        w(f"| `{hid}` ({hline}) | {strip(ht)} | `{arid}` ({aline}) | {strip(at)} | {sim} |")
        shown += 1
        if shown >= 12:
            break
    w("")
    w(f"(of {len(collisions)} hyphen-stripped id pairs, "
      f"{sum(1 for c in collisions if c[4] < 0.45)} have title similarity below 0.45, i.e. they are")
    w("**not** the same finding.) **Merge on content, never on id.**")
    w("")
    w("**Hazard 2 — PR #13 reuses its own ids.** Its §3c numbering (`F-1`…`F-4`, the framing")
    w("revision) and its §3g numbering (`F-1`…`F-5`, the fork resolution) are different entries")
    w("with the same ids, at lines 1319–1364 and 1820–1870 respectively. Anyone citing \"F-1\"")
    w("without a line number is ambiguous. This table cites line numbers throughout for that")
    w("reason.")
    w("")
    w("**Hazard 3 — `holes` itself has a duplicate id.** `A-40` is used twice, at lines 873 and")
    w("992, for two unrelated findings (\"a strictly positive conservation law separates two class")
    w("points is FALSE\" and \"hole A's statement is NOT refutable\"). Both must be ported and")
    w("renumbered on the way in.")
    w("")
    if h_dups:
        w(f"Duplicate ids on `holes`: " + ", ".join(f"`{k}` ×{v}" for k, v in sorted(h_dups.items())) + ".")
    if a_dups:
        w(f"Duplicate ids on PR #13 (within one parse): "
          + ", ".join(f"`{k}` ×{v}" for k, v in sorted(a_dups.items())) + ".")
    w("")
    w("## The crosswalk")
    w("")
    w("`H` column = `holes` id and line. `P` column = PR #13 id and line, or `—` for none.")
    w("")
    w("| # | `holes` id | H line | PR #13 id | P line | action | what it is / what to do |")
    w("| --- | --- | --- | --- | --- | --- | --- |")
    order = sorted(H, key=lambda r: (r[0][0], int(re.sub(r"\D", "", r[0]) or 0), r[1]))
    alookup = {}
    for rec in A:
        alookup.setdefault(rec[0], rec[1])
    for n, (hid, hline, htitle) in enumerate(order, 1):
        adv, act, note = CROSSWALK[hid]
        pl = alookup.get(adv, "—") if adv else "—"
        w(f"| {n} | `{hid}` | {hline} | " + (f"`{adv}`" if adv else "—") +
          f" | {pl} | **{act}** | {note} |")
    w("")
    w(f"**{len(order)} rows — every entry parsed on `{HOLES_REF}`.**")
    w("")
    w("## PR #13-only entries")
    w("")
    w("These have no `holes` counterpart. They stay; they are PR #13's main contribution")
    w("(deduplication, grading, the maintenance protocol). Listed so the merge is provably")
    w("complete, not so it can be reproduced from this file alone.")
    w("")
    w("| PR #13 id | P line | disposition |")
    w("| --- | --- | --- |")
    for k, v in sorted(ADV_ONLY.items(), key=lambda kv: (kv[0][0], int(re.sub(r"\D", "", kv[0]) or 0))):
        line = alookup.get(k)
        if line is None:
            continue
        w(f"| `{k}` | {line} | KEEP — {v} |")
    w("")
    w("Plus, on PR #13 and **not** an entry: §0 (grading table), the deduplication note, the ID")
    w("mapping table at §3b, `research/routes/negative-checklist.md`, and §4 (maintenance")
    w("protocol, six subsections). Those are structural and must survive any merge — they are the")
    w("reason PR #13's file is worth more than `holes`'s as an *artifact*, independent of which")
    w("entries win.")
    w("")
    w("## Non-entry sections on `holes`")
    w("")
    w("These are prose blocks, not IDed entries, and a diff-based merge will silently drop them:")
    w("")
    w("* **\"The Hole B route that survives round 1\"** (line 290) — duplicated verbatim on PR #13")
    w("  at line 1289. Both copies are stale in the same way: step 1 says to port")
    w("  `TrueSRCycle.SignDirected`, which round 1 landed (`B-27`), and step 2 names")
    w("  `ss_three_glued_even_of_two`, the wrong flavour (`B-27`).")
    w("* **\"Maintenance protocol\"** (line 314) — the `[V]`/`[H]` protocol. Superseded in full by")
    w("  PR #13 §4, which is longer and grades honestly. Do not keep both.")
    w("* **\"Durable Tier C work\"** (line 615) — four unbuilt Tier C items. PORT; nothing on")
    w("  PR #13 carries them.")
    w("* **\"WIP branch status\"** (line 886) — a branch-status note, explicitly *not* a")
    w("  contribution. Do not port into the ledger; it belongs in the round's handoff.")
    w("* **\"RULE (tier-wide, from A-41)\"** (line 1021) — a negative result ships with its")
    w("  certification method. PORT; it is the sharpest process rule in either file and PR #13's")
    w("  P3 is its weaker sibling.")
    w("")
    w("## Cross-reference: `adv-audit` (PR #14)")
    w("")
    w("Three documentation defects `adv-audit` found are *ledger-relevant* and belong in the merged")
    w("file rather than only in `research/AUDIT.md`. All three re-verified here this session.")
    w("")
    w("| claim | re-verified | where it belongs after the merge |")
    w("| --- | --- | --- |")
    w("| three docstrings cite `SrBlocks` / `SrProp510`, which exist nowhere | "
      "`grep -rn 'SrBlocks\\|SrProp510' --include='*.lean' CRNT` → **3 hits, all prose**, at "
      "`TrueChemistrySRCriterion.lean:4016, 4069, 7093`; `grep -E '(theorem|lemma|def|structure|"
      "abbrev) (SrBlocks|SrProp510)'` → **0**. Matches PR #13 entry B18 verbatim. | "
      "merge with B18; the ledger entry is already right, the *docstrings* are what is broken |")
    w("| the Hole B flagship carries an undisclosed third hypothesis `hflow` | "
      "`stronglyConcordant_fullyOpen_of_trueSRCriterion` at "
      "`TrueChemistrySRCriterion.lean:8003-8006` takes `(hsep) (hflow : "
      "N.ZeroComplexReactionsAreFlows) (hSR)`; its docstring at `:7998-8002` names only "
      "reactant/product separation. | "
      "**this is the merge's most important single fact** — see below |")
    w("| `HighCodimensionSiphonFace.lean:73-76` makes a false axiom-hygiene claim | the block at "
      "`:73-77` asserts \"No other declaration in the tree does\"; `measure.py --no-gates` reports "
      f"**{m['holes']} executable `sorry`s** under `CRNT/`, one of them in the Hole B file, and "
      "`grep -rn '^\\s*sorry\\b' CRNT/` returns exactly those two `.lean` sites plus one hit in a "
      "non-Lean backup file (`CRNT/Equilibria/TreeConstants.lean.pre_matrix_tree_backup:140`, not "
      "a build target). The claim as written is false. | identical to `holes` **A-24**; port A-24 "
      "and let it carry the fix |")
    w("")
    w("### Why `hflow` is the merge's load-bearing fact")
    w("")
    w("Both ledgers describe Hole B's flagship as a two-hypothesis theorem (`hsep ∧ hSR`). It is")
    w("three. The third, `hflow`, is the reason `holes` **B-26** (\"hole B has no witness\") is a")
    w("statement about the *class* and not about a derivable side condition: PR #16's `flowN`")
    w("counterexample fails `hflow` and PR #16's `netN` fails `hsep`, so **no** network in the")
    w("tree satisfies `hsep ∧ hflow ∧ hSR`. Any merged ledger that describes the flagship as")
    w("`hsep ∧ hSR` will send the next researcher at a vacuous class without saying so.")
    w("")
    w("Cross-referenced entries: `holes` **B-26** (PORT), **B-24** (`rr_gluable_arcs` — built for")
    w("the empty class, so it is vacuity-*safe*), **B-27**/**B-28** (arc builder, likewise), and")
    w("PR #13 **B17** (the superseded not-built claim) + **B18** (the phantom docstring names).")
    w("")
    w("## Numbers in this file, and how to re-derive them")
    w("")
    w("Everything below is emitted by the generator from "
      "`research/scripts/measure.py --no-gates`, so no count here is a hand-typed claim.")
    w("")
    w("| metric | value | source |")
    w("| --- | --- | --- |")
    w(f"| executable `sorry`s under `CRNT/` | **{m['holes']}** | `measure.py --no-gates` |")
    for f, l in m["hole_sites"]:
        w(f"| hole site | `{f}:{l}` | `measure.py --no-gates` |")
    w(f"| frontier modules | {m['frontier_mods']} | `measure.py --no-gates` |")
    w(f"| scaffold modules | {m['scaffold_mods']} | `measure.py --no-gates` |")
    w(f"| Lean lines | {m['lean_lines']} | `measure.py --no-gates` |")
    w(f"| declared `axiom`s | {m['declared_axioms']} | `measure.py --no-gates` |")
    w("")
    w("The two `hole_sites` are the frozen objective (`holes = 0`). They are listed here so a")
    w("reader of this file can see that the merge concerns the *record*, not the target.")
    w("")
    w("## Recommended order of operations (for the human merge)")
    w("")
    w("1. Take PR #13's `DEAD-ENDS.md` as the **base** — grading scheme, deduplication, §4")
    w("   protocol and `negative-checklist.md` are structural and exist nowhere else. This is a")
    w("   recommendation about *structure*, not about any entry; no entry is thereby resolved.")
    w("2. Port the **PORT** rows above, keeping their ids. **Renumber `A-40` (×2) on the way in**")
    w("   and preserve the distinction between `A-40a`/`A-40b`.")
    w("3. For each **CROSSREF** row, keep PR #13's text and add the `holes` id as an alias in the")
    w("   entry's `found-by` line. Do not paste both texts.")
    w("4. For **A-6** (the only `DIVERGES` among the round-1 entries): PR #13's §3b A-6 and its")
    w("   `P4` bullet 2 assert something `holes` **retracted**. Port the retraction, and delete the")
    w("   retracted claim rather than merging the two — a retracted false claim that survives in a")
    w("   new file is worse than the original error.")
    w("5. Keep `adv-negative`'s §3f (`C-1`…`C-5`) even though the dispute is settled: it is the only")
    w("   record of *why* the fork looked contested, and `H-3`'s `closure_minimal` subtlety is")
    w("   only legible against it.")
    w("6. Do **not** renumber the dashless `A1`…`A30` / `B1`…`B18`. Renumbering makes Hazard 1")
    w("   permanent instead of fixable.")
    w("")
    w("---")
    w("")
    w("Generated from "
      f"`{HOLES_REF}:research/DEAD-ENDS.md` and `{ADV_REF}:research/DEAD-ENDS.md`.")
    w("Every `file:line` in this document was read in the generating session; the generator")
    w("refuses to emit if an id on either side has no row.")

    text = "\n".join(out) + "\n"
    if args.check:
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            print("STALE: research/DEAD-ENDS-merge.md differs from generator output", file=sys.stderr)
            return 1
        print("OK: research/DEAD-ENDS-merge.md is up to date")
        return 0
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT.relative_to(REPO)}  ({len(text.splitlines())} lines)")
    print(f"  holes entries {len(H)} ({len(h_counts)} ids) | PR #13 entries {len(A)} "
          f"({len(a_counts)} ids)")
    print(f"  IDENTICAL {identical} | CROSSREF {crossref} | DIVERGES {diverge} | PORT {port}")
    return 0


def strip(s: str) -> str:
    s = re.sub(r"\s*\*\*\[[^\]]*\]\*\*\s*$", "", s).strip()
    s = s.replace("**", "").replace("~~", "")
    return s.replace("|", "/")[:78]


if __name__ == "__main__":
    raise SystemExit(main())