#!/usr/bin/env python3
"""pr_score.py — score a researcher's PR from the tree, per research/README.md §5.

    python3 scripts/pr_score.py holes research/form-sr-deg2a
    python3 scripts/pr_score.py holes HEAD --json

Both refs are exported with `git archive` into a temporary directory (no worktree, no
checkout, no interference with whatever else is running against this repository) and
`research/scripts/measure.py` is run on each.  The metric script is taken from the *head*
ref when it has one and from the *base* otherwise, and the choice is printed: scoring two
refs with two different metric scripts would confound the comparison, so the head's is
used and the base is re-measured with it.

Three things make this the honest version rather than a diff pretty-printer:

* **Hole statements are compared textually.**  A PR that closes a hole by deleting a
  hypothesis moves `holes` and would otherwise look like the best submission of the
  round.  The statement of every open hole is extracted from both refs and compared
  after whitespace normalisation; a change is reported as `hole statement changed`
  regardless of what it did to the score.
* **Only machine-readable events are scored.**  The README's table has entries that are
  judgements ("survives adversary review", "used downstream").  Those are listed as
  `unscored` rather than guessed at, so the printed total is a floor, not a guess.
* **The headline points are marked as needing certification.**  `+100` per `sorry`
  eliminated requires the enclosing module to still elaborate axiom-cleanly, which
  `measure.py` cannot see.  That is what `scripts/close_hole.sh` is for, so the summary
  says so instead of paying out on an unverified claim.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# research/README.md §5, restricted to what a script can decide from the tree.
PTS_SORRY_ELIMINATED = 100
PTS_TREE_CLEAN = 1000
PTS_NEW_MODULE = 8
PTS_GATE_BROKEN = -60
PTS_SORRY_INTRODUCED = -60
PTS_FORBIDDEN = -60
PTS_HOLE_CHANGED = -200

UNSCORED = (
    "new machine-checked lemma on an identified route (+25 used downstream / +10 not)",
    "route document with signatures, citations and a dead-end list (+12)",
    "machine-checked refutation that kills a route or statement (+30)",
    "a proved lemma another researcher's PR builds on (+15)",
)

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)",
    re.M,
)
BAD_RE = {
    "admit": re.compile(r"(?<![A-Za-z_.'\"])\badmit\b"),
    "native_decide": re.compile(r"(?<![A-Za-z_.'\"])\bnative_decide\b"),
    "implemented_by": re.compile(r"@\[implemented_by"),
    "declared axiom": re.compile(r"^\s*(axiom|constant)\s+\w+", re.M),
}


# ------------------------------------------------------------------- plumbing


def git(*args: str) -> str:
    p = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"git {' '.join(args)} failed:\n{p.stderr.strip()}")
    return p.stdout


def export(ref: str, dest: Path) -> None:
    """`git archive | tar -x` — read-only, and leaves the working tree untouched."""
    p = subprocess.Popen(["git", "-C", str(ROOT), "archive", "--format=tar", ref],
                         stdout=subprocess.PIPE)
    assert p.stdout is not None
    data = p.stdout.read()
    if p.wait() != 0:
        raise SystemExit(f"git archive {ref} failed")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r|") as tf:
        tf.extractall(dest)


def load_measure(root: Path):
    """Import the ref's own `measure.py`.  Head's if it has one, else base's."""
    for cand in (root / "research" / "scripts" / "measure.py",):
        if cand.is_file():
            spec = importlib.util.spec_from_file_location(
                f"crnt_measure_{cand.stat().st_mtime_ns}", cand
            )
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            return mod, str(cand.relative_to(root))
    raise SystemExit(f"no research/scripts/measure.py in {root}")


def strip_comments(text: str) -> str:
    return re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)


def decl_body(code: str, start: int, limit: int = 4000) -> str:
    """The declaration's statement: up to the first top-level `:=`, `where` or `begin`."""
    depth, i, n = 0, start, min(len(code), start + limit)
    while i < n:
        if code.startswith("/-", i):
            j = code.find("-/", i)
            i = n if j < 0 else j + 2
            continue
        ch = code[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and code.startswith(":=", i):
            return code[start:i]
        elif depth == 0 and re.match(r"\b(where|begin)\b", code[i:i + 6]):
            return code[start:i]
        i += 1
    return code[start:n]


def decl_marks(code: str) -> list[tuple[int, str]]:
    """`(line, namespace-qualified name)` for every theorem/lemma, in file order."""
    marks, stack = [], []
    for i, text in enumerate(code.splitlines(), 1):
        ns = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", text)
        if ns:
            stack.append(ns.group(1))
            continue
        if re.match(r"^end\s+[A-Za-z_]", text) and stack:
            stack.pop()
            continue
        m = DECL_RE.match(text)
        if m:
            marks.append((i, ".".join(stack + [m.group(2)])))
    return marks


def owner(marks, line: int) -> str | None:
    """The declaration containing `line`: the last one that starts at or before it."""
    found = None
    for start, name in marks:
        if start > line:
            break
        found = name
    return found


def statements(root: Path) -> dict[str, str]:
    """Normalised `theorem`/`lemma` statements, keyed by `<file>#<name>`, namespace-qualified.

    A file's own `namespace`/`end` stack is tracked so that `theorem foo` inside
    `namespace Network` is keyed `...#Network.foo`: comparing statements by bare name
    would silently compare two different declarations if a namespace were added or
    removed, which is exactly the edit this tool exists to catch.
    """
    out: dict[str, str] = {}
    for base in ("CRNT", "Scaffold"):
        top = root / base
        if not top.is_dir():
            continue
        for path in sorted(top.rglob("*.lean")):
            code = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
            stack: list[str] = []
            for line in code.splitlines():
                ns = re.match(r"^namespace\s+([A-Za-z_][\w'.]*)", line)
                if ns:
                    stack.append(ns.group(1))
                    continue
                if re.match(r"^end\s+[A-Za-z_]", line) and stack:
                    stack.pop()
                    continue
                m = DECL_RE.match(line)
                if m:
                    qual = ".".join(stack + [m.group(2)])
                    out[f"{path.relative_to(root)}#{qual}"] = " ".join(
                        decl_body(code, m.end()).split()
                    )
    return out



def sorry_decls(root: Path) -> set:
    """Every declaration in `CRNT/` that contains an executable `sorry`.

    Keyed `file#namespace-qualified.name`, so comparing two refs is a set difference
    that does *not* shift when an unrelated line is inserted above the hole.  The
    file+line difference that `measure.py` reports would score every hole-closing
    PR as one hole eliminated plus one hole introduced, which is exactly the kind of
    mechanical false positive that gets a good submission thrown out.
    """
    out = set()
    top = root / "CRNT"
    if not top.is_dir():
        return out
    rx = re.compile(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])")
    for path in sorted(top.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        marks = decl_marks(code)
        for i, line in enumerate(code.splitlines(), 1):
            if rx.search(line):
                name = owner(marks, i)
                if name:
                    out.add(f"{path.relative_to(root)}#{name}")
    return out


def module_files(root: Path) -> set:
    return {str(p.relative_to(root)) for base in ("CRNT", "Scaffold")
            if (root / base).is_dir() for p in (root / base).rglob("*.lean")}


def bad_counts(root: Path) -> dict[str, int]:
    counts = {k: 0 for k in BAD_RE}
    for base in ("CRNT", "Scaffold"):
        if not (root / base).is_dir():
            continue
        for path in (root / base).rglob("*.lean"):
            code = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
            for k, rx in BAD_RE.items():
                counts[k] += len(rx.findall(code))
    return counts


def measure_tree(root: Path, with_gates: bool) -> dict:
    mod, source = load_measure(root)
    m = mod.scan(root)
    g = mod.gates(root) if with_gates else {}
    return {"m": m, "g": g, "score": mod.score(m, g), "measure_source": source}


# ---------------------------------------------------------------------- scoring


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("base_ref")
    ap.add_argument("head_ref")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--no-gates", action="store_true",
                    help="skip the static gates (faster; the -60 gate penalty then unproven)")
    args = ap.parse_args()

    base_sha = git("rev-parse", args.base_ref).strip()
    head_sha = git("rev-parse", args.head_ref).strip()
    with_gates = not args.no_gates

    rows: list[tuple[str, int, str]] = []
    total = 0

    def add(label, points, detail=""):
        nonlocal total
        total += points
        rows.append((label, points, detail))

    # One export per ref, reused for the metrics *and* the statement comparison:
    # `git archive` of a 137k-line tree is the expensive part of this command, and
    # doing it twice doubled the cost for no extra information.
    with tempfile.TemporaryDirectory() as tmp:
        rb, rh = Path(tmp) / "base", Path(tmp) / "head"
        rb.mkdir()
        rh.mkdir()
        export(base_sha, rb)
        export(head_sha, rh)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            fb, fh = pool.map(lambda r: measure_tree(r, with_gates), (rb, rh))
        b, h = fb["m"], fh["m"]

        # --- holes ----------------------------------------------------------
        # Compared by enclosing declaration, not by (file, line): inserting a lemma
        # above a hole shifts every line below it, and a line-based diff reports that
        # as one hole closed *and* one hole opened, which is how a correct
        # hole-closing PR gets thrown out on a mechanical false positive.
        sorry_b = sorry_decls(rb)
        sorry_h = sorry_decls(rh)
        eliminated = sorted(sorry_b - sorry_h)
        introduced = sorted(sorry_h - sorry_b)

        if eliminated:
            add("`sorry` eliminated in CRNT/", PTS_SORRY_ELIMINATED * len(eliminated),
                f"{len(eliminated)}: " + ", ".join(eliminated)
                + "  [needs close_hole.sh: elaborates + axiom-clean to actually pay]")
        if h["holes"] == 0 and b["holes"] > 0:
            add("tree reaches holes = 0", PTS_TREE_CLEAN, "split across contributors")
        if introduced:
            add("`sorry` introduced", PTS_SORRY_INTRODUCED * len(introduced),
                ", ".join(introduced))

        # --- statements of the hole-carrying files ---------------------------
        # Scored for a hole's own declaration; merely *named* for its neighbours,
        # because adding a lemma next to a hole is normal work and silently editing
        # one is not -- but only a hole is the subject of the -200 rule.
        files = {k.split("#", 1)[0] for k in sorry_b | sorry_h}
        sb = {k: v for k, v in statements(rb).items() if k.split("#", 1)[0] in files}
        sh = {k: v for k, v in statements(rh).items() if k.split("#", 1)[0] in files}
        moved = sorted(k for k in (sorry_b | sorry_h) if sh.get(k) != sb.get(k))
        if moved:
            add("hole statement changed", PTS_HOLE_CHANGED * len(moved), "; ".join(moved))
        else:
            rows.append(("hole statements unchanged", 0,
                         f"{len(sb)} declarations compared in {len(files)} hole file(s)"))
        others = sorted(k for k in set(sb) | set(sh)
                        if k not in sorry_b | sorry_h and sh.get(k) != sb.get(k))
        if others:
            rows.append(("neighbouring decls edited", 0,
                         f"{len(others)}: " + ", ".join(others[:6])
                         + (" ..." if len(others) > 6 else "")))

        # --- new consumable modules ------------------------------------------
        new_mods = sorted(module_files(rh) - module_files(rb))
        if new_mods:
            add("new CRNT//Scaffold/ module", PTS_NEW_MODULE * len(new_mods),
                f"{len(new_mods)}: " + ", ".join(new_mods))

        # --- forbidden constructs --------------------------------------------
        cb, ch = bad_counts(rb), bad_counts(rh)
        for k in sorted(BAD_RE):
            d = ch[k] - cb[k]
            if d > 0:
                add(f"new `{k}`", PTS_FORBIDDEN * d, f"+{d}")
            elif d < 0:
                rows.append((f"`{k}` removed", 0, f"-{-d}"))

        # --- gates -----------------------------------------------------------
        if with_gates:
            broken = sorted(k for k, v in fh["g"].items()
                            if v == "FAIL" and fb["g"].get(k) != "FAIL")
            if broken:
                add("static gate broken", PTS_GATE_BROKEN * len(broken), ", ".join(broken))
            for k, v in sorted(fh["g"].items()):
                rows.append((f"gate {k}", 0, f"{v} (base: {fb['g'].get(k, '?')})"))

    metrics = {
        k: {"base": b[k], "head": h[k]}
        for k in ("holes", "frontier_mods", "scaffold_mods", "lean_lines", "declared_axioms")
    }
    payload = {
        "base": args.base_ref, "head": args.head_ref,
        "base_sha": base_sha, "head_sha": head_sha,
        "measure_source": fh["measure_source"],
        "metrics": metrics,
        "measure_score": {"base": fb["score"], "head": fh["score"]},
        "rows": [{"event": e, "points": p, "detail": d} for e, p, d in rows],
        "scored_total": total,
        "unscored_manual_events": list(UNSCORED),
    }

    if args.json:
        print(json.dumps(payload, indent=2))
        return 0

    print(f"{payload['base']} ({base_sha[:9]})  ->  {payload['head']} ({head_sha[:9]})")
    print(f"metric script: {payload['measure_source']} (from the head ref)")
    print()
    print(f"{'metric':<22}{'base':>10}{'head':>10}{'delta':>10}")
    for k, v in metrics.items():
        print(f"{k:<22}{v['base']:>10}{v['head']:>10}{v['head'] - v['base']:>+10}")
    ds = payload["measure_score"]
    print(f"{'measure.py score':<22}{ds['base']:>10}{ds['head']:>10}{ds['head'] - ds['base']:>+10}")
    print()
    print("scoring (research/README.md §5, machine-decidable rows only)")
    print(f"{'event':<38}{'points':>8}  detail")
    for e, p, d in rows:
        print(f"{e:<38}{p:>+8}  {d}")
    print(f"{'TOTAL (machine-decidable)':<38}{total:>+8}")
    print()
    print("not scored here (needs a human or an adversary): " + "; ".join(UNSCORED))
    return 0


if __name__ == "__main__":
    sys.exit(main())
