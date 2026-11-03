#!/usr/bin/env python3
"""`#print axioms` on one declaration, asserting the axiom set is exactly the allowed one.

    python3 scripts/check_axioms.py CRNT/Dynamics/HighCodimensionSiphonFace.lean \
        Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

This is the check `test/AxiomAudit.lean` pins for the headline results, made into a
tool so that *any* theorem can be certified on demand -- in particular the two swarm
holes, whose whole point is that closing them must not be a licence to introduce a new
axiom.  A `sorry` in the proof is not a special case here: Lean's `sorryAx` shows up in
the axiom list and fails the subset test, which is the behaviour we want.  An `axiom`
declared in a dependency surfaces under its own name, likewise.

The allowed set is `propext`, `Classical.choice`, `Quot.sound` -- the three every
Mathlib theorem depends on.  Exit 0 means the declaration resolved *and* its axioms are
a subset of the allowed set; exit 1 means anything else, with the observed axiom list
printed.

The declaration may be named bare (`exists_isComplexBalanced`) or fully qualified
(`Network.exists_isComplexBalanced`); a bare name is resolved against the file's own
`namespace` stack, because every declaration in this repository that is worth
certifying lives in a namespace and an `unknown identifier` failure here would be
misread as "the check is broken".

The elaboration runs through the `lean` binary directly with a hand-assembled
`LEAN_PATH` rather than `lake env`: `lake env` resolves the whole workspace and costs
minutes per invocation, and this path costs the same elaboration for a fraction of it.
Expect a few minutes anyway -- importing a CRNT module means loading its entire
`.olean` closure, and that cost is inherent, not an artefact of how it is invoked.
`--lake-env` restores the `checkmod.sh` behaviour for anyone who wants it.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ALLOWED = ("propext", "Classical.choice", "Quot.sound")
NO_OLEAN = re.compile(r"object file '.*\.olean' of module (\S+) does not exist")

# `'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]`
AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*)")
END_RE = re.compile(r"^end\s+[A-Za-z_]")


def qualified_names(path: str) -> dict[str, str]:
    """`theorem foo` inside `namespace Network` is looked up as `Network.foo`."""
    out: dict[str, str] = {}
    stack: list[str] = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            ns = NAMESPACE_RE.match(line)
            if ns:
                stack.append(ns.group(1))
                continue
            if END_RE.match(line) and stack:
                stack.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                out.setdefault(m.group(2), ".".join(stack + [m.group(2)]))
    return out


def lean_path() -> str:
    """The shared cache FIRST, then this worktree, then every dependency's.

    ORDERING IS LOAD-BEARING, and this is the same trap `research/scripts/checkmod.sh`
    documents.  Lean resolves a module against the FIRST `LEAN_PATH` entry whose
    directory prefix exists -- it does NOT fall through to a later entry that holds
    the file.  A worktree that has elaborated even one module therefore has a
    `.lake/build/lib/lean/CRNT/` directory, and putting the worktree first shadows the
    shared cache for the whole `CRNT` namespace:

        error: object file '<worktree>/.lake/build/lib/lean/CRNT/Dynamics/FaceCodimension.olean'
        of module CRNT.Dynamics.FaceCodimension does not exist

    ...naming a file that does exist, in the shared cache, one entry later.  Measured:
    moving the worktree's `CRNT/` directory aside changes that error into a successful
    elaboration, so the shadowing is the cause and not a missing artefact.

    The shared cache is also what `checkmod.sh` elaborates against, so an axiom check
    here means the same thing it would mean in CI.
    """
    shared = os.environ.get("CRNT_ROOT", "/Users/akutuva/Documents/Proofs/crnt-lean")
    entries = [os.path.join(shared, ".lake", "build", "lib", "lean"),
               os.path.join(ROOT, ".lake", "build", "lib", "lean")]
    pkg = os.path.join(ROOT, ".lake", "packages")
    if os.path.isdir(pkg):
        for name in sorted(os.listdir(pkg)):
            p = os.path.join(pkg, name, ".lake", "build", "lib", "lean")
            if os.path.isdir(p):
                entries.append(p)
    seen, out = set(), []
    for e in entries:
        if e not in seen:
            seen.add(e)
            out.append(e)
    return os.pathsep.join(out)


def module_of(path: str) -> str:
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    return rel[: -len(".lean")].replace(os.sep, ".")


def run_probe(path: str, name: str) -> str:
    """Elaborate the module's SOURCE with a trailing `#print axioms` appended.

    Importing the module by name would certify a stale artefact: with the shared cache
    first (required, see `lean_path`), `import CRNT.Foo` reads whatever `CRNT.Foo.olean`
    the cache happens to hold -- for this tree, a September build, which does not even
    contain the declarations now in the source.  Measured: the name-based probe reports
    `Unknown constant`; this one reports the axiom set.

    Inlining the source instead means the declaration under certification is the one on
    disk, while its own imports resolve from the shared cache exactly as `checkmod.sh`
    resolves them.  This is also the only shape that makes step 2 of `close_hole.sh`
    mean what it claims: "the axiom set of the theorem you just wrote".
    """
    with open(path, encoding="utf-8", errors="replace") as fh:
        source = fh.read()
    with tempfile.TemporaryDirectory() as tmp:
        probe = os.path.join(tmp, "AxiomProbe.lean")
        with open(probe, "w", encoding="utf-8") as fh:
            fh.write(source)
            # The source's own `namespace` blocks are closed by the time we get here, so
            # the name must be fully qualified -- `qualified_names` supplies that.
            fh.write(f"\n#print axioms {name}\n")
        p = subprocess.run(["lean", probe], cwd=ROOT, capture_output=True, text=True,
                           env=dict(os.environ, LEAN_PATH=lean_path()))
    return p.stdout + p.stderr


def missing_olean(out: str) -> str | None:
    """The module named by a `does not exist` error, if any.

    `object file '<path>' of module <Name> does not exist` -- the path is unreliable as a
    diagnosis (see `lean_path`), but the module name is not.
    """
    m = NO_OLEAN.search(out)
    return m.group(1) if m else None


def explain_failure(out: str, name: str) -> None:
    """Name the actual cause.  An unelaborated dependency and an axiom outside the
    allowed set are different failures, and conflating them sends the reader looking for
    a `sorry` that is not there."""
    missing = missing_olean(out)
    if missing:
        print(f"::error::{missing} has no compiled .olean in the shared cache, so it "
              f"cannot be imported.", file=sys.stderr)
        print("::error::elaborate it first -- `research/scripts/checkmod.sh <path>`, "
              f"or let scripts/close_hole.sh do it (step 1).", file=sys.stderr)
        return
    if "unknown constant" in out or "Unknown identifier" in out:
        print(f"::error::'{name}' does not resolve after elaborating the module's source. "
              f"It is not declared at top level of that namespace, or is `private`.",
              file=sys.stderr)
        sys.stderr.write(out[-2000:])
        return
    print(f"::error::the axiom probe for '{name}' did not elaborate", file=sys.stderr)
    sys.stderr.write(out[-4000:])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("module", help="path to the .lean file, e.g. CRNT/Foo/Bar.lean")
    ap.add_argument("theorem", nargs="?", help="qualified or bare declaration name")
    ap.add_argument("--list", action="store_true",
                    help="list the module's theorems/lemmas with their qualified names, and exit")
    args = ap.parse_args()

    if not os.path.exists(args.module):
        print(f"::error::no such file: {args.module}", file=sys.stderr)
        return 1

    if args.list:
        names = qualified_names(args.module)
        for bare in sorted(names):
            print(names[bare])
        print(f"{len(names)} declaration(s)", file=sys.stderr)
        return 0
    if not args.theorem:
        print(f"usage: check_axioms.py {args.module} <TheoremName>   "
              f"(or --list to see what it declares)", file=sys.stderr)
        return 2

    names = qualified_names(args.module)
    bare = args.theorem.rsplit(".", 1)[-1]
    # `qualified_names` is keyed by the BARE name, so `args.theorem in names` is also true
    # for a bare name -- and taking it there hands Lean an unqualified name, which cannot
    # resolve once the module's `namespace` blocks have closed.  Consult the qualified
    # form only when the caller actually supplied a dotted name.
    if "." in args.theorem and args.theorem in names:
        name = args.theorem
    elif bare in names:
        name = names[bare]
    else:
        print(f"::error::{args.theorem} is not declared in {args.module}", file=sys.stderr)
        near = sorted(n for n in names if bare.lower() in n.lower())[:5]
        if near:
            print("::error::did you mean: " + ", ".join(near), file=sys.stderr)
        else:
            print("::error::this module declares "
                  f"{len(names)} theorem(s)/lemma(s); list them with --list", file=sys.stderr)
        return 1

    out = run_probe(args.module, name)

    if missing_olean(out) or "error:" in out:
        explain_failure(out, name)
        return 1

    m = AXIOM_LINE.search(out)
    if not m:
        print(f"::error::no axiom report for '{name}' -- the name did not resolve",
              file=sys.stderr)
        sys.stderr.write(out[-4000:])
        return 1

    found = [a.strip() for a in m.group(1).split(",") if a.strip()]
    extra = [a for a in found if a not in ALLOWED]

    if extra:
        print(f"::error::{name} depends on axioms outside {ALLOWED}: "
              f"{', '.join(extra)}", file=sys.stderr)
        if "sorryAx" in extra:
            print("::error::`sorryAx` means the proof is incomplete -- this theorem is "
                  "still a hole, whatever the module's other declarations look like.",
                  file=sys.stderr)
        return 1

    print(f"ok: {name}: axioms [{', '.join(found)}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
