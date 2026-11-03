#!/usr/bin/env python3
"""Add the seven classical results that the repository already proves but the
field map did not list, as new leaves (F16–F18, S22–S23, D21–D22).

The field map's identifiers are never reused, so these take the next free
identifiers in each section.  Every declaration listed here already exists and is
pinned axiom-clean; the script only records them.
"""
from __future__ import annotations

import re
from pathlib import Path

MAP = Path(__file__).resolve().parent.parent.parent / "docs" / "field-map.md"

# leaf id -> (title, reference, [declarations], notes)
NEW_LEAVES: dict[str, tuple[str, str, list[str], str]] = {
    "F16": (
        "Conservation laws are constants of motion",
        "Feinberg 2019, ch. 3",
        ["CRNT.Network.conservationLaw_const_along_solution"],
        "The dynamic half of the conservation-law theory, which leaf F4 records only "
        "dimensionally: along every mass-action solution, the pairing of a conservation law "
        "with the trajectory is constant.",
    ),
    "F17": (
        "The directed matrix-tree theorem in cofactor form",
        "Moon 1964; Horn–Jackson 1972",
        [
            "CRNT.Network.kineticCofactor_eq_treeConstant",
            "CRNT.Network.kineticCofactor_pos_of_weaklyReversible",
        ],
        "The kinetic (cofactor) form of the matrix-tree theorem, which leaf F12 records only "
        "in the combinatorial identification: the cofactor of the kinetic matrix is the tree "
        "constant, and it is strictly positive for a weakly reversible network.",
    ),
    "F18": (
        "Subnetwork and embedded-network theory",
        "Feinberg 2019, ch. 2",
        [
            "CRNT.Network.restrictReactions",
            "CRNT.Network.restrictReactions_complexes_subset",
            "CRNT.Complex.restrict",
            "CRNT.Reaction.restrictSpecies",
        ],
        "The two elementary constructions on which every network reduction rests: the "
        "reaction-restricted subnetwork and the species-projected embedded network.",
    ),
    "S22": (
        "The Wegscheider converse",
        "Wegscheider 1901; Feinberg 1989",
        [
            "CRNT.Network.satisfiesWegscheider_iff_hasWegscheiderPotential",
            "CRNT.Network.satisfiesWegscheider_iff_exists_positive_reactionwiseDetailedBalanced",
        ],
        "The converse of leaf S1: a network satisfies the Wegscheider conditions if and only if "
        "it has a reactionwise detailed-balanced state (equivalently a Wegscheider potential).",
    ),
    "S23": (
        "Perron–Frobenius theory for primitive nonnegative matrices",
        "Gantmacher 1960, ch. VIII; Horn–Jackson 1974",
        [
            "CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero",
            "CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive",
            "CRNT.Network.collatz_wielandt_bounds",
            "CRNT.Network.exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive",
        ],
        "The Perron–Frobenius step of leaf S20 in its classical form: a primitive nonnegative "
        "matrix (entrywise nonnegative with a strictly positive power) is not nilpotent and "
        "has a nonzero eigenvalue; the Collatz–Wielandt inequalities bound a Perron-type "
        "eigenvalue. Mathlib has no Perron root and no Perron–Frobenius theorem, so the "
        "spectral-radius statement itself is out of reach.",
    ),
    "D21": (
        "The linearization at a complex-balanced equilibrium",
        "Horn–Jackson 1972, Thm 7.B",
        [
            "CRNT.Network.complexBalanced_hasStrictStoichQuadraticLyapunov",
            "CRNT.Network.strictStoichQuadraticLyapunov_implies_hurwitz",
            "CRNT.Network.complexBalanced_isHurwitzOnStoich",
        ],
        "The linearization theorem behind leaf D4: the reduced Jacobian at a positive "
        "complex-balanced equilibrium is Hurwitz on the stoichiometric subspace, and there is a "
        "strict quadratic Lyapunov function there.",
    ),
    "D22": (
        "Global asymptotic stability under persistence",
        "Anderson 2011; Craciun 2015",
        ["CRNT.Network.omegaLimit_eq_singleton_of_persistent"],
        "The persistence-conditional form of global asymptotic stability, which is distinct "
        "from the local statement of leaf D4 and from the single-linkage theorem of leaf D6.",
    ),
}

# where each new leaf is inserted in its section, and the tree line
TREE_LINES = {
    "F16": "│   ├── F16 conservation laws are constants of motion            proved",
    "F17": "│   ├── F17 directed matrix-tree theorem, cofactor form      proved",
    "F18": "│   ├── F18 subnetworks and embedded networks                proved",
    "S22": "│   ├── S22 the Wegscheider converse                          proved",
    "S23": "│   ├── S23 Perron–Frobenius for primitive matrices          proved",
    "D21": "│   ├── D21 the linearization at a complex-balanced point     proved",
    "D22": "│   ├── D22 global stability under persistence              proved",
}

# the tree line after which each new leaf is inserted
TREE_AFTER = {
    "F16": "│   └── F15 circulation decomposition                              proved",
    "F17": None,   # handled below (F15 is the last of the F block)
    "F18": None,
    "S22": None,
    "S23": None,
    "D21": None,
    "D22": None,
}


def main() -> None:
    text = MAP.read_text(encoding="utf-8")
    lines = text.split("\n")

    # ---- 1. insert the new leaf rows into the leaf tables -------------------
    section_of = {"F": "F. Foundations", "S": "S. Steady states", "D": "D. Deterministic dynamics"}
    out: list[str] = []
    cur_section = ""
    for line in lines:
        if line.startswith("### "):
            cur_section = line[4:].strip()
        if line.startswith("|") and not line.startswith("|---"):
            cols = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cols) >= 5 and re.fullmatch(r"[A-Z]\d+", cols[0]):
                out.append(line)
                # append the new leaves of this section right after the LAST row of it
                continue
        out.append(line)

    # find the last row of each section and insert the new rows there
    rows_by_section: dict[str, list[int]] = {}
    cur_section = ""
    for i, line in enumerate(out):
        if line.startswith("### "):
            cur_section = line[4:].strip()
        if line.startswith("|") and not line.startswith("|---"):
            cols = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cols) >= 5 and re.fullmatch(r"[A-Z]\d+", cols[0]):
                rows_by_section.setdefault(cur_section, []).append(i)

    inserts: list[tuple[int, str]] = []
    for leaf, (title, ref, decls, notes) in NEW_LEAVES.items():
        sect = section_of[leaf[0]]
        if sect not in rows_by_section:
            raise SystemExit(f"section {sect} not found")
        idx = rows_by_section[sect][-1] + 1
        lean = ", ".join(f"`{d}`" for d in decls)
        row = f"| {leaf} | {title} | {ref} | {lean} | proved | {notes} |"
        inserts.append((idx, row))

    for idx, row in sorted(inserts, reverse=True):
        out.insert(idx, row)

    # ---- 2. update the tree --------------------------------------------------
    tree_idx = None
    for i, line in enumerate(out):
        if line.startswith("```") and tree_idx is None:
            tree_idx = i
            break
    if tree_idx is None:
        raise SystemExit("tree block not found")

    # locate the end of the tree block
    end = tree_idx + 1
    while end < len(out) and out[end].strip() != "```":
        end += 1

    tree = out[tree_idx + 1:end]
    # insert the new leaves after the last line of the relevant block
    def block(prefix: str) -> list[int]:
        return [i for i, l in enumerate(tree) if l.startswith(prefix)]

    # F block: F15 is the last line starting with "│   └── F15"
    f_last = next(i for i, l in enumerate(tree) if "F15 " in l)
    tree[f_last:f_last + 1] = [
        TREE_LINES["F16"], TREE_LINES["F17"], TREE_LINES["F18"],
        "│   └── F15 circulation decomposition                              proved",
    ]
    # S block: S21 is the last line starting with "│   └── S21"
    s_last = next(i for i, l in enumerate(tree) if "S21 " in l)
    tree[s_last:s_last + 1] = [
        TREE_LINES["S22"], TREE_LINES["S23"],
        "│   └── S21 King–Altman formula: the steady state as a ratio       proved",
    ]
    # D block: D20 is the last line starting with "│   └── D20"
    d_last = next(i for i, l in enumerate(tree) if "D20 " in l)
    tree[d_last:d_last + 1] = [
        TREE_LINES["D21"], TREE_LINES["D22"],
        "│   └── D20 intermediates and their elimination                    proved",
    ]

    out = out[:tree_idx + 1] + tree + out[end:]

    MAP.write_text("\n".join(out), encoding="utf-8")
    print("added leaves:", ", ".join(sorted(NEW_LEAVES)))


if __name__ == "__main__":
    main()
