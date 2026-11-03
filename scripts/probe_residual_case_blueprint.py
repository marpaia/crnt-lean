#!/usr/bin/env python3
"""The residual case, concretely:  A + B <-> 2B,  A + C <-> 2C.

This network satisfies *every* hypothesis of the branch the Global Attractor hole sits in:

  * weakly reversible (two reversible pairs);
  * deficiency zero -- complexes {A+B, 2B, A+C, 2C} so n = 4, linkage classes {A+B,2B} and
    {A+C,2C} so l = 2, rank s = 2, hence n - l - s = 0 -- so it is **complex balanced for every
    rate vector**;
  * conservative: every reaction preserves total count, so `c = (1,1,1)` is a conservation law and
    the positive compatibility class is bounded, making `hMclass` automatic;
  * `P = {B, C}` is a **siphon**: the only reactions producing `B` are `A+B -> 2B` and
    `2B -> A+B`, both of which consume `B`, and symmetrically for `C`.  Nothing produces `B` or `C`
    from `A` alone;
  * `P` is **critical**: the conservation laws are the multiples of `(1,1,1)`, whose support is all
    three species, so no conservation law is supported inside `P`;
  * the face has **codimension 2**: the class is `{x_A + x_B + x_C = T}` of dimension 2, and
    `{x_B = x_C = 0}` meets it in the single point `(T,0,0)`.

So this is not a toy standing in for the residual case -- it is an instance of it.  The script
computes the source-order arrangement, the cones the face direction cone meets, and checks whether
the geometric clauses of `exists_positive_omegaPoint_of_blueprintData` can be met.

Usage:  python3 scripts/probe_residual_case_blueprint.py
"""

from __future__ import annotations

import itertools
import numpy as np

SPECIES = ["A", "B", "C"]
N = 3

# source complexes of the four reactions, as exponent vectors
SOURCES = {
    "A+B -> 2B": np.array([1.0, 1.0, 0.0]),
    "2B -> A+B": np.array([0.0, 2.0, 0.0]),
    "A+C -> 2C": np.array([1.0, 0.0, 1.0]),
    "2C -> A+C": np.array([0.0, 0.0, 2.0]),
}


def proj_V(v: np.ndarray) -> np.ndarray:
    return v - v.sum() / N * np.ones(N)


def unit(i: int) -> np.ndarray:
    e = np.zeros(N)
    e[i] = 1.0
    return e


def normalise_line(a: np.ndarray) -> tuple:
    """A canonical representative of the line spanned by `a`, for deduplication."""
    n = np.linalg.norm(a)
    if n < 1e-12:
        return None
    a = a / n
    for x in a:
        if abs(x) > 1e-9:
            if x < 0:
                a = -a
            break
    return tuple(np.round(a, 9))


def main() -> int:
    u = [proj_V(unit(i)) for i in range(N)]

    print("source-order arrangement normals  proj_V(y_r2 - y_r1):")
    lines = {}
    for (n1, y1), (n2, y2) in itertools.permutations(SOURCES.items(), 2):
        a = proj_V(y2 - y1)
        key = normalise_line(a)
        if key is not None and key not in lines:
            lines[key] = a
    normals = list(lines.values())
    for a in normals:
        print(f"     {np.round(a, 6)}")
    print(f"     distinct hyperplanes in V: {len(normals)}")
    print(f"     so the fan has {2*len(normals)} chambers + {2*len(normals)} rays + origin"
          f" = {4*len(normals)+1} cones")

    print("\nface P = {B, C}: evaluations on X = lam*u_B + mu*u_C, using <a,u_s> = (a)_s")
    breaks = []
    for a in normals:
        cB, cC = a[1], a[2]
        print(f"     a={np.round(a,4)}:  {cB:+.4f} * lam  {cC:+.4f} * mu")
        if abs(cC) > 1e-12 and cB * cC < 0:
            breaks.append(-cB / cC)
    breaks = sorted(set(round(r, 9) for r in breaks if r > 0))
    print(f"     breakpoints in the ratio r = mu/lam inside the open face cone: {breaks}")
    print(f"     => K_P is cut into {len(breaks)+1} sectors by {len(breaks)} interior walls")

    print("\nwall directions, and hpos coverage")
    covered = {s: False for s in SPECIES if s in ("B", "C")}
    for r in breaks:
        X = 1.0 * u[1] + r * u[2]
        print(f"     wall r={r}:  direction {np.round(X,6)}   (B)={X[1]:+.4f}  (C)={X[2]:+.4f}")
        if X[1] > 1e-12:
            covered["B"] = True
        if X[2] > 1e-12:
            covered["C"] = True
    print(f"     hpos coverage from wall normals alone: {covered}")

    print("\nmargins along each wall (depth rho, unit direction)")
    for r in breaks:
        X = 1.0 * u[1] + r * u[2]
        Xn = X / np.linalg.norm(X)
        vals = [float(a @ Xn) for a in normals]
        nz = sum(1 for v in vals if abs(v) > 1e-9)
        print(f"     wall r={r}: {nz} of {len(normals)} normals grow with rho, "
              f"{len(normals)-nz} vanish on the wall")
        print(f"        min nonzero |slope| = "
              f"{min(abs(v) for v in vals if abs(v) > 1e-9):.4f}")

    print("\nverdict")
    print("  * the arrangement, the sector count and the wall directions are all explicit;")
    print("  * every interior wall direction is nonnegative on B and C, and the walls jointly")
    print("    cover both face species with strictly positive coordinates, so `hpos` is met;")
    print("  * on each wall the vanishing normals are exactly the ones defining it, which is why")
    print("    `hm_of_cone_family` (normal *in* the wall) is the usable form, not")
    print("    `hm_of_single_chamber`;")
    print("  * every non-defining normal has |slope| bounded below, so the separation margin")
    print("    grows linearly in the depth rho, as `margin_of_scale_ratio` requires.")
    print("\n  Not checked here: the orbit clauses `hstart`, `hregime`, `hdeep`, which need the")
    print("  ODE integrated.  This settles the geometry of the residual case, not the blueprint.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
