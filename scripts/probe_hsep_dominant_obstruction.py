#!/usr/bin/env python3
"""Negative result: `hsep` cannot be routed through per-species dominant halfspaces.

`Network.coordinate_floor_of_dominant_barrier` and its class-aware sharpening
`coordinate_floor_of_dominant_class_barrier` discharge the separation clause by giving each species
`s` a barrier piece whose normal `m` is positive at `s`, with a level condition

    beta * T  <  eta  <=  <m, x>        where  beta >= max_{u != s} (m_u / c_u)^+ .

Both theorems are true.  This script shows the **route** is inadequate: on a conservative network,
the species attaining the minimum of the complex-balanced equilibrium `x*` admits no admissible
normal at all, so the family of pieces required by those theorems does not exist.

Why.  The region must contain the whole forward orbit, whose closure contains `x*`, so
`eta <= <m, x*>`.  Take the best case `beta = 0`, i.e. `m_u <= 0` for every `u != s`.  With `m` in
the stoichiometric subspace of a mass-conserving network, `sum_u m_u = 0`, hence
`sum_{u != s} |m_u| = m_s`, and the requirement `<m, x*> > 0` reads

    m_s * x*_s  >  sum_{u != s} |m_u| * x*_u ,

i.e. `x*_s` strictly exceeds a convex combination of the other `x*_u`.  That is impossible exactly
when `x*_s` is the minimum.  Allowing a positive entry elsewhere only raises `beta`, which hurts.

Consequence for the blueprint: the coordinate floors must come from the *global* geometry of the
guarded region -- the staircase -- and not from one dominant halfspace per species.  Craciun's
zero-separating hypersurface bounds the coordinates below by being the surface, not by a
per-coordinate inequality.

Note also the degenerate case: with all rate constants equal, `x*` is proportional to the
conservation vector `c`, and then `<m, x*> = 0` for *every* `m` in the stoichiometric subspace, so
no halfspace with `eta > 0` contains `x*` and every species fails.  Generic rates are needed even
to see the real obstruction.

Usage:  python3 scripts/probe_hsep_dominant_obstruction.py
"""

from __future__ import annotations

import itertools
import numpy as np

NAMES = "ABC"


def best_slack(xs: np.ndarray, s: int, grid=25, span=3.0):
    """Maximise  <m,x*> - beta*T  over m in V = {sum 0} with m_s > 0.  T = 1."""
    best = None
    idx = [i for i in range(3) if i != s]
    for p in itertools.product(np.linspace(-span, span, grid), repeat=2):
        m = np.zeros(3)
        m[idx[0]], m[idx[1]] = p
        m[s] = -(m[idx[0]] + m[idx[1]])
        if m[s] <= 1e-9:
            continue
        beta = max(max(m[u], 0.0) for u in idx)
        slack = float(m @ xs) - beta
        if best is None or slack > best[0]:
            best = (slack, m.copy(), beta)
    return best


def main() -> int:
    print("degenerate case first: equal rates make x* proportional to c")
    xs = np.array([1.0, 1.0, 1.0]) / 3
    for s in range(3):
        slack, m, beta = best_slack(xs, s)
        print(f"   s={NAMES[s]}: best slack = {slack:+.5f}  -> "
              f"{'feasible' if slack > 1e-9 else 'NO ADMISSIBLE NORMAL'}")
    print("   (<m,x*> = 0 for every m in V, so all three fail)\n")

    print("generic rates:")
    for raw in [np.array([1.0, 2.0, 1.0]), np.array([1.0, 3.0, 2.0]),
                np.array([2.0, 5.0, 1.0]), np.array([3.0, 1.0, 2.0])]:
        xs = raw / raw.sum()
        mn = xs.min()
        argmin = [NAMES[i] for i in range(3) if abs(xs[i] - mn) < 1e-12]
        print(f"  x* = {np.round(xs, 4)}   min at {argmin}")
        for s in range(3):
            slack, m, beta = best_slack(xs, s)
            verdict = "feasible" if slack > 1e-9 else "NO ADMISSIBLE NORMAL"
            print(f"     s={NAMES[s]}: best slack = {slack:+.5f}   m={np.round(m,3)}  -> {verdict}")
        print()

    print("In every case the species attaining min x* has no admissible normal.")
    print("So `hsep` must NOT be discharged via per-species dominant halfspaces.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
