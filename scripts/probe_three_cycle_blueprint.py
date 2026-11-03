#!/usr/bin/env python3
"""Concrete instance check of the blueprint geometry.

Network: the monomolecular 3-cycle  A -> B -> C -> A  on species {A, B, C}.
Weakly reversible, deficiency zero, hence complex balanced for every rate vector; conservative
(A + B + C is conserved), so the bounded-class hypothesis `hMclass` is automatic.

Its stoichiometric subspace is `V = {v : sum v = 0}` (dimension 2), and the source complexes are
the three single-species complexes, so the source-complex differences are

    a1 = e_B - e_A,   a2 = e_C - e_B,   a3 = e_A - e_C

which already lie in `V`.  The arrangement of their orthogonal complements inside the 2-plane `V`
is three lines through the origin: **six chambers, six rays, one origin — thirteen cones**, which is
exactly the fan drawn in Craciun v3 Figure 3(a).

What this script checks, all against the Lean statements it is meant to validate:

  1  `coord_euclideanStoichUnit_self`:  (u_s)_s = ||u_s||^2
  2  `inner_euclideanStoichUnit`:       <m, u_s> = m_s
  3  the arrangement really has 13 cones
  4  for P = {A, B} (a codimension-2 face of the compatibility class), which cones the face
     direction cone meets, and what the wall between them is
  5  that the wall normal is positive at *both* face species, so one piece can serve both
  6  that the separation margins against every non-containing cone grow linearly in the depth,
     as `margin_of_scale_ratio` predicts

Usage:  python3 scripts/probe_three_cycle_blueprint.py
"""

from __future__ import annotations

import itertools
import numpy as np

SPECIES = ["A", "B", "C"]
N = 3


def proj_V(v: np.ndarray) -> np.ndarray:
    """Orthogonal projection onto V = {v : sum v = 0}."""
    return v - v.sum() / N * np.ones(N)


def unit(i: int) -> np.ndarray:
    e = np.zeros(N)
    e[i] = 1.0
    return e


def main() -> int:
    u = [proj_V(unit(i)) for i in range(N)]  # euclideanStoichUnit
    # source-complex differences (already in V)
    a = [proj_V(unit(1) - unit(0)), proj_V(unit(2) - unit(1)), proj_V(unit(0) - unit(2))]

    print("1  coord_euclideanStoichUnit_self:  (u_s)_s == ||u_s||^2")
    for i, s in enumerate(SPECIES):
        lhs, rhs = u[i][i], float(u[i] @ u[i])
        print(f"     s={s}:  {lhs:.6f}  vs  {rhs:.6f}   {'ok' if abs(lhs-rhs) < 1e-12 else 'MISMATCH'}")

    print("\n2  inner_euclideanStoichUnit:  <m, u_s> == m_s   (m ranges over the arrangement normals)")
    ok = True
    for j, aj in enumerate(a):
        for i, s in enumerate(SPECIES):
            lhs, rhs = float(aj @ u[i]), aj[i]
            if abs(lhs - rhs) > 1e-12:
                ok = False
                print(f"     MISMATCH a{j+1}, s={s}: {lhs} vs {rhs}")
    print(f"     all {len(a)*N} pairs agree: {ok}")

    print("\n3  the arrangement inside V: chambers and rays")
    # orthonormal basis of V
    b1 = proj_V(unit(0));  b1 /= np.linalg.norm(b1)
    b2 = proj_V(unit(1) - unit(2));  b2 = b2 - (b2 @ b1) * b1;  b2 /= np.linalg.norm(b2)

    def sv(X):
        return tuple(int(np.sign(round(float(aj @ X), 12))) for aj in a)

    # rays: each line {<a_j, .> = 0} in the 2-plane V meets the circle in two antipodal points.
    # Computing them exactly rather than by sampling, which almost never lands on a line.
    rays = set()
    for aj in a:
        c1, c2 = float(aj @ b1), float(aj @ b2)
        d = -c2 * b1 + c1 * b2          # in V, orthogonal to aj
        d /= np.linalg.norm(d)
        rays.add(sv(d))
        rays.add(sv(-d))
    # chambers: sample the open sectors between consecutive rays
    angles = []
    for aj in a:
        c1, c2 = float(aj @ b1), float(aj @ b2)
        th = np.arctan2(c1, -c2)
        angles += [th % (2 * np.pi), (th + np.pi) % (2 * np.pi)]
    angles = sorted(angles)
    chambers = set()
    for k in range(len(angles)):
        mid = (angles[k] + (angles[(k + 1) % len(angles)]
               + (2 * np.pi if k == len(angles) - 1 else 0))) / 2
        chambers.add(sv(np.cos(mid) * b1 + np.sin(mid) * b2))
    print(f"     full-dimensional chambers: {len(chambers)}")
    print(f"     rays: {len(rays)}")
    print(f"     total cones = {len(chambers)} + {len(rays)} + 1 (origin) = "
          f"{len(chambers) + len(rays) + 1}")
    print("     Figure 3(a) of v3 shows 13 cones: six 2-dimensional, six 1-dimensional, the origin.")

    print("\n4  face P = {A, B}: which cones does K_P = cone(u_A, u_B) meet?")
    print("     <a_j, lam*u_A + mu*u_B> = lam*(a_j)_A + mu*(a_j)_B :")
    for j, aj in enumerate(a):
        print(f"       a{j+1}:  {aj[0]:+.0f} * lam  {aj[1]:+.0f} * mu")
    met = set()
    for lam, mu in [(1, 0.5), (1, 1), (0.5, 1), (1, 0), (0, 1)]:
        X = lam * u[0] + mu * u[1]
        sv = tuple(int(np.sign(round(aj @ X, 12))) for aj in a)
        met.add((round(lam, 3), round(mu, 3), sv))
    for lam, mu, sv in sorted(met):
        kind = "chamber" if 0 not in sv else "wall/ray"
        print(f"       lam={lam}, mu={mu}:  signs={sv}   {kind}")
    print("     => K_P meets two chambers, separated by the wall lam = mu.")

    print("\n5  the wall normal, and hpos on both face species")
    w = u[0] + u[1]
    print(f"     wall direction m = u_A + u_B = {np.round(w, 6)}")
    print(f"     (m)_A = {w[0]:+.6f}   (m)_B = {w[1]:+.6f}    both > 0: {w[0] > 0 and w[1] > 0}")
    print("     => a single piece with this normal satisfies hpos for both A and B,")
    print("        and it lies in the wall cone, hence in both adjacent chambers.")

    print("\n6  separation margins grow linearly in the depth")
    print("     tile point at depth rho along the wall: X(rho) = rho * (u_A + u_B) / ||u_A + u_B||")
    wn = w / np.linalg.norm(w)
    print("     for each arrangement normal a_j, the signed evaluation <a_j, X(rho)>:")
    for j, aj in enumerate(a):
        val = float(aj @ wn)
        print(f"       a{j+1}:  {val:+.6f} * rho     "
              f"{'(wall: identically 0)' if abs(val) < 1e-12 else '(grows with rho)'}")
    print("     the two normals with nonzero coefficient separate the tile from every cone not")
    print("     containing the wall; the third vanishes on the wall, which is precisely why the")
    print("     normal must be taken *in* the wall (hm_of_cone_family, not hm_of_single_chamber).")
    print("\n     margin against the origin cone {0} is ||X(rho)|| = rho, so the depth condition")
    print("     rho > delta + B of not_small_of_mem_activeFaceImage is exactly the separation")
    print("     from {0}.  All three requirements are met by one scale parameter.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
