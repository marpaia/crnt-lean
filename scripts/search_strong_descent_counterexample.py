#!/usr/bin/env python3
"""Search for a counterexample to the unseparated strong-concordance descent theorem.

Wanted: a network N that is
  (1) weakly normal,
  (2) strongly discordant,
  (3) whose fully open extension is strongly concordant.

Such an N would refute `stronglyConcordant_of_fullyOpen_of_weaklyNormal` as stated
(without `ReactantProductSeparated`).

All three properties reduce to finitely many homogeneous linear feasibility problems,
indexed by the sign vector xi in {-1,0,+1}^S of the witness displacement sigma, because the
strong clauses depend on sigma only through its sign pattern:

  dirSign r s = source r s - target r s
  Pallowed(r, xi)  <->  exists s, dirSign r s != 0 and xi s ==  sgn (dirSign r s)
  Oallowed(r, xi)  <->  exists s, dirSign r s != 0 and xi s == -sgn (dirSign r s)
  Zallowed(r, xi)  <->  (forall s, source r s != 0 -> xi s == 0) or (Pallowed and Oallowed)

N strongly discordant
  <->  exists xi != 0 realizable as the sign pattern of some sigma in S, with some
       alpha in the allowed sign classes and sum_r alpha_r nu_r = 0.

fullyOpen(N) strongly discordant
  <->  exists xi != 0 and beta in the allowed sign classes with
       sign ((sum_r beta_r nu_r) s) == xi s for every s.
  (sigma' ranges over all of R^S in the fully open extension, so every xi is realizable.)

Homogeneity lets every strict inequality "x > 0" be replaced by "x >= 1".
"""

import itertools
import numpy as np
from scipy.optimize import linprog

SIGNS = (-1, 0, 1)


def feasible(n_vars, eqs, lower, upper):
    """Feasibility of {A x = b} with per-variable bounds, via an LP with zero objective."""
    A_eq = np.array([e[0] for e in eqs], dtype=float) if eqs else None
    b_eq = np.array([e[1] for e in eqs], dtype=float) if eqs else None
    bounds = list(zip(lower, upper))
    res = linprog(np.zeros(n_vars), A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    return res.status == 0


def sgn(x):
    return (x > 0) - (x < 0)


class Net:
    def __init__(self, name, nspecies, reactions):
        # reactions: list of (source, target) with source/target tuples of naturals
        self.name = name
        self.n = nspecies
        self.rx = reactions
        self.nu = [tuple(t[i] - s[i] for i in range(nspecies)) for s, t in reactions]
        self.dir = [tuple(s[i] - t[i] for i in range(nspecies)) for s, t in reactions]

    def separated(self):
        return all(t[i] == 0 for s, t in self.rx for i in range(self.n) if s[i] != 0)

    def allowed(self, r, xi):
        """Which signs alpha_r may take: set subset of {-1,0,1}."""
        d = self.dir[r]
        src = self.rx[r][0]
        P = any(d[i] != 0 and xi[i] == sgn(d[i]) for i in range(self.n))
        O = any(d[i] != 0 and xi[i] == -sgn(d[i]) for i in range(self.n))
        Z = all(xi[i] == 0 for i in range(self.n) if src[i] != 0) or (P and O)
        out = set()
        if P:
            out.add(1)
        if O:
            out.add(-1)
        if Z:
            out.add(0)
        return out

    def bounds_for(self, xi):
        """Per-reaction (lower, upper) encoding the allowed sign classes, or None if empty.

        A sign class set is encoded as an interval only when it is one of
        {0}, [1,inf), (-inf,-1], (-inf,inf).  The set {-1,1} (zero disallowed) is not an
        interval; such reactions are split on separately by the caller.
        """
        res = []
        for r in range(len(self.rx)):
            a = self.allowed(r, xi)
            if not a:
                return None
            if a == {0}:
                res.append((0.0, 0.0, None))
            elif a == {1}:
                res.append((1.0, None, None))
            elif a == {-1}:
                res.append((None, -1.0, None))
            elif a == {0, 1}:
                res.append((0.0, None, None))
            elif a == {0, -1}:
                res.append((None, 0.0, None))
            elif a == {0, 1, -1}:
                res.append((None, None, None))
            else:  # {1,-1}: needs a branch
                res.append((None, None, "split"))
        return res

    def _branches(self, bnds):
        """Expand the non-interval {1,-1} cases into explicit branches."""
        idx = [i for i, b in enumerate(bnds) if b[2] == "split"]
        for choice in itertools.product((1, -1), repeat=len(idx)):
            out = list(bnds)
            for i, c in zip(idx, choice):
                out[i] = (1.0, None, None) if c == 1 else (None, -1.0, None)
            yield [(b[0], b[1]) for b in out]

    def xi_realizable_in_S(self, xi):
        """Is some sigma in the stoichiometric subspace S of sign pattern exactly xi?"""
        m = len(self.rx)
        # sigma = sum_r c_r nu_r ; variables c (free)
        eqs, lower, upper = [], [None] * m, [None] * m
        # encode sign constraints on sigma coordinatewise via extra variables
        # sigma_i = sum_r c_r nu_r i ; add slack variable t_i = sigma_i with bounds
        nv = m + self.n
        lower = [None] * m + []
        low, up = [None] * m, [None] * m
        for i in range(self.n):
            row = [self.nu[r][i] for r in range(m)] + [0.0] * self.n
            row[m + i] = -1.0
            eqs.append((row, 0.0))
            if xi[i] == 0:
                low.append(0.0); up.append(0.0)
            elif xi[i] == 1:
                low.append(1.0); up.append(None)
            else:
                low.append(None); up.append(-1.0)
        return feasible(nv, eqs, low, up)

    def strongly_discordant(self):
        m = len(self.rx)
        for xi in itertools.product(SIGNS, repeat=self.n):
            if all(x == 0 for x in xi):
                continue
            bnds = self.bounds_for(xi)
            if bnds is None:
                continue
            if not self.xi_realizable_in_S(xi):
                continue
            for bb in self._branches(bnds):
                eqs = []
                for i in range(self.n):
                    eqs.append(([self.nu[r][i] for r in range(m)], 0.0))
                low = [b[0] for b in bb]
                up = [b[1] for b in bb]
                if feasible(m, eqs, low, up):
                    return True, xi
        return False, None

    def fullyopen_strongly_discordant(self):
        """exists xi != 0 and beta allowed with sign((sum beta nu) s) == xi s for all s."""
        m = len(self.rx)
        for xi in itertools.product(SIGNS, repeat=self.n):
            if all(x == 0 for x in xi):
                continue
            bnds = self.bounds_for(xi)
            if bnds is None:
                continue
            for bb in self._branches(bnds):
                nv = m + self.n
                eqs, low, up = [], [b[0] for b in bb], [b[1] for b in bb]
                for i in range(self.n):
                    row = [self.nu[r][i] for r in range(m)] + [0.0] * self.n
                    row[m + i] = -1.0
                    eqs.append((row, 0.0))
                    if xi[i] == 0:
                        low.append(0.0); up.append(0.0)
                    elif xi[i] == 1:
                        low.append(1.0); up.append(None)
                    else:
                        low.append(None); up.append(-1.0)
                if feasible(nv, eqs, low, up):
                    return True, xi
        return False, None

    def weakly_normal(self, trials=200, seed=0):
        """Is some source-influence family's operator injective on S?

        T_P sigma = sum_r (p_r . sigma) nu_r with p_r > 0 exactly on the source support.
        Restrict to S = span{nu_r}: pick a basis of S and test the matrix determinant.
        A single nonzero determinant is a proof; all-zero over many random rationals is
        strong evidence of identical vanishing.
        """
        rng = np.random.default_rng(seed)
        m, n = len(self.rx), self.n
        NU = np.array(self.nu, dtype=float).T  # n x m
        rank = np.linalg.matrix_rank(NU)
        if rank == 0:
            return True  # S = 0, injectivity on the zero space is vacuous
        # orthonormal basis of S
        U, sv, _ = np.linalg.svd(NU)
        B = U[:, :rank]  # n x rank
        for _ in range(trials):
            P = np.zeros((m, n))
            for r in range(m):
                for i in range(n):
                    if self.rx[r][0][i] != 0:
                        P[r, i] = rng.integers(1, 6)
            # T sigma = sum_r (P[r] . sigma) nu_r  ->  matrix NU @ P
            T = NU @ P  # n x n
            M = B.T @ T @ B  # rank x rank
            if abs(np.linalg.det(M)) > 1e-9:
                return True
        return False


def catalogue():
    nets = []
    # one species, non-separated autocatalysis and friends
    nets.append(Net("A->2A", 1, [((1,), (2,))]))
    nets.append(Net("A->2A, A->0", 1, [((1,), (2,)), ((1,), (0,))]))
    nets.append(Net("2A->3A, A->0", 1, [((2,), (3,)), ((1,), (0,))]))
    # two species, catalytic / non-separated patterns
    nets.append(Net("A+B->2A", 2, [((1, 1), (2, 0))]))
    nets.append(Net("A+B->2A, A->0", 2, [((1, 1), (2, 0)), ((1, 0), (0, 0))]))
    nets.append(Net("A+B->2A, B->0", 2, [((1, 1), (2, 0)), ((0, 1), (0, 0))]))
    nets.append(Net("A+B->2A, A->B", 2, [((1, 1), (2, 0)), ((1, 0), (0, 1))]))
    nets.append(Net("A+B->2A, B->A", 2, [((1, 1), (2, 0)), ((0, 1), (1, 0))]))
    nets.append(Net("A+B->2B, A->B", 2, [((1, 1), (0, 2)), ((1, 0), (0, 1))]))
    nets.append(Net("A->A+B, B->0", 2, [((1, 0), (1, 1)), ((0, 1), (0, 0))]))
    nets.append(Net("A->A+B, B->A", 2, [((1, 0), (1, 1)), ((0, 1), (1, 0))]))
    nets.append(Net("2A->A+B, B->A", 2, [((2, 0), (1, 1)), ((0, 1), (1, 0))]))
    nets.append(Net("A+B->2A, 2B->A+B", 2, [((1, 1), (2, 0)), ((0, 2), (1, 1))]))
    nets.append(Net("A+B->2A, A+B->2B", 2, [((1, 1), (2, 0)), ((1, 1), (0, 2))]))
    nets.append(Net("A->2A, B->2B, A+B->0", 2,
                    [((1, 0), (2, 0)), ((0, 1), (0, 2)), ((1, 1), (0, 0))]))
    nets.append(Net("A+B->2A, A->0, B->0", 2,
                    [((1, 1), (2, 0)), ((1, 0), (0, 0)), ((0, 1), (0, 0))]))
    nets.append(Net("A->A+B, A+B->2B, B->0", 2,
                    [((1, 0), (1, 1)), ((1, 1), (0, 2)), ((0, 1), (0, 0))]))
    # three species catalytic
    nets.append(Net("A+B->2A+C, C->0, B->0", 3,
                    [((1, 1, 0), (2, 0, 1)), ((0, 0, 1), (0, 0, 0)), ((0, 1, 0), (0, 0, 0))]))
    nets.append(Net("A+B->2A, B+C->2B, C->0", 3,
                    [((1, 1, 0), (2, 0, 0)), ((0, 1, 1), (0, 2, 0)), ((0, 0, 1), (0, 0, 0))]))
    return nets


def main():
    print(f"{'network':28s} {'sep':>4s} {'wnorm':>6s} {'sdisc':>6s} {'FO-sdisc':>9s}  verdict")
    print("-" * 78)
    hits = []
    for N in catalogue():
        sep = N.separated()
        wn = N.weakly_normal()
        sd, _ = N.strongly_discordant()
        fo, _ = N.fullyopen_strongly_discordant()
        # counterexample: weakly normal, strongly discordant, fully open STRONGLY CONCORDANT
        ce = wn and sd and (not fo)
        verdict = "*** COUNTEREXAMPLE ***" if ce else ("consistent" if not ce else "")
        if ce and not sep:
            hits.append(N.name)
        print(f"{N.name:28s} {str(sep):>4s} {str(wn):>6s} {str(sd):>6s} {str(fo):>9s}  {verdict}")
    print()
    if hits:
        print("NON-SEPARATED COUNTEREXAMPLES FOUND:", hits)
    else:
        print("No counterexample in this catalogue: every weakly normal, strongly discordant")
        print("network here also has a strongly discordant fully open extension.")


if __name__ == "__main__":
    main()
