#!/usr/bin/env python3
"""Exact rational verification of a candidate counterexample to

    stronglyConcordant_of_fullyOpen_of_weaklyNormal   (without separation)

No floating point. Feasibility of each homogeneous rational system is decided by
Gaussian elimination of the equalities followed by Fourier-Motzkin elimination on the
nullspace parameters.
"""

from fractions import Fraction as F
import itertools

SIGNS = (-1, 0, 1)


# ---------- exact linear algebra ----------

def nullspace(A, ncols):
    """Rational basis of {x | A x = 0}, as a list of basis vectors."""
    M = [[F(c) for c in row] for row in A]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = F(1) / M[r][c]
        M[r] = [v * inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f_ in free:
        v = [F(0)] * ncols
        v[f_] = F(1)
        for i, c in enumerate(piv):
            v[c] = -M[i][f_]
        basis.append(v)
    return basis


# ---------- Fourier-Motzkin ----------

def fm_feasible(cons, nvars):
    """cons: list (coeffs, const) meaning  coeffs . t + const >= 0.  Decide nonemptiness."""
    cons = [(list(c), k) for c, k in cons]
    for k_var in reversed(range(nvars)):
        pos, neg, zer = [], [], []
        for c, k in cons:
            if c[k_var] > 0:
                pos.append((c, k))
            elif c[k_var] < 0:
                neg.append((c, k))
            else:
                zer.append((c, k))
        new = list(zer)
        for cp, kp in pos:
            for cn, kn in neg:
                a, b = cp[k_var], -cn[k_var]          # a > 0, b > 0
                comb = [b * x + a * y for x, y in zip(cp, cn)]
                comb[k_var] = F(0)
                new.append((comb, b * kp + a * kn))
        cons = new
        if len(cons) > 20000:
            raise RuntimeError("FM blowup")
    return all(k >= 0 for _, k in cons)


def feasible_exact(eqs, ncols, bounds):
    """eqs: rows of a homogeneous system A x = 0.  bounds[i] in
    {'zero','ge1','le-1','ge0','le0','free'}."""
    B = nullspace(eqs, ncols) if eqs else [
        [F(1) if j == i else F(0) for j in range(ncols)] for i in range(ncols)]
    if not B:
        # only x = 0
        return all(b in ('zero', 'ge0', 'le0', 'free') for b in bounds)
    d = len(B)
    cons = []
    for i, b in enumerate(bounds):
        row = [B[j][i] for j in range(d)]
        if b == 'zero':
            cons.append((row, F(0)))
            cons.append(([-v for v in row], F(0)))
        elif b == 'ge1':
            cons.append((row, F(-1)))
        elif b == 'le-1':
            cons.append(([-v for v in row], F(-1)))
        elif b == 'ge0':
            cons.append((row, F(0)))
        elif b == 'le0':
            cons.append(([-v for v in row], F(0)))
    return fm_feasible(cons, d)


# ---------- CRN encoding ----------

def sgn(x):
    return (x > 0) - (x < 0)


class Net:
    def __init__(self, rx, n):
        self.rx = rx
        self.n = n
        self.m = len(rx)
        self.nu = [tuple(t[i] - s[i] for i in range(n)) for s, t in rx]
        self.dir = [tuple(s[i] - t[i] for i in range(n)) for s, t in rx]

    def separated(self):
        return all(t[i] == 0 for s, t in self.rx for i in range(self.n) if s[i] != 0)

    def allowed_strong(self, r, xi):
        d, src = self.dir[r], self.rx[r][0]
        P = any(d[i] != 0 and xi[i] == sgn(d[i]) for i in range(self.n))
        O = any(d[i] != 0 and xi[i] == -sgn(d[i]) for i in range(self.n))
        Z = all(xi[i] == 0 for i in range(self.n) if src[i] != 0) or (P and O)
        return {s for s, ok in ((1, P), (-1, O), (0, Z)) if ok}

    @staticmethod
    def branches(sets):
        opts = []
        for a in sets:
            if not a:
                return
            if a == {0}:
                opts.append(['zero'])
            elif a == {1}:
                opts.append(['ge1'])
            elif a == {-1}:
                opts.append(['le-1'])
            elif a == {0, 1}:
                opts.append(['ge0'])
            elif a == {0, -1}:
                opts.append(['le0'])
            elif a == {0, 1, -1}:
                opts.append(['free'])
            else:                      # {1,-1}
                opts.append(['ge1', 'le-1'])
        yield from itertools.product(*opts)

    def xi_bounds(self, xi):
        return ['zero' if x == 0 else ('ge1' if x == 1 else 'le-1') for x in xi]

    def strongly_discordant(self):
        for xi in itertools.product(SIGNS, repeat=self.n):
            if all(x == 0 for x in xi):
                continue
            # sigma in S with sign pattern xi:  sigma = sum c_r nu_r
            eqs = []
            for i in range(self.n):
                row = [self.nu[r][i] for r in range(self.m)] + [0] * self.n
                row[self.m + i] = -1
                eqs.append(row)
            if not feasible_exact(eqs, self.m + self.n,
                                  ['free'] * self.m + self.xi_bounds(xi)):
                continue
            sets = [self.allowed_strong(r, xi) for r in range(self.m)]
            for bnd in self.branches(sets):
                eqs2 = [[self.nu[r][i] for r in range(self.m)] for i in range(self.n)]
                if feasible_exact(eqs2, self.m, list(bnd)):
                    return True, xi, bnd
        return False, None, None

    def fullyopen_strongly_discordant(self):
        for xi in itertools.product(SIGNS, repeat=self.n):
            if all(x == 0 for x in xi):
                continue
            sets = [self.allowed_strong(r, xi) for r in range(self.m)]
            for bnd in self.branches(sets):
                eqs = []
                for i in range(self.n):
                    row = [self.nu[r][i] for r in range(self.m)] + [0] * self.n
                    row[self.m + i] = -1
                    eqs.append(row)
                if feasible_exact(eqs, self.m + self.n,
                                  list(bnd) + self.xi_bounds(xi)):
                    return True, xi, bnd
        return False, None, None

    def weakly_normal_exact(self, p):
        """p[r][i] rational weights, must be > 0 exactly on the source support.
        Returns (valid_family, det_of_operator_on_S)."""
        for r in range(self.m):
            for i in range(self.n):
                if self.rx[r][0][i] != 0 and not p[r][i] > 0:
                    return False, None
                if self.rx[r][0][i] == 0 and p[r][i] != 0:
                    return False, None
        # S basis from the reaction vectors (exact column reduction)
        cols = [[F(self.nu[r][i]) for i in range(self.n)] for r in range(self.m)]
        basis = []
        for c in cols:
            v = c[:]
            for b in basis:
                piv = next(j for j in range(self.n) if b[j] != 0)
                if v[piv] != 0:
                    f = v[piv] / b[piv]
                    v = [x - f * y for x, y in zip(v, b)]
            if any(x != 0 for x in v):
                basis.append(v)
        k = len(basis)
        if k == 0:
            return True, F(1)
        # T sigma = sum_r (p_r . sigma) nu_r, expressed in the basis
        M = []
        for bj in basis:
            img = [F(0)] * self.n
            for r in range(self.m):
                pair = sum(F(p[r][i]) * bj[i] for i in range(self.n))
                for i in range(self.n):
                    img[i] += pair * self.nu[r][i]
            # coordinates of img in basis (exact solve)
            coords = [F(0)] * k
            v = img[:]
            for idx, b in enumerate(basis):
                piv = next(j for j in range(self.n) if b[j] != 0)
                if v[piv] != 0:
                    f = v[piv] / b[piv]
                    coords[idx] = f
                    v = [x - f * y for x, y in zip(v, b)]
            if any(x != 0 for x in v):
                return True, None      # image left S: cannot happen
            M.append(coords)
        # determinant of M (k x k), exact
        A = [row[:] for row in M]
        det = F(1)
        for c in range(k):
            piv = next((i for i in range(c, k) if A[i][c] != 0), None)
            if piv is None:
                return True, F(0)
            if piv != c:
                A[c], A[piv] = A[piv], A[c]
                det = -det
            det *= A[c][c]
            inv = F(1) / A[c][c]
            A[c] = [v * inv for v in A[c]]
            for i in range(c + 1, k):
                if A[i][c] != 0:
                    f = A[i][c]
                    A[i] = [a - f * b for a, b in zip(A[i], A[c])]
        return True, det


def report(name, rx, n):
    N = Net(rx, n)
    print(f"=== {name}")
    for r, (s, t) in enumerate(rx):
        print(f"    r{r}: source {s} -> target {t}   nu = {N.nu[r]}   dirSign = {N.dir[r]}")
    print(f"    reactant/product separated : {N.separated()}")
    sd, xi, bnd = N.strongly_discordant()
    print(f"    strongly DISCORDANT        : {sd}   (sign pattern of sigma = {xi})")
    fo, xif, bf = N.fullyopen_strongly_discordant()
    print(f"    fullyOpen strongly discord.: {fo}")
    # weak normality: try small integer families
    import random
    random.seed(0)
    best = None
    for _ in range(400):
        p = [[(random.randint(1, 4) if rx[r][0][i] != 0 else 0) for i in range(n)]
             for r in range(N.m)]
        ok, det = N.weakly_normal_exact(p)
        if ok and det is not None and det != 0:
            best = (p, det)
            break
    print(f"    weakly normal (exact det)  : {best is not None}"
          + (f"   witness p = {best[0]}, det = {best[1]}" if best else ""))
    verdict = (best is not None) and sd and (not fo) and (not N.separated())
    print(f"    >>> COUNTEREXAMPLE: {verdict}")
    print()
    return verdict


if __name__ == "__main__":
    c1 = [((2, 0, 2), (1, 1, 2)), ((0, 0, 2), (1, 2, 2)), ((0, 1, 0), (1, 0, 1))]
    c2 = [((0, 0, 1), (0, 2, 1)), ((2, 1, 0), (1, 2, 2)), ((2, 0, 2), (0, 2, 1))]
    r1 = report("candidate 1", c1, 3)
    r2 = report("candidate 2", c2, 3)
    # sanity: the separated case must never be a counterexample
    sep = [((1, 0, 0), (0, 1, 0)), ((0, 1, 0), (0, 0, 1)), ((0, 0, 1), (1, 0, 0))]
    report("separated control (A->B->C->A)", sep, 3)
    print("candidate1 verified:", r1, " candidate2 verified:", r2)
