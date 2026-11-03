#!/usr/bin/env python3
"""holeA_refute_search.py — systematic search for a counterexample to Hole A.

Target: `CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`,
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`.

HYPOTHESIS SET UNDER TEST (BRIEF-A.md A.1), written in the notation of the
Python objects below.  A network is a list of (source, target) complexes over a
species set `S = {0..n-1}`, complexes being tuples of natural numbers;
`Concentration S = S -> R` in the Lean development, so signs are unconstrained
by the type.  Rate constants `k[i] > 0`.

  hxs  : xstar.Positive                        xstar[s] > 0 for all s
  hcb  : N.IsComplexBalanced k xstar          inflow = outflow at every complex
  hsol : the orbit of x0 solves dx/dt = massActionVectorField k x
  hK,hmaps : the forward orbit is bounded
  hwmax : wmax is in the omega-limit set
  hzeroMax : Pmax = { s | wmax[s] = 0 }
  hcard : |Pmax| >= 2
  hmaxExact : every omega-point vanishing on Pmax vanishes exactly on Pmax
  hzcard : no omega-point has a zero set larger than Pmax
  hcodim : rank( proj_{Pmax} stoichSubspace ) >= 2
  hrank : stoichRank != 1
  homegaaff : every omega-point is in the stoichiometric class of x0
  hx0 : x0.Positive

CONCLUSION (what must be refuted): some omega-point is strictly positive.

So a counterexample is: a network with a certified strictly positive
complex-balanced point, and a positive start point whose genuine trajectory has
omega-limit set equal to a nonnegative point `w` with `|zero(w)| >= 2` and
`rank(proj_{zero(w)} stoichSubspace) >= 2`.  When the trajectory converges to a
single point, `hmaxExact` and `hzcard` hold automatically (the omega-limit set is
a singleton), and `hzeroMax` holds with `Pmax = zero(w)`.

Complex balance is NEVER accepted from a floating-point residual: candidates are
snapped to rationals and the complex-balance equations are re-verified with
`fractions.Fraction`.  Weakly reversible networks are complex balanced by
Craciun's theorem and are searched too — the Global Attractor Conjecture is open
precisely there.

Deterministic: fixed `random.Random(seed)`; re-running a seed reproduces it.

Usage:  python3 holeA_refute_search.py [1|2|both] [seed] [iters]
"""

import itertools
import random
import sys
from fractions import Fraction

import numpy as np

try:
    from scipy.integrate import solve_ivp
    from scipy.optimize import least_squares
except ImportError:  # pragma: no cover
    sys.exit("holeA_refute_search.py needs numpy and scipy")


# ------------------------------------------------------------- networks -----

def complexes(recs):
    out = []
    for s, t in recs:
        for c in (s, t):
            if c not in out:
                out.append(c)
    return out


def rand_network(rng, n, nreac, maxc):
    seen, recs = set(), []
    for _ in range(800):
        if len(recs) >= nreac:
            break
        src = tuple(rng.randint(0, maxc) for _ in range(n))
        tgt = tuple(rng.randint(0, maxc) for _ in range(n))
        if not any(src) or not any(tgt) or src == tgt:
            continue
        if (src, tgt) in seen:
            continue
        seen.add((src, tgt))
        recs.append((src, tgt))
    return recs


def singleton(n, k):
    """The complex `{k}` as a length-`n` tuple of multiplicities."""
    return tuple(1 if a == k else 0 for a in range(n))


def unimolecular_networks(n, max_reacs):
    """Every first-order network with at most `max_reacs` distinct ordered
    reactions `i -> j`, `i != j`; a reaction is the pair `({i}, {j})`."""
    edges = [(i, j) for i in range(n) for j in range(n) if i != j]
    for size in range(1, max_reacs + 1):
        for combo in itertools.combinations(edges, size):
            yield [(singleton(n, i), singleton(n, j)) for (i, j) in combo]


def stoich_matrix(recs):
    n = len(recs[0][0])
    return np.array([[float(t[a]) - float(s[a]) for a in range(n)] for s, t in recs])


def rank(A, tol=1e-9):
    if A.size == 0:
        return 0
    return int(np.linalg.matrix_rank(A, tol=tol))


def proj_rank(recs, cols):
    A = stoich_matrix(recs)
    B = A[:, list(cols)]
    return rank(B) if B.size else 0


def is_weakly_reversible(recs):
    n = len(recs[0][0])
    parent = list(range(2 * len(recs)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for i, (s, t) in enumerate(recs):
        union(2 * i, 2 * i + 1)
        for a in range(n):
            if s[a]:
                union(2 * i, a)
            if t[a]:
                union(2 * i + 1, a)
    return len({find(2 * i) for i in range(len(recs))}) == 1


def balanced_source_set(recs):
    """Necessary for CB at a strictly positive point: every complex that occurs
    as a source also occurs as a target (rates and xstar are strictly positive)."""
    return {s for s, _ in recs} == {t for _, t in recs}


# ------------------------------------------------------ complex balance ----

def cb_residual(recs, k, x):
    cs = complexes(recs)
    res = np.zeros(len(cs))
    for idx, (s, t) in enumerate(recs):
        mon = 1.0
        for a, sa in enumerate(s):
            if sa:
                mon *= max(x[a], 0.0) ** sa
        r = k[idx] * mon
        res[cs.index(t)] += r
        res[cs.index(s)] -= r
    return res


def rational_cb_residual(recs, k, x):
    res = {c: Fraction(0) for c in complexes(recs)}
    for (s, t), kk in zip(recs, k):
        mon = Fraction(1)
        for a, sa in enumerate(s):
            if sa:
                mon *= x[a] ** sa
        res[t] += kk * mon
        res[s] -= kk * mon
    return res


def certify_positive_cb(recs, k, x, den=10**6):
    """x floats -> exact rational certificate of complex balance at a strictly
    positive point, or None."""
    if any(v <= 0 for v in x):
        return None
    kq = [Fraction(int(round(ki * den)), den) for ki in k]
    for d in (den, den * 100, den * 10000):
        xq = [Fraction(int(round(v * d)), d) for v in x]
        if any(v <= 0 for v in xq):
            continue
        if all(v == 0 for v in rational_cb_residual(recs, kq, xq).values()):
            return xq
    return None


def positive_cb_point(recs, k, n, rng, nstart=24):
    """Return ('WR', None) for weakly reversible networks (Craciun), or an exact
    certificate, or None."""
    if is_weakly_reversible(recs) and balanced_source_set(recs):
        return ("WR", None)
    if not balanced_source_set(recs):
        return None
    best = None
    for _ in range(nstart):
        x0 = np.array([rng.uniform(0.2, 2.5) for _ in range(n)])
        try:
            sol = least_squares(lambda z: cb_residual(recs, k, z), x0,
                                xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=6000)
        except Exception:
            continue
        if np.max(np.abs(sol.fun)) < 1e-10 and np.min(sol.x) > 1e-7:
            best = sol.x if best is None or np.min(sol.x) > np.min(best) else best
    if best is None:
        return None
    cert = certify_positive_cb(recs, k, best)
    return ("numeric", cert) if cert is not None else None


# -------------------------------------------------------------- dynamics ----

def vector_field(recs, k):
    n = len(recs[0][0])
    data = [(s, np.array(t, float) - np.array(s, float)) for s, t in recs]

    def f(t, x):
        out = np.zeros(n)
        for idx, (s, v) in enumerate(data):
            mon = 1.0
            for a, sa in enumerate(s):
                if sa:
                    mon *= max(x[a], 0.0) ** sa
            out += k[idx] * mon * v
        return out

    return f


def inspect_tail(recs, tail):
    """A converged nonnegative limit with >= 2 zero coordinates and the rank
    conditions of hcodim/hcard/hrank, or None."""
    if len(tail) < 3:
        return None
    w = tail[-1]
    if np.any(w < -1e-7):
        return None
    w = np.clip(w, 0.0, None)
    zeros = [a for a in range(len(w)) if w[a] < 1e-6]
    if len(zeros) < 2:
        return None
    if proj_rank(recs, zeros) < 2:
        return None
    if rank(stoich_matrix(recs)) == 1:
        return None
    seg = tail[len(tail) // 3:]
    if np.max(np.abs(seg - w)) > 1e-5:
        return None
    return {"w": [float(v) for v in w], "zeros": zeros}


def positive_kernel_vector(M, n, tries=40000, seed=0):
    """A strictly positive vector of `ker M`, or None.

    `M x = 0` with `x > 0` is decided by `ker M` meeting the open positive
    orthant.  We take an exact-rational nullspace basis (via `fractions` row
    reduction on the SVD-identified free columns is fragile, so instead: find
    the nullspace with SVD, then search a positive combination of the basis
    vectors, then hand the winner to exact certification)."""
    U, sv, Vt = np.linalg.svd(M)
    tol = 1e-9 * max(1.0, float(sv[0]) if sv.size else 1.0)
    ns = int(np.sum(sv < tol))
    if ns == 0:
        return None
    basis = Vt[len(sv) - ns:].T          # columns spanning ker M
    if basis.shape[1] == 1:
        v = basis[:, 0]
        if np.min(v) <= 1e-12:
            return None
        return v / np.max(np.abs(v))
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(tries):
        w = rng.random(ns) * 10 + 1e-9
        x = basis @ w
        if np.max(np.abs(x)) < 1e-12:
            continue
        x = x / np.max(np.abs(x))
        if np.min(x) > 1e-9:
            best = x
            break
    if best is not None:
        return best
    # Fall back to a coarse grid: for nullity 1 this is exact, for higher
    # nullity it is a heuristic, and the caller certifies anyway.
    for combo in itertools.product(np.linspace(0, 2, 9), repeat=ns):
        x = basis @ np.array(combo, float)
        if np.max(np.abs(x)) < 1e-12:
            continue
        x = x / np.max(np.abs(x))
        if np.min(x) > 1e-9:
            return x
    return None


# -------------------------------------------------------------- phase 1 -----

def phase1(max_reacs=4, T=400.0):
    """Exhaustive exact search over first-order (unimolecular) networks."""
    hits = []
    stats = {"nets": 0, "rank_ok": 0, "cb": 0, "traj": 0}
    for n in (2, 3, 4):
        for recs in unimolecular_networks(n, max_reacs):
            stats["nets"] += 1
            A = stoich_matrix(recs)
            if rank(A) < 2:
                continue
            stats["rank_ok"] += 1
            # first-order mass action: dx/dt = M x,  M[:, sole reactant] += k*v
            M = np.zeros((n, n))
            for s, t in recs:
                b = s.index(1)
                M[:, b] += np.array([float(t[a]) - float(s[a]) for a in range(n)])
            # Complex balance at a strictly positive point for a first-order
            # network is exactly `M x = 0` for some `x` with `x > 0`: species `b`
            # gains `sum_{r: target = b} x_{sole reactant} - sum_{r: source = b}
            # x_{sole reactant}`, which is the `b`-th component of `M x`.  So
            # decide it on `ker M` -- NOT the range of `M^T`, which is where an
            # earlier revision looked and which is why it reported `cb = 0` on
            # every single network.
            found = positive_kernel_vector(M, n)
            if found is None:
                continue  # `ker M` has no strictly positive vector
            if certify_positive_cb(recs, [1.0] * len(recs), found) is None:
                continue  # the float kernel vector failed exact certification
            stats["cb"] += 1
            wr = is_weakly_reversible(recs)

            def f(t, y, M=M):
                return M @ y

            for x0 in (np.ones(n), np.linspace(0.7, 2.1, n)):
                try:
                    sol = solve_ivp(f, (0, T), x0, method="LSODA",
                                    rtol=1e-11, atol=1e-13, max_step=1.0)
                except Exception:
                    continue
                if not sol.success or sol.t.size < 5:
                    continue
                stats["traj"] += 1
                tail = np.array([sol.y[:, i] for i in
                                 range(sol.t.size * 2 // 3, sol.t.size)])
                d = inspect_tail(recs, tail)
                if d:
                    hits.append({"recs": recs, "x0": list(x0), "weakly_reversible": wr, **d})
                    print("PHASE1 HIT", recs, "x0=", list(x0), d, flush=True)
    print("phase1", stats, "hits", len(hits))
    return hits


# -------------------------------------------------------------- phase 2 -----

def phase2(seed=0, niter=4000, T=400.0, report_every=1000):
    rng = random.Random(seed)
    hits = []
    stats = {"nets": 0, "rank_ok": 0, "srcset_ok": 0, "cb_certified": 0,
             "cb_wr": 0, "traj": 0, "hits": 0}
    for it in range(niter):
        n = rng.choice([2, 3, 4])
        nr = rng.choice([2, 3, 4, 5])
        maxc = rng.choice([1, 2])
        recs = rand_network(rng, n, nr, maxc)
        if len(recs) < 2:
            continue
        stats["nets"] += 1
        if rank(stoich_matrix(recs)) < 2:
            continue
        stats["rank_ok"] += 1
        if not balanced_source_set(recs):
            continue
        stats["srcset_ok"] += 1
        k = np.array([rng.choice([0.5, 1.0, 2.0, 3.0]) for _ in recs])
        cb = positive_cb_point(recs, list(k), n, rng)
        if cb is None:
            continue
        stats["cb_certified"] += 1
        if cb[0] == "WR":
            stats["cb_wr"] += 1
        f = vector_field(recs, list(k))
        for _ in range(6):
            x0 = np.array([rng.uniform(0.4, 2.5) for _ in range(n)])
            try:
                sol = solve_ivp(f, (0, T), x0, method="LSODA",
                                rtol=1e-11, atol=1e-13, max_step=1.0)
            except Exception:
                continue
            if not sol.success or sol.t.size < 5:
                continue
            stats["traj"] += 1
            # hK / hmaps: the forward orbit must be bounded
            if np.max(np.abs(sol.y)) > 1e4:
                continue
            tail = np.array([sol.y[:, i] for i in
                             range(sol.t.size * 2 // 3, sol.t.size)])
            d = inspect_tail(recs, tail)
            if d:
                stats["hits"] += 1
                print("PHASE2 HIT", recs, list(k), "x0=", list(x0),
                      "cb=", cb[0], d, flush=True)
                hits.append({"recs": recs, "k": list(k), "x0": list(x0),
                             "cb_kind": cb[0], "cb_cert": cb[1], **d})
        if report_every and (it + 1) % report_every == 0:
            print(f"  it={it+1} " + " ".join(f"{a}={b}" for a, b in stats.items()),
                  flush=True)
    print(f"phase2 seed={seed} " + " ".join(f"{a}={b}" for a, b in stats.items()))
    return hits


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "both"
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    total = []
    if which in ("1", "both"):
        total += phase1()
    if which in ("2", "both"):
        total += phase2(seed=seed, niter=iters)
    print("TOTAL HITS", len(total))
    sys.exit(0 if not total else 1)