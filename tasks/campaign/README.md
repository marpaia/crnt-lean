# The CRNT-Lean 12-hour formalization campaign (2026-10-21)

This directory holds the orchestrator's infrastructure for the 12-hour campaign that formalized
as much of chemical reaction network theory as possible into the `crnt-lean` library.

## Starting point

| | |
|---|---|
| start commit | `3065e963124a04e0e4830ac2f320df8c16909ba8` |
| leaves | 90 (70 proved, 20 partial) |
| pinned declarations | 1020 |
| Lean / Mathlib | 4.34.0 / v4.34.0 (`lean-toolchain`, `lake-manifest.json` unchanged) |

## Files

| file | purpose |
|---|---|
| `WORKER_PROTOCOL.md` | the rules every theorem-proving worker follows |
| `registry.py` / `registry.json` | the machine-readable task registry (the orchestrator is the only writer) |
| `check_module.py` | rejects a candidate module that uses `sorry`, `admit`, a new `axiom`, `native_decide`, `unsafe` or `@[implemented_by]` (comments and strings are stripped first) |
| `integrate.sh` | the orchestrator's integration path: forbidden-token check, `import` insertion into `CRNT.lean`, re-elaboration, static gates, field-map pins |
| `update_field_map.py`, `update_field_map2.py` | fold the campaign's declarations into `docs/field-map.md` |
| `add_leaves.py` | add the new leaves (F16–F18, S22–S23, D21–D22) |
| `base_build.sbatch` | the one-time base build of the library on the cluster |
| `sync_build.sbatch` | the authoritative independent build + axiom audit on the cluster |
| `verify_module.sbatch`, `submit.sh` | per-module isolated verification jobs |
| `diag.sbatch` | the diagnostic used to find the cluster's `--mem`/address-space interaction |

## How the campaign was run

* **Model.** Every theorem-proving worker ran on `opencode/minimax-m3.1-flash-free` (MiniMax M3.1
  Flash). Workers were given an exact target, the mathematical reference, the repository
  definitions to read, the single file they owned, and the verification command.
* **Isolation.** A worker owned exactly one new file under `CRNT/`; it never touched `CRNT.lean`,
  `CRNTFrontier.lean`, `lakefile.toml`, `docs/field-map.md`, `test/` or `scripts/`. The
  orchestrator owned the shared files and every integration.
* **Local iteration, cluster verification.** Workers elaborated their module locally with
  `lake env lean <file>` (the library was already built). The *authoritative* check — a build
  from scratch on the cluster, followed by the field-map pin audit — was run inside Slurm
  allocations on the `any_cpu` partition.
* **Nothing heavy on the login node.** `elan`'s toolchain download and `git` were the only things
  run on the login node; every Lean compilation and every audit ran inside a `sbatch` job.

## The cluster: the `--mem` / address-space interaction

The CSB cluster's Slurm applies `--mem` as an **address-space** limit (`RLIMIT_AS`), not as a
cgroup limit. Lean reserves a large virtual arena and allocates one thread stack per worker, so
*any* `--mem` below roughly 32 GB makes `lake build` abort with

```
libc++abi: terminating due to uncaught exception of type lean::exception:
failed to create thread: Resource temporarily unavailable
```

This was diagnosed with `tasks/campaign/diag.sbatch` (which prints `ulimit -a`, the cgroup
`pids.max`, and tries to spawn threads from both Python and Lean). The fix is to request **no**
address-space cap (`--mem=0`) and to bound the campaign by the number of concurrent jobs; the
*actual* consumption is read back from `sacct` (`MaxRSS`). The base build and the verification
jobs were run this way, with 4 CPUs each — well inside the campaign's budget of 48 CPUs.

## Results

See the final campaign report. In brief: every leaf that the field map listed as *missing* was
either closed or closed with a **machine-checked refutation of the proposed statement** (which is
a result too: it records that the naive reading is false). The field map now has **99 leaves**
(79 proved, 20 partial) and **1245 pinned declarations**, and `docs/field-map.md` records, for
every leaf, what was added and what remains.

The campaign added **59 new Lean modules** (about 38 000 lines) to the library, in **30 commits**,
all axiom-clean (`[propext, Classical.choice, Quot.sound]`) and all verified by an independent
from-scratch build on the cluster.

## Notable mathematical findings of the campaign

Several of the statements the field map proposed as targets turned out to be **false**, and the
campaign proved them false rather than weakening them silently:

* the total-degree theorem is false for a general fully open network (the repository already knew
  this; the campaign generalized the counterexample to an arbitrary invertible affine linear part);
* the Halanay estimate is false without `0 ≤ M` (a negative solution is *raised* by the delayed
  term) — the campaign proved the correct form and the counterexample;
* "two positive steady states of opposite sign ⟹ an even number of positive steady states" is
  false; the correct consequence is about the *parity* of the class degree;
* the BKK bound for an `n+2`-monomial circuit system in the "mixed volume of the circuit
  simplex" reading is false — the Newton polytope is a *larger* polytope;
* the Markus–Yamabe *flow* version (an operator-norm contraction alone forces attraction) is
  false — `X → 2X` is a counterexample;
* "strictly positive inflow ⟹ the open conservation-law space is trivial" is false;
* the global uniqueness of the entropy-production minimizer is false — the minimizers form the
  toric manifold of detailed-balanced states;
* no Lyapunov function of the proposed piecewise-quadratic shape can give the antithetic closed
  loop an exponential drift, and allowing the slope to depend on `z₁` does not help.

## Preserved for later

The field map's remaining gaps are now precisely localised. The items that are **open in the
literature** (and are therefore not formalized) are listed in the map's own "Gaps by tier"
section. The items that are *formalization* gaps are recorded per leaf, together with the
precise obstruction that was found.
