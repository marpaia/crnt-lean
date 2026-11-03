# Toolchain, API, and verification changes

The development uses Lean 4.34.0 and Mathlib v4.34.0. Consumers built against the previous Lean
4.31.0 release must rebuild their dependencies and proofs; compiled Lean artifacts are specific
to the toolchain. The foundational `Complex`, `Reaction`, `Network`, and mass-action data
representations are preserved.

## Analyzer

The JSON output contract is version 19. Relative to version 14 it adds
`noPositivePeriodicOrbitCertified`, `stoichRankTwo`, `noDrainableSiphon`,
`noSelfReplicableSiphon`, `minimalCriticalSiphonDichotomy`, and `persistenceSiphonDichotomy`.
Consumers that pin the version or validate a fixed set of keys must update accordingly. The
input shape and coefficient-vector padding/truncation rules are described in
[`analyze-contract.md`](analyze-contract.md).

`NetworkData.analyze` and the drainability/self-replicability decisions are computable. Their
rational feasibility systems use explicit finite enumerations, with the `Decidable` instances
lifted through `Trunc.recOnSubsingleton`, as in the existing critical-siphon decision procedure.
The executable imports `CRNT.Interop.Analysis` directly and supports single-network and batch
JSON input. Compiled evaluation retains the compiler trust boundary documented in the contract.

## Lean compatibility

`refined_patch_normal_exists` is retained as a deprecated alias of
`exists_patch_normal_of_card_lt_finrank`. Both require the explicit cardinality bound; neither
constructs a refinement satisfying that bound.

The original signatures of `Network.siphonFace_forwardInvariant`,
`Network.siphonFace_forwardInvariant_confined`, and
`Network.siphonFace_forwardInvariant_of_relEntropy_le` accept solutions satisfying the equation
at every real time. They remain available. The generalized forms append `_forward` and only
require the differential equation for nonnegative time. Callers with the original derivative
witness can keep using the original names without inserting extra lambdas.

The default `CRNT` import exposes substantially more mathematics. Consumers that only need
network analysis can import `CRNT.Interop.Analysis`; other consumers can import their specific
modules. Import expansion and the toolchain upgrade can affect elaboration and instance search
even where declaration names and types remain stable.

## Build coverage

CI requires the public library, historical frontier aggregator, scaffolds, analyzer executable,
and all Lean tests to build. No frontier build failure is ignored. Every module under `Scaffold/`
is covered by `Scaffold.+`, independently of whether the public umbrella imports it. The static
audit checks that coverage and rejects proof holes in scaffolds as well as the core and tests.

`test.FrontierAudit` checks the current conditional oscillation constructors. Their planar,
Floquet, continuation, and inheritance targets remain explicit hypotheses. The audit does not
turn those inputs into unconditional results. `test.GlobalPersistenceSmoke` and
`test.LotkaNonVacuity` also run under `lake test`.

Use Python 3.11 or later for the static audits and executable smoke tests. Reproduce the checks
with:

```bash
lake exe cache get
python3 scripts/gen_lakefile.py --check
python3 scripts/check_imports.py
python3 scripts/check_stubs.py
python3 scripts/check_undefined_names.py
python3 scripts/check_exclusions.py
lake build CRNT CRNTFrontier Scaffold analyze
lake test
python3 -m unittest discover -s test -p '*_cli.py' -v
```

The executable tests exercise the reversible-pair invariants, draining and self-replicating
siphons, batch input, the zero-species case, and invalid input. They test compiled execution in
addition to the theorem-level bridges audited by Lean.

## Mathematical review boundaries

The multistationarity modules prove capacity equivalent to semantic real-flux certificates
`DOAFeasible` and `ADAFeasible`. The first contains exponential balance equations in the unknown
log-ratio; the second permits the entire reaction set as one shelf. These are existence
characterizations. They do not implement the published algorithms' finite linear searches.
`DeficiencyOneAlgorithmCorrectness` and `ShelfFluxConstruction` make the extra shelf-flux,
placement, and upper-balance inputs explicit. General construction of those inputs and the
multi-shelf converse remain separate obligations.

The general global-attraction result is exposed both as `complexBalanced_globalAttractor`,
which quantifies over supplied global flows, and `complexBalanced_trajectory_converges`, which
states convergence of a supplied genuine forward solution. Its coordinate-floor argument runs
through `Persistence.ZeroSeparatingRegion` and `Geometry.PolyhedralBarrier`. A review of the
full claim must check those geometric statements and the existence/trajectory interfaces,
alongside the axiom guards. Build success alone is not an independent review of their
correspondence with the mathematical literature.

The Banaji–Craciun SR criterion requires `ReactantProductSeparated`, `FlowsAreSingletons`, and
`TrueSRStrongCriterion`. Its conclusion concerns strong concordance of the fully open extension.
Those hypotheses and the extension must be retained when describing or applying the theorem.
