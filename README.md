# Chemical Reaction Network Theory in Lean 4

[![CI](https://github.com/marpaia/crnt-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/marpaia/crnt-lean/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.34.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.34.0-blue)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
![axioms: Mathlib only](https://img.shields.io/badge/axioms-Mathlib%20only-brightgreen)

A Lean 4 formalization of **Chemical Reaction Network Theory**, oriented toward synthetic biology,
molecular programming, and biochemical design automation.

A chemical reaction network is a set of chemical species together with the reactions among them: the
model behind gene regulatory circuits, metabolic pathways, and cell-signaling cascades. Chemical
Reaction Network Theory studies how that structure (which species react, and into what) constrains the
dynamics a network can produce, often independent of the reaction rates.

That makes the theory valuable to anyone engineering biochemical systems. When you design a circuit
such as a genetic toggle switch or a biochemical oscillator, the rate constants are usually unknown and
can drift, so the guarantees worth having are the ones that depend only on the wiring. From the
structure alone, the theory can often settle whether the network has a unique steady state, whether it
can be bistable or oscillate, whether it returns to equilibrium from any starting point, and whether
some species holds steady while others vary. You can rule a behavior out, or guarantee it, before you
build the circuit.

This library makes that theory machine-checked. The proved statements are checked by Lean's kernel. Some structural criteria have decidable procedures and exact certificates; other results require supplied analytic or algebraic hypotheses. The field map records these distinctions.

The library is built in two layers. The CRN layer formalizes structural and dynamical theory over a
composable core: species, complexes, reactions, stoichiometry, mass-action kinetics, linkage classes,
and deficiency. The mathematics layer supplies results used throughout the CRN development, including
Sperner's lemma and Brouwer's theorem in every dimension, Gale–Nikaido univalence, and forward
semiflows with LaSalle's principle.

- **Package:** `crnt-lean`
- **Namespace:** `CRNT`
- **Lean:** 4.34.0
- **Mathlib:** v4.34.0
- The default import (`import CRNT`) is **`sorry`-free** and introduces **no axioms beyond Mathlib's**
  (`[propext, Classical.choice, Quot.sound]`). CI enforces this with `test/AxiomAudit.lean`, which
  pins `#print axioms` on the headline results.

## Quick start

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (needs network)
lake build           # build the library and examples
lake test            # run the smoke tests and the axiom-cleanliness audit
```

**Score a network from the command line, no Lean required.** The `analyze` executable reads a network
as JSON and returns its structural invariants as JSON:

```bash
echo '{"numSpecies":2,"reactions":[{"source":[1,0],"target":[0,1]},
      {"source":[0,1],"target":[1,0]}]}' | lake exe analyze
```

For the reversible pair `A ⇌ B` the output includes, among about two dozen fields:

```json
{"deficiency": 0, "weaklyReversible": true, "persistenceCertified": true,
 "noPositivePeriodicOrbitCertified": true, "hasCriticalSiphon": false}
```

`A ⇌ B` is weakly reversible of deficiency zero, so `persistenceCertified` reports that for any rate
constants every positive trajectory converges to the network's complex-balanced equilibrium in its
compatibility class (Feinberg–Horn–Jackson), while `noPositivePeriodicOrbitCertified` (weakly reversible deficiency zero, or
stoichiometric rank at most one) gives the
all-parameter theorem that no nonconstant positive periodic orbit exists. Each field is a computable companion of a proven theorem,
tied to it by a bridge lemma; the full record is in [`docs/analyze-contract.md`](docs/analyze-contract.md).

**Or state and check a network in Lean:**

```lean
import CRNT
open CRNT

inductive Species | A | B deriving DecidableEq, Fintype, Repr
open Species

def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

inductive Rxn | fwd | bwd deriving DecidableEq, Fintype, Repr

def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

example : N.numComplexes = 2 := by decide
example : N.WeaklyReversible := by
  intro r; cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩
```

`Complex S` is `S → ℕ` (stoichiometric coefficients). See
[`docs/foundations.md`](docs/foundations.md) for the data model and
[`docs/decidability.md`](docs/decidability.md) for `decide` / `crnt_check` and certificates.

## Where to start

- **Designing or screening networks** (synthetic biology, molecular programming): the `analyze`
  contract in [`docs/analyze-contract.md`](docs/analyze-contract.md), and the per-network kernel-checked
  Lean certificates in [`docs/generated-certificates.md`](docs/generated-certificates.md).
- **Lean and formal methods:** [`docs/architecture.md`](docs/architecture.md) lays out the two layers,
  the core abstractions, and how the theorems depend on one another.
- **Chemical reaction network theory:** the per-area documents below, starting from the result you want.
- **Upgrading from Lean 4.31:** [`docs/pr1-migration.md`](docs/pr1-migration.md) describes the
  toolchain, analyzer contract, compatibility entry points, and validation commands.

## Mathematical coverage

The [field map](docs/field-map.md) lists all 99 areas with theorem names, hypotheses, and remaining obligations. A module that builds can still contain only a conditional or restricted result. The [semantic audit](docs/semantic-audit.md) records the reviewed snapshot; [the fixes](docs/semantic-audit-fixes.md) explain the corrected APIs and coverage claims.

- **Foundations and equilibria:** finite indexed networks, reaction graphs, stoichiometry, deficiency, exact structural certificates, Birch's theorem, deficiency-zero and deficiency-one results, complex/detailed balance, and the directed matrix-tree formula. The Perron–Frobenius development for column-stochastic matrices is separate from the incomplete general primitive-matrix theory.
- **Global attraction:** the complex-balanced trajectory theorem proves convergence of every supplied positive forward solution to its compatible positive equilibrium. A cutoff-flow construction also gives existence of such a global forward solution from every positive compatible start. Persistence is a conclusion in this chain. An ambient mass-action flow from all real, including negative, starts is a stronger interface and need not exist. See [the correspondence check](test/SemanticCorrespondence.lean).
- **Dynamics:** entropy dissipation, LaSalle, local stability, bounded Lipschitz flow construction, monotone comparison, delay-equation constructions, finite-time slow–fast error estimates, and conditional all-time tracking under transverse contraction. `LaSalleConvergence` uses a strongly monotone increasing operator to obtain equilibrium uniqueness; it does not prove Hirsch's generic convergence theorem for strongly order-preserving flows.
- **Hopf calculations:** actual mass-action derivatives and the calibrated first Lyapunov coefficient feed a periodic branch of the **cubic truncated normal form**. `MassActionHopfTaylorData` requires a positive equilibrium branch. A periodic orbit of the original mass-action field is not a conclusion of this API; nonlinear transfer and joint parameter regularity remain to be supplied.
- **Oscillation:** genuine positive periodic-trajectory predicates, explicit Lotka periodic orbits, deficiency-zero and planar cooperative non-oscillation results, child selections, and instability certificates. Minimal planar omega-limit subset classification is conditional on a supplied `PoincareBendixsonKernelBundle` and trapping hypotheses; the locally defined nonregularity predicate is not a general chaos definition.
- **Deterministic persistence:** genuine bounded-trajectory coordinate floors, complex-balanced persistence/global attraction, and tempered-rate strongly endotactic permanence. General weakly reversible global boundedness/persistence remains a distinct frontier.
- **Stochastic systems:** the count generator, minimal transition semigroup, complex-balanced product-form invariance, finite closed-region invariant laws, explicit Lyapunov/Foster recurrence criteria, one-species and additional count-tier classes, generator scaling, and nonlinear **fixed-time** Gaussian limits under their stated hypotheses. Strong endotacticity alone does not imply stochastic recurrence or non-explosion in several species; published counterexamples rule out that unrestricted claim. A filtered path process and general path-space LLN/CLT remain incomplete. Deadlock (all reactions disabled) and state absorption (no enabled firing changes the state) have separate APIs.
- **Injectivity and multistationarity:** Gale–Nikaido univalence, concordance characterization including nonnegative pairs with one positive member, sign/circuit criteria, and degree consequences. The degree implementation is a finite signed zero count at regular values. Rate homotopies require regularity of every intermediate zero; the general total-degree theorem under dissipativity is still missing.
- **Parity:** odd total class degree implies an odd count of finite nondegenerate positive steady states when boundary zeros are excluded. Full openness supplies boundary exclusion, but does not supply the total degree: a checked fully open network has exactly two positive steady states.
- **Flux feasibility:** `HasMultistationarityCapacity ↔ DOAFeasible` and the corresponding `ADAFeasible` equivalence concern real flux/log-ratio certificates. They do not implement finite Deficiency One/Advanced Deficiency decision procedures; shelf placement, general multi-shelf converse, and finite algorithm correctness remain incomplete.
- **Restricted elimination and computation:** `SingletonSource` means every reaction consumes one molecule of one species, with unrestricted products; it is a homogeneous linear class, distinct from published partitioned MESSI systems. Toric exponential log-kernel parametrizations do not yet give general rational parametrizations. `PiecewiseNatAffine` uses finitely many natural-coefficient affine expressions and has closure/construction results; it is narrower than classical semilinearity. The network `2X → Y` computes `floor(n/2)`, which is outside this predicate. The full chemical-computation characterization remains incomplete.
- **Algebra and geometry:** siphon support reformulations, determinant expressions for zonotope generators, algebraic volume polynomials, and univariate/separated-variable root bounds. Actual reaction-ideal minimal primes, the general Lebesgue-volume bridge, and the general sparse BKK multiplicity theorem remain incomplete.
- **Design and composition:** ACR, antithetic stationary setpoint identities, supplied plant Lyapunov/Foster certificate transfers, and network interconnections. General-plant ergodicity still requires the displayed drift/integrability hypotheses. Interconnection monostationarity assumes injectivity of the **combined** field; translation faithfulness assumes the displayed forward steady-state bridge.
- **Analysis:** Sperner/Brouwer on the n-simplex, equal-dimension Sard, P-matrix calculus, exact rational rank, and finite semidiscrete reaction–diffusion ODEs. The latter do not establish nonlinear continuum PDE well-posedness.

The original release's compatibility entry points are retained. Several names introduced in PR #1 were changed to describe their actual definitions; see the [migration guide](docs/pr1-migration.md) and [fix record](docs/semantic-audit-fixes.md).

## Documentation

- [`docs/field-map.md`](docs/field-map.md): the field of CRNT as a tree of leaves, each with its
  reference, Lean declarations, and status; pinned by `test/FieldMapAudit.lean`.

[`docs/architecture.md`](docs/architecture.md) is the hub: the mathematical layering, core
abstractions, and theorem dependency structure. From there:

| Doc | Covers |
|---|---|
| [`foundations.md`](docs/foundations.md) | networks, the reaction graph, stoichiometry |
| [`global-persistence.md`](docs/global-persistence.md) | global persistence/permanence APIs, proved classes, theorem frontier |
| [`dynamics.md`](docs/dynamics.md) | kinetics, complex-space factorization, the semiflow, Lyapunov/LaSalle, local stability, reduced models |
| [`oscillation.md`](docs/oscillation.md) | periodic-orbit semantics and certificates, global exclusions, return maps, child selections/unstable cores, planar global frontiers |
| [`deficiency.md`](docs/deficiency.md) | complex balancing, Birch, Perron–Frobenius, the deficiency-zero and deficiency-one theorems |
| [`persistence-gac.md`](docs/persistence-gac.md) | siphons, persistence, the global attractor conjecture (proven vs. open) |
| [`stochastic.md`](docs/stochastic.md) | the chemical master equation and Anderson–Craciun–Kurtz product form |
| [`multistationarity-robustness.md`](docs/multistationarity-robustness.md) | injectivity, the SR-graph, concordance, ACR, adaptation, open systems, composition |
| [`decidability.md`](docs/decidability.md) | decision procedures, `crnt_check`, rational rank/deficiency certificates |
| [`generated-certificates.md`](docs/generated-certificates.md) · [`analyze-contract.md`](docs/analyze-contract.md) | the contract for external tools that emit checkable Lean |
| [`design.md`](docs/design.md) | implementation and representation decisions |

## Citing this work

The accompanying paper is in preparation. Until it is published, cite the software directly: GitHub's
"Cite this repository" button reads [`CITATION.cff`](CITATION.cff). This section and the citation
metadata will be updated with the paper reference and a Zenodo DOI at the v1.0.0 release.

## License

Released under the MIT License. See [`LICENSE`](LICENSE).

## Contributing

- Keep the default import (`CRNT`) `sorry`-free and axiom-clean (`[propext, Classical.choice,
  Quot.sound]`); no `native_decide` (`decide` is fine). CI checks both.
- Provide both a propositional definition and, where feasible, a decidable computable companion,
  related by a theorem.
- Exercise every new abstraction with at least one example network and a `test/Smoke.lean` entry.
- Module docstrings describe the mathematics as present fact and cite source literature by author and
  title; place unfinished proofs in clearly named modules that `CRNT.lean` does not re-export.
