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

This library makes that theory machine-checked. Every result is verified by Lean's kernel, and the
structural criteria carry decidable procedures and exact certificates, so a design tool can hand it a
candidate network and get back a checkable answer instead of a heuristic.

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

## Highlights

- Feinberg's deficiency-zero and deficiency-one theorems: network structure alone pins down the
  equilibria, for any rate constants.
- Unconditional global convergence for no-critical-siphon networks: a decidable sufficient condition
  for the global attractor property.
- The global attractor conjecture reduced to a single explicit hypothesis: for weakly-reversible
  complex-balanced networks, global convergence follows from one geometric predicate (a bounded region
  that confines the orbit a fixed distance away from every species facet), with every step from that
  predicate to convergence machine-checked.
- The Anderson–Craciun–Kurtz product form: the exact stationary distribution of a complex-balanced
  stochastic network.
- Concordance forces at most one steady state per class, for every weakly-monotonic kinetics,
  independent of the rate constants.
- Gale–Nikaido univalence without topological degree: a P-matrix Jacobian on a box is injective,
  resting on n-dimensional Sperner and Brouwer theorems formalized here.
- A decidable, certificate-emitting core: check deficiency, reachability, and siphons, with
  kernel-checked certificates and a stable JSON contract for external tools.
- A unified oscillation-certificate layer: exact positive periodic-orbit semantics, all-parameter
  deficiency-zero exclusion, Poincare-return-map closure, child selections/unstable cores, and explicit
  Poincare--Bendixson/Bendixson--Dulac frontiers; see [`docs/oscillation.md`](docs/oscillation.md).

## What's Proven

Grouped by area; the precise statements and module names are in each linked doc.

**[Foundations & decidability](docs/foundations.md)**
- The network, reaction-graph, and stoichiometry core
- Decidable reachability, weak reversibility, and linkage, plus the `crnt_check` tactic
- Exact rational-rank and deficiency certificates, and a versioned `analyze` JSON contract

**[Equilibria & deficiency](docs/deficiency.md)**
- Complex balancing and the toric structure of steady states
- Birch's theorem, and Perron–Frobenius for column-stochastic matrices
- The deficiency-zero theorem, weakly reversible deficiency-one existence, and deficiency-one uniqueness (single- and multi-class)
- The **linear-elimination class** (every source complex of molecularity one): linear homogeneous
  steady-state equations, a convex cone of positive steady states, "never exactly multistationary",
  and the linear steady-state invariants — which need not coincide with the conservation laws
- The **toric parametrization** of the steady-state variety (the exponential parametrization by the
  kernel of the exponent-difference matrix) and the general steady-state invariants
- The **King–Altman formula** for a unimolecular network: the steady state is the tree constant at a
  species divided by the total tree weight, i.e. the cofactor ratio of the directed Matrix–Tree
  theorem; it is the only positive steady state up to scaling
- The **nilpotent-Jacobian criterion**: at a positive complex-balanced equilibrium a nilpotent
  Jacobian forces every reaction with positive flux to be stoichiometrically null, so the
  complex-balanced equilibrium is unique in its class — and a nontrivial weakly reversible network
  never has a nilpotent Jacobian there
- The **parity theorem**: the number of isolated positive steady states of a fully open network is odd
- The **spectral factorization** of the mass-action Jacobian, `J(x) = Yᵀ A_κ(x) Y D(x)⁻¹`, with the
  characteristic-polynomial consequence — and a machine-checked refutation of the naive claim that
  the eigenvalues of `J` are the negatives of those of the bare weighted adjacency
- The **Cauchy–Binet expansion** of the reduced determinant: in rank `s` it is a sum of products of
  `s` rate constants, and a positive circuit in a reaction set kills the corresponding term
- The **two-reaction classification**: a machine-checked table of the multistationary and the atom
  members of the 75 two-species bimolecular two-reaction networks
- The **mixed volume** in the classical Shephard/BKK form, with additivity and homogeneity proved
  and the BKK bound sharp in one variable

**[Dynamics & stability](docs/dynamics.md)**
- The complex-space factorization `ẋ = Y(A_k(Ψ x))` and the forward semiflow
- The relative-entropy Lyapunov function, LaSalle's invariance principle, and local asymptotic stability
- A Michaelis–Menten quasi-steady-state reduction, error-quantified in time: the full trajectory tracks
  the slow-manifold reduction within an O(ε) Grönwall bound on compact time, and within a
  horizon-uniform O(ε) ceiling for all time under a coupled contraction hypothesis (ε the timescale
  separation)
- Routh–Hurwitz stability to degree 4 (Liénard–Chipart) with the degree-3 and degree-4 Hopf crossing
  gates, and a dimension-free Gershgorin test certifying mass-action Jacobian stability (so oscillation
  is excluded)
- The planar Poincaré normal form with its first Lyapunov coefficient, and the closed-form limit cycle
  of the truncated normal form; the sustained-oscillation verdict for the full field is reduced to
  explicit center-manifold, averaging, and smooth-flow-dependence hypotheses (see Scope & Open Problems)
- The **Poincaré–Dulac normal form to cubic order**, computed: the quadratic part of a planar field is
  removable exactly when the linearization is non-degenerate, the cubic push-forward is exact, and the
  resonant coefficient `w² w̄` is an explicit rational function of the Taylor data
- The **Guckenheimer–Holmes calibration** of that coefficient to the classical real-coordinate first
  Lyapunov coefficient formula, so the repository's `lyapunovFromPartials` is identified with the
  normal-form computation rather than assumed
- The **angular averaging** of the reduced field, computed rather than assumed, with the averaged
  radial field constructed and its amplitude law proved
- The **mass-action Hopf verdict**: the Taylor data of a mass-action family are computed from the
  genuine field, the first Lyapunov coefficient is the Guckenheimer–Holmes calibration, and the
  branch of periodic orbits is exhibited for a concrete two-species network
- The **tube hypothesis** of Tikhonov's theorem is a theorem, not an assumption: a first-exit
  argument on the shifted Lyapunov function keeps the coupled solution in the tube, and the slow
  error is bounded
- The **tropical → slow–fast link**: the tropical system is the `ε → 0⁺` limit of the rescaled
  mass-action field, and a tropical critical point with a Hurwitz fibre derivative has a local `C¹`
  slow manifold
- The **strong order** `≪` with the monotone separating functionals of Hirsch–Smith, and the
  non-ordering argument for the incomparable-orbit case
- The **method of steps** for delay equations on a Banach space: the one-step theorem, the gluing
  lemma, the induction over the steps, and the global solution with its uniqueness
- **Hirsch's generic convergence** for strongly monotone fields, with the order-convexity of the
  ω-limit set derived rather than assumed

**[Oscillation & recurrent dynamics](docs/oscillation.md)**
- Exact `PeriodicTrajectory`, fixed-parameter positive periodic-orbit, oscillatory-capacity, and
  all-parameter non-oscillation predicates
- Weakly reversible deficiency-zero networks are proved globally non-oscillatory in the positive
  orthant for every positive rate vector; the analyzer exposes a kernel-backed certificate bridge
- Poincare-return fixed points construct the common periodic-trajectory witness
- Child selections, child-selection matrices, right-half-plane instability, minimal unstable cores,
  and positive/negative-feedback classification are represented natively
- Rank-two Poincare--Bendixson and Bendixson--Dulac routes are specified as explicit proof frontiers,
  not axioms or numerical heuristics
- A **structural criterion for the absence of oscillations**: an order-preserving (or Kamke) planar field
  has no nonconstant periodic orbit, so a cooperative planar mass-action network never oscillates for
  any positive rate vector
- The network-specific half of the **Poincaré–Bendixson route**: a compact, positively invariant,
  equilibrium-free trapping region built from a first integral, giving a positive periodic orbit
- **"No chaos in the plane"**: a minimal compact closed invariant subset of a planar ω-limit set is
  exactly a periodic orbit, so there is no Solenoid, Plykin or horseshoe attractor

**[Persistence & global attraction](docs/persistence-gac.md)**
- The reduction GAC ⟺ persistence, and unconditional convergence for the no-critical-siphon class
- The sharp "one positive ω-limit point ⇒ convergence" reduction
- The global attractor conjecture for weakly-reversible complex-balanced networks reduced to a single
  predicate, `SeparatingConfinement` (a bounded, forward-invariant region holding the orbit off every
  facet), proven sufficient for global convergence end to end; the affine separating surface is built
  in every dimension
- That predicate shown equivalent to persistence and constructed outright on two classes (near
  equilibrium, and the entire decidable no-critical-siphon class), so it is realized rather than only
  assumed; the construction supplies the no-critical-siphon persistence certificate as a by-product
- A development of the toric-differential-inclusion approach

**[Stochastic CRN](docs/stochastic.md)**
- The chemical-master-equation generator on `ℕ^S`
- The Anderson–Craciun–Kurtz product-form stationary distribution
- A normalized invariant probability measure on any finite closed enabled region, with product-form
  singleton ratios
- The Kurtz density-dependent generator-convergence estimate: the volume-scaled generator of a
  differentiable observable converges to its derivative along the deterministic mass-action field
- **Positive recurrence and non-explosion** for strongly endotactic stochastic mass-action systems,
  via a count-lattice Lyapunov function with a constant negative drift outside a finite set
- The **exit-mass factorization**: the union-bound mechanism of the sample-path law of large numbers,
  with the exit mass of the frozen chain proved to be probability-like
- The **distributional CLT for networks whose chains may explode** — the fluctuation law is a
  sub-probability measure completed at the origin, and Lévy's continuity theorem gives the weak
  convergence to the linear-noise Gaussian, with no conservation, weight or non-explosion hypothesis

**[Multistationarity & robustness](docs/multistationarity-robustness.md)**
- Degree-free Gale–Nikaido univalence, bound to class injectivity
- Concordance ⇒ kinetics-independent monostationarity
- The signed species–reaction graph and the determinant cycle-cover expansion
- Topological-degree steady-state existence (a nonzero reduced degree forces a steady state in the
  compatibility class) and a multistationarity-capacity test from a sign-indefinite reduced Jacobian
- The **degree equals the sign of the reduced Jacobian determinant** at a steady state, with the
  Conradi–Feliu–Mincheva–Wiuf conclusion (a second positive steady state) obtained by a perturbation
  argument, and the degree shown independent of the rate constants
- **Flux-feasibility characterizations of multistationarity capacity**, in both directions, with
  rank-one reductions and conditional bridges from shelf/confluence data. The finite published
  Deficiency One and Advanced Deficiency Algorithms are not yet verified end to end.
- The **two-reaction atom criterion** for the fully open network, and the **parity theorem** (the
  number of positive steady states of a fully open network is odd)
- An **explicit description of the multistationarity region** of a rank-one network: the sign of the
  reduced determinant at a steady state
- The **semilinear characterization** of stably computable functions: a piecewise-affine
  (over polyhedral regions) notion of semilinearity, closure under `+`, `min`, `k·`, an explicit
  network computing every affine function and every minimum of affine functions, and a proof that
  `2ⁿ` is not semilinear
- Absolute concentration robustness, antithetic integral feedback, open (CFSTR) systems, and composition
- **Robust perfect adaptation for a general plant**: the setpoint of the antithetic internal model,
  a linear-quadratic Lyapunov certificate, and a Foster–Lyapunov ergodicity transfer theorem
- The **Gibbs free energy with standard chemical potentials**: the chemical affinity, De Donder's
  identity, and the classical dissipation formula, linked to the entropy production

Every abstraction is exercised by at least one worked example network in [`CRNT/Examples/`](./CRNT/Examples/).

### General mathematics formalized here

The CRN results rest on general-purpose mathematics built here and cited by name from the CRN layer.
[`docs/architecture.md`](docs/architecture.md) gives the full inventory; the four areas are:

- **Fixed-point theory** ([`CRNT/Analysis`](CRNT/Analysis)): Sperner's lemma and Brouwer's theorem for
  the standard `n`-simplex in every dimension, via the Kuhn (Freudenthal) triangulation and mesh
  refinement.
- **Univalence & matrices** ([`CRNT/Multistationarity`](CRNT/Multistationarity)): degree-free
  Gale–Nikaido global univalence over a P-matrix calculus (Schur complements, signature invariance),
  and computable exact rational matrix rank with a nonsingular-minor certificate.
- **Topological degree** ([`CRNT/Multistationarity`](CRNT/Multistationarity)): the Brouwer degree at a
  regular value as a finite signed sum of Jacobian-determinant signs, with Sard's theorem, degree
  additivity, homotopy invariance, and local constancy for proper maps.
- **Dynamical systems** ([`CRNT/Dynamics`](CRNT/Dynamics)): forward semiflows, Lyapunov stability, and
  LaSalle's principle, with the flow of a bounded Lipschitz field and single-valued Nagumo invariance.

## Scope & Open Problems

The library proves the classical canon and a large decidable fraction of the design-relevant criteria.
What remains is of two kinds: established mathematics Mathlib does not yet have, where building it
unlocks the CRN results noted, and questions where the mathematics itself is still open.

**General mathematics still to build.** The apparatus in each of these areas is in place; what
remains is a specific missing piece.
- The *total-degree* theorem for topological degree. Brouwer degree, Sard's theorem, and homotopy
  invariance are formalized; a nonzero reduced degree forces a steady state; the degree of the
  steady-state map is now identified with the sign of the reduced Jacobian determinant at a steady
  state, and the Conradi–Feliu–Mincheva–Wiuf conclusion (a second positive steady state) follows by a
  perturbation argument. What remains is the computation of the *total* degree of a class (that it is
  `(−1)^s` under dissipativity), which is the last missing ingredient for the parity theorem.
- Critical-siphon facet repulsion. The Butler–McGehee lemma and non-siphon (codimension-1) facet
  repulsion are proven, as is the Anderson–Shiu influx estimate for a singleton critical siphon (a
  linear lower bound on the mass-action field at the facet). From that bound together with a near-facet
  relative-entropy dissipation bound, a uniform positive facet floor follows. What remains is the
  dissipation bound itself, carried as a hypothesis, and its assembly into a persistence conclusion;
  discharging it would extend unconditional global attraction past the no-critical-siphon class
- Fenichel normally-hyperbolic invariant-manifold persistence. The O(ε) quasi-steady-state reduction
  holds on compact time and lifts to the infinite horizon: all-time invariance of the substrate-varying
  slow manifold with an O(ε) ceiling is proven for the closed-form contracting field, and a
  horizon-uniform O(ε) tracking ceiling for the genuine coupled Michaelis–Menten trajectory is proven by
  a dissipative (log-norm) Grönwall estimate. The latter assumes a coupled transverse contraction bound;
  deriving that bound from the enzyme field itself is what remains
- The stochastic process layer. The chemical-master-equation generator, the uniformized transition
  semigroup, and the deterministic (Kurtz) scaling skeleton (the generator-convergence estimate and a
  conditional fluid-limit bound) are built, together with a Poisson probability space (an independent
  scaled-Poisson clock family) and an in-probability law of large numbers for the aggregate scaled
  fluctuation. What remains is the continuous-time sample-path process itself, a time-indexed random
  trajectory with its filtration, and the process-level (Skorokhod) law of large numbers, which rest on
  the compensated-Poisson martingale theory Mathlib lacks
- The center-manifold gaps behind sustained oscillation. The Hopf crossing gates, the planar normal
  form, and the truncated-normal-form limit cycle are proven, and the full-field "clock verdict" is
  reduced to three explicit inputs: center-manifold existence, center-manifold averaging, and C¹
  dependence of the flow on initial data (a return-map construction). Two of the three are discharged
  independently: the center manifold is constructed as a Lyapunov–Perron fixed point, and the flow's C¹
  dependence on its initial data is proven through the variational equation. **Center-manifold
  averaging is now supplied**: the angular average of the reduced field is computed rather than
  assumed, the averaged radial field is constructed with its `C¹` regularity and amplitude law, and
  the Poincaré–Dulac normal form to cubic order is computed (with the Guckenheimer–Holmes calibration
  of the resonant coefficient). The clock verdict still consumes the three inputs, but the averaging
  piece is now a theorem rather than a gap

**Global persistence layer (new)**
- Global quantifier APIs distinguish pointwise `PersistentFrom`, fixed-rate persistence, structural
  persistence, omega-limit boundary exclusion, and permanence.
- `WeaklyReversible.endotactic`, the standard stoichiometric strong-endotactic predicate,
  single-linkage connectedness/reachability bridges, tier definitions, and drainable/self-replicable
  siphon definitions are exposed in the core import.
- The already-proved deficiency-zero/no-critical-siphon route now yields a proof-carrying
  `GlobalPersistenceCertificate`; the analyzer's `persistenceCertified = true` flag constructs that
  certificate directly.
- Published but not yet machine-discharged global classes are represented as explicit proposition
  contracts rather than axioms; see `docs/global-persistence.md`.

**Open research**
- The global attractor conjecture (Horn 1974) is **proved** for complex-balanced mass-action
  systems: `Network.complexBalanced_globalAttractor`, via the coordinate floor
  `Network.complexBalanced_forward_floor` (`CRNT/Persistence/`). See `HANDOFF_gac_closed.md`.
  The persistence conjecture for weakly reversible networks remains open (leaf D12 of
  `docs/field-map.md`).
- The correctness of the higher-deficiency (Deficiency One and Advanced Deficiency) algorithms:
  - The apparatus is formalized (network consistency via Stiemke, cut pairs, regularity, confluence
    vectors with their proven antisymmetry, shelves, signatures, colinearity classes), and the
    exclusion direction is proven: an injective network has no capacity for multiple steady states
  - `HasMultistationarityCapacity ↔ DOAFeasible` and
    `HasMultistationarityCapacity ↔ ADAFeasible` are proved for semantic flux certificates.
    `DOAFeasible` quantifies over real log-ratios and fluxes with exponential balance equations;
    `ADAFeasible` allows a one-shelf certificate. These equivalences do not supply a finite decision
    procedure or establish correctness of the separately defined shelf verdicts
    `DOAAffirmsCapacity` and `ADAAffirmsCapacity`. The bridge requires additional shelf-flux and
    placement data; the general shelf construction, multi-shelf converse, and numerical procedure
    remain incomplete. See [`docs/pr1-migration.md`](docs/pr1-migration.md).
- Absolute concentration robustness (Shinar–Feinberg 2010) is proved:
  `Network.shinarFeinberg_ACRAt` (leaf S13 of `docs/field-map.md`).

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
