# Mathematical architecture

Coverage is stated in the [field map](field-map.md). In particular the LaSalle, truncated Hopf, abstract graph-transform, algebraic determinant-volume, semantic DOA/ADA, and fixed-time stochastic limit components have restricted or conditional scope; they do not establish their full named classical theories.

This document describes how the `CRNT` library is organized as mathematics: the two layers it is
built in, the core abstractions each introduces, and how the major theorems depend on one another.
It is the hub for the per-area documents, each of which states one area's definitions and proven
results in detail.

- **What is here and what works** is documented here and in the per-area docs below.
- **Why the code is shaped the way it is** (representation choices) is in [`design.md`](design.md).
- **How external tools emit checkable Lean** is in
  [`generated-certificates.md`](generated-certificates.md) and
  [`analyze-contract.md`](analyze-contract.md).

## Two layers

The library is built in two layers. The lower one supplies general-purpose mathematics used by the
upper layer: the structural and dynamical theory of reaction networks, stated over a small composable
core and resting on the mathematics beneath it.

### Mathematics layer

These directories hold results that are not specific to reaction networks. The CRN theorems above
them cite these by name.

- **`CRNT/Analysis`**: fixed-point theory. Sperner's lemma in every dimension, via the Kuhn
  (Freudenthal) triangulation and a parity/handshake involution on door incidences; Brouwer's
  fixed-point theorem for the standard `n`-simplex, obtained from Sperner by mesh refinement
  (`SpernerBrouwerN`, `BrouwerConvex`). This is what makes the Gale–Nikaido univalence and the
  invariant-set steady-state results unconditional rather than degree-theoretic.
- **`CRNT/Multistationarity`**: univalence and matrix theory. Degree-free Gale–Nikaido global
  univalence (Gale and Nikaido, *The Jacobian matrix and global univalence of mappings*) built from
  Stiemke's alternative, an order-monotonicity theorem, and a ±1 sign-conjugation P-matrix calculus
  (`PMatrix`, `PMatrixSchur`, `PMatrixSignature`); the determinant cycle-cover expansion
  (`SRGraphCycleDict`, with `CRNT/LinearAlgebra/DetCycleCover`). The CRN-specific injectivity and
  concordance criteria live in the same directory and sit on this matrix core.
- **`CRNT/LinearAlgebra`**: Perron–Frobenius positivity for column-stochastic matrices
  (`PerronFrobenius`), sign vectors and oriented-matroid/conformal decomposition of subspaces,
  `finrank` subadditivity over finite suprema, and power-product monotonicity.
- **`CRNT/Geometry`**: convex geometry for the toric-differential-inclusion development —
  polyhedral and toric fans, dual cones and cone faces, zero-separating surfaces and curves, and
  faithful-curve existence.
- **`CRNT/Dynamics`** (lower part): forward semiflows and stability theory. The flow of a bounded
  Lipschitz field via Picard–Lindelöf (`FlowConstruction`), Lyapunov stability and LaSalle's
  invariance principle (`LaSalle`), single-valued Nagumo invariance through first-exit arguments
  (`Nagumo`, `FirstExit`), and Routh–Hurwitz / Hurwitz stability tests (`RouthHurwitz`, `Hurwitz`).
- **`CRNT/Combinatorics`**: decidable undirected cycles and a digraph excess function used by the
  graph layer.

### CRN layer

On top of the mathematics layer sit the reaction-network abstractions and the classical theory.

1. **Foundations** (`CRNT/Basic`, `CRNT/Graph`, `CRNT/Stoich`): finite reaction networks as data,
   the reaction graph, and stoichiometry. The `Network` structure over a `Fintype` of species;
   directed reachability, weak reversibility, linkage and strong-linkage classes, cycle covers;
   reaction vectors, the stoichiometric subspace, and rank. See [`foundations.md`](foundations.md).

2. **Kinetics and dynamics** (`CRNT/Kinetics`, `CRNT/Equilibria`, upper `CRNT/Dynamics`): rate laws
   and the resulting differential equations. The general `Kinetics` abstraction and mass-action as
   its instance; the Feinberg–Horn–Jackson factorization `ẋ = Y(A_k(Ψ x))` through complex space
   (`MassActionAlgebra`, `MassActionField`); the genuine forward semiflow `Flow ℝ≥0` of that field
   (`FlowConstruction`); steady states, compatibility classes, and complex balancing; local
   asymptotic stability; and the reduced models (quasi-steady-state / Michaelis–Menten via Tikhonov
   and Fenichel). See [`dynamics.md`](dynamics.md).

3. **Equilibria and deficiency** (`CRNT/Deficiency`, `CRNT/Theorems/DeficiencyZero`,
   `CRNT/Theorems/DeficiencyOne`): existence, uniqueness, and the structure that controls them.
   Complex balancing and the toric structure of equilibria; Birch's theorem; Perron–Frobenius for
   column-stochastic matrices; deficiency as a kernel dimension; Feinberg's deficiency-zero theorem
   and the deficiency-one uniqueness theorem (single and multi-class). See
   [`deficiency.md`](deficiency.md).

4. **Global dynamics** (`CRNT/Dynamics`, persistence and GAC modules): behavior in the large —
   whether trajectories avoid extinction and converge. Petri-net siphons and persistence
   (`Siphon`, `Persistence`); the global attractor conjecture, its reduction to persistence
   (`PersistenceGAC`), the unconditional no-critical-siphon case (`GACNoCriticalSiphon`), and the
   toric-differential-inclusion development (`ToricInclusion`, `DifferentialInclusion`,
   `FacetRepulsion`). See [`persistence-gac.md`](persistence-gac.md).

5. **Multistationarity, robustness, and composition** (`CRNT/Multistationarity`, `CRNT/Design`,
   `CRNT/Open`, `CRNT/Compose`): when multiple equilibria are possible, when an output is robust,
   and how networks compose. Injectivity, the signed species–reaction graph, and the
   P-matrix/Gale–Nikaido criteria, with concordance forcing kinetics-independent monostationarity
   (`Concordance`, `Capacity`); absolute concentration robustness and antithetic integral feedback
   (`Design/ACR`, `Design/Adaptation`); open (CFSTR) extensions (`Open/Augmentation`); network
   interconnection (`Compose/Interconnect`). See
   [`multistationarity-robustness.md`](multistationarity-robustness.md).

6. **Stochastic CRN** (`CRNT/Stochastic`): the discrete-molecule regime on the count lattice
   `ℕ^S`. The chemical-master-equation generator as an explicit pointwise-finite operator
   (`Generator`, `CTMC`), the Anderson–Craciun–Kurtz product-form stationary distribution for
   complex-balanced networks (`ProductForm`), and the master-equation jump kernel (`JumpKernel`,
   `Kernel`). Process-level stochastics and the Kurtz scaling limit are open. See
   [`stochastic.md`](stochastic.md).

7. **Decidability and certificates** (`CRNT/Decision`, `CRNT/Interop`): computable companions.
   Decidable reachability, weak reversibility, and linkage; the `crnt_check` tactic
   (`Decision/Tactic`); exact rational rank and deficiency certificates (`Decision/RankExact`,
   `Decision/ExactDeficiency`); and the contract by which external tools emit checkable Lean
   (`Interop/Certificates`, `Interop/Analysis`). See [`decidability.md`](decidability.md),
   [`generated-certificates.md`](generated-certificates.md), and
   [`analyze-contract.md`](analyze-contract.md).

## Core abstractions

A few types carry the whole development:

- **`Network S`**: a finite reaction network over a `Fintype` of species `S` — a finite reaction
  index `R` and, per reaction, source and target `Complex S` (a `Complex` is a function `S → ℕ` of
  stoichiometric coefficients, with `toRealVector` the bridge into real space). Everything
  structural — the reaction graph, linkage, and deficiency — is read off this.
- **`Kinetics`**: the rate-law abstraction, a rate function with admissibility (nonnegativity,
  support-vanishing, weak monotonicity). Mass-action is the canonical instance and recovers the
  mass-action vector field definitionally; the stoichiometry/deficiency/linkage algebra is
  kinetics-agnostic over it.
- **The mass-action vector field** and its factorization `ẋ = Y(A_k(Ψ x))`: the dynamics expressed
  through complex space, where `Y` is the complex matrix (`complexMap`), `A_k` the kinetic Laplacian
  matrix (`kineticMap`), and `Ψ` the monomial map. Complex balancing is exactly `A_k(Ψ x) = 0`.
- **`Flow ℝ≥0`**: the forward semiflow of the genuine dynamics, constructed from a bounded-Lipschitz
  cutoff of the field via Picard–Lindelöf with continuous dependence and uniqueness; the substrate
  for every dynamical statement (`Flow.laSalle`, ω-limit theory). There is no two-sided `Flow ℝ`:
  solutions can leave the positive orthant in finite time.
- **`relEntropy x* ·`**: the Horn–Jackson relative entropy (pseudo-Helmholtz free energy), the
  strict Lyapunov function whose dissipation vanishes exactly at complex-balanced equilibria.

## Theorem dependency structure

The principal results and what they rest on:

```
Network / reaction graph / stoichiometry  (foundations)
        │
        ├── mass-action field  ─► factorization ẋ = Y(A_k(Ψ x))  ─► complex balancing = A_k(Ψ x)=0
        │                                                              │
        │                                                              ▼
        │   Perron–Frobenius (column-stochastic)  ─► WR ⇒ positive kernel of A_k
        │   Birch (existence + uniqueness per positive class)   ─────────────┐
        │                                                                    ▼
        ├── deficiency = dim(ker Y ∩ Im ∂)  ─► deficiency-zero theorem  ─► (unique complex-balanced eq.)
        │                                   └► deficiency-one uniqueness (single + multi-class)
        │
        ├── relEntropy Lyapunov + dissipation  ─► Flow ℝ≥0  ─► LaSalle
        │            │                                          │
        │            ▼                                          ▼
        │   local asymptotic stability (deficiency-zero)   ω-limit machinery
        │                                                       │
        └── siphons / boundary ω-points ──────────────────────► GAC ⟺ persistence
                                                                 │
                                          no-critical-siphon ⇒ GAC ; one positive ω-point ⇒ GAC
```

The Lyapunov/LaSalle stack reduces the global attractor conjecture (Horn's 1974 conjecture, open
in general) to **persistence** — no boundary ω-limit points. Persistence is proven for the
no-critical-siphon class of complex-balanced networks and is otherwise the open frontier; Craciun's
toric-differential-inclusion architecture is formalized with its remaining steps isolated as
explicit hypotheses. The stochastic Anderson–Craciun–Kurtz product form reuses the same
complex-balancing notion as the deficiency-zero theorem, with the complex-balanced equilibrium as
the Poisson parameter.

The injectivity strand is separate: a P-matrix Jacobian on a box is injective by the degree-free
Gale–Nikaido theorem, which rests on the `n`-dimensional Sperner and Brouwer theorems of
`CRNT/Analysis`. Concordance bounds the network to at most one steady state per compatibility class
for every weakly-monotonic kinetics, independent of the rate constants.

## Conventions

- **Two axes of completeness.** Where applicable each notion has both a propositional definition and
  a decidable computable companion related by a theorem (see [`decidability.md`](decidability.md)).
- **Each abstraction is exercised** by at least one worked example network (`CRNT/Examples/`).
- Module docstrings describe the mathematics as present fact and cite the source literature by
  author and title; they do not reference internal plans or paper section numbers.
```
