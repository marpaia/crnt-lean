# Kinetics and dynamics

The increasing-operator convergence result is a LaSalle/uniqueness theorem, not Hirsch generic convergence. Mass-action Hopf data give a periodic branch of the cubic truncation, with original-field transfer incomplete. Graph-transform fixed points give discrete invariance; all-time invariance uses time-indexed operators or explicit flows. General Fenichel persistence remains incomplete.

This document describes the second layer of the `CRNT` library: the passage from the discrete
reaction-network structure of [`foundations.md`](foundations.md) to continuous dynamics. A
network plus a rate law gives a vector field `ẋ = f(x)`; this layer builds that field, factors it
through the complex space, packages its solutions as a forward semiflow, and studies the
asymptotics of that semiflow: Lyapunov descent, LaSalle invariance, local asymptotic stability,
time-scale separation, and the stability of linearizations.

Where this sits: the rate-law abstraction and mass-action field are the inputs to everything
downstream. The equilibrium-existence and deficiency theory (Birch, complex balancing, the
deficiency-zero and deficiency-one theorems) lives in [`deficiency.md`](deficiency.md); the
global-attractor / persistence theory (siphons, the global attractor conjecture) lives in
[`persistence-gac.md`](persistence-gac.md). The overall picture and theorem dependency graph are
in [`architecture.md`](architecture.md).

## Kinetics: the rate-law abstraction

A **concentration** (`CRNT.Concentration S = S → ℝ`) assigns a real number to each species, with
predicates `Concentration.Nonnegative` and `Concentration.Positive`. The concentration-dependent
part of a rate is the **mass-action monomial** `Complex.massActionMonomial y x = ∏ s, (x s) ^ (y s)`,
nonnegative on the nonnegative orthant (`massActionMonomial_nonneg`) and positive on the positive
orthant (`massActionMonomial_pos`).

### Mass action

`Network.RateConstants N` is a choice of strictly positive rate constant per reaction. The
**mass-action rate** of reaction `r` is `massActionRate κ r x = κ.k r * (source r).massActionMonomial x`,
nonnegative at nonnegative concentrations (`massActionRate_nonneg`), strictly positive at positive
ones (`massActionRate_pos`). The **mass-action vector field**

```text
massActionVectorField κ x s = ∑ r, massActionRate κ r x * reactionVector r s
```

is the right-hand side of the induced polynomial ODE. This is the bridge from discrete CRN
structure to continuous dynamics.

### The general `Kinetics` abstraction

`Network.Kinetics N` makes the rate law a parameter. It bundles a map
`rate : N.R → Concentration S → ℝ` together with Feinberg's admissibility hypotheses:

- `rate_nonneg`: nonnegativity at nonnegative concentrations;
- `rate_vanishing`: the rate vanishes when a species required by the source complex is absent;
- `rate_supportDep`: the rate depends only on the concentrations of the source species;
- `rate_mono`: weak monotonicity, each rate is nondecreasing in the species concentrations on the
  nonnegative orthant.

A kinetics induces `Kinetics.vectorField K x s = ∑ r, K.rate r x * reactionVector r s`, the
right-hand side of `ẋ = f(x)`. Two structural facts about it are **kinetics-agnostic**: they hold
for every admissible kinetics, not just mass action:

- `Kinetics.vectorField_nonneg_of_zero`, **boundary non-attraction**: at a nonnegative
  concentration with `x_s = 0` the `s`-component of the field is `≥ 0` (any reaction that would
  decrease `x_s` consumes `s`, so its rate vanishes there). The orthant face `{x_s = 0}` is
  non-attracting.
- `Kinetics.vectorField_mem_stoichSubspace`, **conservation**: the field always lies in the
  stoichiometric subspace, so every solution stays in the compatibility class of its initial
  condition.

A concentration is a steady state when the field vanishes componentwise (`IsKineticSteadyState`).

Mass action is recovered as the instance `Network.massActionKinetics κ`: its four admissibility
proofs are exactly the mass-action lemmas, and its induced field is the mass-action field
*definitionally* (`massActionKinetics_vectorField : (massActionKinetics κ).vectorField = massActionVectorField κ`).
Mass-action steady states are exactly its kinetic steady states (`isMassActionSteadyState_iff_kinetic`).

The mass-action field is differentiable, and its derivative is available as data. Each monomial
is differentiable (`massActionMonomial_differentiable`) with an explicit gradient
(`massActionMonomialGrad`, `massActionMonomial_hasFDerivAt`); each rate
(`massActionRate_differentiable`) and the whole field (`massActionVectorField_differentiable`)
inherit this. `Network.massActionJacobianCLM` is the Fréchet derivative as a continuous linear
map (`massActionVectorField_hasFDerivAt`), and `Network.massActionJacobian` its matrix
(`massActionJacobianCLM_apply`: the map acts by `mulVec`). This Jacobian is the linearization the
Routh–Hurwitz stability test below reads.

### Generalized mass action

Müller–Regensburger generalized mass-action kinetics separates two subspaces of `ι → ℝ`: the
**stoichiometric** subspace `S` and the **kinetic-order** subspace `T`. A positive `x` is a
generalized equilibrium relative to a positive reference when `x − c ∈ S` and the log-ratio
`log(x/x*)` lies in `orthSum T`. The Müller–Regensburger **sign condition** `SignCompatible S T`
(via `SameSign`) is the hypothesis under which such equilibria are unique:

- `gen_birch_uniqueness`: under `SignCompatible S (orthSum T)`, two positive vectors in the same
  `S`-coset with log-ratio orthogonal to `T` are equal;
- `signCompatible_self`: `SignCompatible S (orthSum S)` holds unconditionally, the bridge showing
  the framework subsumes the classical case;
- `birch_uniqueness_of_self`: the `T = S` specialization, recovering classical complex-balanced
  uniqueness;
- `gen_birch_existence`: the single-subspace specialization of generalized existence.

(The two-subspace existence with `S ≠ T` is beyond this module's scope.)

## The complex-space factorization

The mass-action field factors through the finite-dimensional **complex space** indexed by
`Network.ComplexIdx` (the vertices of the reaction graph). Writing `Y` for the complex matrix
(`complexMap`), `A_k` for the kinetic Laplacian (`kineticMap`), and `Ψ` for the monomial map
(`complexMonomialVector`), the induced ODE is the standard Feinberg–Horn–Jackson factorization

```text
ẋ = Y (A_k (Ψ x))            massActionVectorField_eq
```

- `complexMap` (`Y`) is the linear map `v ↦ (s ↦ ∑_c v_c · c_s)` combining complexes with given
  coefficients.
- `kineticMap` (`A_k`) is the kinetic Laplacian: at each complex it is inflow minus outflow, each
  reaction contributing its rate constant times the value at its source. Its columns sum to zero
  (`kineticMap_sum_eq_zero`), the Laplacian property that the Perron–Frobenius / Matrix-Tree
  argument later builds on to produce a positive kernel vector for weakly reversible networks.
- `complexMonomialVector` (`Ψ`) sends `x` to the vector of complex monomials.

Consequences:

- `isComplexBalanced_iff_kineticMap`: a concentration is complex-balanced **iff** `A_k(Ψ x) = 0`;
- `IsComplexBalanced.isMassActionSteadyState`: every complex-balanced concentration is a steady
  state (complex balancing kills `A_k`, and `Y` sends `0` to `0`).

## Regularity and the forward semiflow `Flow ℝ≥0`

Before any flow can be built, the field must be regular and the orthant must be non-attracting:

- `massActionVectorField_contDiff`: the field is `C^∞` (it is a polynomial map), the regularity
  hypothesis of Picard–Lindelöf;
- `massActionVectorField_nonneg_of_zero`: the mass-action specialization of boundary
  non-attraction;
- `exists_local_solution`: local existence of solutions through every starting point.

The general (chemistry-free) ODE-to-flow construction lives in the `ODE` namespace and is written
Mathlib-style:

- `ODE.dist_le_of_isIntegralCurve`, **continuous dependence**: two global solutions of the same
  autonomous Lipschitz ODE diverge at most exponentially in forward time (Grönwall);
- `ODE.eqOn_Ici_of_isIntegralCurve`, **uniqueness on `[0, ∞)`**: a solution is determined on
  forward time by its initial value;
- `ODE.exists_isIntegralCurve`, **global existence** for a *bounded* Lipschitz field: because the
  field is globally bounded, the Picard–Lindelöf radius can be taken arbitrarily large, giving a
  solution on `[−T, T]` for every `T`; interval solutions are glued by uniqueness (the step the
  Mathlib ODE library otherwise lacks);
- `ODE.exists_flow`, **the flow**: a bounded Lipschitz autonomous field generates a forward
  semiflow `Flow ℝ≥0 E` whose orbits are its solutions. Existence supplies the orbits, uniqueness
  the semigroup law, continuous dependence the joint continuity.

A forward semiflow is exactly `Flow ℝ≥0` (the `Flow` structure only requires the time monoid to be
an additive monoid). Mass-action dynamics is *forward only*: solutions stay positive and
are confined forward, but the backward flow can leave the orthant in finite time, so there is no
two-sided `Flow ℝ`.

### Monotone / order-preserving flows

The order-preserving fragment of monotone dynamical systems (Hirsch, Smith; Angeli–Sontag for the
I/O variant):

- `Monotone.IsMonotoneFlow`: a forward semiflow each of whose time-`t` maps is order preserving,
  with `IsMonotoneFlow.le` (orbits from ordered points stay ordered forward) and
  `IsMonotoneFlow.forwardInvariant_Icc` (an order interval bracketed by two equilibria is forward
  invariant); `isMonotoneFlow_id` witnesses non-vacuity;
- `Monotone.scalar_comparison` and `Monotone.traj_le`, the one-dimensional differential-inequality
  engine: if `u 0 ≤ v 0` and `u`'s right derivative is dominated by `v`'s, then `u ≤ v`.

The vector Kamke–Müller comparison principle and the full Angeli–Sontag input/output theory are not
formalized (Mathlib lacks cooperative-field flows and quasimonotone vector ODE comparison).

## The relative-entropy Lyapunov function and local asymptotic stability

The strict Lyapunov function is the Horn–Jackson relative entropy (pseudo-Helmholtz free energy)

```text
relEntropy x* x = ∑ i, (x_i · log(x_i / x*_i) − x_i + x*_i)
```

with `relEntropy_nonneg` (Gibbs' inequality), `relEntropy_eq_zero_iff` (vanishes exactly at `x*`),
and `relEntropy_pos_of_ne` (strictly positive away from `x*`).

**Dissipation.** Pairing the field against the log-ratio gives the dissipation rate, which is
nonpositive and vanishes exactly at complex balancing:

- `dissipation_nonpos`: relative to a complex-balanced positive reference, the dissipation
  `∑_s (log(x_s) − log(x*_s)) · f_s(x) ≤ 0`;
- `complexBalanced_of_dissipation_eq_zero`: vanishing dissipation in a positive class forces
  complex balancing;
- `dissipation_eq_zero_of_complexBalanced`: and conversely.

**Descent along solutions.** Via the chain rule `relEntropy_hasDerivAt`
(`d/dt relEntropy x* (γ t) = ∑_s (log γ_s − log x*_s) γ'_s`):

- `relEntropy_antitone_along_solution`: along any positive solution of `ẋ = f(x)`, relative to a
  complex-balanced reference, `t ↦ relEntropy x* (γ t)` is nonincreasing.

This descent statement needs no flow: it holds for any differentiable positive solution.

**LaSalle's invariance principle** (general, chemistry-free, Mathlib-style):

- `Flow.laSalle`: for a forward semiflow `ϕ` and continuous `V` that is nonincreasing along the
  forward orbit of `x` and whose orbit is eventually absorbed by a compact set, the ω-limit set
  `ω(x)` is nonempty, invariant, and `V` is **constant** on it.

**Local asymptotic stability** assembles these. Because Mathlib's flow theory needs a globally
bounded Lipschitz field, the genuine field is replaced by its bounded-Lipschitz cutoff
(`clampBox`, `exists_cutoff`); confinement and positivity of the cutoff orbit, compactness and
positive-confinement of relative-entropy sublevel sets, and a field lower bound (`exists_cutoff`,
`orbit_pos`, `orbit_relEntropy_le`, `isCompact_relEntropy_sublevel`, `positive_of_relEntropy_lt`,
`sub_mem_stoichSubspace_of_solution`, `exists_field_lower_bound`) feed into:

- `omegaLimit_eq_singleton_of_local`: for a weakly reversible network with complex-balanced
  positive equilibrium `x*`, starting from a positive `x₀` in the same compatibility class and
  sufficiently close to `x*` (the relative-entropy locality bound `relEntropy x* x₀ < x*_s` for all
  `s`), the mass-action semiflow has `ω(x₀) = {x*}`.

LaSalle forces the relative entropy constant on `ω(x₀)`, so the dissipation vanishes there, forcing
each ω-point complex-balanced, hence equal to `x*` by the deficiency-zero uniqueness of the
complex-balanced equilibrium in a positive class. That uniqueness input is the Birch / deficiency
material documented in [`deficiency.md`](deficiency.md).

**Global asymptotic stability under persistence.**
`omegaLimit_eq_singleton_of_persistent` removes the closeness bound and replaces it with
**persistence**: for a weakly reversible network with positive complex-balanced reference `x*` and
a positive start `x₀` in the same class, if the genuine orbit is absorbed by a compact set `K₀` of
strictly positive concentrations, then `ω(x₀) = {x*}`. Persistence is exactly what the closeness
bound was for in the local theorem — it keeps the ω-limit set off the orthant boundary — and it is
isolated as the single hypothesis. This is the persistence-conditional form of single-linkage-class
global asymptotic stability (Anderson, "A Proof of the Global Attractor Conjecture in the Single
Linkage Class Case"). Persistence itself, the no-boundary-attraction estimate, is the open input;
its decidable sufficient cases are in [`persistence-gac.md`](persistence-gac.md).

**Forward confinement of the orthant.** The semiflow is forward-only because the nonnegative orthant
is forward invariant for mass action but not backward invariant. The orthant invariance is a
single-valued Nagumo argument: `nagumo_halfspace_scalar` is the scalar dissipative form (a
differentiable `g` with `g 0 ≥ 0` and the inward inequality `−L·g ≤ g'` where `g < 0` stays
nonnegative on `[0, ∞)`), `forwardInvariant_nonnegOrthant` lifts it coordinatewise, and
`Network.massAction_forwardInvariant_nonneg` specializes it: the boundary inward condition on each
face `{x_s = 0}` is discharged by `massActionVectorField_nonneg_of_zero`
(`massActionVectorField_inwardOnBoundary`), and the caller supplies the per-coordinate dissipativity
bound. The general Nagumo viability theorem over an arbitrary closed convex set, with a Bouligand
subtangent-cone hypothesis, is out of reach: Mathlib has no tangent-cone-to-a-set apparatus, so
`CRNT/Dynamics/Viability.lean` proves only the scalar-halfspace closure and the easy direction
(invariance ⇒ subtangency, `mem_tangentConeAt_of_solution`). The siphon-boundary refinements of this
invariance story live in [`persistence-gac.md`](persistence-gac.md).

## Time-scale separation and Michaelis–Menten

This is the quasi-steady-state / singular-perturbation development. It is honest about its ceiling:
the error estimates are **compact-time** and the small parameter `ε` is *not* fully quantified:
the slaving defect is supplied as a hypothesis (or derived as a slow-drift magnitude), and the
Grönwall bounds diverge as the horizon `T → ∞`. There is no infinite-horizon shadowing.

**Compact-time QSSA error bound** (Tikhonov-style, chemistry-free, in `ODE`). The
`ODE.QssaDefect f γᵣ γᵣ' a b εf` predicate is the slaving defect: the reduced curve satisfies the
full field up to a residual `εf`.

- `ODE.qssa_error_bound`: the exact-versus-reduced gap is bounded by `gronwallBound δ K εf (t − a)`
  on `[a, b]` (initial mismatch `δ`, defect `εf`);
- `ODE.qssa_exact_of_zero_defect`: zero defect and zero mismatch recover exact coincidence;
- `ODE.qssa_error_tendsto_zero`: on a fixed horizon `[0, T]` the bound is monotone, and
  `gronwallBound δ K εf T → 0` as `(δ, εf) → (0, 0)`: the reduced trajectory converges uniformly to
  the exact one on compact time as the mismatch and defect vanish.

**Boundary-layer attraction** (the fast side, supplying the defect as a derived quantity).
`ODE.OneSidedContraction f zstar lam` is the dissipativity condition for a contracting fast fibre.

- `ODE.norm_sub_le_exp_neg_mul`: an integral curve of a one-sided-contracting field decays to its
  equilibrium at the explicit rate `‖z t − zstar‖ ≤ ‖z 0 − zstar‖ · exp(−lam·t)`;
- `ODE.norm_sub_tendsto_zero`: for `lam > 0` the layer collapses onto the fast equilibrium;
- `ODE.FastSubsystem` bundles a fast field, its equilibrium, and a positive rate, with
  `FastSubsystem.attraction_bound` / `tendsto_equil` re-exporting the estimate;
- `ODE.qssaDefect_of_fastSubsystem`: for a full field `fast + slow`, the constant reduced curve at
  the fast equilibrium has slaving defect exactly the slow-drift magnitude, composable with
  `qssa_error_tendsto_zero`.

**Fenichel slow manifold (reachable rung).** `ODE.SlowManifold` lifts the flat fibre to a
slow-variable-dependent fast equilibrium `z = h y`, the graph of a manifold map. The three defining
geometric properties are proved:

- `SlowManifold.attraction_bound` / `tendsto_fiber`: per-fibre exponential attraction;
- `SlowManifold.eq_of_stationary` / `fiber_eq_singleton`: per-fibre uniqueness of the equilibrium,
  so `h` is the *only* graph of fast equilibria;
- `SlowManifold.const_isIntegralCurve` / `invariant_graph`: invariance of the graph under the
  frozen layer flow.

`FenichelManifold` derives `manifoldMap` as data with proven uniqueness (`manifoldMap_unique`) and,
under a contraction-rate bound, Lipschitz continuity and continuity (`manifoldMap_lipschitzWith`,
`continuous_manifoldMap`); `FenichelSlowDrift` records the `O(ε)` slow-drift bounds
(`manifoldMap_slowDrift_le`, `manifoldMap_slowDrift_tendsto_zero`).

**Graph-transform persistence.** `GraphTransform` builds the Lyapunov–Perron graph transform on
bounded sections `Y →ᵇ E`: `GraphTransformData` packages the supremum-metric contraction whose
Banach fixed point `manifold` has a fixed-point distance bound from the
base section (`manifold_dist_base_le`) and the spectral-gap constructor `ofSpectralGap`.
`FenichelPersistence` ties a fixed-point section of the flow-then-regraph operator
(`CoupledFlowGraphTransform`) to discrete forward-invariance of its graph under the sampled coupled semiflow
(`graphTransform_discrete_invariant_and_dist_le`). Two concrete instances discharge the operator-from-flow hypothesis from an
explicit field:

- `FenichelPersistenceConcrete`: the bounded constant fast-drift field `ż = v` whose flow comes from
  `ODE.exists_flow`; its persisted manifold is the zero section, exact only at vanishing drift
  (`graphTransform_discrete_invariant_and_dist_le_constDrift`).
- `FenichelPersistenceContracting`: the contracting fast fibre `ż = −rate·(z − c)` whose
  closed-form exponential flow `(y, z) ↦ (y, c + e^{−rate·t}·(z − c))` is built directly as a
  `Flow`; the graph transform is an honest contraction with factor `e^{−rate·τ} < 1` and the
  persisted manifold is the genuine attracting fibre `z = c`, an explicit constant graph
  (`graphTransform_discrete_invariant_and_dist_le_contracting`).

For all-time invariance, `FlowGraphTransformFamily.op t` carries a graph at time `t`; a graph fixed by every operator is invariant. The contracting example proves the time-zero operator is identity and the time-one operator is not identity. General perturbed NHIM persistence remains incomplete.

**Michaelis–Menten** instantiates this machinery on the enzyme system `E + S ⇌ ES → E + P`:

- `MichaelisMenten.linearFastField` and `enzymeFastSubsystem`: the linear inward fast field, its
  one-sided contraction (`linearFastField_oneSidedContraction`), and its boundary-layer collapse
  `michaelisMenten_boundaryLayer`;
- `michaelisMenten_qssa_error`: the compact-time error theorem against the flat complex-equilibrium
  fibre;
- `MichaelisMentenManifold`: the substrate-dependent complex equilibrium `mmComplexEquil`
  `= Vmax·s/(Km+s)`, its manifold map (`mmManifoldMap_eq`, `continuousOn_mmManifoldMap`), and the
  substrate-dependent error theorems (`michaelisMenten_manifold_qssa_error`,
  `michaelisMenten_manifold_qssa_error_const`);
- `MichaelisMentenReduced`: the reduced scalar Michaelis–Menten field `mmReducedField`
  `= −Vmax·s/(Km+s)` on `s ≥ 0` (extended by `0`), which is `(Vmax/Km)`-Lipschitz
  (`mmReducedField_lipschitz`) and bounded (`mmReducedField_abs_le`); the **constructed** substrate
  curve `mmSubstrate` from `ODE.exists_isIntegralCurve`, its forward positivity
  (`mmSubstrate_nonneg`), and the closed compact-time error theorem
  `michaelisMenten_reduced_qssa_error`;
- `MichaelisMentenDepletion`: the qualitative dynamics of the reduced flow: the substrate is
  monotonically depleted (`mmSubstrate_antitone`), stays in `[0, s₀]` (`mmSubstrate_le_init`,
  `mmSubstrate_nonneg_all`), and settles to a limit as `t → ∞` (`mmSubstrate_tendsto_atTop`).

Everything stated is fully proved on compact time; the reduction's `ε`-dependence and
infinite-horizon behavior are out of scope.

## Routh–Hurwitz and the Hopf crossing gate

The stability of linearizations, through degree 4. A real polynomial is **Hurwitz**
(`CRNT.IsHurwitz`) when all complex roots lie in the open left half-plane: exactly the
characteristic polynomial of a linear system whose every mode decays.

**Degree 2 and 3.**

- `hurwitz_quadratic_iff` / `hurwitz_quadratic_root_iff`, the **degree-2** criterion:
  `z² + a₁z + a₀` is Hurwitz iff `0 < a₁` and `0 < a₀`;
- `hurwitz_cubic_necessary`, the **degree-3 necessity** direction: a Hurwitz monic real cubic
  satisfies `0 < a₂`, `0 < a₁`, `0 < a₀`, and `a₀ < a₂·a₁`;
- `hurwitz_cubic_sufficient_allReal` / `hurwitz_cubic_sufficient_conjPair` and
  `hurwitz_cubic_root_iff`, the **degree-3 sufficiency** cores and the full degree-3 criterion as a
  root-predicate `iff` (given the Vieta identities and the real-coefficient conjugation dichotomy);
- `cubic_mem_roots_of_isRoot` and `hurwitz_cubic_root_iff_coeff` discharge the conjugation dichotomy
  from the reality of the coefficients alone, giving the **coefficient-only** degree-3 criterion
  (no structural hypothesis).

**Degree 4 (Liénard–Chipart).** For the monic real quartic `X⁴ + a₃X³ + a₂X² + a₁X + a₀` the
Liénard–Chipart form of Routh–Hurwitz tests the coefficients together with the single third Hurwitz
determinant `Δ₃ = a₃a₂a₁ − a₁² − a₃²a₀`, not the whole determinant sequence:

- `hurwitz_quartic_necessary` (with cores `hurwitz_quartic_necessary_allReal`,
  `_oneConjPair`, `_twoConjPair`): a Hurwitz monic real quartic satisfies `0 < a₃`, `0 < a₂`,
  `0 < a₁`, `0 < a₀`, and `a₁² + a₃²a₀ < a₃a₂a₁` (the strict `Δ₃ > 0`);
- `hurwitz_quartic_sufficient_allReal` / `_oneConjPair` / `_twoConjPair` and
  `hurwitz_quartic_root_iff`, the sufficiency cores and the **full degree-4 criterion** in
  root-predicate form: those five conditions hold iff every root lies in the open left half-plane.

The conjugate-pair cores rest on a factored form of `Δ₃` in the root parameters
(`2p(r+s)((r+p)²+q)((s+p)²+q)` for one pair, `4pu(((p+u)²+q+v)² − 4qv)` for two), which reads the
sign of each real part off the determinant condition.

**The Hurwitz matrix and the eigenvalue bridge.** `hurwitzMatrix` / `hurwitzDet` are the general
`n × n` Hurwitz matrix and its leading principal minors. The low-degree minors are tied to the
scalar determinant conditions: `hurwitzDet_two_cubic : hurwitzDet a 3 2 _ = a₂·a₁ − a₀` and
`hurwitzDet_three_quartic : hurwitzDet a 4 3 _ = a₃a₂a₁ − a₁² − a₃²a₀`. The criteria above are
stated about polynomial coefficients; `CRNT/Dynamics/Hurwitz2Matrix.lean` makes the planar case a
genuine statement about eigenvalues. A real `2 × 2` matrix has characteristic polynomial
`X² − (tr M)X + (det M)` over `ℂ` (`hurwitz_matrix_fin_two_charpoly`), so
`hurwitz_matrix_fin_two_iff` reads the degree-2 criterion as the classical trace–determinant test:
every eigenvalue is in the open left half-plane iff `tr M < 0` and `0 < det M`. Applied to the
mass-action Jacobian, `massActionJacobian_fin_two_hurwitz_iff` is a no-oscillation gate at a state
`x` for a two-species network: the linearization `N.massActionJacobian κ x` is a stable
linearization iff its trace is negative and its determinant positive.

**The Hopf crossing gate.** On the boundary of the Hurwitz region, where the penultimate Hurwitz
determinant vanishes while the lower data stay positive, an eigenvalue pair reaches the imaginary
axis:

- `hopf_crossing_gate` (core `hopf_crossing_core`), **degree 3**: at `a₂·a₁ = a₀` with `0 < a₁`,
  `0 < a₀`, the cubic carries a **purely imaginary conjugate eigenvalue pair** (zero real part,
  nonzero imaginary part) and the remaining real root is negative;
- `hopf_crossing_gate_quartic` (core `hopf_crossing_core_quartic`), **degree 4**: at `Δ₃ = 0` with
  `0 < a₃`, `0 < a₀`, exactly one conjugate pair lands on the imaginary axis while the other stays
  in the open left half-plane.

These are the algebraic eigenvalue-crossing conditions under which a Hopf bifurcation can occur.

**The dynamical Hopf bifurcation.** The planar Poincaré normal form `ẇ = (α + iω) w + c₁ w |w|²` and
the first Lyapunov coefficient `ℓ₁ = Re c₁` are formalized in `HopfNormalForm.lean`, together with the
radial amplitude law (a positive equilibrium amplitude `√(−α/ℓ₁)` exists when `α/ℓ₁ < 0`), sub/
supercriticality, and the conditional Hopf–Andronov theorem `hopf_andronov_periodic_orbits` (the
periodic-orbit existence carried as a `PeriodicOrbitSeed`, mirroring the center-manifold seed pattern).
`HopfLimitCycle.lean` constructs the closed-form limit cycle `Rstar e^{i(θ₀ + Ω t)}` of the
*truncated* normal form, proves it solves the truncated field, is periodic and nonconstant, and
assembles it into the seed, so `hopf_andronov_truncated` fires unconditionally for the truncation.
`HopfPersistentOrbit.lean` discharges the persistence of that cycle under the `O(|w|⁴)` tail: the
scalar Lyapunov–Schmidt reduction — the implicit function theorem applied to the full averaged radial
field at the nondegenerate root `2ℓ₁ Rstar² ≠ 0` — produces a persistent amplitude branch
(`amplitudeBranch`, `amplitudeBranch_isRoot`) varying continuously with the parameter; the remaining
rotation-closure (turning a positive root into a genuine periodic orbit of the full planar field) is
the one step needing Poincaré-return-map infrastructure Mathlib lacks, and is carried as the explicit
hypothesis of `hopf_andronov_full_field`. The center-manifold reduction down to the planar field, and
the averaging that produces the radial field, are recorded as data; Mathlib provides neither
center-manifold theory nor a return-map construction. The general-degree Routh–Hurwitz converse
(positivity of all `n` Hurwitz determinants implies Hurwitz, via Hermite–Biehler / Routh-array
continued fractions) is **not formalized**; the root-predicate criterion is complete through degree 4.

## Modules

Kinetics:
- `CRNT/Kinetics/Concentration.lean`: concentrations, nonnegativity/positivity, mass-action
  monomial.
- `CRNT/Kinetics/MassAction.lean`: rate constants, mass-action rate and vector field.
- `CRNT/Kinetics/MassActionJacobian.lean`: differentiability of the field; the Jacobian as a
  continuous linear map and as a matrix.
- `CRNT/Kinetics/General.lean`: the `Kinetics` abstraction; boundary non-attraction and
  conservation; mass action as an instance.
- `CRNT/Kinetics/Generalized.lean`: generalized (Müller–Regensburger) mass action.

Dynamics:
- `CRNT/Dynamics/MassActionAlgebra.lean`: the `ẋ = Y(A_k(Ψ x))` factorization.
- `CRNT/Dynamics/MassActionField.lean`: smoothness, boundary non-attraction, local existence.
- `CRNT/Dynamics/FlowConstruction.lean`: the `Flow ℝ≥0` of a bounded Lipschitz field.
- `CRNT/Dynamics/LaSalle.lean`: LaSalle's invariance principle for forward semiflows.
- `CRNT/Dynamics/Monotone.lean`: order-preserving flows and scalar comparison.
- `CRNT/Dynamics/Nagumo.lean`: single-valued Nagumo invariance of the nonnegative orthant.
- `CRNT/Dynamics/QSSA.lean`: the compact-time quasi-steady-state error bound.
- `CRNT/Dynamics/Tikhonov.lean`: boundary-layer exponential attraction; the derived defect.
- `CRNT/Dynamics/Fenichel.lean`, `FenichelManifold.lean`, `FenichelSlowDrift.lean`: the slow
  manifold, its manifold map, and slow-drift bounds.
- `CRNT/Dynamics/MichaelisMenten.lean`, `MichaelisMentenManifold.lean`, `MichaelisMentenReduced.lean`,
  `MichaelisMentenDepletion.lean`: the Michaelis–Menten reduction and depletion.
- `CRNT/Dynamics/RouthHurwitz.lean`, `Hurwitz.lean`: the degree-2 and degree-3 criteria and the
  Hurwitz matrix.
- `CRNT/Dynamics/RouthHurwitz4.lean`, `RouthHurwitz4Suff.lean`: degree-4 Liénard–Chipart necessity
  and sufficiency.
- `CRNT/Dynamics/Hurwitz2Matrix.lean`: the planar trace–determinant test from the characteristic
  polynomial, and the two-species mass-action Jacobian gate.
- `CRNT/Dynamics/HopfGate.lean`, `HopfGate4.lean`: the degree-3 and degree-4 Hopf crossing gates.
- `CRNT/Dynamics/HopfNormalForm.lean`: the planar Poincaré normal form, the first Lyapunov
  coefficient, the radial amplitude law, and the conditional Hopf–Andronov theorem.
- `CRNT/Dynamics/HopfLimitCycle.lean`: the closed-form limit cycle of the truncated normal form and
  its constructed periodic-orbit seed.
- `CRNT/Dynamics/HopfPersistentOrbit.lean`: the scalar Lyapunov–Schmidt reduction persisting the
  limit-cycle amplitude through the `O(|w|⁴)` tail via the implicit function theorem.

Lyapunov / stability stack:
- `CRNT/Theorems/DeficiencyZero/Lyapunov.lean`: `relEntropy` and its positive definiteness.
- `CRNT/Theorems/DeficiencyZero/Dissipation.lean`: the dissipation rate and its sign.
- `CRNT/Theorems/DeficiencyZero/Stability.lean`: descent along solutions.
- `CRNT/Theorems/DeficiencyZero/Confinement.lean`: the `clampBox` cutoff and coercivity.
- `CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean`: `omegaLimit_eq_singleton_of_local`.
- `CRNT/Dynamics/GlobalStability.lean`: `omegaLimit_eq_singleton_of_persistent`, the
  persistence-conditional global form.

## Related documents

- [`architecture.md`](architecture.md): the layered organization and theorem dependency graph.
- [`deficiency.md`](deficiency.md): equilibrium existence, complex balancing, Birch, and the
  deficiency theorems (the uniqueness input to local asymptotic stability).
- [`persistence-gac.md`](persistence-gac.md): global dynamics, siphons, persistence, and the global
  attractor conjecture.
