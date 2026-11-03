# Stochastic CRN

Recurrence/non-explosion results use explicit Lyapunov data, restricted count-tier structures, one-species hypotheses, or the other assumptions in their signatures. Several-species strong endotacticity alone is insufficient; the unrestricted assertion is false (arXiv:1808.05328, Examples 3.1–3.2). Scaling theorems include generator estimates and fixed-time Gaussian weak limits; a general filtered path process and path-space LLN/CLT remain incomplete. `IsDeadlockedCount` excludes enabled channels; `IsAbsorbingCount` permits enabled null channels.

This document describes the discrete-molecule regime of the `CRNT` library: the
chemical master equation of stochastic mass-action kinetics, the Anderson–Craciun–Kurtz
product-form stationary distribution for complex-balanced networks, and the ergodic and
scaling theory built on top of it — the embedded jump chain, the uniformized
continuous-time transition semigroup, and the density-dependent (Kurtz) generator limit.
It is one of the per-area documents linked from [`architecture.md`](architecture.md).

When molecule counts are small, concentrations are not a faithful description: the state is
a vector of nonnegative integer counts, one per species, and each reaction firing is a
discrete jump that shifts the count by the reaction's net stoichiometry. The state space is
the count lattice `ℕ^S`, modelled here as `S → ℕ`. The dynamics is a continuous-time Markov
chain: reaction `r` fires from a count `n` at the *stochastic mass-action propensity*
`κ r · ∏ s (n s)^{(source r s)}`, the falling-factorial counting law, the combinatorial
analogue of the deterministic monomial. The evolution of the law of the chain is the
**chemical master equation** `π̇ = πQ`, with generator `Q` assembling the inflow into and
outflow out of each count.

The main result is that for a **complex-balanced** network the stationary law is a
product of independent Poissons, one per species, with rate the complex-balanced equilibrium
concentration `c`. This is the discrete-state counterpart of the deterministic
deficiency-zero theory: complex balancing is the same notion `IsComplexBalanced`
(`CRNT.Equilibria.ComplexBalanced`) that controls the deterministic equilibria (see
[`deficiency.md`](deficiency.md)), and the equilibrium concentration that solves
`A_k(Ψ x) = 0` is exactly the Poisson parameter here. The literature is Anderson, Craciun &
Kurtz, *Product-form stationary distributions for deficiency zero chemical reaction
networks* (2010).

The layers run bottom-up: the product-Poisson density and its algebra, the
master-equation generator and generator-level stationarity, the embedded discrete-time jump
kernel and its measure invariance, the restriction of that invariant measure to a closed
communicating region, its canonical maximal form, the normalized invariant probability
measure, and the support and product-form proportionality of that probability measure. On
that base sits the ergodic theory of the region: uniqueness of the stationary law, geometric
convergence of the embedded chain under primitivity, and — because the embedded chain of a
genuine network carries no aperiodicity self-loop — the *uniformized* transition semigroup
`P_t = exp(tQ)`, which supplies the missing self-loop, preserves the product-Poisson law for
all time, and relaxes to it. A final layer is the density-dependent (Kurtz) scaling that ties
this regime to the deterministic mass-action ODE.

## The product-form density

`CRNT/Stochastic/ProductForm.lean` supplies the measure-theoretic candidate and the
algebraic identity at the heart of the theorem.

- **`productPoisson c hc`**: the product-of-Poissons measure on `S → ℕ`, the `Measure.pi` of
  one Poisson factor per species, with rate `c s`. It is a probability measure
  (`IsProbabilityMeasure` instance).
- **`productPoissonPMF c n`**: the explicit density `∏ s, exp(-(c s))·(c s)^(n s)/(n s)!`.
  `productPoissonPMF_nonneg` records nonnegativity; `productPoisson_singleton` identifies the
  measure of a single count vector `{n}` with `ENNReal.ofReal (productPoissonPMF c n)`.
- **`stochasticMassActionRate κ n r`**: the stochastic propensity of reaction `r` at count
  `n`, the rate constant times the falling-factorial counting law `∏ s (n s)^{(source r s)}`
  (via `Nat.descFactorial`). `stochasticMassActionRate_nonneg` gives nonnegativity.

The product-form identity is what makes the proof go through. Per species,
`poissonFactor_mul_descFactorial` proves
`(exp(-c)·c^m/m!) · m^{(k)} = c^k · (exp(-c)·c^{m-k}/(m-k)!)` for `k ≤ m`. Taking the product
over all species, **`productPoissonPMF_mul_descFactorial`** gives, for a count `n` dominating
the source complex of `r`,

```
productPoissonPMF c n · ∏ s (n s)^{(source r s)}
  = (∏ s (c s)^{source r s}) · productPoissonPMF c (n − source r).
```

This is `π(n)·n^{(k)} = c^k·π(n − k)`: multiplying the density by a falling-factorial
propensity reproduces the density at the shifted count weighted by a power of the rate. It
is the exact content that lets the stochastic flux balance reduce to the deterministic
complex-balance equation.

## The master-equation balance and generator-level ACK stationarity

Mathlib has no continuous-time Markov generator type, so the generator is rendered as an
explicit pointwise-finite algebraic operator on real-valued state functions over `ℕ^S`. This
is done in two layers.

`CRNT/Stochastic/Generator.lean` works at the global-balance level. For a complex-balanced
concentration `c`, the per-reaction product-form substitution turns each literal jump flux
into the complex-indexed quantity
`massActionRate κ r c · (shiftedPMF c n (target r) − shiftedPMF c n (source r))`, where
`shiftedPMF c n y = productPoissonPMF c (n − y)`. Their reaction-indexed sum is
**`generatorFlux`**, and the count-indexed total is the **`ackResidual`**;
**`IsMasterStationary`** is its vanishing at every count (the global balance `πQ = 0`, i.e.
`∑ inflow = ∑ outflow` at each `n`).

- **`sum_target_flux_eq_inflow`** / **`sum_source_flux_eq_outflow`** regroup the
  reaction-indexed inflow and outflow sums over the finite set of complexes `N.complexes`,
  producing the complex-indexed `inflow`/`outflow` of the network.
- **`productPoisson_isStationary_of_complexBalanced`**: the Anderson–Craciun–Kurtz theorem
  at the master-equation level: for `c` complex-balanced (`IsComplexBalanced`), `ackResidual`
  vanishes at every count. The proof regroups inflow and outflow by complex and collapses the
  balance termwise via complex balance `inflow = outflow` at each complex.
  `ackResidual_eq_zero_of_complexBalanced` is the pointwise restatement.
- **`productPoissonPMF_mul_stochasticRate`** is the grounding bridge: for a count dominating
  the source complex, the raw outflow flux `π(n)·λ_r(n)` equals the complex-indexed
  `massActionRate κ r c · shiftedPMF c n (source r)`.

`CRNT/Stochastic/CTMC.lean` exhibits the literal generator. **`cmeGenerator κ c n`** is
`(∑_r generatorInflow) − (∑_r generatorOutflow)`, the value `(Qπ)(n)` with
`π = productPoissonPMF c`. The exit/holding rate of a state,
**`exitRate κ n = ∑_r stochasticMassActionRate κ n r`** (nonnegative by `exitRate_nonneg`),
is the rate at which the chain leaves `n`. A reaction is **`Enabled`** at `n` when `n`
dominates its source complex (decidable instance provided).

- **`cmeGenerator_eq_ackResidual`** rewrites the literal generator into the master-equation
  residual reaction-by-reaction, and **`isGeneratorStationary_iff_isMasterStationary`** shows
  the two stationarity predicates coincide.
- **`productPoisson_isGeneratorStationary_of_complexBalanced`** is ACK at the generator
  level: for `c` complex-balanced, **`IsGeneratorStationary`** holds — the generator
  annihilates the product-Poisson density at every count, `πQ = 0`.
- **`stochasticOutflow_eq_generatorOutflow`** identifies the literal per-reaction outflow flux
  `π(n)·λ_r(n)` with `generatorOutflow` at an enabled count, and
  **`stochasticTotalOutflow_eq_generatorOutflow`** identifies the holding-rate departure flux
  `π(n)·exitRate κ n` with the total complex-indexed outflow on the fully-enabled part of the
  lattice.

## The jump kernel and `Kernel.Invariant`

The continuous-time chain carries an embedded discrete-time **jump chain**: when the process
leaves a count `n`, the next reaction to fire is `r` with probability proportional to its
propensity. This is rendered first at the real-arithmetic level, then lifted to a Mathlib
`ProbabilityTheory.Kernel`.

`CRNT/Stochastic/JumpKernel.lean` is the real-valued layer. The transition probability is
**`jumpProb κ n r = stochasticMassActionRate κ n r / exitRate κ n`** (`jumpProb_nonneg`). On
the positive-exit part of the lattice the row is stochastic, `sum_jumpProb_eq_one`; at an
absorbing count where `exitRate κ n = 0` every `jumpProb` is zero
(`jumpProb_eq_zero_of_exitRate_zero`), the boundary defect. The jump chain's
stationary weight is **`jumpStationaryMass κ c n = productPoissonPMF c n · exitRate κ n`**,
the product-Poisson density reweighted by the holding rate. On the fully-enabled part this
weight equals the total complex-indexed generator outflow
(`jumpStationaryMass_eq_generatorOutflowSum`), and `jumpGlobalBalance_of_complexBalanced` is
the embedded global balance: there, generator stationarity forces the total complex-indexed
inflow to equal this stationary mass.

`CRNT/Stochastic/Kernel.lean` lifts the jump chain to a measure-theoretic kernel. The count
lattice is given the discrete `⊤` `MeasurableSpace` (a module-local instance
`instMeasurableSpaceCount`), under which every set, singleton, and function out of the
lattice is measurable, discharging all measurability obligations. The post-firing count is
**`jumpNextCount n r = n − source r + target r`**, and the kernel is

```
jumpKernel κ n = if exitRate κ n = 0 then dirac n
                 else ∑_r ofReal (jumpProb κ n r) • dirac (jumpNextCount n r),
```

holding (self-loop Dirac) at absorbing counts. **`instIsMarkovKernel_jumpKernel`** proves it
is a Markov kernel everywhere on the lattice (`jumpKernel_univ_eq_one`), `jumpKernel_apply'`
gives the explicit per-set mass, and `jumpKernel_apply_of_exitRate_pos` is its positive-exit
reading as a single reaction sum.

`CRNT/Stochastic/KernelInvariant.lean` builds the candidate stationary measure
**`jumpStationaryMeasure κ c = Measure.sum (fun n => ofReal (jumpStationaryMass κ c n) • dirac n)`**,
the `ℝ≥0∞`-density measure on the countable lattice. Its singleton mass is
`jumpStationaryMeasure_singleton`, and `jumpStationaryMeasure_bind_apply` computes the
pushforward `μ.bind (jumpKernel κ)` on any set as the predecessor-indexed tsum
`∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ n s`;
`jumpStationaryMeasure_bind_singleton` is its singleton specialization with the kernel row
expanded over reactions. This module states the predecessor `bind`-to-sum identity; closing
it into invariance is the content of `KernelStationary` below.

`CRNT/Stochastic/KernelStationary.lean` closes this into measure invariance. The
unique source-dominating **`predecessorCount r m = m + source r − target r`** is the only
count that fires `r` to land on `m` while dominating the source; every other count landing on
`m` has vanishing propensity (`stochasticMassActionRate_eq_zero_of_not_source_le`). The key
cancellation `jumpStationaryMass_mul_jumpProb_eq_generatorOutflow` removes the holding-rate
denominator, and **`predecessor_sum_eq`** proves the predecessor summation
`∑' n, ofReal (jumpStationaryMass κ c n) · jumpKernel κ n {m} = ofReal (jumpStationaryMass κ c m)`.
This yields **`jumpKernel_invariant_jumpStationaryMeasure`**:
`Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)` for `c` complex-balanced, under
explicit **no-boundary** hypotheses: every count has positive exit rate (`hexit`), is enabled
for every reaction (`henabled`), and dominates every reaction's target complex (`htarget`).
These are needed because the `exitRate = 0` holding states are absorbing, where strict
pointwise balance fails.

## The closed-enabled-region restriction

The global no-boundary hypotheses fail on the genuine lattice: small counts are absorbing or
under-resource a reaction. `CRNT/Stochastic/KernelIrreducible.lean` removes them by
restricting the invariant measure to a self-contained region.

A **`ClosedEnabledRegion κ T`** is a structure on a set of counts `T` that is closed and
boundary-free for the jump chain: no member is absorbing (`exit_ne`), every member is
`Enabled` for and dominates every reaction (`enabled`, `target_le`), and both the post-firing
count (`forward`) and the source-dominating predecessor (`backward`) of any member stay in
`T`. These are the membership-gated readings of the global hypotheses; `closedEnabledRegion_univ`
recovers them at `T = Set.univ`, so the structure is a strict weakening.

The exported result is **unconditional** support-restricted invariance,
**`jumpKernel_invariant_restrictedStationaryMeasure`**:
`Kernel.Invariant (jumpKernel κ) (restrictedStationaryMeasure κ c T)` for any closed
enabled region `T` at a complex-balanced concentration, with no global `hexit`/`htarget`,
where `restrictedStationaryMeasure κ c T = (jumpStationaryMeasure κ c).restrict T`. The two
measures agree on singletons: equal to the lifted stationary weight inside `T`
(`restricted_predecessor_sum_eq`) and zero outside it (`restricted_predecessor_sum_eq_zero`,
since closure admits no inbound mass).

`CRNT/Stochastic/KernelMaximalRegion.lean` makes the region canonical. The family of closed
enabled regions is closed under arbitrary union (`sUnion_closedEnabledRegion`), so the union
of all of them, **`maximalClosedEnabledRegion`**, is itself a closed enabled region
(`closedEnabledRegion_maximal`) containing every other (`subset_maximalClosedEnabledRegion`).
**`jumpKernel_invariant_maximalRegion`** carries the invariant measure on this canonical
region with no region supplied by hand. The maximal region is an existence object; pinning it
down to a concrete count set for a given network is addressed, for the reversible pair, by the
conservation-class construction below.

## Normalization, support, and product-form proportionality

`CRNT/Stochastic/KernelNormalized.lean` normalizes to a probability measure. Scaling an
invariant measure preserves invariance (`invariant_smul`), so a finite nonzero invariant
measure divided by its total mass is an invariant probability measure (`invariant_normalize`).
The restricted stationary measure is finite over a finite region
(`restrictedStationaryMeasure_isFiniteMeasure`), so
**`jumpKernel_normalized_isInvariant_probabilityMeasure`** delivers, for a finite closed
enabled region of positive mass, a measure that is both `Kernel.Invariant` under the jump
kernel and an `IsProbabilityMeasure`: the stationary distribution of the embedded jump chain
on the region.

The positive-mass condition is then discharged at a **strictly positive** concentration. The
product-Poisson density is positive at every count (`productPoissonPMF_pos`), so the lifted
jump-chain weight is positive on a closed enabled region (`jumpStationaryMass_pos`, using
`exit_ne`), forcing the restricted measure's total mass positive over a nonempty region
(`restrictedStationaryMeasure_univ_pos`). The capstone
**`jumpKernel_isInvariant_probabilityMeasure_of_nonempty`** is therefore unconditional in the
mass: at a strictly positive complex-balanced concentration, the normalized restricted
stationary measure of a nonempty finite closed enabled region is an invariant probability
measure with no positive-mass hypothesis supplied by hand.

`CRNT/Stochastic/KernelSupport.lean` identifies the support of that probability measure. It is
strictly positive on every singleton inside the region
(`jumpKernel_invariantProb_singleton_pos`), null on every count outside it
(`jumpKernel_invariantProb_singleton_eq_zero`), and null on the whole complement
(`jumpKernel_invariantProb_compl_eq_zero`): the stationary distribution is supported exactly on
the region.

`CRNT/Stochastic/KernelProductForm.lean` records the product-form proportionality of the
singleton masses. Cross-multiplying two singleton masses inside the region cancels the shared
reciprocal total mass, leaving the lifted jump-chain weights symmetric
(`jumpKernel_invariantProb_singleton_ratio`); the masses are stated without division or
positivity, the discrete shadow of the Anderson–Craciun–Kurtz product form. The support
biconditional `jumpKernel_invariantProb_singleton_ne_zero_iff` records that a singleton mass is
nonzero exactly when the count lies in the region.

## Uniqueness and geometric convergence of the embedded jump chain

Existence of a stationary law is not uniqueness, and invariance is not convergence. On a
finite region the embedded jump chain is a finite-state Markov chain, and the finite-state
Perron–Frobenius theory of `CRNT.LinearAlgebra.PerronFrobenius` supplies both. Mathlib's
`ProbabilityTheory.Kernel.Irreducible` is a stub carrying no uniqueness, so the ergodic
content is obtained through the restricted transition matrix rather than the kernel API.

`CRNT/Stochastic/Ergodicity.lean` sets up the matrix bridge. **`regionMatrix κ T`** is the
restricted transition matrix on the finite type `↥T`, entry `i, j` the kernel mass
`(jumpKernel κ j {i}).toReal`; it is nonnegative (`regionMatrix_nonneg`) and, by
forward-closure of a closed enabled region, column-stochastic (`regionMatrix_colStochastic`).
**`stationaryVec μ`** is the real singleton-mass vector of a region-supported measure, and
**`stationaryVec_mulVec_fixed`** reads invariance of a region-supported probability measure as
the matrix fixed-point equation `regionMatrix · v = v`. The irreducibility hypothesis is
**`regionStronglyConnected`**: the support digraph of `regionMatrix` is strongly connected.
Under it, **`invariant_probabilityMeasure_unique_on_region`** proves that any two invariant
probability measures supported on a finite strongly connected closed enabled region coincide —
uniqueness via Perron–Frobenius, the finite-state replacement for general Meyn–Tweedie
ergodicity.

`CRNT/Stochastic/ErgodicConvergence.lean` and `CRNT/Stochastic/ErgodicConvergenceGeneral.lean`
prove geometric mixing in the `ℓ¹` distance `l1Dist u v = ∑ i, |u i − v i|`. A column-stochastic
matrix is `ℓ¹`-nonexpansive on mass-balanced differences (`colStochastic_l1_le`); a strictly
positive one contracts by the Doeblin factor `1 − card · δ < 1` (`colStochastic_l1_contraction`).
**`colStochastic_pow_mulVec_tendsto`** handles the strictly-positive (one-step primitive) case,
and **`colStochastic_primitive_pow_mulVec_tendsto`** the general **primitivity** case — some
fixed power `P^N` is entrywise strictly positive — by interleaving the `N`-step Doeblin
contraction with per-step nonexpansiveness of the residual factor. The region-level payoff is
**`regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec`**: on a finite primitive closed
enabled region, the `n`-step singleton masses of any region-supported initial law converge to
the canonical stationary singleton masses (`stationaryProbabilityMeasure`).

`CRNT/Stochastic/RegionPrimitive.lean` discharges primitivity from a checkable structural
class: **`primitive_of_stronglyConnected_self_loop`** — a nonnegative matrix with strongly
connected support digraph and a single self-loop (a state with positive diagonal) has a strictly
positive fixed power, the standard irreducibility-plus-aperiodicity criterion; its region form
is **`regionPrimitive_of_stronglyConnected_self_loop`**.

The strong-connectivity hypothesis is itself reduced to network structure.
`CRNT/Stochastic/RegionStronglyConnected.lean` defines **`RegionJumpStronglyConnected`** — every
ordered pair of region counts joined by a forward walk of positive-probability enabled jumps —
and **`regionStronglyConnected_of_jumpReaches`** discharges `regionStronglyConnected` from it.
`CRNT/Stochastic/JumpReachabilityLift.lean` and `CRNT/Stochastic/CountWitnessPath.lean` lift
reaction-graph reachability (`Reaches`) to count-level jump walks through a `FireableList`,
discharging `RegionJumpStronglyConnected` on a *complex-shift region* (a region that is a base
count shifted along reachable complexes) from weak reversibility alone
(`weaklyReversible_pow_mulVec_tendsto_stationaryVec`,
`complexShiftRegion_pow_mulVec_tendsto_stationaryVec`).

### The self-loop obstruction

The catch is aperiodicity. `CRNT/Examples/StochasticConvergenceExample.lean` proves two
obstructions on the reversible pair `A ⇌ B`, generic to any genuine network:

- **`no_aperiodic_self_loop`**: a positive-probability reaction is enabled, so its firing is the
  exact untruncated shift `n − source + target`, which equals `n` only when `source = target`.
  A reaction between distinct complexes therefore never holds, so the embedded jump chain has
  **no** aperiodicity self-loop, and its restricted matrix is never primitive.
- **`pair_not_closed_of_mem`**: enabled-everywhere forces every member of a closed enabled
  region off the propensity-vanishing simplex boundary, while forward-closure drags boundary-
  adjacent firings back onto it. No nonempty conservation window of `A ⇌ B` is a closed enabled
  region.

So the closed-enabled-region-plus-self-loop convergence interface, though sound, is jointly
unsatisfiable on the genuine count lattice of a mass-action network. The resolution is
uniformization.

## The uniformized transition semigroup

`CRNT/Stochastic/Semigroup.lean` builds the continuous-time transition semigroup
`P_t = exp(tQ)` by **uniformization** (Jensen; Norris, *Markov Chains*). Over a finite region
the exit rate is bounded by **`uniformizationRate`** `Λ = 1 + ∑_{n ∈ T} exitRate κ n`, so the
generator factors through a single bounded stochastic kernel

```
uniformizedKernel  U = (1 − w)·δ_n + w·jumpKernel,   w = exitRate κ n / Λ ,
```

a genuine Markov kernel (`instIsMarkovKernel_uniformizedKernel`) that carries a **holding
term** at every region state — the self-loop the embedded chain lacks. The semigroup is the
Poisson-weighted superposition of its powers,

```
cmeSemigroup κ hTfin t (n, ·) = ∑_{k ≥ 0} e^{−Λt}(Λt)^k/k! · U^{∘k}(n, ·) ,
```

each **`cmeSemigroup t`** a Markov kernel (`instIsMarkovKernel_cmeSemigroup`). The structure of
the semigroup:

- **`cmeSemigroup_zero`**: `P_0 = id` (the rate-zero Poisson mass concentrates on `U^{∘0}`).
- **`cmeSemigroup_comp`** (`CRNT/Stochastic/SemigroupComposition.lean`): the Chapman–Kolmogorov
  law `P_{s+t} = P_s ∘ₖ P_t`, from the Poisson point-mass convolution
  `∑_{j+k=m} Po(s){j}·Po(t){k} = Po(s+t){m}` (the binomial theorem) and the kernel power law
  `U^{∘j} ∘ₖ U^{∘k} = U^{∘(j+k)}`.
- **`cmeSemigroup_preserves_stationarity`**: the support-restricted, normalized product-Poisson
  probability measure is invariant under every `P_t`, at a nonnegative complex-balanced
  concentration. This is the process-level companion of the generator stationarity `πQ = 0`:
  the continuous-time semigroup carries the Anderson–Craciun–Kurtz law to itself for all time.
  The preserved law is the product-Poisson density **`cmeStationaryMeasure`** itself — *not* the
  holding-rate-reweighted jump-chain law of `KernelNormalized`; the two differ by the `exitRate`
  factor, and uniformization maps the density to itself through the embedded jump-chain balance.

`CRNT/Stochastic/UniformizedConvergence.lean` proves convergence of the uniformized chain.
Its region matrix **`uRegionMatrix`** is column-stochastic (`uRegionMatrix_colStochastic`) and
has a **strictly positive diagonal** (`uRegionMatrix_diag_pos`): the holding weight
`1 − w > 0` supplies the aperiodicity self-loop from `U`, not from a network reaction, so the
obstruction `no_aperiodic_self_loop` does not apply. Inheriting strong connectivity from the
embedded chain (`uRegionMatrix_stronglyConnected_of_regionStronglyConnected`, since the jump
term keeps every support edge), the matrix is primitive (`uRegionMatrix_primitive`) and its
powers converge geometrically (**`uRegionMatrix_pow_mulVec_tendsto`**) — non-vacuous exactly
where the embedded-chain theorem was empty.

## The conservation-class realization and the `A ⇌ B` instance

The closed-enabled-region hypothesis is still unsatisfiable on a genuine conservation window,
so `CRNT/Stochastic/ConservationClassRegion.lean` relaxes it to precisely what column-
stochasticity of `U` needs. A **`ConservationClassRegion`** requires only that no member is
absorbing (`exit_ne`) and that every *positive-probability* firing lands in the region
(`forward`) — no enabled-everywhere or target-domination demand, so boundary members belong.
Every `ClosedEnabledRegion` is one (`ClosedEnabledRegion.toConservationClassRegion`). Under it,
`U`'s region matrix is column-stochastic (`uRegionMatrix_colStochastic_of_conservationClass`)
and primitive on a jump-strongly-connected region
(`uRegionMatrix_primitive_of_conservationClass`), giving geometric convergence
(**`uRegionMatrix_pow_mulVec_tendsto_of_conservationClass`**).

The reversible pair `A ⇌ B` on a fixed conservation class `{n : n_A + n_B = K}` is exhibited as
such a region: finite (`conservationClass_finite`), non-absorbing and jump-forward-closed
(`conservationClassRegion`), and jump-strongly-connected as a birth–death chain on `{0,…,K}`
(`conservationClass_jumpStronglyConnected`, routed through the boundary count `(K,0)`). This
discharges every hypothesis, giving unconditional discrete geometric convergence
**`conservationClass_pow_mulVec_tendsto`** on a weakly reversible network — the aperiodicity
self-loop supplied by the uniformized holding mass even at the simplex boundary where a closed
enabled region cannot exist.

`CRNT/Stochastic/SemigroupConvergence.lean` lifts this discrete mixing to continuous time. The
analytic engine is **`tendsto_poissonAverage_atTop`**: if a real sequence `a_k → L`, its Poisson
average `∑_k Po(r){k}·a_k → L` as the rate `r → ∞` (a Poisson-tail/dominated-convergence
argument, from `x^k e^{−x} → 0`). Threading `r = Λt` with `Λ > 0` (`tendsto_poissonRate_atTop`),
the continuous-time region vector **`cmeRegionVec`** `= P_t x` relaxes to the discrete stationary
law: **`cmeRegionVec_tendsto_of_conservationClass`** gives `P_t x → π` as `t → ∞` on a jump-
strongly-connected conservation-class region, and **`conservationClass_cmeRegionVec_tendsto`**
delivers it **unconditionally** on the `A ⇌ B` conservation class — the process-level
relaxation to the Anderson–Craciun–Kurtz product-Poisson law on a genuine network.

## Density-dependent (Kurtz) scaling

`CRNT/Stochastic/KurtzScaling.lean` relates the stochastic chain to the deterministic mass-action
ODE in the large-volume limit (Kurtz, *Solutions of ordinary differential equations as limits of
pure jump Markov processes*). The volume-scaled generator **`scaledGenerator κ V f x`** acts on an
observable `f` by `∑_r V·massActionRate κ r x · (f(x + V⁻¹·reactionVector r) − f x)`, and
**`tendsto_scaledGenerator`** proves its pointwise limit: for any Fréchet-differentiable `f`,
`scaledGenerator κ V f x → f'(x)(massActionVectorField κ x)` as `V → ∞`. This is the
generator-convergence estimate, unconditional apart from the differentiability of `f`, with a
worked instance on `A ⇌ B` (`tendsto_scaledGenerator_reversiblePair`).

`CRNT/Stochastic/KurtzFluidLimit.lean` is the deterministic skeleton of the fluid limit. The
limiting reaction-rate ODE is well-posed on a bounded region (Picard–Lindelöf existence
`exists_fluidODE_local`; Grönwall uniqueness `fluidODE_unique`, given a Lipschitz bound). The
fluid-limit estimate **`fluidLimit_dist_le`** bounds the scaled trajectory against the ODE
solution by a Grönwall envelope `gronwallBound δ K η (t − a)`, and
**`fluidLimit_tendsto_uniformly`** sends that bound to zero, conditional on an explicit
fluctuation-residual hypothesis `hfluct : dist(Ẋ^V, F(X^V)) ≤ η_V` with `η_V → 0`. The
probabilistic content is carried in `η_V`; the theorem itself is a deterministic Grönwall
argument.

That fluctuation residual is studied probabilistically, at the level of a static Poisson-clock
model, in `CRNT/Stochastic/{PoissonFluctuation,MultiPoissonFluctuation,PoissonClockFamily,
TimeChangedFluctuation}.lean`. Mathlib carries no Poisson mean or variance, so both are proved
there (`integral_id_poissonMeasure`, `variance_id_poissonMeasure`). The independent scaled-
Poisson clock family `clockMeasure = ⊗_r Po(V·a_r)` is constructed with its independence and
per-term variance proved (`indepFun_scaledClock`, `variance_scaledClock`), giving an
**unconditional** aggregate law of large numbers: the total weighted scaled count converges to its
mean in probability as `V → ∞`, with variance of order `1/V`
(`variance_aggregate_scaledClock`, `tendsto_meas_aggregate_scaledClock`,
`tendsto_meas_aggregate_centeredTimeChange`, `exists_timeChanged_fluct_bound`, the last packaged as
the `η_V → 0` datum). The convergence is Chebyshev-based (in probability), and the time change is
deterministic — each clock is evaluated at the integrated intensity `V·∫₀ᵗ λ_r(x_s) ds` along the
*limit* ODE, the leading term of the genuine state-dependent time change.

## Scope

The probabilistic content lives in three objects: the generator as an explicit pointwise-finite
operator, the embedded discrete-time jump chain as a Mathlib `Kernel`, and the uniformized
continuous-time transition semigroup `P_t = exp(tQ)`. The following lie outside it:

- **No sample-path stochastic process.** There is no path space (Skorokhod / càdlàg trajectories),
  no filtration, no martingale object, and no strong Markov property. Statements are about
  generators, kernels, transition semigroups, and static product-Poisson random variables, not
  about trajectories of a constructed process.
- **The continuous-time semigroup is region-scoped.** `cmeSemigroup` is built by uniformization,
  which needs a bounded exit rate, so it is defined over a *finite* region, not on the full count
  lattice where mass-action exit rates grow without bound.
- **Full-lattice unconditional invariance requires region restriction.** Measure invariance
  (`jumpKernel_invariant_jumpStationaryMeasure`) requires global no-boundary hypotheses, since
  absorbing low-count states break strict pointwise balance; the unconditional forms restrict to a
  closed enabled region (or, for `U`, a conservation-class region).
- **The maximal communicating class is identified only for `A ⇌ B`.** `maximalClosedEnabledRegion`
  is an existence object; its concrete count set — the complex-shift-orbit characterization — is
  pinned down for the `A ⇌ B` conservation class, not for an arbitrary network.
- **The Kurtz fluid limit is a conditional process-level statement.** The generator-convergence
  estimate and the Poisson-clock aggregate law of large numbers are unconditional, but the
  fluid-limit convergence `fluidLimit_tendsto_uniformly` is conditional on a supplied fluctuation-
  residual bound; no theorem connects the Poisson-clock tail bound to that hypothesis, and the
  state-dependent random time change and the Skorokhod-path convergence it supports are not present.
- **No central-limit / diffusion limit.** The fluctuations carry a second-moment order
  `Var = O(1/V)` and Chebyshev convergence in probability, not convergence in distribution to a
  Gaussian or diffusion.
- **Reversibility / detailed balance is not established.** `Kernel.IsReversible`, which needs
  network reversibility, is not proved.

## Modules

Product form, generator, and the embedded jump chain:

`CRNT/Stochastic/`: `ProductForm`, `Generator`, `CTMC`, `JumpKernel`, `Kernel`,
`KernelInvariant`, `KernelStationary`, `KernelIrreducible`, `KernelMaximalRegion`,
`KernelNormalized`, `KernelSupport`, `KernelProductForm`.

Ergodic theory of the embedded chain:

`CRNT/Stochastic/`: `Ergodicity` (`regionMatrix`, `stationaryVec`, `regionStronglyConnected`,
uniqueness), `ErgodicConvergence` (strictly-positive Doeblin convergence),
`ErgodicConvergenceGeneral` (`colStochastic_primitive_pow_mulVec_tendsto`, `regionPrimitive`),
`RegionPrimitive` (primitivity from a self-loop), `RegionStronglyConnected`
(`RegionJumpStronglyConnected`, irreducibility from jump-reachability),
`JumpReachabilityLift`, `CountWitnessPath` (reaction-graph reachability lifted to count walks).

Uniformized continuous-time semigroup and the conservation-class realization:

`CRNT/Stochastic/`: `Semigroup` (`uniformizedKernel`, `cmeSemigroup`, stationarity preservation),
`SemigroupComposition` (Chapman–Kolmogorov), `UniformizedConvergence` (`uRegionMatrix`
primitivity and convergence), `ConservationClassRegion` (the relaxed region and the `A ⇌ B`
conservation class), `SemigroupConvergence` (continuous-time relaxation `P_t x → π`).
`CRNT/Examples/StochasticConvergenceExample.lean` records the self-loop and closed-region
obstructions on `A ⇌ B`.

Density-dependent (Kurtz) scaling and fluctuations:

`CRNT/Stochastic/`: `KurtzScaling` (generator convergence), `KurtzFluidLimit` (the deterministic
Grönwall skeleton, conditional on a fluctuation residual), `PoissonFluctuation`,
`MultiPoissonFluctuation`, `PoissonClockFamily`, `TimeChangedFluctuation` (the Poisson-clock law of
large numbers).

## Related documents

- [`architecture.md`](architecture.md): how this area fits the whole library.
- [`deficiency.md`](deficiency.md): complex balancing and the deficiency-zero theory this regime
  mirrors, with the complex-balanced equilibrium as the Poisson parameter.
