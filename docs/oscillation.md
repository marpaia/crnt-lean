# Oscillation and recurrent dynamics

The explicit Lotka periodic-orbit and non-oscillation results are separate from conditional planar classification. `MinimalSetClassification` takes a `PoincareBendixsonKernelBundle`, trapping data, and equilibrium exclusion. Its nonregular-minimal-set predicate does not define a standard notion of chaos. `MassActionHopfTaylorData` constructs periodic curves of a cubic normal form, without proving they solve the original mass-action ODE.

`CRNT/Oscillation` is the deterministic oscillation layer of `crnt-lean`.  Its contract is
proof-carrying and deliberately incomplete in the logical sense: for an arbitrary finite CRN the
library may prove oscillation, prove non-oscillation, or return `unknown`.  Failure of a sufficient
test is never interpreted as evidence for the opposite conclusion.

The central scientific question is not whether one numerical trajectory looks wavy.  It is which
recurrent behaviours are **forced, permitted, or excluded by the reaction-network mechanism**.

## Semantics

`Basic.lean` separates the main propositions:

- `PeriodicTrajectory field`: an exact nonconstant periodic solution of an autonomous field;
- `N.HasPositivePeriodicOrbit κ`: a fixed positive mass-action parameterization has a positive
  periodic orbit;
- `N.OscillatoryCapacity`: some positive rate vector admits a positive periodic orbit;
- `N.NeverPositivePeriodic`: no positive rate vector admits one;
- `GlobalLimitCycleOnClass`: a positive periodic orbit attracts every positive exact solution in its
  stoichiometric class (apart from the usual phase ambiguity along the cycle).

Existence, linear stability, nondegeneracy, and global attraction are kept as different statements.

## Proof-carrying certificates and automatic exclusion

`Certificate.lean` provides fixed-parameter and structural certificates with three outcomes:
`excluded`, `capable`, and `unknown`.  Certificates compose without a priority convention; an
all-parameter exclusion and an existential positive witness are definitionally contradictory.

The analyzer contract is version 16.  Its automatic all-parameter exclusion flag is justified by
either of two independent theorems:

1. weakly reversible + deficiency zero; or
2. stoichiometric rank at most one.

The second route covers networks such as an irreversible `A -> B`, which are not weakly reversible.
The rank-one proof is geometric: project to the one-dimensional stoichiometric chart, apply Rolle to
a hypothetical period, lift the zero reduced velocity to a full equilibrium, then use autonomous ODE
uniqueness to collapse the entire orbit.  The geometry is factored from the kinetics and is stated
for admissible locally Lipschitz kinetics where appropriate.

`Exclusion.lean` also supplies reusable contradictions from strict Lyapunov observables, strictly
monotone observables, point convergence, and an exact solution hitting an equilibrium.

## Return maps, Floquet data, and stability

The return-map stack now contains:

- exact Poincare return-map fixed point -> `PeriodicTrajectory`;
- compact scalar return interval -> fixed point -> periodic trajectory;
- parameterized return-map implicit-function persistence;
- scalar `P'(x*) != 1` -> invertible displacement derivative;
- nonlinear contraction of a scalar return map from `|P'(x*)| < 1`;
- geometric convergence of successive section hits;
- a continuous-time section-hit interpolation interface for orbital attraction;
- monodromy matrices, Floquet multipliers, nondegenerate positive cycles, and linearly stable
  positive cycles.

`PlanarFloquetAttraction.lean` composes the scalar return-map and interpolation layers.  The remaining
universal local theorem is `ScalarFloquetAttractionConstructionTarget`: construct those scalar
section/interpolation data from a linearly stable Floquet orbit.  Once supplied,
`floquetOrbitalStability_of_scalarAttraction` closes the older broad Floquet-stability target.

A separate absorption theorem for a concrete stoichiometric class upgrades local orbital attraction
to `GlobalLimitCycleOnClass`; global attraction is never inferred from local Floquet stability alone.

## Stoichiometric coordinates and the rank-two planar route

`CoordinateDynamics.lean` defines the reduced mass-action field in stoichiometric coordinates and
proves that exact reduced solutions lift to full mass-action solutions.  `RankTwoPlanar.lean`
transports a rank-two compatibility class to an explicit `Fin 2` planar field and lifts a resulting
planar periodic trajectory back to a positive CRN orbit.

### Poincare--Bendixson reduction

The repository now proves the surrounding infrastructure rather than exposing one giant
"Poincare--Bendixson" placeholder:

1. trapped complete flow -> nonempty compact invariant equilibrium-free omega-limit set;
2. descent to a minimal compact invariant omega subset;
3. every point of that minimal set is recurrent, with arbitrarily late returns to every
   neighbourhood;
4. every such point has a canonical transversal with normal `field q`;
5. the transversal has an explicit scalar coordinate
   `q + u * rotate90(field q)` and an inverse coordinate;
6. autonomous uniqueness gives the no-crossing/time-shift lemmas used in planar ordering;
7. a continuous compact scalar self-return interval has a fixed point;
8. that fixed point closes to an exact nonconstant periodic trajectory and, in the strengthened
   data, remains inside the omega-limit set.

The irreducible planar geometry is therefore
`Planar.CanonicalReturnOrderingTarget`: recurrent minimal-set point + local flow box + planar
ordering -> a compact canonical self-return interval.  `PlanarReturnOrdering.lean` proves that this
single theorem implies the full flow-aware omega-limit Poincare--Bendixson classification.

## Bendixson--Dulac reduction

The exclusion route has likewise been decomposed:

- a locally Lipschitz periodic orbit admits a least-positive-period simple representative;
- the Dulac-scaled vector field has zero normal flux pointwise along its own periodic orbit;
- `periodBoundaryFlux` is an actual interval line integral and is proved to be exactly zero;
- strict one-sign divergence on a nonempty connected bounded interior forces a nonzero area
  integral;
- the remaining geometry is separated into:
  - `PeriodicJordanInteriorTarget`;
  - `JordanInteriorContainmentTarget` for an orbit lying in a convex Dulac region;
  - `JordanDulacRegularityTarget`;
  - `PeriodicGreenDivergenceTarget`.

`GreenJordanFoundations.lean`, `PlanarEndToEnd.lean`, and `CompatibilityAdapters.lean` compose those
four universal planar facts into the historical Green/Jordan certificates, Dulac area data, and the
public `BendixsonDulacTarget`.

## Vassena 2025 full-matrix mass-action criteria

The CRN-specific realization side is implemented explicitly.

For a positive steady reaction flux `v`, define the flux core `B(v)`.  The library proves

`J(x) = B(v) * diag(1/x)`

at the corresponding positive steady state and, conversely, realizes every positive right-diagonal
scaling `B(v) D` as a genuine positive mass-action steady-state Jacobian.

The continuation uses the globally positive exponential path

`d_i(mu) = d0_i * exp(mu * log(d1_i / d0_i))`.

The corresponding steady-state branch, positive rate constants, vector field, and Jacobian path are
constructed explicitly.  `VassenaAnalyticity.lean` proves the continuation is analytic by composing
analytic exponentials, reciprocals, source monomials, reaction rates, and finite reaction sums.
If `B(v)` is invertible, the Jacobian is nonsingular along the whole continuation.

`VassenaEndToEnd.lean` now closes the old broad
`VassenaFluxCriteriaRealizationTarget` from exactly three independent theorem kernels:

- `Matrix.NotPMinusZeroImpliesUnstableScalingTarget`;
- `Matrix.FisherFullerStabilizingScalingTarget`;
- `FiedlerAnalyticGlobalHopfTarget`.

Criterion I and Criterion II no longer require a separate CRN realization assumption.
The conserved-system **principal-block** extension remains an independent perturbation/reduction
kernel (`VassenaPrincipalFluxCriteriaRealizationTarget`) because a principal submatrix of the full
Jacobian is not automatically the reduced stoichiometric Jacobian.

For concrete dimensions three and four, `VassenaFiniteDimHopf.lean` also connects the diagonal path
to the existing Routh--Hurwitz/Hopf boundary gates as a local fallback.

## 2026 oscillatory cores and parameter-rich kinetics

The structural route is CRN-native.

`StructuralCore.lean` and `ChildSelectionSearch.lean` provide theorem-facing and finite-search-friendly
child selections.  The indexed representation stores injective species/reaction maps, has an exact
child-selection matrix, supports restriction to principal blocks, carries finite size bounds, and
converts definitionally from the theorem-facing representation.

`DHopf.lean` introduces explicit strong D-Hopf witnesses.  Exact class-I cores reduce to Vassena
Criterion I.  Exact class-II cores are resolved through either the Fisher--Fuller branch or the
stable-codimension-one strong-D-Hopf-block theorem.

`ChildSelectionReactivity.lean` implements the epsilon-reactivity embedding:

- at `epsilon = 0`, the selected symbolic-Jacobian block is exactly the child-selection matrix;
- for positive epsilon, all allowed reactant derivatives regain positive support.

`ReactivityScaling.lean` proves the exact structural identity

`G(R D) = G(R) D`

and lifts a selected diagonal scaling to the full CRN.  `DHopfOpenness.lean` reduces robustness of
the selected D-Hopf block under the epsilon embedding to the generic finite-matrix spectral
openness theorem `Matrix.StrongDHopfPerturbationTarget`.

`OscillatoryCoreEndToEnd.lean` resolves class-I and both class-II branches into one
`ResolvedIndexedOscillatoryCoreCertificate`, then feeds that proof object into the parameter-rich
smooth kinetic continuation.  The original theorem-facing and indexed search-facing oscillatory-core
realization targets are now derived automatically from the finite matrix kernels plus
`ParameterRichDHopfContinuationTarget`.

## Recipe 0 and parameter-rich kinetics

`RecipeZeroContinuation.lean` no longer jumps directly from a recipe certificate to a periodic
orbit.  It constructs the smooth kinetic continuation first.  The remaining nonlinear theorem is
`RecipeZeroSmoothContinuationTarget`; from it the historical
`ParameterRichRecipeZeroRealizationTarget` is derived.

## Network enlargement / Banaji-style inheritance

Several inheritance levels are deliberately distinguished.

**Exact inheritance.** Adding arbitrary zero-vector/self-reaction channels preserves the vector
field and Jacobian exactly.  Ordinary oscillation, Floquet nondegeneracy, and linear stability
therefore transfer exactly.

**One stoichiometrically dependent added reaction.** The library proves:

- the stoichiometric subspace and rank are unchanged;
- the exact vector-field and Jacobian perturbations;
- a smooth real epsilon-family through the original network at epsilon zero;
- scalar parameterized return-map IFT persistence -> a nearby periodic branch;
- any positive-epsilon positive branch -> oscillatory capacity of the enlarged CRN.

`BanajiEndToEnd.lean` reduces ordinary-capacity inheritance to the concrete
`ScalarDependentReactionPersistenceConstructionTarget`.  Retaining Floquet nondegeneracy or linear
stability is stronger and is kept as the independent
`NondegenerateDependentReactionPersistenceTarget` / `StableDependentReactionPersistenceTarget`.

## Compatibility layer

`CompatibilityAdapters.lean` ensures refinement did not fragment the public API.  In particular:

- canonical return ordering implies the older minimal, omega-recurrent, and recurrent-section
  construction targets;
- the refined Jordan/regularity/Green decomposition constructs the historical Dulac area data and
  Green/Jordan proof certificates;
- the modern end-to-end Vassena/core/recipe/Floquet adapters discharge the older broad realization
  interfaces wherever the implication is valid.

## Exact remaining theorem kernels

`OscillationKernelBundle.lean` is an audit manifest, not an axiom.  Route-specific bundles expose the
smallest currently independent mathematical theorems.

### Universal planar analysis

- `Planar.CanonicalReturnOrderingTarget`;
- `Planar.PeriodicJordanInteriorTarget`;
- `Planar.JordanInteriorContainmentTarget`;
- `Planar.JordanDulacRegularityTarget`;
- `Planar.PeriodicGreenDivergenceTarget`.

### Full-matrix Vassena

- `Matrix.NotPMinusZeroImpliesUnstableScalingTarget`;
- `Matrix.FisherFullerStabilizingScalingTarget`;
- `FiedlerAnalyticGlobalHopfTarget`.

### Parameter-rich oscillatory cores

- `Matrix.StrongDHopfPerturbationTarget`;
- the two Vassena finite-matrix scaling kernels above;
- `Matrix.StableCodimOneClassIIImpliesStrongDHopfBlockTarget`;
- `Network.ParameterRichDHopfContinuationTarget`.

### Other nonlinear kernels

- `Network.ScalarFloquetAttractionConstructionTarget`;
- `Network.ScalarDependentReactionPersistenceConstructionTarget`;
- `Network.RecipeZeroSmoothContinuationTarget`.

### Independent stronger/conserved extensions

- `Network.VassenaPrincipalFluxCriteriaRealizationTarget`;
- `Network.NondegenerateDependentReactionPersistenceTarget`;
- `Network.StableDependentReactionPersistenceTarget`.

Everything else in the deterministic framework is intended to be composition around these exact
interfaces.  `CompleteOscillationKernelBundle` records the complete dependency manifest in the type
system without asserting any of the kernels.

## Scope

This layer concerns deterministic autonomous ODE periodic orbits.  A stochastic NFsim/CTMC trace can
show quasi-cycles, coherence, or spectral peaks without possessing a deterministic periodic orbit;
those require separate stochastic semantics and are intentionally not identified with the results
above.
