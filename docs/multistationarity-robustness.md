# Multistationarity, robustness, and composition

Concordance now has a boundary-inclusive injectivity equivalence for compatible nonnegative pairs with one positive member; the older `Injective` remains the positive-class restriction. Degree arguments use finite regular-zero signed counts; rate homotopies require intermediate regularity and the general dissipative total-degree theorem is missing. Parity is conditional on the total degree. DOA/ADA semantic real-feasibility equivalences do not implement finite published algorithms. Interconnection uniqueness assumes combined-field injectivity; general-plant adaptation retains certificate/integrability hypotheses.

This document describes the top structural layer of the `CRNT` library: the questions that go
beyond existence and uniqueness of equilibria. When can a network admit *several* positive steady
states in one stoichiometric compatibility class? When is a species' concentration *robust* to the
rate constants and the initial condition? What happens when a network is *opened* to material
exchange with its surroundings, and how do the structural invariants behave when two networks are
*composed* over a shared species pool? It sits on the foundations, kinetics, deficiency, and
equilibria layers below it; see the [architecture](architecture.md).

The named criteria are Feinberg's reaction-network theory and its descendants: injectivity and the
species–reaction graph (Gheorghe Craciun and Martin Feinberg, *Multiple Equilibria in Complex
Chemical Reaction Networks: I/II*); the degree-free global-univalence theorem behind the Jacobian
form of the criterion (David Gale and Hukukane Nikaido, *The Jacobian Matrix and Global Univalence
of Mappings*); concordance (Guy Shinar and Martin Feinberg, *Concordant Chemical Reaction
Networks*); the toric / sign-condition reduction of multistationarity (Stefan Müller and Georg
Regensburger, and Mercedes Pérez-Millán, Alicia Dickenstein, Anne Shiu, and Carsten Conradi,
*Chemical Reaction Systems with Toric Steady States*); absolute concentration robustness (Guy Shinar
and Martin Feinberg, *Structural Sources of Robustness in Biochemical Reaction Networks*); and
antithetic integral feedback (Corentin Briat, Ankit Gupta, and Mustafa Khammash, *Antithetic
Integral Feedback Ensures Robust Perfect Adaptation in Noisy Biomolecular Networks*).

The boundaries between what is proved unconditionally, what is reduced to a named
hypothesis, and what needs mathematics absent from this development are stated as plain facts at the
end of each section.

## Injectivity and monostationarity

A network is **monostationary** when each positive stoichiometric compatibility class contains at
most one positive steady state. The structural property that guarantees this is *injectivity* of the
vector field.

- **`Kinetics.InjectiveOnClass K x₀`** (`CRNT/Multistationarity/Injectivity.lean`) holds when the
  induced vector field `K.vectorField` is injective (`Set.InjOn`) on the positive compatibility class
  of `x₀`; **`Kinetics.Injective K`** is injectivity on every positive class. This is the
  Craciun–Feinberg notion of injectivity, stated over an arbitrary `Kinetics`.

- **`Kinetics.InjectiveOnClass.subsingleton_steadyState`** is the easy, fully proved direction: two
  steady states lying in one positive class are both zeros of the field, so injectivity on that class
  forces them equal — at most one positive steady state per class.
  **`Kinetics.Injective.subsingleton_steadyState`** is the same for a globally injective kinetics,
  and **`massAction_subsingleton_steadyState_of_injective`** is the mass-action corollary.

- **`Network.HasMultistationarityCapacity N`** (`CRNT/Multistationarity/Capacity.lean`) is the
  network's *capacity for multiple steady states*: some choice of positive rate constants admits two
  distinct positive steady states in one positive compatibility class. This is what the
  deficiency-one, advanced-deficiency, and species–reaction-graph algorithms are designed to decide.
  **`not_hasMultistationarityCapacity_of_injective`** is the Craciun–Feinberg *exclusion* direction:
  if the mass-action kinetics is injective for every choice of rate constants, the network has no
  such capacity. The converse — *affirming* the capacity by exhibiting the witnessing rate constants
  and steady states — is a separate development.

**Coverage.** The injectivity ⇒ monostationarity implication and the exclusion of multistationarity
capacity are complete. The criteria that *establish* injectivity are the subject of the next three
sections.

## The P-matrix Gale–Nikaido univalence theorem

The linear-algebraic engine behind the Jacobian form of the injectivity criterion is the P-matrix,
and the analytic payoff is the Gale–Nikaido global-univalence theorem, proved here **degree-free**
on the n-dimensional Sperner and Brouwer theorems formalized elsewhere in the library — with no
appeal to topological degree.

- **`Matrix.IsPMatrix M`** (`CRNT/Multistationarity/PMatrix.lean`) is a square matrix over a
  `LinearOrderedField` all of whose principal minors are positive. The central reindexing fact is
  **`Matrix.IsPMatrix.submatrix_det_pos`**: for any *injective* index map `f`, `(M.submatrix f f).det`
  is positive. From it follow **`det_pos`**, **`det_ne_zero`**, **`isUnit_det`** (nonsingularity),
  **`submatrix_isPMatrix`** (closure under principal submatrices), and **`diag_pos`** (positive
  diagonal). Over `ℝ`, **`Matrix.PosDef.isPMatrix`** shows a symmetric positive-definite matrix is a
  P-matrix.

- The P-matrix calculus that the inductive proof rests on:
  **`Matrix.IsPMatrix.schurAt`** / **`Matrix.IsPMatrix.schurLast`**
  (`CRNT/Multistationarity/PMatrixSchur.lean`) — the Schur complement of a P-matrix is a P-matrix,
  the dimension-drop step, with the determinant identities `det_schurAt` / `det_schurLast`; and
  **`Matrix.IsPMatrix.signatureConj`** (`CRNT/Multistationarity/PMatrixSignature.lean`) — a P-matrix
  is invariant under `±1` diagonal (signature) conjugation, the normalization that reduces an
  arbitrary collision to the ordered case.

- The Gale–Nikaido development follows the original proof
  (`CRNT/Multistationarity/PMatrixUnivalence.lean`): **`IsPMatrix.eq_zero_of_mulVec_nonpos`**
  (Theorem 1 — a P-matrix sends no nonnegative vector to a nonpositive one except `0`),
  **`IsPMatrix.exists_pos_le_mulVec`** (Corollary 1 — a uniform `λ > 0` with a component of `A *ᵥ v`
  at least `λ‖v‖` for every nonnegative `v`), and **`IsPMatrix.exists_nonneg_mulVec_pos`**
  (Corollary 2, through Stiemke's alternative).

- The analytic theorems are in `CRNT/Multistationarity/GaleNikaido.lean`,
  `GaleNikaidoBox.lean`, and `GaleNikaidoUniv.lean`. **`isLocalHomeomorph_of_pmatrix_fderiv`** is the
  local-homeomorphism step. **`pmatrix_order_eq`** is the order-interval monotonicity theorem
  (Gale–Nikaido Theorem 3), proved by induction on dimension via point isolation
  (`pmatrix_isolated`), a strict-descent direction (`pmatrix_descent`), the reduced-map Jacobian as a
  Schur complement (`jacobianMatrix_reduced_eq_schurLast`, `reduced_isPMatrix`), and a
  boundary-coordinate face reduction. The main result is
  **`injOn_of_pmatrix_fderiv`** (Gale–Nikaido Theorem 4):

  ```lean
  theorem injOn_of_pmatrix_fderiv {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
      {F' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ}
      (hF : ∀ z ∈ Set.Icc lo hi, HasFDerivAt F (F' z) z)
      (hP : ∀ z ∈ Set.Icc lo hi, (jacobianMatrix (F' z)).IsPMatrix) :
      Set.InjOn F (Set.Icc lo hi)
  ```

  a `C¹` map whose Jacobian is a P-matrix at every point of a box is injective on that box.

**Coverage.** The P-matrix calculus and the box Gale–Nikaido univalence theorem are complete. The theorem is stated on a box (an order interval), the form
that binds to a compatibility class in the next section.

## From the reduced Jacobian to class injectivity

A coordinate reduction binds the box Gale–Nikaido theorem to chemical-reaction-network
class-injectivity.

- **`Network.stoichChart`** and **`Network.affineChart`** (`CRNT/Multistationarity/StoichChart.lean`)
  build a linear chart of the stoichiometric subspace from a fixed basis `stoichBasis`, with the
  projection `stoichProj` as a left inverse. **`affineChart_chartCoord`** recovers a class point from
  its chart coordinate; **`chartCoord_affineChart`** is the other inverse.

- **`Network.reducedField`** (`CRNT/Multistationarity/ReducedJacobian.lean`) is the mass-action vector
  field on the affine slice through `x₀`, read in the `Fin (stoichRank N)` chart coordinates;
  **`Network.reducedJacobian`** is its `s × s` Jacobian matrix, the compression
  `stoichProj ∘ J ∘ stoichChart` of the full mass-action Jacobian.
  **`massActionInjectiveOnClass_of_jacobian_pmatrix`** is the bridge: if the reduced Jacobian is a
  P-matrix on a box enclosing the chart coordinates of the positive compatibility class, then
  `injOn_of_pmatrix_fderiv` makes the reduced field injective on the box, and pulling back through
  the injective affine chart makes the mass-action field injective on the class.
  **`subsingleton_steadyState_of_jacobian_pmatrix`** reads off the monostationarity conclusion: at
  most one positive steady state in that class.

- **`injOn_of_hasFDerivAt_dotProduct_pos`** (`CRNT/Multistationarity/JacobianInjectivity.lean`) is the
  separate *positive-definite* fragment: a `C¹` map on a convex set whose Jacobian quadratic form
  `v ↦ ∑ i, vᵢ (J(x) v)ᵢ` is strictly positive for `v ≠ 0` is injective there, by the one-dimensional
  mean value theorem along each segment. **`massActionInjectiveOnClass_of_jacobian_pos`** specializes
  it to a positive-definite mass-action Jacobian on a compatibility class.

**Coverage.** Both routes to mass-action class-injectivity — the box P-matrix reduced Jacobian and
the positive-definite Jacobian — are complete, including the reduction to a full-dimensional chart.
What each consumes is a hypothesis on the Jacobian *at every point of a box*; turning a structural
network property into that pointwise P-matrix condition is the species–reaction-graph criterion,
which is not yet closed (next section).

## The species–reaction graph and concordance

Two structural routes aim to establish injectivity from the network alone. The species–reaction
graph reads cycle data off a combinatorial graph; concordance forbids a sign-counting configuration
on the reaction vectors directly.

### The species–reaction graph

- **`Network.srGraph N`** (`CRNT/Multistationarity/SRGraph.lean`) is the undirected bipartite
  **species–reaction graph** on the vertex type `S ⊕ N.R`: an edge joins a species `s` to a reaction
  `r` exactly when `s` occurs in `r` (**`Network.OccursIn`**: nonzero stoichiometry as a source or
  target). The adjacency is decidable; **`srGraph_adj_iff`** characterizes it, and
  **`srGraph_isBipartiteWith`** / **`srGraph_isBipartite`** prove bipartiteness with the species and
  reactions as the two parts.

- The bipartite alternation underlying the cycle bookkeeping is in
  `CRNT/Multistationarity/SRGraphCriterion.lean`. **`srGraph_getVert_isLeft`** shows every walk
  strictly alternates sides; from it, **`srGraph_even_length_of_closed`** and
  **`srGraph_even_length_of_isCycle`** prove every closed walk and every cycle has even length,
  **`srGraph_not_isCycle_of_odd_length`** is the contrapositive (no odd cycle), and
  **`srGraph_four_le_egirth`** gives edge-girth at least four (triangle-free).

- The length/parity half of the permutation-cycle ↔ SR-graph-cycle dictionary is in
  `CRNT/Multistationarity/SRGraphCycleDict.lean`. **`srCycleWalk`** turns a permutation orbit (with a
  reaction chosen at each step) into a closed SR-graph walk, and **`srCycleWalk_length_eq_two_mul`** /
  **`srCycle_length_eq_two_mul`** establish that a permutation cycle of length `k` corresponds to an
  SR-graph cycle of length `2k`, in both directions.

- The signed refinement is in `CRNT/Multistationarity/SignedSRGraph.lean`. **`Network.signedEdge`** is
  the `SignType` sign of the reaction vector's coordinate at a species–reaction incidence;
  **`signedEdge_ne_zero_iff_netChange`** relates a nonzero sign to a net stoichiometric change.
  **`Network.walkSign`** is the product of incidence signs along a walk, with the algebra
  `walkSign_cons`, `walkSign_append` (multiplicativity under concatenation), and `walkSign_copy`.
  **`Network.negEdgeCount`** counts negative incidences, and
  **`walkSign_eq_negOnePow_negEdgeCount`** shows the walk sign is `(-1)` to that count when no step is
  a zero incidence. **`Network.CycleSignNegative`** names the sign-`-1` cycle predicate.

### The determinant cycle-cover expansion

- **`det_eq_sum_cycleCover_terms`** (`CRNT/LinearAlgebra/DetCycleCover.lean`) regroups the Leibniz
  expansion of a determinant by cycle type, so each block is one cycle-cover shape (a multiset of
  cycle lengths). **`coverCoeff_eq_sign`** identifies the cycle-type product with the permutation
  sign, **`cycle_term_sign`** gives a single cycle's sign in closed form, and
  **`cycleCover_factor_prod`** factors a permutation's diagonal product over its disjoint cycles. The
  module is stated over an abstract matrix over a commutative ring, with no Jacobian factorization
  assumed; it is the algebraic substrate of the determinant-via-cycle-covers reading of the Jacobian
  determinant in the Craciun–Feinberg criterion.

**Coverage.** What is proved is the complete combinatorial and algebraic substrate: SR-graph
bipartiteness and cycle parity, the length half of the permutation-cycle ↔ SR-cycle dictionary, the
signed walk-sign algebra, and the determinant-by-cycle-cover-shape expansion. The full
Craciun–Feinberg SR-graph criterion — that the signed-cycle structure implies the mass-action
Jacobian (or reduced Jacobian) is a P-matrix, hence injectivity through `injOn_of_pmatrix_fderiv` —
is not closed: it requires relating the signed-cycle data to the sign of the Jacobian determinant by
specializing the abstract cycle-cover expansion to the factored mass-action Jacobian, the sign half
of the dictionary. That specialization is not done here, so the substrate is present but the
criterion itself is open.

### Concordance

- A network is **concordant** (`CRNT/Multistationarity/Concordance.lean`, following Shinar and
  Feinberg, *Concordant Chemical Reaction Networks*) when no **`Network.ConcordanceWitness`** exists:
  a rate displacement `α` in the kernel of the stoichiometric map together with a nonzero
  stoichiometric vector `σ` meeting two sign-implication clauses on the reactions' source supports.
  **`Network.Concordant N`** asserts the absence of any such witness — a purely structural,
  rate-constant-free property.

- **`Kinetics.WeaklyMonotonic K`** is Feinberg's monotonicity hypothesis on the rate law (a rate's
  change has its sign reflected by a change of the composition on the source support), and
  **`massActionKinetics_weaklyMonotonic`** confirms mass action satisfies it. The payoff is
  **`Concordant.injective_of_weaklyMonotonic`**: a weakly monotonic kinetics on a concordant network
  is injective in the Craciun–Feinberg sense, hence has at most one positive steady state per class
  (**`Concordant.subsingleton_steadyState`**), kinetics-independently, with
  **`Concordant.massAction_subsingleton_steadyState`** the mass-action specialization for every
  choice of rate constants.

**Coverage.** The concordance ⇒ injectivity ⇒ monostationarity chain is proved unconditionally, for
every weakly monotonic kinetics, with no rate-constant assumption. The converse direction — that a
discordant network admits a noninjective weakly monotonic kinetics — is not developed.

## Toric steady states

For networks whose steady-state equations are *binomial*, the positive steady states form a toric
(log-linear) set, and multistationarity reduces to a sign condition on two subspaces.

- **`ToricSteadyStates S T xstar c`** (`CRNT/Multistationarity/Toric.lean`) is the positive `x` that
  is stoichiometrically compatible (`x − c ∈ S`) and whose log-ratio `log(x/xstar)` is orthogonal to
  the kinetic-order subspace `T` (lies in `orthSum T`). This log-linear set is taken here *as the
  definition* of the steady-state set. **`mem_toricSteadyStates`** unfolds membership.

- **`toric_nonempty_self`** gives the monomial parametrization in the single-subspace case `T = S`:
  every positive class contains a toric steady state, the complex-balanced equilibrium produced by
  Birch existence.

- **`SignIncompatible S T`** is the failure of the Müller sign condition (a nonzero `u ∈ S` sharing
  its coordinatewise sign pattern with some `v ∈ T`), and
  **`signCompatible_iff_not_signIncompatible`** states that `SignCompatible` is exactly its absence
  (`σ(S) ∩ σ(T) = {0}`).

- **`toric_subsingleton_of_signCompatible`** is the proved uniqueness half of the Müller–Regensburger
  reduction: sign-compatibility of `S` with the kinetic orthogonal complement `orthSum T` forces the
  toric steady-state set in each positive class to be a subsingleton — multistationarity ruled out.
  **`toric_subsingleton_self`** and **`toric_unique_self`** are the mass-action corollaries at
  `T = S`, recovering classical complex-balanced existence and uniqueness for every rate constant.

**Coverage.** Binomiality of the steady-state equations is taken as the *definition* of the toric
set; deriving it from the network's reaction structure (the toric-ideal step) needs binomial-ideal
machinery not in this development. The uniqueness half of the sign-condition reduction is proved; the
converse — constructing two distinct toric steady states when sign-compatibility fails — is the
degree-theoretic half and needs topological degree, which is absent here.

## Absolute concentration robustness

A network has **absolute concentration robustness** in a species when that species' steady-state
concentration is the same value at every positive mass-action steady state, for every choice of rate
constants.

- **`Network.HasACR N s`** (`CRNT/Design/ACR.lean`) is that predicate: a single value `v` with
  `x s = v` at every positive steady state, for all rate constants.

- **`Network.ShinarFeinbergHypotheses N s`** is the Shinar–Feinberg structural hypothesis bundle: a
  deficiency-one network with two non-terminal complexes `c`, `d` lying in distinct linkage classes
  and differing in exactly the single species `s`.

- The algebraic lever is fully proved: **`monomial_cross_of_differ`** is the cross-multiplied monomial
  identity for complexes agreeing away from `s`; **`pin_xs_of_lt`** and **`pin_of_pinned_ratio`** show
  a *pinned* monomial ratio of `c` and `d` forces the species-`s` concentrations to coincide.
  **`ShinarFeinbergHypotheses.PinnedRatio`** names the deficiency-one content (the pinned monomial
  ratio across all positive steady states) and **`HasACR.of_pinnedRatio`** reduces `HasACR s` to that
  input plus a witness steady state.

- The deficiency-one machinery bearing on the pinned ratio is in `CRNT/Design/ACRUnconditional.lean`.
  **`logMonomialRatio_eqOn_linkageClass`** is the keystone, and it is *proved*: the log-monomial ratio
  `Φ` is constant on *every* linkage class of a network satisfying the deficiency-one hypotheses
  (`DeficiencyOneHypotheses`).
  **`monomialRatio_pinned_of_sameClass`** is its exponentiated *same-class* form. The remaining
  cross-class content — equality of the two a-priori-independent per-class constants for complexes in
  *distinct* classes — is isolated as **`ShinarFeinbergHypotheses.CrossClassRatioPinned`**, with
  **`HasACR.of_crossClassRatioGap`** deriving ACR from it.

- The cross-class equality is analyzed through the toric condition in `CRNT/Design/ACRCrossClass.lean`.
  **`Network.ToricRelated x y`** names orthogonality of the log-ratio vector to the stoichiometric
  subspace; **`logMonomialRatio_const_along_reaction_of_toric`** and **`logMonomialRatio_eqOn_linked`**
  prove `Φ` is constant along reactions and across whole linkage classes under that condition.
  **`crossClassRatio_eq_iff_robust`** pins the residual obligation exactly: for two complexes
  differing only at `s`, the cross-class equality `Φ(c) = Φ(d)` holds **iff** `x s = y s` — the
  difference collapses to the single coordinate `(c_s − d_s)·(log x_s − log y_s)`.
  **`HasACR.of_speciesRobust`** then re-derives full `HasACR s` from a precisely-named
  species-robustness hypothesis fed through that equivalence.

**Coverage.** The complete chain is proved: the pinning lever, the same-class constancy of `Φ`, the
toric per-reaction and per-class constancy, and the reduction of the cross-class equality to the
statement `x s = y s`. The single missing step is the cross-class equality itself — forcing
robustness from non-terminality and the deficiency-one cut structure. It is consumed as the named
input `CrossClassRatioPinned` (equivalently the robustness hypothesis of `HasACR.of_speciesRobust`)
rather than discharged, because it rests on the deficiency-one characterization of the positive
steady-state set, which is not yet available here. The Shinar–Feinberg theorem is therefore present
as a reduction to one bridging equality, not as an unconditional statement.

## Antithetic integral feedback and perfect adaptation

The antithetic integral feedback motif realizes *perfect adaptation*: a sensed output pinned to a
setpoint independent of every other rate constant.

- `CRNT/Design/Adaptation.lean` models the Briat–Gupta–Khammash motif as a concrete `Network` over
  three species (controller species `Z1`, `Z2` and output `X`) with reactions `ref : 0 → Z1`,
  `sense : X → X + Z2`, and `seq : Z1 + Z2 → 0`. The plant-coupling actuation reaction is omitted so
  the motif is a drop-in, plant-agnostic controller.

- **`setpoint`** is the integral-feedback property, fully proved: at any mass-action steady state the
  two controller production rates balance, `κ.sense · x_X = κ.ref`. **`setpoint_value`** solves it to
  **`x_X = κ.ref / κ.sense`** — the output is pinned by the reference and sensing rates alone,
  independent of the sequestration rate and of any plant dynamics.

**Coverage.** The setpoint and its value are proved unconditionally for this concrete network. This is
the steady-state (algebraic) statement of perfect adaptation; the dynamical claim that trajectories
*converge* to the setpoint is not part of this module.

## Open (CFSTR) extensions

A closed network conserves total amounts along its stoichiometry; a continuous-flow stirred-tank
reactor exchanges material with its surroundings. Adjoining a synthesis `0 → s` and a degradation
`s → 0` for every species gives the **fully open extension**.

- **`Network.fullyOpen N`** (`CRNT/Open/Augmentation.lean`) is that extension, with reactions indexed
  by `N.R ⊕ S ⊕ S` (original, inflows, outflows). **`reactionVector_inflow`** and
  **`reactionVector_outflow`** give the inflow/outflow vectors as `±e_s`. From the standard basis
  being present: **`stoichSubspace_fullyOpen_eq_top`** (the stoichiometric subspace is the whole
  species space), **`stoichRank_fullyOpen`** (rank `card S`), and
  **`orthSum_stoichSubspace_fullyOpen_eq_bot`** (the conservation laws vanish: no nonzero conserved
  quantity).

- The deficiency and linkage consequences are in `CRNT/Open/Deficiency.lean`.
  **`deficiencyInt_fullyOpen`** reads the deficiency as `δ⁺ = n⁺ − ℓ⁺ − card S`, and
  **`numComplexes_fullyOpen_eq_add`** is the structural identity `n⁺ = ℓ⁺ + card S + δ⁺`. The
  inflow/outflow pseudo-reactions tie the zero complex to every singleton:
  **`linked_zero_singletonComplex_fullyOpen`** and **`linked_singletonComplex_fullyOpen`** collapse
  the zero complex and all singletons into one linkage class.

- The boundary behavior is in `CRNT/Open/Boundary.lean`. **`Network.IsBoundary`** and
  **`Network.faceOf`** describe the orthant faces; **`Network.BoundarySteadyState`** is a nonnegative
  equilibrium on a face. **`massActionVectorField_fullyOpen_apply`** splits the open field into the
  original part, the constant inflow, and the linear outflow. The main results:
  **`fullyOpen_steadyState_positive`**, every nonnegative steady state is strictly interior (a
  held-at-zero species sees nonnegative original contributions, a vanishing outflow, and a strictly
  positive inflow, so the field cannot vanish); **`not_boundarySteadyState_fullyOpen`**, the open
  extension has *no* boundary steady states; **`faceOf_fullyOpen_steadyState_eq_empty`**, the only face
  carrying an equilibrium is the interior face `∅`.

- The partial-open reactor is in `CRNT/Open/PartialOpen.lean`. **`Network.partialOpen N O`** opens only
  a chosen subset `O ⊆ S` of species, indexing reactions by `N.R ⊕ {s // s ∈ O} ⊕ {s // s ∈ O}`. With
  influx confined to `O`, the no-vanishing argument holds only on the open species:
  **`partialOpen_steadyState_pos_on_open`** (every open species is strictly positive at a nonnegative
  steady state), **`faceOf_partialOpen_steadyState_disjoint`** (the face carrying an equilibrium is
  disjoint from `O`, so any boundary equilibrium touches only closed species), and
  **`not_boundarySteadyState_on_open`** (no boundary steady state vanishes on an open species).

**Coverage.** The structural facts (stoichiometric subspace, rank, vanishing conservation laws,
deficiency and linkage bookkeeping) and the no-boundary-equilibria result are complete for the fully
open extension, and the partial-open reactor sharpens them to strict positivity on the chosen open
species.

## Network composition

Two networks over a common species type compose by taking the disjoint union of their reaction
channels.

- **`Network.interconnect N₁ N₂`** (`CRNT/Compose/Interconnect.lean`) has reactions indexed by
  `N₁.R ⊕ N₂.R`, acting on the shared concentration vector;
  `interconnect_reactionVector_inl` / `interconnect_reactionVector_inr` identify the component reaction
  vectors. **`interconnect_reactionVectors`** shows the reaction-vector set is the union of the
  components'.

- **`stoichSubspace_interconnect`** is the proved composition law: the interconnection's stoichiometric
  subspace is the *join* `N₁.stoichSubspace ⊔ N₂.stoichSubspace` of the components'.
  **`stoichSubspace_le_interconnect_left`** and **`stoichSubspace_le_interconnect_right`** record that
  each component's subspace embeds into the interconnection's.

- **`Kinetics.sum K₁ K₂`** (`CRNT/Compose/InterconnectKinetics.lean`) is the induced kinetics on the
  interconnection, dispatching by the sum index; **`sum_vectorField`** proves the combined field is the
  sum of the component fields `K₁.vectorField x + K₂.vectorField x`.

- Monostationarity of the composite is in `CRNT/Compose/InterconnectMonostationary.lean`. Each
  component's positive compatibility class embeds into the interconnection's
  (`positiveCompatibilityClass_subset_interconnect_left` / `_right`), and
  **`Kinetics.InjectiveOnClass.sum_subsingleton_steadyState`** lifts the monostationarity payoff: if
  the combined field is injective on a positive class of the interconnection, that class carries at
  most one steady state.

- Stoichiometric independence is in `CRNT/Compose/StoichIndependent.lean`.
  **`Network.StoichIndependent N₁ N₂`** is disjointness of the two stoichiometric subspaces.
  **`vectorField_separate_of_stoichIndependent`** is the decoupling fact: when the combined fields
  agree at two points and the subspaces are disjoint, the component fields agree separately. From it,
  **`InjectiveOnClass.interconnect_of_stoichIndependent_left`** / **`_right`** show that injectivity of
  *either* component (on the interconnection's class) lifts to injectivity of the combined kinetics.

- Siphons of the composite are in `CRNT/Compose/InterconnectSiphon.lean`:
  **`interconnect_isSiphon_iff`** proves a species set is a siphon of the interconnection iff it is a
  siphon of *both* components, the siphon condition over `N₁.R ⊕ N₂.R` splitting as a conjunction.

**Coverage.** Composition is treated at the level of the stoichiometric subspace (the exact join law),
the combined kinetics (the sum-of-fields law), monostationarity (injectivity lifts to the composite),
stoichiometric-independence decoupling, and siphons (the conjunction law). Stoichiometric
independence is a structural sufficient condition for field decoupling, not the Del Vecchio–Ninfa–
Sontag insulation condition: the retroactivity / loading effect a downstream module imposes on an
upstream one through the shared interface is not modeled here.
