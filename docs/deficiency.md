# Equilibria and deficiency

`SingletonSource` describes homogeneous linear mass-action systems with singleton sources and unrestricted products. It is distinct from published partitioned MESSI systems. Toric parametrizations here are exponential log-kernel parametrizations; the general rational-coordinate bridge remains incomplete. Primitive-matrix Perron–Frobenius coverage is partial, separate from the column-stochastic positive-kernel theorem below.

This document describes the equilibrium theory of the `CRNT` library: what an equilibrium is, when
it exists and is unique, and the structural quantity, the *deficiency*, that controls these
questions. It is one of the per-area documents hung off [`architecture.md`](architecture.md); the
dynamical companions of these results (the relative-entropy Lyapunov function, LaSalle's invariance
principle, and local asymptotic stability) live in [`dynamics.md`](dynamics.md), and this document
keeps its focus on the *existence* and *uniqueness* of equilibria.

The deficiency program, due to **Horn, Jackson, and Feinberg**, is the observation that a single
nonnegative integer `δ = n − ℓ − s`, read off purely from the reaction graph (number of complexes
`n`, linkage classes `ℓ`, stoichiometric rank `s`), governs the equilibrium behavior of a
mass-action network *independently of the rate constants*. When `δ = 0` and the network is weakly
reversible, every positive choice of rate constants gives exactly one equilibrium per positive
compatibility class, and that equilibrium is complex-balanced (Feinberg, *Chemical reaction network structure and the
stability of complex isothermal reactors: the deficiency-zero and deficiency-one theorems*). When
`δ = 1`, under additional graph hypotheses, uniqueness persists. The deficiency-one and
advanced-deficiency algorithms that decide the capacity for multiple steady states from this same
structure sit at the end of this document: the apparatus and the exclusion direction are proven,
while the algorithm correctness equivalences are stated as named propositions but not proved.

## Complex balancing and the toric structure of equilibria

A **steady state** is a concentration where the vector field vanishes. The general predicate is
`IsSteadyState f x` (the field `f` is zero in every species coordinate at `x`), specialized to the
mass-action field by `Network.IsMassActionSteadyState`, whose unfolding
`Network.isMassActionSteadyState_iff` says the rate-weighted sum of reaction vectors is zero at
every species (`CRNT/Equilibria/SteadyState.lean`).

The dynamics are confined to **stoichiometric compatibility classes**. Two concentrations are
compatible (`Network.StoichCompatible x y`) when their difference lies in the stoichiometric
subspace; this is an equivalence relation, witnessed by `Network.StoichCompatible.refl`, `.symm`,
and `.trans`. The class of a point is `Network.compatibilityClass` (characterized by
`Network.mem_compatibilityClass`), and its intersection with the strictly positive orthant is the
`Network.positiveCompatibilityClass`, the arena in which the existence/uniqueness theorems are
stated (`CRNT/Equilibria/CompatibilityClass.lean`).

A concentration is **complex-balanced** when, at every complex, total mass-action inflow equals
total outflow: `Network.IsComplexBalanced`, built from `Network.inflow` and `Network.outflow`
(`CRNT/Equilibria/ComplexBalanced.lean`). Equivalently, in the Feinberg–Horn–Jackson factorization
`ẋ = Y(A_k(Ψ x))`, complex balancing is `A_k(Ψ x) = 0`.

Complex-balanced equilibria form a **log-linear ("toric") set**. Relative to a positive
complex-balanced reference `x*`, any positive concentration whose log-ratio `log(x/x*)` is
orthogonal to the stoichiometric subspace is itself complex-balanced. This is the existence
direction `complexBalanced_of_logRatio_orthogonal`, proved termwise from the monomial scaling laws
`log_complexMonomialVector` and `complexMonomialVector_eq_mul_exp`. From it follows
`exists_isComplexBalanced_in_positiveClass`: a complex-balanced equilibrium exists in every positive
compatibility class once *one* complex-balanced reference is known. The converse,
`logRatio_orthogonal_of_complexBalanced` (for weakly reversible networks), gives that two positive
complex-balanced concentrations differ by an orthogonal log-ratio, and these combine into
`isComplexBalanced_unique_in_positiveClass`: uniqueness of the complex-balanced equilibrium in a
positive class for a weakly reversible network (`CRNT/Theorems/DeficiencyZero/Toric.lean`).

## Perron–Frobenius and positive kernels

The existence of *one* complex-balanced equilibrium rests on a self-contained Perron–Frobenius
theorem for column-stochastic nonnegative matrices (`CRNT/LinearAlgebra/PerronFrobenius.lean`). It
comes in three pieces, all `sorry`-free:

- **Existence**: `exists_nonneg_mulVec_fixed_of_colStochastic`: a column-stochastic nonnegative
  matrix has a nonnegative, nonzero fixed vector (a Cesàro/Markov–Kakutani limit; the
  invariant-mass refinement is `exists_nonneg_mulVec_fixed_invariant`).
- **Positivity**: `pos_of_nonneg_mulVec_fixed_of_stronglyConnected`: if the support digraph is
  strongly connected, that fixed vector is strictly positive. The combinatorial engine is
  `pos_of_supportReaches_pos` (positivity spreads along the support-reachability relation
  `supportReaches`) and its block-localized form `pos_of_supportReaches_pos_on`.
- **Combined and unique**: `exists_pos_mulVec_fixed_of_stronglyConnected` gives a strictly positive
  fixed vector outright, and `mulVec_fixed_unique_of_stronglyConnected` shows it is unique up to a
  scalar.

Applied to a network, this yields **weak reversibility ⇒ a strictly positive kernel vector of the
kinetic matrix** `A_k`. The kinetic matrix is rescaled to a column-stochastic matrix `P = 1 + d⁻¹
A_k` (`smat`, with `d = dscale = 1 + ∑_r κ_r`); `P` is block-diagonal across linkage classes
(`smat_blockdiag`), each of which weak reversibility makes strongly connected
(`reaches_supportReaches` lifts a reaction path to a support path; strong-connectedness is assembled
from it and weak reversibility at the call site). The main result is
`weaklyReversible_exists_positive_kernelVector` (`CRNT/Theorems/DeficiencyZero/PositiveKernel.lean`).

A companion is the **substochastic** Perron–Frobenius input
(`CRNT/LinearAlgebra/Substochastic.lean`). A nonnegative matrix with column sums at most one and at
least one strict deficit ("leak") has *no* nonzero fixed vector when every index can reach a leak
along the support digraph. The closed-set form `mulVec_fixed_eq_zero_of_substochastic_of_closed`
quantifies over sets closed under reverse support edges; the reachability corollary is
`mulVec_fixed_eq_zero_of_substochastic`. Both are `sorry`-free, proved by a single mass-balance
pinch. This is the trivial-kernel fact behind drainage arguments, where a transient block of a
Markov-type generator loses all its mass to absorbing classes.

## Birch's theorem (existence + uniqueness per positive class)

**Birch's theorem** is the toric global-injectivity result underlying deficiency zero: relative to a
positive reference `x*`, every positive stoichiometric compatibility class `c + S` contains exactly
one positive point whose log-ratio to `x*` is orthogonal to the subspace `S`. The library proves it
in full as `birch` (`CRNT/Theorems/DeficiencyZero/BirchExistence.lean`), assembled from two halves:

- **Uniqueness**: `birch_uniqueness` (`CRNT/Theorems/DeficiencyZero/Birch.lean`): at most one such
  point. This is the elementary order-theoretic half, using only the strict monotonicity of
  `Real.log` together with the orthogonality, no convexity. It is the source of uniqueness of
  complex-balanced equilibria in the deficiency-zero theorem.
- **Existence**: `birch_existence`: at least one such point. Obtained by minimizing the strictly
  convex **dual objective** `birchDual x* c w = ∑ᵢ (x*ᵢ exp wᵢ − cᵢ wᵢ)` over `Sᗮ`. The supporting
  lemmas are the per-coordinate Fenchel–Young inequality `birchDualTerm_ge` and its sum
  `birchDual_ge`, coercivity `birchDual_coercive`, continuity `continuous_birchDual`, the resulting
  minimizer `birchDual_exists_isMinOn`, and first-order optimality `birchDual_firstOrder`; the
  finite-dimensional duality `(Sᗮ)ᗮ = S` then places the stationary point in `S`.

## Deficiency as a kernel dimension

The deficiency is defined over `ℤ` to avoid truncated subtraction: `Network.deficiencyInt = n − ℓ −
s`, with `DeficiencyZero` the proposition `deficiencyInt = 0` (`CRNT/Deficiency/Definition.lean`).
The natural-number form `Network.deficiency` and the structural identity `n = ℓ + s + δ`
(`numComplexes_eq_add`), together with nonnegativity `deficiencyInt_nonneg`, live in
`CRNT/Deficiency/DeficiencyOne.lean`.

The content of the definition is the **kernel-dimension characterization**
(`CRNT/Deficiency/KernelDimension.lean`). The stoichiometric map factors through complex space as
`stoichMap = complexMap ∘ incidenceMap` (`complexMap_comp_incidenceMap`), i.e. `Y ∘ ∂`. The
**deficiency subspace** is `deficiencySubspace = ker(Y) ⊓ Im(∂)`, and the central theorem
`deficiencyInt_eq_finrank_deficiencySubspace` proves

> `δ = dim(ker Y ∩ Im ∂)`.

It rests on the rank bridge `incidenceRank_eq_stoichRank_add` (`rank ∂ = s + dim(ker Y ∩ Im ∂)`) and
the incidence-rank identity `incidenceRank_eq` (`rank ∂ = n − ℓ`, itself from
`incidenceRank_add_numLinkageClasses` and `finrank_ker_incidenceTranspose`). The corollary
`deficiencyZero_iff_deficiencySubspace_eq_bot` says `δ = 0` exactly when the complex map is injective
on `Im ∂`.

The deficiency localizes over linkage classes (`CRNT/Deficiency/LinkageDeficiency.lean`). Each class
carries a `linkageDeficiency δ_θ = n_θ − 1 − s_θ`, which is nonnegative
(`linkageDeficiency_nonneg`) and sums to at most the global deficiency
(`sum_linkageDeficiency_le_deficiency`), since the stoichiometric subspace is the join of the
per-class subspaces (`stoichSubspace_eq_sup`). Tightness, equality `∑_θ δ_θ = δ`, is isolated as
`TightLinkageDeficiency` (`CRNT/Deficiency/HigherDeficiency.lean`), and under it the per-class
deficiency subspaces form an internal direct sum (`deficiencySubspace_directSum_of_tight`) with
exact dimensions `finrank_linkageDeficiencySubspace_eq_of_tight`. These hold for arbitrary `δ ≥ 0`;
they are the structural fragments on which any higher-deficiency analysis would build, and they are
complete theorems in their own right rather than a finished higher-deficiency theorem.

## The deficiency-zero theorem

The Feinberg–Horn–Jackson **deficiency-zero theorem** is `deficiencyZeroTheorem`
(`CRNT/Theorems/DeficiencyZero/Existence.lean`): for a weakly reversible network of deficiency zero,
every positive choice of rate constants and positive starting concentration determines a *unique*
complex-balanced equilibrium in the positive compatibility class of the start. The statement
interface is exposed separately as `SatisfiesDeficiencyZeroHypotheses` and
`DeficiencyZeroConclusion` (`CRNT/Theorems/DeficiencyZero/Statement.lean`).

The proof consumes the deficiency-zero condition exactly once. Weak reversibility supplies a
strictly positive kernel vector of `A_k` (`weaklyReversible_exists_positive_kernelVector`); to
realize it as a monomial vector `Ψ x` one needs the row space of the stoichiometric matrix to equal
that of the incidence matrix, which is precisely where `δ = 0` is used: `range_stoichTranspose_eq`,
built from the rank identities `finrank_range_stoichTranspose` and
`finrank_range_incidenceTranspose`. That produces `exists_isComplexBalanced` (a positive
complex-balanced concentration exists); the toric inclusion then spreads it across every class, and
Birch supplies uniqueness.

## Deficiency-one uniqueness (single and multi-class)

Feinberg's **deficiency-one theorem** proves at most one positive mass-action steady state per
compatibility class under its graph hypotheses. A separate existence theorem now proves that every
weakly reversible mass-action system has a positive steady state in each positive compatibility class,
for every positive rate vector. When the classical deficiency-one hypotheses also hold, the two results
combine to give exactly one steady state per class.

**Hypotheses.** `Network.DeficiencyOne` is `deficiencyInt = 1`
(`CRNT/Deficiency/DeficiencyOne.lean`). The graph conditions are `DeficiencyOneConditions` (each
class has `δ_θ ≤ 1` and `∑_θ δ_θ = δ`, `CRNT/Deficiency/LinkageDeficiency.lean`), extended with one
terminal strong linkage class per linkage class (`OneTerminalSLCPerLinkageClass`, via
`IsTerminalSLClass`) into the bundle `DeficiencyOneHypotheses`
(`CRNT/Deficiency/DeficiencyOneHypotheses.lean`). Under these conditions every linkage class has `δ_θ
∈ {0,1}` (`linkageDeficiency_eq_zero_or_one`), the number of deficient classes equals `δ`
(`card_deficientLinkageClasses`), and a deficiency-one network has *exactly one* deficient linkage
class (`existsUnique_deficient_of_deficiencyOne`), the rest being deficiency-zero
(`CRNT/Deficiency/DeficiencyOneStructure.lean`).

**Uniqueness (single class).** For a `δ = 1` network meeting the hypotheses,
`deficiencyOneUniqueness` (`CRNT/Theorems/DeficiencyOne/Uniqueness.lean`) proves at most one positive
mass-action steady state per compatibility class. The heart is Feinberg's sign-counting argument:
the log-monomial ratio of two positive steady states is constant on the deficient class
(`logMonomialRatio_eqOn_deficientClass`), via the proportionality lemma
`proportional_of_kineticImage_ne`.

**Uniqueness (multi-class).** `deficiencyOneUniqueness_multiClass`
(`CRNT/Theorems/DeficiencyOne/MultiClass.lean`) removes the `δ = 1` assumption, asking only for the
deficiency-one *conditions* (which permit several deficient classes). The argument is localized
class-by-class: each per-class deficiency subspace has dimension `δ_θ`
(`finrank_linkageDeficiencySubspace_eq`), a deficiency-one class carries a spanning generator
(`exists_spanning_linkageDeficiencySubspace_of_deficiency_one`), and a restricted-kinetic-image
form of the sign argument (`proportional_of_restrictedKineticImage`) drives the per-class log-ratio
constancy `logMonomialRatio_eqOn_deficientClass_of_conditions`. This generalizes the single-class
result.

**Reductions.** Two modules record that uniqueness reduces cleanly to a toric/log-ratio obligation:
`deficiencyOneUniqueness_of_deficientClassRatioConst` reduces it to deficient-class log-ratio
constancy `DeficientClassRatioConst` (`CRNT/Theorems/DeficiencyOne/ToricReduction.lean`), and
`deficiencyOneUniqueness_of_logRatio` reduces it to the toric characterization
`LogRatioCharacterization` (`CRNT/Theorems/DeficiencyOne/LogRatioUniqueness.lean`).

**Existence.** The statement interface remains in `CRNT/Theorems/DeficiencyOne/Statement.lean`.
`exists_positiveSteadyState_of_weaklyReversible` (`CRNT/Deficiency/WeaklyReversibleSteadyState.lean`)
now proves that every weakly reversible mass-action system has a positive steady state in every
positive compatibility class. Its Boros–Birch construction builds a positive class section, derives a
strict inward estimate for the projected kinetic field, and obtains a zero from the resulting
finite-dimensional existence argument.

`weaklyReversible_deficiencyOne_exists_positive_steadyState`
(`CRNT/Theorems/DeficiencyOne/WeaklyReversibleExistence.lean`) records the deficiency-one
structural split into additive linkage deficiencies and linkage-coupling deficiency. Under the classical
`DeficiencyOneHypotheses`, the existing uniqueness theorem then strengthens existence to uniqueness.

The local-degree machinery remains a separate route: `exists_zero_of_deficiencyOneDegreeCertificate`
turns a nonzero degree certificate into a steady state. The certificate constructor now uses an
already-established weakly reversible equilibrium as a constant homotopy; it does not independently
derive the equilibrium or the nonzero degree from network structure. Positive existence for
non-weakly-reversible networks satisfying only the classical deficiency-one hypotheses remains open.
The complex-balanced special case and the relative-entropy/LaSalle reductions remain available in
`Existence.lean` and `ExistenceDynamical.lean`.
## The deficiency-one and advanced-deficiency algorithms

A network **has the capacity for multiple steady states** when some positive rate constants admit
two distinct positive steady states in one compatibility class: `Network.HasMultistationarityCapacity`
(`CRNT/Multistationarity/Capacity.lean`). The deficiency-one and advanced-deficiency algorithms
(Feinberg, *The existence and uniqueness of steady states for a class of chemical reaction
networks*; Ji, *Uniqueness of equilibria for complex chemical reaction networks*, Ohio State
University, 2011) are parameter-independent linear feasibility tests designed to decide this
capacity from network structure alone. The library
formalizes the apparatus and proves the **exclusion direction**; the algorithm correctness
*equivalences* are recorded but not proved.

**The structural apparatus (proven, `sorry`-free).** A network is **consistent** when its
reaction vectors admit a strictly positive linear combination summing to zero (`Network.IsConsistent`,
`CRNT/Deficiency/Consistent.lean`), a Stiemke-alternative condition; weak reversibility implies it
(`isConsistent_of_weaklyReversible`, `CRNT/Deficiency/ConsistentWR.lean`). A `RegularNetwork`
(`CRNT/Deficiency/Regular.lean`) bundles consistency, one terminal strong linkage class per linkage
class, and the cut-pair condition (`CutPair`, `CRNT/Deficiency/CutPair.lean`). A **confluence
vector** is a member of the incidence image (`Network.IsConfluenceVector`, `CRNT/Deficiency/Confluence.lean`);
its defining structural property, the cut-sum **antisymmetry** `cutSum_antisymm`, is a complete
theorem. **Shelves** partition reactions into upper/middle/lower tiers (`Shelf`, `ShelfPartition`,
`ShelfPartition.imposes`, `CRNT/Deficiency/Shelf.lean`); a **signature** is a nonzero vector
sign-compatible with the stoichiometric subspace that solves a shelf system (`SignCompatibleWithStoich`,
`DOASystem`, `IsSignature`, `CRNT/Deficiency/Signature.lean`). **Colinearity classes** group
reactions whose reaction vectors are scalar multiples (`ColinearVec`, `ColinearReactions`,
`colinearityClasses`, `CRNT/Deficiency/Colinearity.lean`, `ColinearityClasses.lean`), the discrete
index of the advanced-deficiency extension. Each of these carries proven supporting lemmas and incurs
no `sorry`.

**The exclusion direction (proven).** `not_hasMultistationarityCapacity_of_injective`
(`CRNT/Multistationarity/Capacity.lean`) is the Craciun–Feinberg exclusion direction: if the
mass-action kinetics is injective for every rate constant, the network has no capacity for multiple
steady states. This is the half on which the injectivity and species–reaction-graph criteria rest.
The forward direction's **entry step** is also proven: from two distinct positive compatible
concentrations the log-ratio `μ = ln y − ln x` is nonzero and sign-compatible with the
stoichiometric subspace (`signCompatible_logRatio`,
`exists_signCompatible_of_hasMultistationarityCapacity`, `CRNT/Deficiency/DOAForward.lean`). Bridging
from such a `μ` to a full shelf signature is Feinberg's structural analysis (Feinberg, *The
existence and uniqueness of steady states for a class of chemical reaction networks*) and is not
carried out.

**The correctness equivalences (stated, not proved).** The Deficiency One Algorithm affirms capacity
when some nonzero confluence vector and shelf partition admit a nonzero sign-compatible `μ` meeting
the placement constraints (`DOAAffirmsCapacity`); its correctness, for a regular deficiency-one
network, is `DeficiencyOneAlgorithmStatement`: `HasMultistationarityCapacity ↔ DOAAffirmsCapacity`
(`CRNT/Deficiency/DeficiencyOneAlgorithm.lean`). The Advanced Deficiency Algorithm adds a per-class
unknown `Mᵢ` and shelves reactions against it (`ADAData`, `ADAData.imposes`, `ADAAffirmsCapacity`),
with correctness `AdvancedDeficiencyAlgorithmStatement` for a regular network
(`CRNT/Deficiency/AdvancedDeficiencyAlgorithm.lean`). Both correctness statements are written as
`def` propositions — named targets, **proved in neither direction**. They are Feinberg's deficiency-one theorem (Feinberg, *The existence and uniqueness
of steady states for a class of chemical reaction networks*) and its higher-deficiency successor.
What is proven of each is **non-vacuity**: affirming capacity exhibits a nonzero stoichiometric vector
(`stoichSubspace_ne_bot_of_doaAffirmsCapacity`, `stoichSubspace_ne_bot_of_adaAffirmsCapacity`). The
advanced-deficiency module captures the per-class `Mᵢ` variables and shelf constraints but omits the
within-class sign comparisons and coplanar-set `Mᵢ`-orderings of Ji's advanced-deficiency system,
which only enlarges the set of runs considered.

**Semantic flux certificates.** The separate modules
`CRNT/Multistationarity/DeficiencyOneAlgorithm.lean` and
`CRNT/Multistationarity/AdvancedDeficiencyAlgorithm.lean` prove
`HasMultistationarityCapacity ↔ DOAFeasible` and
`HasMultistationarityCapacity ↔ ADAFeasible`. These quantify over real fluxes and log-ratios
with exponential balance equations. They are existence characterizations; their names do not
identify them with the finite shelf searches above. The shelf bridge in
`CRNT/Deficiency/DeficiencyOneAlgorithmCorrectness.lean` requires additional shelf-flux and
placement data, and `ShelfFluxConstruction.lean` gives conditional assembly results and a
concrete instance. General algorithm correctness and the numerical procedure remain incomplete.

## Modules

Equilibria:

- `CRNT/Equilibria/SteadyState.lean`: steady-state predicate and its mass-action specialization.
- `CRNT/Equilibria/CompatibilityClass.lean`: stoichiometric compatibility (an equivalence relation)
  and the positive compatibility class.
- `CRNT/Equilibria/ComplexBalanced.lean`: inflow, outflow, and the complex-balanced predicate.
- `CRNT/Equilibria/BrouwerSteadyState.lean`: a mass-action steady state on a nonempty compact convex
  set whose inward displacement maps it into itself.

Linear algebra:

- `CRNT/LinearAlgebra/PerronFrobenius.lean`: Perron–Frobenius for column-stochastic matrices
  (existence, positivity, uniqueness of a positive fixed vector).
- `CRNT/LinearAlgebra/Substochastic.lean`: column-substochastic matrices with no trapped mass have
  trivial fixed space.

Deficiency-zero theorem:

- `CRNT/Theorems/DeficiencyZero/PositiveKernel.lean`: weak reversibility ⇒ positive kernel of `A_k`.
- `CRNT/Theorems/DeficiencyZero/Birch.lean`, `BirchExistence.lean`: Birch's theorem (existence +
  uniqueness per positive class) via the convex dual objective.
- `CRNT/Theorems/DeficiencyZero/Toric.lean`: the toric structure of complex-balanced equilibria.
- `CRNT/Theorems/DeficiencyZero/Existence.lean`, `Statement.lean`: `deficiencyZeroTheorem` and its
  statement interface.

Deficiency as kernel dimension:

- `CRNT/Deficiency/Definition.lean`: `deficiencyInt = n − ℓ − s` and `DeficiencyZero`.
- `CRNT/Deficiency/KernelDimension.lean`: `δ = dim(ker Y ∩ Im ∂)`.
- `CRNT/Deficiency/DeficiencyOne.lean`: natural-number deficiency, `n = ℓ + s + δ`, `DeficiencyOne`.
- `CRNT/Deficiency/LinkageDeficiency.lean`: per-class deficiency and `DeficiencyOneConditions`.
- `CRNT/Deficiency/HigherDeficiency.lean`: tightness and the per-class direct-sum decomposition.
- `CRNT/Deficiency/DeficiencyOneStructure.lean`: the unique deficient linkage class.
- `CRNT/Deficiency/DeficiencyOneHypotheses.lean`: Feinberg's three-condition hypothesis bundle.

Deficiency-one theorem:

- `CRNT/Theorems/DeficiencyOne/Statement.lean`: uniqueness/existence statement interface.
- `CRNT/Theorems/DeficiencyOne/Uniqueness.lean`: single-class uniqueness.
- `CRNT/Theorems/DeficiencyOne/MultiClass.lean`: multi-class uniqueness.
- `CRNT/Theorems/DeficiencyOne/ToricReduction.lean`, `LogRatioUniqueness.lean`: reductions to the
  toric/log-ratio obligation.
- `CRNT/Deficiency/WeaklyReversibleSteadyState.lean` and
  `CRNT/Theorems/DeficiencyOne/WeaklyReversibleExistence.lean`: positive existence for weakly
  reversible systems, including the deficiency-one linkage split.
- `CRNT/Theorems/DeficiencyOne/DegreeExistence.lean`: local-degree certificates and the implication
  from nonzero degree to a steady state.
- `CRNT/Theorems/DeficiencyOne/Existence.lean`, `ExistenceDynamical.lean`: complex-balanced and
  relative-entropy/LaSalle reductions.

Deficiency-one and advanced-deficiency algorithms:

- `CRNT/Multistationarity/Capacity.lean`: the capacity for multiple steady states and the
  injective-exclusion direction.
- `CRNT/Deficiency/Consistent.lean`, `ConsistentWR.lean`: network consistency via Stiemke, and weak
  reversibility ⇒ consistency.
- `CRNT/Deficiency/CutPair.lean`, `Regular.lean`: cut pairs and the regular-network bundle.
- `CRNT/Deficiency/Confluence.lean`: confluence vectors and cut-sum antisymmetry.
- `CRNT/Deficiency/Shelf.lean`, `Signature.lean`: shelves and signatures.
- `CRNT/Deficiency/Colinearity.lean`, `ColinearityClasses.lean`: colinearity classes.
- `CRNT/Deficiency/DOAForward.lean`: the proven entry step of the forward direction.
- `CRNT/Deficiency/DeficiencyOneAlgorithm.lean`, `AdvancedDeficiencyAlgorithm.lean`: the verdicts,
  the correctness equivalences stated as `def` propositions (not proved), and their non-vacuity.

## Related documents

- [`architecture.md`](architecture.md): the mathematical architecture and how this area fits.
- [`dynamics.md`](dynamics.md): the relative-entropy Lyapunov function, LaSalle's invariance
  principle, and local asymptotic stability that accompany the deficiency-zero equilibrium.
- [`foundations.md`](foundations.md): networks, the reaction graph, stoichiometry, weak
  reversibility, and linkage classes that this theory is read off.
- [`design.md`](design.md): the representation choices behind these definitions.
