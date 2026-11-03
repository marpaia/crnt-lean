# Fundamental CRNT formalization program

This program expands the library through complete, reusable mathematical results.
Its scope is fundamental reaction-network theory and the mathematical infrastructure
needed for its frontier results. Biological model fitting, simulator engineering, and
application-specific studies are outside this program. Small examples are useful as
nonvacuity checks of general theorems.

## What counts as progress

A theorem family must add mathematical content beyond existing definitions and wrappers.
It must use the library's network/kinetics objects, state its actual hypotheses, elaborate
with the pinned Lean/Mathlib toolchain, and have audited proof dependencies. A conditional
result is useful when its premise is an independently meaningful property; repackaging
the desired conclusion as an input does not close a mathematical gap. Defining an open
claim does not prove it. Passing the whole build does not remove the existing proof hole.

The start of this program is `99c61ccb9b2e07df18e9c92c9e92be9887d27c3e` on
`origin/wt/holes-20261010-a`. It has one reserved executable `sorry`, in
`CRNT/Dynamics/HighCodimensionSiphonFace.lean`. The user is working on it separately.
All expansion results must audit without `sorryAx` and must preserve that file.

## Mathematical coverage map

The paths below identify existing infrastructure, not a claim of completeness.

| Area | Existing infrastructure | Expansion questions |
| --- | --- | --- |
| Network and reaction graphs | `Basic`, `Graph`, `Combinatorics` | Canonical representations and invariance under transformations |
| Stoichiometry and conservation | `Stoich`, `LinearAlgebra`, `Geometry/ConservativeCompatibility` | Exact structural interfaces and constructive certificates |
| Deficiency and fluxes | `Deficiency/ExactSequence`, `Deficiency/CycleExactSequence`, `Flux` | Quantify the interaction of incidence and stoichiometric coupling |
| Decomposition and composition | `Decomposition`, `Compose` | Exact relation spaces; criteria transporting balances and ranks |
| Equilibrium geometry | `Equilibria`, `Theorems/DeficiencyZero` | Broader parameterizations and converse structural certificates |
| Realization and translation | `Translation`, staged `Scaffold/CRNTExpansion/Realization*` | Completeness of source coefficients; constructive realization criteria |
| Reduction and intermediates | `Reduction/SingleIntermediateElimination`, `Reduction/IntermediateSchurComplement` | General network elimination and invariant transfer |
| Injectivity and multistationarity | `Multistationarity`, `LinearAlgebra/OrientedMatroid` | Higher-deficiency and sign-algorithm correctness bridges |
| Robustness and adaptation | `Design` | Unconditional structural conclusions with faithful hypotheses |
| Persistence and global dynamics | `Dynamics`, `Geometry`, `Topology` | Additional independently proved classes, excluding the reserved hole |
| Oscillation and bifurcation | `Oscillation`, `Dynamics/Hopf*` | Discharge analytic premises and connect actual reaction-network realizations |
| Generalized and general kinetics | `Kinetics` | Identify exactly which structural conclusions survive kinetic generalization |
| Stochastic networks | `Stochastic` | Reversible energy identities, communicating classes, process-level foundations |
| Algebraic reaction geometry | `Algebra`, staged positive-torus/elimination modules | Constructive algebraic certificates tied to positive concentrations |
| Decision procedures | `Decision` | Soundness and completeness against structural predicates, beyond flags alone |

## First wave and dependency order

Three independent slices start the expansion:

1. Stochastic detailed balance → finite closed-region Dirichlet identity → nonnegative energy.
2. Source-monomial coefficients → finite certificates/constructive realization theory.
3. Reaction partitions → incidence and stoichiometric relation spaces → exact deficiency balance.

The exact implemented endpoints, proof audits, builds, and follow-on dependencies are tracked
in `tasks/todo.md`. Each verified batch is committed and pushed to `wt/holes-20261010-a`
after refreshing concurrent remote changes. The user's original dirty worktree is preserved.

Broader work follows these proved slices: energy-zero communicating-class structure, complete
polynomial realization certificates, and interblock relation maps. The sequence remains
adaptive: inspect what is actually missing before scheduling a theorem.

## Verification boundary

The initial isolated source passed `lake build CRNT CRNTFrontier Scaffold test` (4,723 jobs)
with Lean 4.34.0 and Mathlib v4.34.0. This is baseline evidence, not evidence for later additions.
The baseline import, hollow-definition, exclusion, undefined-name, and generator-sync checks
also passed. The one reserved hole still appears in the frontier axiom audits.

Each new batch needs fresh focused checks and a subsequent integration build. The orchestrator
reviews mathematical hypotheses and audits each principal theorem, rather than inferring
axiom cleanliness from its import list or accepting an agent's report alone.

## First proved batch

`CRNT/Realization/SourceCoefficientCompleteness.lean` closes the converse of the existing
source-coefficient certificate. Equality on the positive orthant determines all coefficients;
checking the finite union of source sets is therefore necessary and sufficient for dynamical
equivalence. Failure has a finite source/species coefficient witness.

`CRNT/Decomposition/RelationSpace.lean` constructs the incidence and stoichiometric block-relation
spaces. Their dimensions are the two rank losses under block composition, and

`total block deficiency - network deficiency = incidence relation dimension - stoich relation dimension`.

The signed formula works without either independence assumption. Exact additivity is equality
of the two relation dimensions; it does not require both dimensions to vanish.

Both modules passed focused elaboration. Fourteen principal theorem audits are pinned with
`#guard_msgs` in `test/AxiomAudit.lean`, each with only `propext`, `Classical.choice`, and `Quot.sound`.
The post-change public-core-closure integration
`lake build +CRNT test.AxiomAudit CRNTFrontier Scaffold` passed (4,660 jobs).
This deliberately excludes unfinished new modules outside the umbrella's closure; the full
`CRNT.+` library build is still required after the remaining drafts are complete. Import,
hollow-definition, exclusion, undefined-name, generated-file sync, and diff-whitespace checks
pass, and the reserved hole file matches the starting revision byte for byte.

## Stochastic detailed-balance energy

`CRNT/Stochastic/DirichletForm.lean` retains enabled reaction channels as individual edges.
Their paired-reaction reversal is an involution on any fire-closed region, so microscopic
detailed balance permits exact finite-sum reindexing. The result is the bilinear identity

`weighted generator pairing(f,g) = - Dirichlet form(f,g)`.

The product-Poisson weighted generator is symmetric. Positive reactionwise deterministic
detailed balance supplies the microscopic premise through the existing stochastic lift.
The quadratic form is nonnegative at nonnegative concentrations on any finite count region;
no reversibility or closure assumption is needed for that algebraic fact. Conserved linear
count observables likewise have zero energy on any finite region.

Eight additional axiom guards pin these results with only the standard foundational axioms.
After preserving the user's concurrent `cb62825` additions by clean rebase, the combined
public-closure integration `lake build +CRNT test CRNTFrontier Scaffold` passed first with
4,691 jobs and then with 4,692 jobs after this stochastic slice. The one reserved hole remains
unchanged. Communicating-class/kernel characterizations and the full-library build are subsequent
gates; this energy identity alone does not construct a continuous-time sample-path process.

## Deficiency assembly and the relation map

`CRNT/Decomposition/RelationMap.lean` applies the complex map separately to each reaction block
and proves that it commutes with summing block contributions. It therefore induces a linear
map from incidence interblock relations to stoichiometric interblock relations. Its kernel
consists precisely of relations whose components are local deficiency vectors.

The local block deficiency kernels define a product space and an independently specified
sum in the global complex space. This sum always lies in the network deficiency space. The
new theorem identifies the remaining obstruction exactly:

`global deficiency space = sum of block deficiency spaces`
iff the induced interblock relation map is surjective.

The proof lifts block stoichiometric vectors, then corrects their sum by local deficiency
vectors; the reverse direction uses incidence-relation lifts to build those corrections.
Surjectivity is derived from a structural equality, rather than asserted unconditionally.
Six further axiom guards are clean, giving 28 newly pinned principal results across the
expansion so far. Public-closure/test/frontier/scaffold integration passed (4,693 jobs), and
the reserved hole file is unchanged.
