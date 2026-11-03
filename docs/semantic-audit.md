# PR #1: correspondence between Lean statements and advertised mathematics

**Recommendation: do not merge this as an accurate account of the advertised mathematical coverage yet.** The implementation contains substantial, axiom-clean mathematics, including a nonvacuous trajectory formulation of global attraction. It also contains changed definitions, conditional bridges described as completed theorems, and several false or unsupported headline claims. Passing the build and axiom audit does not resolve those discrepancies.

This audit examines PR [#1](https://github.com/marpaia/crnt-lean/pull/1) at `e449a7339a9916ecd9260e0cd09c669c1eef05ad`, incorporated in the local repair branch `codex/pr1-merge-readiness` at `537ed72071a5957ada8e4edfbc606bd9d950910a`. The earlier four engineering-repair commits do not fix the mathematical correspondence findings below. The primary checkout's existing README/CITATION edits were not part of this snapshot and have not been changed.

## Coverage and meaning of the result

The [complete ledger](semantic-audit/field-map.md) covers all **99** field-map rows: **44 Match, 30 Qualified, 20 Partial, 5 Mismatch**. These categories describe correspondence, not percentages of mathematical difficulty completed. A qualified result can be entirely correct and useful; a partial row can accurately describe an honest frontier. Conversely, an inaccurate README claim can concern a row which the field map already labels partial.

The [machine-readable ledger](semantic-audit/field-map.json) retains every named declaration, the source reference, and the assessment. The [elaborated-type export](semantic-audit/declaration-types.txt) covers all **1,382 distinct declarations** named by those rows, including inferred section parameters. All names resolve. Every axiom report is a subset of `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx` or a native-computation axiom. The [validation record](semantic-audit/validation.json) records the examined commit and successful Lean exit status.

Manual review followed the principal theorem interfaces into their defining predicates, inspected the hypotheses responsible for each claimed implication, and compared the most consequential discrepancies with primary papers. The export is exhaustive for named field-map declarations; it is not an assertion that every subsidiary lemma or every sentence of every cited paper received an independent mathematical reproof. In particular, a matching statement plus an axiom-clean Lean proof establishes formal correspondence under the checked definitions; it does not establish publication priority or reproduce a paper line by line.

The additional [Lean correspondence checks](semantic-audit/CorrespondenceChecks.lean) prove concrete counterexamples and a positive existence-and-convergence certificate. They are audit evidence, not replacements for the library's public APIs.

The live PR still points at the examined `e449a733` head. Its description retains measurements from an older head (419 commits and 795 changed files); the current PR metadata reports 519 commits and 1,034 changed files. Its assertion that deterministic strongly endotactic permanence remains a named claim is also stale relative to the genuine-trajectory tempered-rate theorem now present. Its description of `KurtzScaling` as a law of large numbers needs the generator/process distinction in R14. The arXiv identifier `1203.6560` resolves to *Concordant Chemical Reaction Networks and the Species-Reaction Graph*, rather than the different title quoted in the PR body. These are provenance/documentation defects, not additional Lean proof failures.

## Findings requiring correction before claiming the advertised coverage

### R1 — MESSI is a different class, not the published definition

**High priority.** [MESSI.lean](../CRNT/Equilibria/MESSI.lean#L166) defines `N.MESSI` as every reaction having a singleton source. There is no species partition, intermediate/core distinction, or restriction on the product complex.

The published MESSI definition uses a partition with restrictions on complexes and reactions, includes enzyme-substrate mechanisms with bimolecular sources, and implies conservativity. The library's predicate excludes such bimolecular sources and admits `A → 2A`. The audit proves both `Autocatalysis.repo_MESSI` and `Autocatalysis.not_conservative`, so this is a demonstrable difference in meaning. See Definition 3 and the conservation results in [Pérez Millán–Dickenstein](https://arxiv.org/pdf/1612.08763).

The linear-field, convexity, and linear-invariant theorems are useful for the class actually defined. Rename that predicate and its theorem family to describe singleton-source linear systems, or implement the published partitioned definition and establish the bridge. Mark the MESSI component of S17 incomplete. The README already uses the more accurate phrase “linear-elimination class,” but the API and field map still advertise MESSI. An exponential log-kernel parametrization is also not, by itself, a constructed rational parametrization: integer-lattice/exponent conversion remains a distinct task.

### R2 — the unconditional fully open parity claim is false

**High priority.** The README says the number of isolated positive steady states of a fully open network is odd. Full openness alone does not imply this. Consider positive rates

```text
∅ → A       rate 1
A → ∅       rate 3
2A → 3A     rate 2
```

The actual mass-action equation is `a' = 1 - 3a + 2a²`, with exactly two positive steady states, `1/2` and `1`. Both are simple: the scalar derivatives there are `-1` and `1`. The field is positive at large concentrations, so a dissipativity assumption would exclude this example.

`Parity.positive_steady_state_count_eq_two` checks the count against the repository's own `fullyOpen`, rate constants, vector field, positivity, and steady-state definitions. This refutes the advertised unconditional assertion, including a simple-root multiplicity interpretation.

The [actual parity theorem](../CRNT/Multistationarity/ParityOfSteadyStates.lean#L532) correctly assumes finite zeros, nondegeneracy, and a prescribed total degree. S19 is already labelled partial. Preserve the conditional theorem and correct the README. The total-degree hypothesis cannot simply be deleted. The degree argument in [Conradi–Feliu–Mincheva–Wiuf](https://pmc.ncbi.nlm.nih.gov/articles/PMC5626113/) explicitly invokes dissipativity and boundary conditions.

The field map's bare attribution “Šošić–Sibuya 2006” was not identifiable from the supplied information in targeted searches. It needs a title and stable source identifier; this audit does not treat it as verified provenance.

### R3 — `hirsch_generic_convergence` is a LaSalle/uniqueness result under a different monotonicity notion

**High priority.** [HirschConvergence.lean](../CRNT/Dynamics/HirschConvergence.lean#L26) defines metric strong monotonicity by

```text
<f(x)-f(y), x-y> >= c * |x-y|²,  c > 0,
```

and also requires the vector field itself to preserve coordinate order. This is a coercively increasing map condition. It is not the strong order-preservation property of the ODE's flow used in Hirsch theory. The convergence theorem additionally assumes a compact absorbing tail, a Lyapunov function, and a critical-set condition forcing the omega-limit set into the equilibria. Its proof then uses uniqueness of the equilibrium.

The source theorem concerns almost-everywhere convergence for cooperative irreducible dynamics with precompact forward orbits; it does not supply the above coercivity and strict Lyapunov certificate as hypotheses. See [Hirsch's original paper](https://escholarship.org/content/qt67z7c17v/qt67z7c17v.pdf).

The audit proves that `x'=-x` cannot satisfy the repository's positive-coercivity predicate. Its flow `exp(-t)x` is strongly order preserving and converges, so this is not a harmless restatement of the classical assumptions. The later [order-convexity wrapper](../CRNT/Dynamics/OmegaLimitOrderConvex.lean#L458) removes an unused premise but retains the same coercivity and LaSalle hypotheses. Rename these results and remove the generic-Hirsch claim, or formalize the actual flow-level generic theorem. The separate Kamke and strong-order propagation results remain useful.

### R4 — the mass-action Hopf verdict does not exhibit a mass-action periodic solution

**High priority.** The conclusion of [massAction_hasPeriodicOrbit_of_hopf](../CRNT/Dynamics/MassActionHopf.lean#L457) says a particular complex-valued `hopfLimitCycle` is periodic, nonconstant, and has a specified radius. It contains no `HasDerivAt` assertion for the original network and returns no `Network.PositivePeriodicOrbit` witness.

The construction gives the cubic truncated normal form a periodic orbit. Its Taylor-coefficient calibration to the network is meaningful, but a periodic orbit of a truncation is not automatically an orbit of the original field. Furthermore, the [MassActionHopf structure](../CRNT/Dynamics/MassActionHopf.lean#L394) does not even require `xst μ` to be a steady state, despite describing it as a branch of steady states; it does not encode the usual joint parameter/field regularity either.

The README's concrete-network periodic-branch claim therefore exceeds this theorem. Rename the verdict around the truncated normal form. A full network theorem must retain equilibrium-branch and regularity assumptions and construct the nonlinear return-map/normal-form transfer into the existing genuine periodic-orbit predicate. Spectral crossing tests alone establish a separate, weaker result; the cited [Errami et al. paper](https://logic.pdmi.ras.ru/~grigorev/pub/hopf_journal_final.pdf) concerns detecting Hopf bifurcation points, not identifying an arbitrary cubic truncation with the full ODE.

### R5 — Fenichel persistence is not derived from normal hyperbolicity; the all-time predicate is overstrong

**High priority.** [fenichel_persistence](../CRNT/Dynamics/FenichelPersistence.lean#L209) takes an already contractive abstract graph operator, a supplied flow/regraph operator, and a fixed-point compatibility hypothesis. It concludes invariance under the sampled flow `n ↦ Φ(nτ)` and a Banach fixed-point distance bound. It neither constructs this operator from a general normally hyperbolic slow-fast field nor proves the general continuously invariant perturbed-manifold theorem. The abstract structure permits `τ = 0`.

There is also a precise contract problem: [AllTimeRegraph](../CRNT/Dynamics/FenichelPersistence.lean#L171) requires the **same** operator `op` to regraph every section at **every** time, including zero. At zero the flow is the identity, so `σ(y) = (op σ)(y)` for every section and point. The audit proves `allTimeRegraph_forces_identity : F.op = id`. A useful all-time family must depend on time, or the hypothesis should concern preservation of the fixed manifold rather than every candidate section.

The constant-target contracting-fibre example is real mathematics, but it is an exactly solvable frozen-base example; it does not close the general slow-fast persistence step. The implicit-function graph `fast(y,h(y))=0` elsewhere is the critical manifold, not automatically the invariant graph for nonzero timescale separation. For example, `y'=ε, z'=y-z` has critical graph `z=y`, which is not invariant for `ε≠0`; the shifted invariant graph is `z=y-ε`.

The full theorem has a perturbation-to-invariant-manifold conclusion; compare the precise normal-hyperbolicity/persistence statement in [Berger–Bounemoura, Theorem 2.1](https://arxiv.org/pdf/1109.3280). Mark the full Fenichel component of D19 partial, distinguish critical and perturbed invariant graphs, and retain the valid tracking/implicit-function results with their actual hypotheses.

### R6 — the advertised stochastic strongly endotactic theorem is false

**High priority.** The README claims positive recurrence and non-explosion for strongly endotactic stochastic mass-action systems. The cited [Anderson–Cappelletti–Kim–Nguyen paper, Examples 3.1–3.2](https://arxiv.org/pdf/1808.05328) explicitly gives strongly endotactic stochastic systems that are transient and even explosive. Its positive theorem is for a subclass.

The [code](../CRNT/Stochastic/EndotacticPositiveRecurrence.lean#L45) uses extra `LinearLyapunovData` drift hypotheses, irreducibility for ergodicity, count-tier certificates, one-species restrictions, or particular examples. These results are useful. However, [EndotacticFull.lean](../CRNT/Stochastic/EndotacticFull.lean) still describes the false unrestricted assertion as a missing “full ACK theorem.” Correct both the README and that supposed frontier: the unrestricted claim is refuted mathematics, not a proof obligation awaiting completion. Keep deterministic permanence (D9) separate.

### R7 — general planar no-chaos results remain conditional and use bespoke vocabulary

**High priority for the unconditional headline.** [omegaSet_not_chaotic](../CRNT/Oscillation/NoChaos.lean#L405) takes a `PoincareBendixsonKernelBundle`. Its construction still depends on open planar-topological inputs; passing this bundle as an argument is not proving that it exists. The trapping region is additionally equilibrium-free.

`IsChaoticMinimalSet` is defined as “neither an equilibrium nor a periodic orbit.” No equivalence to positive topological entropy, Devaney chaos, or the named strange attractors is established. Excluding that bespoke predicate on minimal subsets is not a machine-checked general statement about all advertised notions of chaos or all omega-limit sets.

Correct the README to describe conditional planar classification. The genuine Lotka periodic-orbit theorem, non-oscillation criteria, and the network-specific trapping arguments do not depend on pretending these general topological inputs have been proved.

### R8 — degree means a finite signed count, with substantial regularity restrictions

**Medium priority.** [regularDegree](../CRNT/Multistationarity/RegularValueDegree.lean#L63) is the sum of determinant signs over a supplied finite preimage. At regular values this is the expected formula. The definition alone is not an extension of Brouwer degree to singular values: for `x ↦ x³` at zero its summand is zero, whereas the local topological degree is one.

The abstract [homotopy theorem](../CRNT/Multistationarity/DegreeHomotopyInvariant.lean#L162) assumes the local degree-count invariance data. The more concrete [rate-independence theorem](../CRNT/Multistationarity/DegreeExistence.lean#L577) derives invariance on a compact region but requires **every intermediate zero** to be regular. This excludes the bifurcation crossings for which general degree is especially useful. The total degree `(-1)^s` under dissipativity remains an input, except for special affine examples.

The cited `hasMultistationarityCapacity_of_signIndefinite` already assumes two positive zeros with opposite determinant signs; it is not a certificate from a single exceptional steady state. Later one-exceptional-sign results additionally assume the total degree. Document these exact dependencies and retain M9/M13 as partial. Neither local sign identification nor signed-count bookkeeping completes the total-degree theorem.

### R9 — the algebraic siphon claim currently has no algebraic prime-ideal bridge

**Medium priority.** [SiphonIdeal.lean](../CRNT/Algebra/SiphonIdeal.lean#L28) defines coordinate-prime “membership” by a species-support test, then defines backward closure by the siphon condition. The key equivalence is proved by `rfl`; `IsSiphonPrimeSupport` is this same condition plus nonemptiness.

This correctly reformulates siphons combinatorially. It does not construct a polynomial ideal, prove actual monomial ideal membership, or characterize supports of minimal primes of the reaction ideal. Those are the content of [Shiu–Sturmfels, Theorem 3.1](https://arxiv.org/pdf/0904.4529). Either add those bridges or mark A1 as the support-level fragment and stop advertising the full algebraic theorem as proved.

### R10 — the chemical-computation “semilinear characterization” changes the target class

**High priority.** [Semilinear](../CRNT/Computation/Semilinear.lean#L257) means finitely many pieces `c + Σ eᵢxᵢ` with **natural-number** coefficients, selected by Boolean combinations of linear inequalities. The classical discrete characterization concerns functions whose graphs are semilinear sets, including congruence structure and integer division; see [Chen–Doty–Soloveichik](https://pmc.ncbi.nlm.nih.gov/articles/PMC4221813/).

The audit proves both that `2X → Y` stably computes `floor(n/2)` under the repository's reachability semantics and that this function is **not** `Computation.Semilinear`. Therefore a classical “stably computable iff Semilinear” theorem using this predicate would be false. The current file proves closure properties and sufficient constructions, not that iff.

Rename the restricted class and narrow the README, or introduce the actual discrete semilinear-graph definition. Preserve the valid min/add/scale/max and stable-computation theorems. Arbitrary `init` functions are also part of the generic computation interface; a characterization theorem needs a prescribed input encoding, not an encoding that can already contain the answer.

### R11 — several broad “proved” descriptions contain only restricted results

**Medium priority.** Three examples require explicit scope labels:

- F6's equality characterization is the reverse numerical inequality, not a structural direct-sum criterion.
- S23's primitive nonnegative-matrix results establish nonnilpotence, some nonzero eigenvalues, and bounds for a supplied positive eigenvector/eigenvalue. They do not establish the full Perron root, algebraic simplicity, and spectral dominance. The row's notes admit this, despite its “proved” label.
- The mixed-volume development defines a determinant expression for lists of zonotope generators and proves algebraic additivity/homogeneity. The [volume polynomial](../CRNT/Algebra/VolumePolynomial.lean) is likewise constructed algebraically. A general identification with Lebesgue volume of the represented body is not supplied. BKK coverage is univariate/separated-variable or restricted support, not the general sparse multiplicity theorem. `mixedVolume_circuit` takes selected simplex generators, not all exponents of a general circuit; the repository itself gives a counterexample to confusing these quantities.

These components should be described as proved components, not completion of the entire named theory. Local C1 equilibrium branches (S24), not unrestricted global smooth dependence, are another case where the hypotheses belong in the headline.

### R12 — some bridges assume the implication suggested by their names

**Medium priority.** [InterconnectMonostationary](../CRNT/Compose/InterconnectMonostationary.lean#L50) assumes injectivity of the **combined** vector field. It does not show that interconnecting two class-injective components preserves injectivity. Indeed, individually injective fields `x'=x` and `x'=-x` cancel under reaction union, leaving every positive state stationary. M12 should describe monostationarity under combined injectivity.

Likewise [SteadyStateFaithfulOn](../CRNT/Translation/DeficiencyImprovement.lean#L176) assumes that every original steady state is generalized complex balanced in the translation. The cited equivalence then combines this supplied implication with a valid reverse bridge. It is not a general structural derivation of steady-state faithfulness. Keep the hypothesis visible and distinguish it from a published translation criterion.

### R13 — absorbing count states exclude enabled null reactions

**Medium priority for API semantics.** [IsAbsorbingCount](../CRNT/Stochastic/Absorbing.lean#L16) means every reaction is disabled. The core explicitly permits self-reactions. For `∅ → ∅`, every count remains unchanged, but this predicate is false everywhere because the reaction is always enabled. A Markov state with only null events is absorbing in the usual state-process sense.

The existing implication from this predicate to zero reaction-event rate is correct. Rename it as a deadlock/no-enabled-reaction condition, impose nontrivial reactions where equivalence is asserted, or define state absorption using zero rates to distinct states. Do not silently use reaction-event exit rates as state-leaving rates when self-loops are allowed.

### R14 — general adaptation and stochastic limits retain meaningful prerequisites

**Scope correction.** The general-plant antithetic development supplies stationary setpoint identities and transfers explicit Lyapunov/Foster certificates. It does not make every plant ergodic or construct the required certificate from arbitrary plant structure. Some obstruction theorems explicitly show why proposed quadratic certificates do not work. The concrete closed-loop examples and integrability-conditional stationary mean formulas remain meaningful.

The same distinction applies to stochastic limits: generator convergence is not a process-level law of large numbers; a fixed-time weak Gaussian limit is not a functional central limit theorem in a path space. The newer nonlinear multivariate CLTs are stronger than a mere generator skeleton and should receive credit for that, including the completed subprobability law near an equilibrium. A filtered time-indexed CRN path process and general Skorokhod LLN/CLT remain separate missing work. E2 likewise proves finite semidiscrete ODE existence, not nonlinear continuum PDE well-posedness. These limits are mostly acknowledged in the detailed docs but must remain visible in the headline inventory.

### R15 — semantic flux feasibility is not a verified finite DOA/ADA implementation

**Scope correction already partly made by the repair branch.** `DOAFeasible` and `ADAFeasible` quantify over real log-ratios and fluxes with exponential balance equations. Their equivalence with multistationarity capacity is substantive mathematics. It is not a finite decision algorithm. The one-shelf ADA converse does not implement the arbitrary multi-shelf procedure, and the bridge from `DOARun`/shelf verdicts still needs extra dependence/placement data.

The repaired README now states this boundary. Keep M7/M8 partial and ensure older module narratives or PR descriptions do not claim that these equivalences establish the correctness/completeness of the separately defined published shelf algorithms.

### R16 — concordance injectivity is restricted to two positive compositions

**Medium priority for exact source fidelity.** [Kinetics.Injective](../CRNT/Multistationarity/Injectivity.lean#L38) quantifies over positive compatibility classes, so both compared compositions are positive. The [published Definition 4.3](https://pmc.ncbi.nlm.nih.gov/articles/PMC4679294/) allows two nonnegative compositions when at least one is positive. The library's weakly monotonic rate predicate does retain the published nonnegative/support guards, but its injectivity conclusion omits this boundary-inclusive case.

The interior concordance equivalence and its positive-monostationarity consequence are valid. Label that scope explicitly or extend the witness argument to one positive and one nonnegative composition before calling the formal statement the full published injectivity result.

## Global Attractor Theorem: the main semantic concern is resolved at the trajectory level

The interface `IsMassActionFlow` in [GlobalPermanence.lean](../CRNT/Dynamics/GlobalPermanence.lean#L34) asks for a global flow from **every real-valued initial concentration**, including negative ones. Such an ambient flow need not exist even for a complex-balanced system. For example, the one-species reversible unit-rate system `A ⇌ 2A` has `x'=x-x²`; negative initial conditions can blow up in finite forward time. Thus a theorem universally quantifying over supplied ambient realizations can be vacuous.

That observation does **not** invalidate the current GAC development. The [trajectory theorem](../CRNT/Dynamics/GlobalAttractorTheorem.lean#L1725) states genuine `Filter.Tendsto` for every supplied global forward solution from a positive compatible start. Its assumptions are finite species, positive rate constants, a positive complex-balanced reference, positivity of the start, and compatibility. It does not assume persistence, absence of critical siphons, or a pre-existing ambient mass-action flow.

To check existence as well, `SemanticAudit.complexBalanced_exists_convergent_solution` proves the following explicit contract against this source:

```text
positive complex-balanced x*, positive x0 in its class
  -> exists Γ : real time -> concentrations,
       Γ(0) = x0,
       Γ'(t) = massActionVectorField κ (Γ(t)) for every t >= 0,
       Γ(t) -> x* as t -> infinity.
```

The proof constructs a bounded-Lipschitz cutoff flow, uses the genuine entropy sublevel bound to show that its orbit never encounters the cutoff, and then invokes the trajectory convergence theorem. The cutoff flow is not claimed to solve the mass-action equation from unrelated negative starts. This check has only the three standard axioms.

The difficult persistence chain was also traced through its main mathematical interfaces:

1. [complexBalanced_forward_floor](../CRNT/Persistence/ComplexBalancedFloor.lean#L30) takes a bounded genuine forward mass-action trajectory and proves one strictly positive coordinate floor for every species and every nonnegative time.
2. [exists_zsh](../CRNT/Persistence/ZeroSeparatingRegion.lean#L711) constructs the finite affine constraints, initial containment, positive floor, and active-facet log-slack validity. The required region is a conclusion, not a hypothesis identical to persistence.
3. [FieldDecomposition](../CRNT/Persistence/FieldDecomposition.lean) relates the actual mass-action field to complex-balanced circulation and proves inward pairing from those log-slack conditions.
4. [PolyhedralBarrier](../CRNT/Geometry/PolyhedralBarrier.lean) traps the trajectory using the maximum of genuine affine constraints and local descent in a band.
5. The compact-interior and entropy/LaSalle arguments convert persistence to the unique class equilibrium and to actual trajectory convergence. The genuine permanence predicate makes the absorbing set class-uniform while allowing entry time to depend on the initial condition.

The target is consistent with the global-attraction statement and zero-separating-surface route in [Craciun's v3 preprint, dated September 2026](https://arxiv.org/pdf/1501.02860v3). This audit does not equate the library's affine/barrier construction with a line-by-line formalization of every geometric construction in that paper, or make a claim about peer-review status. I found no hidden persistence premise or changed mass-action/Tendsto definition in this trajectory result.

The bounded weakly reversible floor is a separate genuine result, not a proof of global boundedness for every weakly reversible system. Preserve that distinction when discussing the remaining persistence conjecture. Replace the README's stale “reduced to one hypothesis” GAC summaries with a single account of the actual trajectory theorem, keeping the ambient-flow limitation explicit.

## Other substantial results whose advertised target is supported

The ledger identifies the supporting interfaces individually. In particular, the ordinary deficiency-zero theorem, weakly reversible positive steady-state existence, Birch intersection, positive complex-balance geometry, fixed-rate Shinar–Feinberg ACR, detailed-balance/Wegscheider converse, directed matrix-tree identity with correct linkage restriction, actual class-restricted complex-balanced linear stability, tempered-rate deterministic strongly endotactic permanence, and the genuine Lotka periodic-orbit construction retain their mathematical substance.

The stochastic product form is not merely a residual equation: [ProductFormInvariance](../CRNT/Stochastic/ProductFormInvariance.lean#L106) connects it to the minimal transition semigroup with summability supplied. This supports the positive complex-balanced product-form claim of [Anderson–Craciun–Kurtz](https://arxiv.org/abs/0803.3042). Nonlinear fixed-time Gaussian limits also have actual weak-convergence conclusions, with the scope recorded under P9.

The n-dimensional [Brouwer simplex theorem](../CRNT/Analysis/SpernerBrouwerN.lean#L100) concludes existence of a fixed point for every continuous simplex self-map. The full [Gale–Nikaido box theorem](../CRNT/Multistationarity/GaleNikaidoUniv.lean#L364) concludes injectivity from a P-matrix derivative throughout the box, without assuming that injectivity. The field map should cite this full theorem rather than only its local-homeomorphism precursor.

The [Sard theorem](../CRNT/Multistationarity/Sard.lean) is correctly the equal-dimension critical-value measure-zero/density result, using Mathlib's Jacobian measure theorem; it does not supply the missing general degree construction on its own. The flow construction genuinely constructs global integral curves for bounded globally Lipschitz fields, then proves uniqueness, continuous dependence, and the semigroup law. That bounded-field assumption is why the cutoff/exact-orbit bridge matters in the GAC audit.

## Reproduction and limits

Run from the repair worktree with its pinned dependencies:

```sh
python3 scripts/audit_advertised_statements.py \
  --output /tmp/crnt-declaration-types.txt \
  --metadata /tmp/crnt-advertised-validation.json
lake env lean docs/semantic-audit/CorrespondenceChecks.lean
```

The export tool only checks elaboration and axiom dependencies. It deliberately does not assign semantic verdicts from theorem names, proof length, or absence of `sorry`. The assessments in the ledger are manual. The correspondence checks use exact mass-action definitions and ordinary Lean proofs, with no `native_decide`, additional axioms, or admitted goals.

The earlier engineering validation at this source completed `lake build CRNT CRNTFrontier Scaffold analyze test`, `lake test`, the five Python analyzer regressions, and the repository's static checks. This audit adds semantic evidence and does not convert that local validation into a claim of green remote CI. The audited PR and repair branch have not been merged or published as part of this review.

The highest-priority repair is to align public definitions and claims: MESSI, semilinearity, Hirsch, full-field Hopf, full Fenichel, stochastic strong endotacticity, and parity. For the remaining partial areas, preserve the useful theorems and state their hypotheses and residual obligations directly. An axiom audit is necessary evidence for the formal proofs; it cannot certify the English-to-Lean correspondence on its own.
