#!/usr/bin/env python3
"""Fold the campaign's new declarations into `docs/field-map.md`.

For every leaf the script
  * appends the new declarations to the *Lean* column, and
  * appends a Notes paragraph recording what the campaign added and what remains.

The script is idempotent: a declaration already present in a row is not added
twice, and a Notes marker already present is not appended twice.
"""
from __future__ import annotations

import re
from pathlib import Path

MAP = Path(__file__).resolve().parent.parent.parent / "docs" / "field-map.md"

# leaf -> (new declarations, notes paragraph)
UPDATES: dict[str, tuple[list[str], str]] = {
    "S19": ([
        "CRNT.Network.card_positiveSteadyStates_odd_iff_classDegree_odd",
        "CRNT.Network.card_positiveSteadyStates_even_iff_classDegree_even",
        "CRNT.Network.weightedCount_eq_classDegree",
        "CRNT.Network.card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd",
    ], """**2026-10-21 (campaign): the parity theorem in its general form.** The relation
`degree = count − 2·negCount` is now packaged as an *equivalence of parities* — the parity of the
number of positive steady states is the parity of the class degree
(`CRNT.Network.card_positiveSteadyStates_odd_iff_classDegree_odd`,
`card_positiveSteadyStates_even_iff_classDegree_even`) — which is the converse of the previously
available implication, and it does **not** require the total degree. The *counted with
multiplicity* reading is formalized without the nondegeneracy hypothesis: the class degree is
literally the weighted count of the positive steady states
(`CRNT.Network.weightedCount_eq_classDegree`), and the parity of the count of the
**nondegenerate** positive steady states equals the parity of the class degree
(`card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd`). The refinement "two positive
steady states of opposite reduced-Jacobian signs" was shown **not** to force an even count
(a machine-checked counterexample is given in the module): the two opposite local degrees cancel in
the class degree, and the *parity* of the degree, not its evenness, is what the parity theorem
relates to the count; the correct consequence is that an odd class degree with two opposite signs
forces an odd count of at least three
(`card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree`)."""),
    "S20": ([
        "CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero",
        "CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive",
        "CRNT.Network.not_isNilpotent_weightedAdjacencyMatrix_of_isIrreducible",
        "CRNT.Network.collatz_wielandt_bounds",
        "CRNT.Network.pos_of_nonneg_of_pos_eigenvector",
        "CRNT.Network.exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive",
    ], """**2026-10-21 (campaign): the explicit eigenvalue theory and the Perron–Frobenius step.**
Eigenvalues are now *named*: nilpotence of the mass-action Jacobian is equivalent to all its
complex eigenvalues vanishing (`CRNT.Network.isNilpotent_massActionJacobian_iff_eigenvalues_zero`,
via Mathlib's `Module.End.hasEigenvalue_iff_isRoot_charpoly` and the Cayley–Hamilton identity).
The Perron–Frobenius step is available in Mathlib's *named* forms: a matrix that is
`Matrix.IsPrimitive` (entrywise nonnegative with a strictly positive power) or
`Matrix.IsIrreducible` is not nilpotent
(`not_isNilpotent_weightedAdjacencyMatrix_of_isPrimitive`,
`not_isNilpotent_weightedAdjacencyMatrix_of_isIrreducible`), and the Collatz–Wielandt inequalities
give the bounds for a Perron-type eigenvalue (`collatz_wielandt_bounds`,
`pos_of_nonneg_of_pos_eigenvector`). The Horn–Jackson consequence follows: at a positive
complex-balanced equilibrium whose weighted adjacency matrix is primitive, the mass-action Jacobian
has a **nonzero** eigenvalue (`exists_eigenvalue_ne_zero_massActionJacobian_of_isPrimitive`).
The literal classical conclusion needed a hypothesis that was **proved false** and is now
recorded: the repository's `weightedAdjacencyMatrix` carries the self-loop contributions, so for the
single self-loop `A → A` it is primitive while the Jacobian is nilpotent; the criterion therefore
carries the hypothesis that the network has at least two complexes. Mathlib has no Perron root
and no Perron–Frobenius theorem, so the *spectral radius* statement itself remains out of reach."""),
    "M7": ([
        "CRNT.Network.DOARun.pairingStep_pos",
        "CRNT.Network.doaRun_twoShelf_capacity",
        "CRNT.Network.confluenceVector_of_shelfFlux",
        "CRNT.Network.threeShelf_decomposition",
        "CRNT.Network.shelfMomentMatrix_det_ne_zero_iff",
        "CRNT.Network.linearised_upper_balance",
        "CRNT.Network.shelfBalances_implies_steadyStates",
        "CRNT.Network.analytic_construction_capacity",
        "CRNT.Network.decidableDeficiencyOneHypotheses",
        "CRNT.Network.deficiencyOneHypotheses_iff_compute",
    ], """**2026-10-21 (campaign): the bridge from the presented algorithm to the multi-shelf
machinery, the analytic core, and the decidable hypotheses.** The μ-step of a reaction is now read
off the shelves of its source and target (`CRNT.Network.DOARun.pairingStep_pos`), and the canonical
two-shelf split of a run yields the multistationarity capacity
(`CRNT.Network.doaRun_twoShelf_capacity`); the shelf's confluence vector is *derived* from the
shelf's flux rather than assumed (`CRNT.Network.confluenceVector_of_shelfFlux`). The **rank
obstruction** to the iteration is now quantified: the three-shelf converse holds when a **third
independent moment** is supplied as data and the moment matrix is nonsingular
(`CRNT.Network.threeShelf_decomposition`, `shelfMomentMatrix_det_ne_zero_iff`), and the
two-moment kernel is explicit (`twoMomentRelations_haveNonzeroSolution`). The **analytic core** of
the forward direction is formalized: the linearised upper balance
(`CRNT.Network.linearised_upper_balance`), the fact that the two shelf balances make `1` and `e^μ`
steady states (`shelfBalances_implies_steadyStates`), and hence the capacity
(`analytic_construction_capacity`), with an explicit end-to-end instance for the deficiency-one
network `0 → A`, `0 → B`, `A + B → 0`. Finally the deficiency-one **hypothesis bundle is
decidable** (`CRNT.Network.decidableDeficiencyOneHypotheses`) and is equivalent to the computable
per-class test (`deficiencyOneHypotheses_iff_compute`). What remains: the *existence* of the shelf
signature for an arbitrary deficiency-one network (Feinberg's structural analysis) and the
numerical version of the algorithm."""),
    "M8": ([
        "CRNT.Network.colinear_pairing_sign_agrees",
        "CRNT.Network.coplanar_rate_relation",
        "CRNT.Network.ADAAffirmsCapacityStrong_hasCapacity",
        "CRNT.Network.ADAAffirmsCapacityStrong_ne_exists_signCompatible",
        "CRNT.Network.threeShelf_decomposition",
    ], """**2026-10-21 (campaign): the combinatorial ADA verdict is no longer degenerate.** The two
constraint layers of Ji §1.7 that the module docstring listed as *omitted* are now formalized: the
within-class sign comparison — the sign of the μ-rate is constant on a half-line of colinear
reactions (`CRNT.Network.colinear_pairing_sign_agrees`) — and the coplanar-set ordering of the `Mᵢ`
(`CRNT.Network.coplanar_rate_relation`). The strengthened verdict
`CRNT.Network.ADAAffirmsCapacityStrong` implies the multistationarity capacity
(`ADAAffirmsCapacityStrong_hasCapacity`) and is **provably not** equivalent to mere sign
compatibility (`ADAAffirmsCapacityStrong_ne_exists_signCompatible`), with a worked instance and a
degenerate data set that the extra layer rejects. A correction to the proposed reading: the
colinearity constrains the *difference* of the pairings, not the pairings themselves (the
repository's `colinear_source_pairings_need_not_agree` is the machine-checked counterexample). What
remains: the extended system of Ji §1.7 (the extended reaction vectors and the extended
stoichiometric subspace), the *derivation* of the coplanar ordering and of the admissible `Mᵢ` from
the network's combinatorics, the converse direction, and the numerical (LP) version."""),
    "M9": ([
        "CRNT.Network.fullyOpen_classDegree_of_affineLinear",
        "CRNT.Network.fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign",
        "CRNT.Network.fullyOpen_exists_positiveSteadyState_of_affineLinear",
        "CRNT.Network.fullyOpen_card_positiveSteadyStates_odd_of_affineLinear",
        "CRNT.Network.CounterexampleGeneral.classDegree_ne_sign_det",
    ], """**2026-10-21 (campaign): the total-degree theorem for a general invertible affine linear
part.** The repository's theorem `fullyOpen_classDegree` assumed the linear part at infinity to be
the *diagonal outflow operator*; the general statement — the class degree is the **sign of the
determinant of the linear part at infinity** — is now proved for an arbitrary invertible `M`
(`CRNT.Network.fullyOpen_classDegree_of_affineLinear`), together with the existence and the
parity corollaries (`fullyOpen_exists_positiveSteadyState_of_affineLinear`,
`fullyOpen_card_positiveSteadyStates_odd_of_affineLinear`) and the recovery of the diagonal case.
The unconditional form is false and is proved false: the class degree is the *relative* degree on
the nonnegative part of the class, so it equals the degree at infinity only when the unique zero
of the field lies in that part; the unconditional dichotomy is
`fullyOpen_classDegree_of_affineLinear_eq_zero_or_sign` and the counterexample is
`CRNT.Network.CounterexampleGeneral.classDegree_ne_sign_det`. What remains: the degree at infinity
of a field with **higher-order** reaction terms (the mixed-volume count)."""),
    "M11": ([
        "CRNT.Network.not_multistationary_of_c_twoY_of_b1_zero",
        "CRNT.Network.not_multistationary_of_c_XplusY_of_v0_zero",
        "CRNT.Network.twoRxn_multistationary_cXY_imp_Q_pos",
        "CRNT.Network.twoRxn_multistationary_cXY_imp_sigma_neg",
        "CRNT.Network.twoRxn_multistationary_cXY_imp_u1_pos",
        "CRNT.Network.twoRxn_multistationary_cXY_imp_v1_neg",
        "CRNT.Network.twoRxnMultistationary_complete_cXY",
        "CRNT.Network.twoRxnMultistationary_complete_cTwoY",
    ], """**2026-10-21 (campaign): the two-reaction criterion is now complete on all 75 members.** The
three necessary conditions of the `c = X+Y` and `c = 2Y` sub-families are proved
(`not_multistationary_of_c_twoY_of_b1_zero`, `not_multistationary_of_c_XplusY_of_v0_zero`,
`twoRxn_multistationary_cXY_imp_Q_pos`) and so are the remaining sign conditions
(`twoRxn_multistationary_cXY_imp_sigma_neg`, `..._imp_u1_pos`, `..._imp_v1_neg`,
`twoRxn_multistationary_cTwoY_imp_v0_pos`, `..._imp_sigma_neg`), using the *discreteness* of the
complexes. With the `c = 2X` half (`not_multistationary_of_c_twoX`) the criterion
`Network.twoRxnMultistationary` is now an exact characterisation of multistationarity on the whole
family (`twoRxnMultistationary_complete_cXY`, `twoRxnMultistationary_complete_cTwoY`). What
remains: the criterion is not claimed outside the two-species bimolecular family (reversible
two-reaction networks, more species), and the *atom* enumeration is not re-proved here."""),
    "M13": ([
        "CRNT.Network.reducedJacobianInChart_det_scale",
        "CRNT.Network.reducedJacobian_det_scale",
        "CRNT.Network.sign_reducedJacobian_det_eq_of_scale",
        "CRNT.Network.cauchyBinet_term_sign",
        "CRNT.Network.circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent",
        "CRNT.Network.localDegree_eq_one_iff_reducedDet_pos",
        "CRNT.Network.exists_two_positiveSteadyStates_of_localDegree_ne_classDegree",
        "CRNT.Network.fullyOpen_exists_two_positiveSteadyStates_affine_of_det_pos",
        "CRNT.Network.multistationary_iff_exists_positiveSteadyState_det_pos",
    ], """**2026-10-21 (campaign): the three missing items of the higher-rank circuit reading, and the
higher-rank criterion.** The reduced determinant is **homogeneous of degree `s = stoichRank`** in the
rate constants (`CRNT.Network.reducedJacobianInChart_det_scale`, `reducedJacobian_det_scale`), so the
sign condition that decides the multistationarity region is invariant under a common positive
rescaling of the rates (`sign_reducedJacobian_det_eq_of_scale`). The **sign rule** for a
Cauchy–Binet term is a theorem of its own (`CRNT.Network.cauchyBinet_term_sign`), and the converse
characterisation of the non-vanishing terms is proved
(`circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent`); the hypothesis
`chart (proj (reactionVector r)) = reactionVector r` that the field map listed as missing turns out
to be **automatic** for the canonical chart (`stoichChart_stoichProj_reactionVector`). The link
between the sign of the reduced determinant and the local degree is now explicit
(`localDegree_eq_one_iff_reducedDet_pos`), and the higher-rank criterion is formalized in the
degree-counting form (`exists_two_positiveSteadyStates_of_localDegree_ne_classDegree`,
`multistationary_iff_exists_positiveSteadyState_det_pos`), with the affine instance
(`fullyOpen_exists_two_positiveSteadyStates_affine_of_det_pos`). What remains: the *explicit
semialgebraic description* of the multistationarity region in rank `s ≥ 2`, and the total-degree
theorem for higher-order reaction terms."""),
    "D12": ([
        "CRNT.Network.weaklyReversible_persistentFrom_of_bounded",
        "CRNT.Network.persistenceConjectureStrong_of_weaklyReversible_of_bounded",
        "CRNT.Network.boundaryOmegaExcluded_of_weaklyReversible",
        "CRNT.Network.weaklyReversible_forward_floor_varK_of_bounded",
        "CRNT.Network.weaklyReversible_confined_varK_of_bounded",
    ], """**2026-10-21 (campaign): the bounded case in its strong (compact-confinement) form.** The
weakly reversible floor gives a uniform positive lower bound on a bounded positive trajectory, and
with it the **compact-interior** certificate `PersistentFrom`
(`CRNT.Network.weaklyReversible_persistentFrom_of_bounded`) — the strong form of the persistence
conjecture that was previously available only for conservative networks — and hence
`persistenceConjectureStrong_of_weaklyReversible_of_bounded`. The ω-limit formulation is now
available **without** the critical-siphon hypothesis
(`CRNT.Network.boundaryOmegaExcluded_of_weaklyReversible`), and the tempered-rate (Extended)
persistence conjecture is proved in the bounded case
(`weaklyReversible_forward_floor_varK_of_bounded`, `weaklyReversible_confined_varK_of_bounded`).
Two unconditional forms were shown to be **false** and are refuted by proof: the ω-limit statement
without the hypothesis that the orbit solves the mass-action ODE (a contracting flow can drive a
positive state to a boundary steady state), and the strong conjecture without a boundedness
hypothesis. The **unbounded** case for weakly reversible networks with three or more species and
no strictly positive conservation law remains **open in the literature** and is not claimed."""),
    "D14": ([
        "CRNT.IsStrictMonotoneSeparator",
        "CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator",
        "CRNT.omegaLimit_orderConvex_of_monotone_flow_of_discreteOmegaLimit",
        "CRNT.massAction_omegaLimit_orderConvex_of_monotone_field_of_uniformSeparator",
    ], """**2026-10-21 (campaign): the remaining strong-order case.** The field map listed, as the
remaining item, "the case where the ω-limit point is merely `≤ z` without being strongly so, which
needs a separating functional strict in the strong order or a uniform gap". Both are now
formalized: `CRNT.IsStrictMonotoneSeparator` is the strict separator, the **uniform gap**
(`CRNT.HasUniformSeparatorGap`) yields the order-convexity of the ω-limit set
(`CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator`), and so does the case of a
**discrete** ω-limit set with a strict separator
(`omegaLimit_orderConvex_of_monotone_flow_of_discreteOmegaLimit`); the mass-action specialisation
is `CRNT.massAction_omegaLimit_orderConvex_of_monotone_field_of_uniformSeparator`. The
canonical Hirsch–Smith separator is strict (`isStrictMonotoneSeparator_sepAbove`), so the
hypothesis is not vacuous. What remains: the **general** order-convexity of the ω-limit set for
arbitrary monotone flows (the classical Hirsch–Smith chain property) is not proved: the strict
separator alone does not close the case of an infinite ω-limit set, because the separator may take
infinitely many values on it."""),
    "D16": ([
        "CRNT.PlanarHopfData.hopfNontrivialMultiplier",
        "CRNT.PlanarHopfData.norm_hopfNontrivialMultiplier",
        "CRNT.PlanarHopfData.hopfNontrivialMultiplier_norm_lt_one_iff",
        "CRNT.PlanarHopfData.hopfCycle_floquetNondegenerate",
        "CRNT.PlanarHopfData.truncatedCycle_isPeriodicTrajectory",
        "CRNT.Hopf.radialDrift_hasDerivAt_of_contDiff",
        "CRNT.Hopf.averagedRemainder_hasDerivAt_of_contDiff",
    ], """**2026-10-21 (campaign): the Floquet multiplier of the Hopf cycle, and the automatic `C¹`
regularity of the averaged remainder.** The **Floquet** vocabulary of the oscillation layer is now
connected to the Hopf layer: the nontrivial multiplier of the closed-form Hopf limit cycle is
computed (`CRNT.PlanarHopfData.hopfNontrivialMultiplier`), its modulus is the transverse Floquet
exponent `2 ℓ₁ R⋆²` (`norm_hopfNontrivialMultiplier`), and the cycle is linearly stable exactly
when the first Lyapunov coefficient is negative
(`hopfNontrivialMultiplier_norm_lt_one_iff`, `hopfCycle_floquetNondegenerate`). The closed-form
cycle is a `CRNT.PeriodicTrajectory` (`truncatedCycle_isPeriodicTrajectory`), which reconnects the
Hopf layer with the whole oscillation layer. The `C¹` regularity of the averaged remainder is now
**automatic** — it follows from the `C¹` regularity of the reduced field by differentiating under
the angular integral (`CRNT.Hopf.radialDrift_hasDerivAt_of_contDiff`,
`averagedRemainder_hasDerivAt_of_contDiff`) — instead of being carried as data. A correction is
recorded: the *complex* multiplier is not itself the planar Floquet multiplier (only its modulus
is), and the transverse exponent is the quantity that the stability criterion concerns. What
remains: the persistence of the cycle for the **full nonlinear mass-action field**, which needs the
differentiable dependence of the flow on the initial point."""),
    "D18": ([
        "CRNT.Oscillation.monotoneIntervalMap_orbit_converges",
        "CRNT.Oscillation.antitoneIntervalMap_evenOdd_converge",
        "CRNT.Oscillation.monotoneIntervalMap_orbit_converges_or_twoCycle",
        "CRNT.Oscillation.returnMap_periodicTrajectory_of_monotone",
    ], """**2026-10-21 (campaign): the one-dimensional ("discrete") Poincaré–Bendixson statement.** The
continuous Jordan curve theorem remains an open target in this repository and is out of Mathlib's
reach, but the **interval** version of the "no wandering" statement is now proved: Coppel's theorem
for a continuous monotone self-map of a compact interval — every orbit converges to a fixed point
(`CRNT.Oscillation.monotoneIntervalMap_orbit_converges`) — and its decreasing counterpart, where the
even and odd subsequences converge to a two-cycle
(`CRNT.Oscillation.antitoneIntervalMap_evenOdd_converge`,
`monotoneIntervalMap_orbit_converges_or_twoCycle`). Applied to the repository's transversal
section, a monotone return map has a fixed point and hence closes into a periodic trajectory
(`CRNT.Oscillation.returnMap_periodicTrajectory_of_monotone`). What remains: the **Jordan
refinement** proper (the ω-limit set is a single periodic orbit or a finite union of them), which
needs the continuous Jordan theorem; and the *rotation number* of a circle map, which Mathlib does
not have."""),
    "P7": ([
        "CRNT.Examples.EndotacticCounterexample.twoSpecies_nonExplosion",
        "CRNT.Examples.EndotacticCounterexample.twoSpecies_positiveRecurrence",
        "CRNT.Examples.EndotacticCounterexample.twoSpecies_geometricErgodic",
        "CRNT.Examples.EndotacticCounterexample.twoSpecies_drift",
        "CRNT.CountableFosterDrift",
        "CRNT.foster_hitting_time_of_constant_drift",
        "CRNT.foster_lyapunov_ergodic_of_constant_drift",
        "CRNT.exists_invariant_of_constant_drift",
        "CRNT.Network.countTierValue",
        "CRNT.Network.countTier_card_le",
        "CRNT.Network.countTier_card_le'",
        "CRNT.Network.countTierDrift_exceptional_card_le",
    ], """**2026-10-21 (campaign): a genuine two-species ACK instance, the reusable Foster criterion with
a constant drift, and the count-lattice tier estimate.** The ACK conclusion is now proved for a
**two-species** strongly endotactic network — the repository's own `0 → A`, `A → 0`, `0 → B`,
`B → 0` — with arbitrary positive rate constants: non-explosion
(`CRNT.Examples.EndotacticCounterexample.twoSpecies_nonExplosion`), positive recurrence with a
strictly positive stationary law (`twoSpecies_positiveRecurrence`) and geometric ergodicity
(`twoSpecies_geometricErgodic`); the drift is the multiplicative Foster bound
`QV ≤ −ε V + K` (`twoSpecies_drift`). The reusable content of the ACK conclusion — the
**countable-state Foster–Lyapunov criterion with a constant drift**, which the repository's
multiplicative `foster_lyapunov_ergodic` does not cover — is now formalized
(`CRNT.CountableFosterDrift`, `CRNT.foster_hitting_time_of_constant_drift`,
`CRNT.foster_lyapunov_ergodic_of_constant_drift`, `CRNT.exists_invariant_of_constant_drift`), with
a worked instance (the pure death chain). The **count-lattice tier estimate** — the tier of a
count, the finiteness of a tier band with its explicit cardinality bound, and the finiteness of the
exceptional set of the tier drift certificate — is formalized
(`CRNT.Network.countTierValue`, `countTier_card_le`, `countTier_card_le'`,
`countTierDrift_exceptional_card_le`). What remains: the **general multispecies** ACK theorem; its
missing input is the deterministic tier-weight construction (the tier separation and coverage
properties), and the naive tier-domination route stays refuted by
`CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate`."""),
    "P8": ([
        "CRNT.JumpSystem.poisson_defect_le_poisson",
        "CRNT.JumpSystem.poisson_defect_le",
        "CRNT.JumpSystem.poisson_jumpCount_tail_le",
        "CRNT.JumpSystem.poisson_jumpCount_bounded",
        "CRNT.JumpSystem.poissonTail",
    ], """**2026-10-21 (campaign): the Poisson domination of the jump count.** The missing
quantitative ingredient of the path-space reading of Kurtz's law of large numbers — which does
**not** need a measure on the path space — is now formalized: for a jump system whose exit rate is
bounded by `Λ`, the probability of more than `k` jumps in a window is dominated by the Poisson tail
`Po(Λ h)` (`CRNT.JumpSystem.poisson_defect_le_poisson`, `poisson_jumpCount_tail_le`), with the
uniform factorial bound `≤ (Λ h)^{k+1}/(k+1)!` (`poisson_defect_le`) and the corollary that the
jump count in a window is `O(1)` in probability, uniformly in the starting state
(`poisson_jumpCount_bounded`). Two corrections to the naive formulations are recorded: the
`k`-jump kernels are **nested** (the row sum is the probability of *at most* `k` jumps), and the
factorial bound is on the **defect**, not on the row sum. What remains: the identification of the
exit mass with the literal path event, which needs an i.i.d.-exponential measure on the path space
and the strong Markov property — neither of which the library has."""),
    "P9": ([
        "CRNT.Stochastic.secondMoment_aggregate_scaledClock",
        "CRNT.Stochastic.secondMoment_centered_aggregate_scaledClock",
        "CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le",
        "CRNT.JumpSystem.drift_sq_le",
        "CRNT.JumpSystem.sum_Pmin_mul_sq_le",
        "CRNT.JumpSystem.fluctuation_chebyshev",
        "CRNT.JumpSystem.dynkin_sq_le",
    ], """**2026-10-21 (campaign): the second moment of the fluctuation, and the compensated
second-moment bound for the jump system.** The **second moment** of the volume-scaled Poisson
fluctuation is now computed — the diagonal term is `O(1/V)` and the cross terms `O(1/V²)`
(`CRNT.Stochastic.secondMoment_aggregate_scaledClock`,
`secondMoment_centered_aggregate_scaledClock`) — with the fluctuation-scale (`O(1)`) Chebyshev
bound (`CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le`). The **compensated
second-moment** estimate of the jump system is formalized: the drift of the square of a bounded
Lyapunov function (`CRNT.JumpSystem.drift_sq_le`), the Dynkin inequality for the second moment
(`dynkin_sq_le`), the terminal second-moment estimate (`sum_Pmin_mul_sq_le`) and the Chebyshev tail
for the fluctuation about its initial value (`fluctuation_chebyshev`). A correction is recorded:
the naive integral form of the second-moment Dynkin inequality is **false** (it is false even for
the constant observable `V ≡ 1`), and the correct forms are the ones proved. What remains: the
**path-space** statement — the identification of the exit event with the exit mass and the
uniform-in-time bound on the running supremum — which needs optional stopping of the compensated
Poisson martingale, and the genuinely *state-dependent* random time change."""),
    "A3": ([
        "CRNT.MixedVolume.zonotopeVolumePolynomial",
        "CRNT.MixedVolume.zonotopeVolumePolynomial_linear",
        "CRNT.MixedVolume.zonotopeVolumePolynomial_smul",
        "CRNT.MixedVolume.zonotopeVolumePolynomial_coeff_eq_mixedVolume",
        "CRNT.MixedVolume.card_solutions_le_volumePolynomial",
    ], """**2026-10-21 (campaign): the volume polynomial of a zonotope.** The volume-polynomial
theorem is now formalized in the zonotope case: the volume of `λ₁Z₁ + … + λ_mZ_m` is the
homogeneous polynomial `∑_{|S|=n} (∏_{i∈S} λ_i)|det(z_S)|`
(`CRNT.MixedVolume.zonotopeVolumePolynomial`), it is linear in each segment length
(`zonotopeVolumePolynomial_linear`) and homogeneous of degree `n`
(`zonotopeVolumePolynomial_smul`), and its coefficients are the **mixed volumes** of the
repository (`zonotopeVolumePolynomial_coeff_eq_mixedVolume`). A BKK reading follows in the
separated-variable instance (`card_solutions_le_volumePolynomial`). A correction is recorded: the
*additive* form of multilinearity needs the "zero convention" term — the monomials not containing
`λ_i` are unaffected by `λ_i`. What remains: the **general convex-body** mixed volume (a
genuine measure-theoretic theorem) and the general BKK bound for arbitrary Newton polytopes."""),
    "A4": ([
        "CRNT.SlowFast.exists_uniform_fast_contraction",
        "CRNT.SlowFast.exists_uniform_contraction",
        "CRNT.SlowFast.uniformContraction_of_hurwitz",
        "CRNT.SlowFast.tikhonov_tube_of_pointwise_contraction",
        "CRNT.Network.tropical_reduction_estimate_uniform",
        "CRNT.Network.tropicalLeadingField_eq_reduced",
        "CRNT.Network.IsTropicalEquilibration_reduced",
        "CRNT.Network.tropicalSlowField_eq_reduced",
        "CRNT.Network.tropicalOrder_reduced",
    ], """**2026-10-21 (campaign): the uniformity of the contraction, the tube hypothesis, and the
dynamical reading of the tropical reduction.** The **uniformity of the contraction in the slow
variable** — the item the field map listed as missing — is now a bridging lemma: a pointwise
contractive condition on a compact region, with a continuous rate, yields a *single* uniform
contraction constant (`CRNT.SlowFast.exists_uniform_fast_contraction`,
`CRNT.SlowFast.exists_uniform_contraction`), a Hurwitz linearization yields a uniform contraction
on a compact neighbourhood (`uniformContraction_of_hurwitz`), and the **tube hypothesis** follows
in the general slow–fast setting (`CRNT.SlowFast.tikhonov_tube_of_pointwise_contraction`). The
tropical reduction is now read **dynamically**: the leading field of the full network is the
leading field of the reduced network (`CRNT.Network.tropicalLeadingField_eq_reduced`), the reduced
network is itself tropically equilibrated (`IsTropicalEquilibration_reduced`), and the tropical
order is the restriction of the full one (`tropicalOrder_reduced`). A discrepancy is quantified:
the *mass-action* field of the reduced network is **not** the leading field, because a reaction may
be reduced (minimal for another species) while changing a species for which it is not minimal. What
remains: the `ε`-dependent Fenichel manifold and the entry into the tube for a solution starting
outside it."""),
    "C2": ([
        "CRNT.Computation.Semilinear.max",
        "CRNT.Computation.semilinear_max_add",
        "CRNT.Computation.MaxAffine.maxAffineCRN_stablyComputes",
        "CRNT.Computation.stablyComputes_comp",
    ], """**2026-10-21 (campaign): closure under `max`, and the composition lemma.** The semilinear
class is now closed under `max` — the regions of the two pieces are split by the hyperplane
`f = g`, whose linear form is the difference of the two affine maps — and the closure under `+`,
`min`, `max` and `k·` is packaged (`CRNT.Computation.Semilinear.max`,
`CRNT.Computation.semilinear_max_add`); the maximum of two affine maps is realized by an explicit
network (`CRNT.Computation.MaxAffine.maxAffineCRN_stablyComputes`). The **composition lemma** — the
technical keystone of the realization direction — is now formalized
(`CRNT.Computation.stablyComputes_comp`): a family of networks running in parallel, followed by a
*collector* network, stably computes the composition of the two computations. A limitation is
recorded and proved: the `Network` formalism cannot express a phase guard (the non-applicability
of the first network's reactions cannot be tested locally), so the second network must be a
collector. What remains: the full Chen–Doty–Soloveichik theorem — the repository's `Semilinear`
predicate is weaker than Presburger semilinearity (no congruences) and the necessity direction for
arbitrary networks is open."""),
    "C3": ([
        "CRNT.AntitheticInstance.antitheticInstance_annihilation_sign_condition",
        "CRNT.AntitheticInstance.lyap_eq_generalPlant_quadratic",
        "CRNT.AntitheticInstance.antitheticInstance_no_quadratic_certificate",
        "CRNT.Stochastic.FosterLyapunovCertificate",
        "CRNT.Antithetic.closedLoop_fosterCertificate",
        "CRNT.Antithetic.closedLoop_ergodic_of_fosterCertificate",
    ], """**2026-10-21 (campaign): the explicit certificate for the antithetic network, and the Foster
certificate for its piecewise quadratic Lyapunov function.** The **annihilation sign condition**
for the repository's own closed loop is proved
(`CRNT.AntitheticInstance.antitheticInstance_annihilation_sign_condition`), together with the
identification of `CRNT.Antithetic.lyap` with the general-plant quadratic form of the shape matrix
(`lyap_eq_generalPlant_quadratic`). The other half of the field map's item is **proved to be
unavailable**: the quadratic Foster certificate of the general-plant route *cannot* exist for this
network, because the `Z₂` direction lies in the kernel of the first-order drift matrix and the
reference reaction feeds `Z₁` at a constant positive rate
(`CRNT.AntitheticInstance.antitheticInstance_no_quadratic_certificate`) — the repository's
network-level ergodicity theorem `CRNT.Antithetic.closedLoop_ergodic` therefore uses the *piecewise*
quadratic `lyap`, and the certificate for it is now formalized in a general form that covers a
nonlinear Lyapunov function (`CRNT.Stochastic.FosterLyapunovCertificate`,
`CRNT.Antithetic.closedLoop_fosterCertificate`), with the ergodicity consequence
(`closedLoop_ergodic_of_fosterCertificate`). A further obstruction is proved: the modified
function `wLyap` has infinite sublevel sets and hence cannot be the `V` of a Foster certificate.
What remains: the geometric ergodicity of the closed loop, which needs a Lyapunov function with
finite sublevel sets *and* a strictly negative exponential drift — neither of the repository's two
functions satisfies it."""),
    "E2": ([
        "CRNT.ReactionDiffusion.laplacianMatrix_charpoly",
        "CRNT.ReactionDiffusion.laplacian_poincare",
        "CRNT.ReactionDiffusion.laplacian_quadratic_nonpos",
        "CRNT.ReactionDiffusion.semidiscrete_mean_zero_turing_iff",
        "CRNT.ReactionDiffusion.exists_reactionDiffusion_solution_global",
        "CRNT.ReactionDiffusion.exists_global_twoSided_solution",
        "CRNT.ReactionDiffusion.exists_reactionDiffusion_flow_semigroup",
    ], """**2026-10-21 (campaign): the spectral analysis of the discretisation, and global existence.**
The **characteristic polynomial and the spectrum of the box Laplacian** are computed
(`CRNT.ReactionDiffusion.laplacianMatrix_charpoly`: `X (X + n)^{n−1}`), the mean-zero subspace is
the `−n`-eigenspace, and the **discrete Poincaré inequality** follows with the sharp constant `1/n`
(`laplacian_poincare`, `laplacian_quadratic_nonpos`). The connection to the Turing criterion is
closed: the mean-zero spatial modes of the semidiscrete two-species linearization are governed by
the library's mode matrix, and the *eigenvalue* formulation of the Turing criterion is now
available (`semidiscrete_mean_zero_turing_iff`). The **continuation argument** — the classical
global-existence step for an ODE with linear growth — is formalized, together with global existence
for the semidiscrete system (`exists_reactionDiffusion_solution_global`), the two-sided solution,
its uniqueness and the **semigroup law** (`exists_global_twoSided_solution`,
`exists_reactionDiffusion_flow_semigroup`). A consequence worth recording: the semidiscrete
box-Laplacian system is *never* diffusion-driven unstable for the library's Brusselator
parameters, because the box Laplacian realizes only the wavenumbers `0` and `n`. What remains:
the PDE-level statements (weak/strong solutions, pattern selection) — Mathlib has no PDE theory —
and the Dirichlet Laplacian on a one-dimensional grid, which is a different operator."""),
    "E3": ([
        "CRNT.Dynamics.gronwall_exp_comparison",
        "CRNT.Dynamics.gronwall_max_principle",
        "CRNT.Dynamics.gronwall_ineq",
        "CRNT.Dynamics.halanay_nonpos",
        "CRNT.Dynamics.halanay_le_exp",
        "CRNT.Dynamics.halanay_le_exp_max",
        "CRNT.Dynamics.delayLinear_sq_deriv_le",
        "CRNT.Dynamics.delayLinear_semistability",
        "CRNT.Dynamics.delay_comparison_scalar",
        "CRNT.Dynamics.delay_comparison_global",
        "CRNT.Dynamics.delay_comparison_eq",
        "CRNT.Dynamics.delay_difference_exp_le",
        "CRNT.Dynamics.delay_comparison_lattice",
        "CRNT.Dynamics.delay_comparison_lattice_global",
        "CRNT.Dynamics.delay_comparison_lattice_eq",
        "CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn",
    ], """**2026-10-21 (campaign): the Halanay comparison principle, the Grönwall estimate and the
semistability of the linear delay equation — the item this leaf listed as missing — are now
formalized.** The **Grönwall** machinery that Mathlib does not provide is added
(`CRNT.Dynamics.gronwall_exp_comparison`, `gronwall_max_principle`, `gronwall_ineq`; Mathlib's own
`gronwallBound` is reused rather than duplicated). The **Halanay comparison principle** is proved
in its nonpositive form (`CRNT.Dynamics.halanay_nonpos`) and in its quantitative form, with the
*admissible rate* condition `ε + d e^{ετ} ≤ c` (`halanay_le_exp`, `halanay_le_exp_max`), and the
**semistability of the linear delay equation** `ẋ = −a x + b x(·−τ)` for `a > |b|` follows
(`CRNT.Dynamics.delayLinear_semistability`). The **comparison principle** for delay equations is
proved in the scalar setting (`CRNT.Dynamics.delay_comparison_scalar`, `delay_comparison_global`,
`delay_comparison_eq`) and in the **componentwise (lattice)** setting with the Kamke hypothesis
class of the repository's ODE comparison (`CRNT.Dynamics.delay_comparison_lattice`,
`delay_comparison_lattice_global`, `delay_comparison_lattice_eq`), with the exponential growth
estimate for the difference of two delay solutions (`delay_difference_exp_le`). Two corrections are
recorded by machine-checked counterexamples: the Halanay estimate is **false** without `0 ≤ M`
(the delayed term raises a negative solution), and the mass-action delay field does **not** satisfy
the comparison hypothesis (`CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn`). What
remains: the comparison principle for the **mass-action** delay system (its field is not
monotone), the joint non-isothermal Lyapunov function, and the path-space LaSalle theory for delay
equations."""),
}


def main() -> None:
    text = MAP.read_text(encoding="utf-8")
    lines = text.split("\n")
    out: list[str] = []
    changed: dict[str, int] = {}
    for line in lines:
        if not line.startswith("|"):
            out.append(line)
            continue
        cols = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cols) < 5 or not re.fullmatch(r"[A-Z]\d+", cols[0]):
            out.append(line)
            continue
        leaf = cols[0]
        if leaf not in UPDATES:
            out.append(line)
            continue
        decls, note = UPDATES[leaf]
        lean_col = cols[3]
        notes_col = cols[5] if len(cols) > 5 else ""
        added = 0
        for d in decls:
            if f"`{d}`" not in lean_col:
                lean_col = lean_col.rstrip() + ", " + f"`{d}`"
                added += 1
        cols[3] = lean_col
        if len(cols) > 5:
            if "2026-10-21 (campaign)" not in notes_col:
                cols[5] = notes_col.rstrip() + " " + note
            else:
                cols[5] = notes_col
        out.append("| " + " | ".join(cols) + " |")
        changed[leaf] = added
    MAP.write_text("\n".join(out), encoding="utf-8")
    for leaf, n in sorted(changed.items()):
        print(f"{leaf}: +{n} declarations")


if __name__ == "__main__":
    main()
