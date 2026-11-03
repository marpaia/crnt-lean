#!/usr/bin/env python3
"""Insert new declarations into the Lean column of `docs/field-map.md` leaf rows.

The leaf tables are Markdown, and some Notes cells contain `|` characters inside
code spans (e.g. `| y − h(x) |`).  Splitting a row on `|` therefore yields more
than six fragments, and the Notes cell is then the *last* fragment(s), not the
fifth.  This script therefore works on the row as a string:

  * the Lean column is located as the fragment that follows the *Reference*
    fragment and precedes the *Status* fragment, using the fragment that
    contains the backticked declaration names;
  * new declarations are appended to that fragment;
  * the new note text is appended at the very END of the row.

The update is idempotent.
"""
from __future__ import annotations

import re
import sys

MAP = "docs/field-map.md"

# leaf id -> (new declarations, note appended at the end of the row)
UPDATES: dict[str, tuple[list[str], str]] = {
    "P7": (
        [
            "CRNT.Network.tierDrift_le_of",
            "CRNT.Network.tier_nonExplosion",
            "CRNT.Network.tier_positiveRecurrence",
            "CRNT.Network.tier_geometricErgodic",
            "CRNT.Examples.EndotacticTrimerDecay.positiveRecurrence",
            "CRNT.Network.foster_hitting_time_of_endotactic",
            "CRNT.Network.nonExplosion_of_endotactic",
            "CRNT.Network.nonExplosion_of_endotactic_of_weight",
            "CRNT.Network.positiveRecurrence_of_endotactic",
            "CRNT.Network.tendsto_transition_self_pos_of_endotactic",
            "CRNT.Examples.EndotacticBirthDeath.positiveRecurrence",
            "CRNT.Examples.EndotacticBirthDeath.nonExplosion",
        ],
        " The Anderson–Cappelletti–Kim–Nguyen conclusion (positive recurrence of a strongly "
        "endotactic stochastic mass-action system) is now proved for the class of networks "
        "admitting a positive linear weight with a strictly inward multiplicative drift outside "
        "a finite set: the count-lattice Lyapunov function `V n = ∑_s w_s n_s` has "
        "`Network.observableGenerator κ V n ≤ −c` there (`endotactic_constant_drift`), so "
        "Foster's theorem gives the hitting-time bound (`foster_hitting_time_of_endotactic`), "
        "Harris' theorem gives geometric ergodicity and hence positive recurrence "
        "(`positiveRecurrence_of_endotactic`), and the minimal transition function is "
        "stochastic (`nonExplosion_of_endotactic`). Instance: `0 → X`, `X → 0`. The full "
        "strongly endotactic hypothesis (the deterministic tier machinery of leaf D9) is not "
        "yet transferred to the count lattice. A second, larger step transfers the "
        "*tier* machinery to the count lattice: a count-lattice tier structure "
        "(`CRNT.Network.CountTier`, derived from the deterministic `StronglyEndotacticStd` "
        "hypothesis by `countTierDescent_of_stronglyEndotacticStd`) yields a count Lyapunov "
        "function with finite sublevel sets and a constant negative drift outside a finite set "
        "(`CRNT.Network.tierDrift_le_of`), hence Foster's hitting-time bound "
        "(`tierFoster_hitting_time`), non-explosion (`tier_nonExplosion`) and positive "
        "recurrence with a strictly positive stationary law (`tier_positiveRecurrence`), even "
        "geometric ergodicity (`tier_geometricErgodic`). Instance: `0 → X`, `X → 0`, "
        "`2X → 0` (`CRNT.Examples.EndotacticTrimerDecay`). The remaining gap is the full ACK "
        "theorem for an arbitrary strongly endotactic network: on the count lattice the "
        "domination of lower-tier monomials by top-tier ones fails along escape directions.",
    ),
    "P8": (
        [
            "CRNT.JumpSystem.exitMass_nonneg",
            "CRNT.JumpSystem.exitMass_le_one",
            "CRNT.JumpSystem.exitMass_zero_of_mem",
            "CRNT.JumpSystem.exitMass_factor",
            "CRNT.JumpSystem.outsideMassENN_factor",
            "CRNT.JumpSystem.insideMassENN_add_outsideMassENN",
            "CRNT.JumpSystem.outsideMassENN_eq_ofReal",
            "CRNT.Network.three_halves_step",
            "CRNT.Network.dist_le_three_halves",
            "CRNT.Network.union_bound_grid",
            "CRNT.Network.grid_exitMass_nonneg",
        ],
        " The exit mass of the frozen chain is now isolated as `JumpSystem.exitMass` and proved "
        "to be a probability-like quantity (`exitMass_nonneg`, `exitMass_le_one`, "
        "`exitMass_zero_of_mem`); the **exit-mass factorization** `exitMass_factor` proves the "
        "union-bound mechanism: the mass outside a set at time `h₁ + h₂` is the mass inside at "
        "time `h₁`, weighted by the frozen transition function, times the exit mass of the "
        "window of length `h₂` (the `ℝ≥0∞` form `outsideMassENN_factor` is the version used in "
        "the proof, because Fubini for infinite sums is unconditional there; "
        "`insideMassENN_add_outsideMassENN` shows the inside and outside masses add up to "
        "`1`). The deterministic `3δ/2` step of the sample-path reading is proved "
        "(`three_halves_step`). Still missing: the identification of the exit mass with a "
        "literal path event and the union bound over the grid as a probability; the library "
        "has no path measure. The **path space** is now built: a jump path (counts, fired "
        "reactions, holding times), the literal exit event "
        "(`CRNT.Network.LeavesDuring`: there is a jump index `k` with the accumulated holding "
        "time at most `h` and the count outside the set), the exit-exact kernel "
        "`CRNT.JumpSystem.Pexit` with its support, non-negativity and recursion, the grid sum "
        "(`CRNT.Network.grid_exitMass`), the union bound over a finite grid of events "
        "(`CRNT.Network.union_bound_grid`) and the `3δ/2` step in the path-free form "
        "(`CRNT.Network.dist_le_three_halves`). What remains is the algebraic identification of "
        "the exit mass with the exit-exact kernel, and a probability measure on the path space "
        "(the library has no i.i.d.-exponential measure and no strong Markov property).",
    ),
    "D14": (
        [
            "CRNT.stronglyMonotone_unique_equilibrium",
            "CRNT.stronglyMonotone_equilibrium_orderConvex",
            "CRNT.omegaLimit_subset_equilibria",
            "CRNT.omegaLimit_orderConvex",
            "CRNT.hirsch_generic_convergence",
            "CRNT.massAction_stronglyMonotone_of_jacobian",
            "CRNT.massAction_hirsch_convergence",
            "CRNT.Examples.HirschInstance.stronglyMonotone",
            "CRNT.omegaLimit_orderConvex_of_stronglyMonotone",
            "CRNT.hirsch_generic_convergence_of_monotone",
            "CRNT.massAction_hirsch_convergence_of_cooperative",
        ],
        " Hirsch's generic convergence is now formalized: a strongly monotone `C¹` field has at "
        "most one equilibrium and an order-convex equilibrium set "
        "(`stronglyMonotone_unique_equilibrium`, `stronglyMonotone_equilibrium_orderConvex`); "
        "the ω-limit set of a bounded forward solution is a set of equilibria "
        "(`omegaLimit_subset_equilibria`, by LaSalle) and is order-convex "
        "(`omegaLimit_orderConvex`); hence the trajectory converges to the unique equilibrium "
        "(`hirsch_generic_convergence`). The mass-action specialization uses the Jacobian "
        "criterion for strong monotonicity (`massAction_stronglyMonotone_of_jacobian`, "
        "`massAction_hirsch_convergence`); instance `X → 2X` "
        "(`CRNT.Examples.HirschInstance`). The order-convexity of the ω-limit set is taken as a "
        "hypothesis (`hωoc`), not derived from the order machinery. The order-convexity is now "
        "**derived**: for a strongly monotone field the ω-limit set is a singleton and hence "
        "order-convex (`CRNT.omegaLimit_orderConvex_of_stronglyMonotone`), and the generic "
        "convergence theorem follows without the extra hypothesis "
        "(`CRNT.hirsch_generic_convergence_of_monotone`, "
        "`CRNT.massAction_hirsch_convergence_of_cooperative`). For a merely order-preserving "
        "field the order-convexity of the ω-limit set is proved under an explicit "
        "comparability hypothesis (`omegaLimit_orderConvex_of_monotone_flow`); the remaining "
        "gap is the incomparable-orbit case, which needs the strong order `≪`.",
    ),
    "D16": (
        [
            "CRNT.Hopf.radialDrift_normalForm",
            "CRNT.Hopf.averagedRadialField_amplitude",
            "CRNT.Hopf.hasDerivAt_averagedRadialField",
            "CRNT.Hopf.hasDerivAt_averagedRadialField_RR",
            "CRNT.Hopf.truncatedFullRadialField",
            "CRNT.Hopf.fullRadialFieldOf",
            "CRNT.Hopf.cubic_normal_form",
            "CRNT.Hopf.cubic_normal_form_cubic",
            "CRNT.Hopf.quadratic_removed",
            "CRNT.Hopf.homologicalQuad_solution",
            "CRNT.Hopf.homologicalQuad_unique",
            "CRNT.Hopf.quadratic_removable_iff",
            "CRNT.Hopf.planar_quadratic_removed",
            "CRNT.Hopf.cubic_pushForward",
            "CRNT.Hopf.resonantCoefficient",
            "CRNT.Hopf.hopf_cubic_resonance",
        ],
        " The angular averaging is now computed rather than assumed: the average of the radial "
        "component of the truncated Hopf normal form over the circle of radius `R` is "
        "`α R + ℓ₁ R³` (`radialDrift_normalForm`), the averaged radial field is `C¹` in `R` "
        "(`hasDerivAt_averagedRadialField`, `hasDerivAt_averagedRadialField_RR`), its zeros "
        "obey the amplitude law `R² = −α/ℓ₁` (`averagedRadialField_amplitude`), and the "
        "repository's `FullRadialField` is *constructed* for the truncated normal form "
        "(`truncatedFullRadialField`, `fullRadialFieldOf`) instead of being assumed as data. "
        "The **Poincaré–Dulac normal form to cubic order** is also computed: for a cubic "
        "complex field `λw + aw² + bw³` the quadratic term is removed by `w ↦ w − (a/λ)w²` "
        "(`quadratic_removed`, `cubic_normal_form`) and the cubic correction removes the "
        "quartic term (`cubic_normal_form_cubic`); for a real planar field the quadratic part "
        "is removable exactly when the linearization is non-degenerate "
        "(`quadratic_removable_iff`, `homologicalQuad_solution`, `homologicalQuad_unique`, "
        "`planar_quadratic_removed`), the cubic push-forward is exact "
        "(`cubic_pushForward`), and the resonant cubic coefficient is an explicit rational "
        "function of the Taylor data (`resonantCoefficient`); the only resonant cubic monomial "
        "is `w²w̄` and it is resonant exactly at a purely imaginary linearization "
        "(`hopf_cubic_resonance`). Still missing: the calibration of that coefficient to the "
        "repository's real-coordinate formula `lyapunovFromPartials`, the `O(R⁴)` remainder "
        "for a general reduced field, and the mass-action verdict on a sustained periodic "
        "orbit.",
    ),
    "S17": (
        [
            "CRNT.Network.MESSI",
            "CRNT.Network.messiCoeff",
            "CRNT.Network.messi_vectorField_eq_linear",
            "CRNT.Network.messi_steadyState_iff_linear",
            "CRNT.Network.messi_steadyState_add",
            "CRNT.Network.messi_class_positiveSteadyStates_convex",
            "CRNT.Network.messi_no_exactly_two",
            "CRNT.Network.IsSteadyStateInvariant",
            "CRNT.Network.messi_linearInvariant_iff",
            "CRNT.Network.messi_linearInvariant_iff_rowSpace",
            "CRNT.Network.messi_variety_eq_orthSum_rowSpace",
            "CRNT.Examples.MESSI.unique_positiveSteadyState_in_class",
            "CRNT.Examples.MESSI.invariantWeight_isSteadyStateInvariant",
            "CRNT.Examples.MESSI.invariantWeight_not_conservationLaw",
            "CRNT.Examples.MESSI.totalWeight_not_steadyStateInvariant",
            "CRNT.Examples.MESSI.Chain.more_invariants_than_conservationLaws",
            "CRNT.Network.toric_positiveSteadyStates_eq_parametrization",
            "CRNT.Network.toric_steadyStates_eq_exp_kernel",
            "CRNT.Network.steadyStateInvariant_iff_log_orthogonal",
            "CRNT.Network.messi_generalInvariant_iff_valueAtOrigin",
            "CRNT.Network.toric_steadyStates_eq_exp_ker",
            "CRNT.Network.messi_variety_eq_linearParametrization",
        ],
        " The class of networks in which every reaction has a source complex of total "
        "molecularity one (the *linear-elimination* class; the term MESSI is used for it here "
        "in the sense of the source-complex condition, which differs from the "
        "Pérez Millán–Dickenstein usage) is now formalized. For such a network the "
        "mass-action steady-state equations are *linear homogeneous* in the concentrations "
        "(`messi_vectorField_eq_linear`, `messi_steadyState_iff_linear`), so the "
        "steady-state variety is a linear subspace, the positive steady states form a convex "
        "cone (`messi_steadyState_add`), the positive steady states in a fixed class are "
        "convex (`messi_class_positiveSteadyStates_convex`), and a MESSI network is never "
        "*exactly* multistationary: two distinct positive steady states in a class force a "
        "third (`messi_no_exactly_two`). Steady-state invariants are formalized: the linear "
        "invariants of a MESSI network are exactly the rows of the coefficient matrix "
        "(`messi_linearInvariant_iff_rowSpace`), and the conservation laws and the "
        "steady-state invariants need not coincide — for `X ⇌ Y` the conservation law "
        "`(1,1)` is *not* a steady-state invariant while `(κ₁,−κ₂)` is and is *not* a "
        "conservation law (`CRNT.Examples.MESSI`). Rational parametrizations of the toric "
        "steady states and the general (non-linear-elimination) steady-state invariants "
        "remain missing.",
    ),
    "M9": (
        [
            "CRNT.Network.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero",
            "CRNT.Network.exists_positiveSteadyState_of_positiveClassDegree_ne_zero",
            "CRNT.Network.nonnegativeClassDegree_rate_independent",
            "CRNT.Network.positiveClassDegree_rate_independent",
            "CRNT.Network.DegreeExample.exists_positive_steady_state",
            "CRNT.Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage",
            "CRNT.Network.nonnegativeClassDegree_eq_one_of_unique_preimage_of_det_pos",
            "CRNT.Network.exists_positiveSteadyState_of_positive_reducedDet",
            "CRNT.Network.nonnegativeClassDegree_eq_card_of_reducedDet_pos",
            "CRNT.Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree",
            "CRNT.Network.exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one",
        ],
        " The degree-theoretic existence argument in dimension `s ≥ 2` is now formalized: the "
        "**relative Brouwer degree** of the steady-state map on the class is defined "
        "(`Network.nonnegativeClassDegree`, `Network.positiveClassDegree`), a nonzero degree "
        "together with non-vanishing on the class boundary gives a **positive steady state in "
        "the class** (`Network.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero`), "
        "and the degree is **independent of the rate constants** as long as the map does not "
        "vanish on the boundary (`Network.nonnegativeClassDegree_rate_independent`), which "
        "makes it a *structural* object: a network with a nonzero degree for one choice of "
        "rates has a positive steady state for every choice with the same boundary sign "
        "(`Network.exists_positiveSteadyState_of_rate_independent_degree`). Instance: the "
        "fully open two-species network `0 → A → 0`, `0 → B → 0` with degree `1` "
        "(`CRNT.Network.DegreeExample`). The remaining gap is a *structural* criterion for a "
        "nonzero degree (the sign of the reduced determinant at a steady state), and the "
        "nonvanishing-on-the-boundary hypothesis is still an explicit assumption. "
        "**The structural criterion is now supplied**: the degree of the steady-state map at a "
        "unique steady state is the sign of the reduced Jacobian determinant there "
        "(`CRNT.Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage`), so a "
        "positive reduced determinant gives degree `+1` and hence a positive steady state "
        "(`exists_positiveSteadyState_of_positive_reducedDet`), and the Conradi–Feliu–"
        "Mincheva–Wiuf conclusion (a *second* positive steady state) is proved by the "
        "perturbation argument `exists_two_positiveSteadyStates_of_classDegree_neg_localDegree`. "
        "Still missing: the total-degree theorem (the class degree is `(−1)^s` under "
        "dissipativity), which needs a semiflow and a bump function, and the parity "
        "refinement (an odd number of equilibria).",
    ),
    "D18": (
        [
            "CRNT.Oscillation.periodicSolution_constant_of_monotone",
            "CRNT.Oscillation.periodicSolution_constant_of_boxedKamke",
            "CRNT.Oscillation.periodicSolution_constant_of_monotone_locallyLipschitz",
            "CRNT.Oscillation.Network.neverPositivePeriodic_of_cooperative",
            "CRNT.Oscillation.Example.neverPositivePeriodic",
            "CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_poincareBendixson",
            "CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion",
            "CRNT.Oscillation.lotka_oscillatoryCapacity_of_trappingRegion",
            "CRNT.Planar.omegaSet_not_chaotic",
            "CRNT.Planar.eq_orbitSet_of_minimal_invariant_subset",
            "CRNT.Oscillation.rankTwo_noChaos",
            "CRNT.Oscillation.lotka_canonical_omegaSet_not_chaotic",
        ],
        " A **structural criterion for the absence of oscillations** is now formalized: an "
        "order-preserving (or Kamke) planar field has no nonconstant periodic orbit "
        "(`CRNT.Oscillation.periodicSolution_constant_of_monotone`, "
        "`periodicSolution_constant_of_boxedKamke`), and hence a **cooperative planar "
        "mass-action network has no positive periodic orbit for any choice of positive rate "
        "constants** (`CRNT.Oscillation.Network.neverPositivePeriodic_of_cooperative`, "
        "instance `CRNT.Oscillation.Example`). The sharpness is checked: the Lotka network, "
        "which does oscillate, is not cooperative. The converse direction (an oscillation "
        "criterion) is reduced to the repository's Poincaré–Bendixson bundle "
        "(`lotka_hasPositivePeriodicOrbit_of_poincareBendixson`); the bundle's universal "
        "hypotheses (flow regularity, Jordan separation) are still unproved, so the general "
        "existence of oscillations is still missing. The **network-specific half of the "
        "Poincaré–Bendixson route is now discharged** for a concrete planar mass-action "
        "network: a compact, positively invariant, equilibrium-free trapping region built "
        "from a first integral, a `C¹` cut-off keeping the field regular, the confinement of "
        "the orbit, and the conclusion that the network has a positive periodic orbit "
        "(`CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion`, "
        "`lotka_oscillatoryCapacity_of_trappingRegion`). The two *universal* inputs (the `C¹` "
        "dependence of the flow on the initial point and the Jordan separation theorem) "
        "remain hypotheses. The **\"no chaos in the plane\"** half is now formalized: a minimal "
        "compact closed invariant subset of a planar omega-limit set is *exactly* a periodic "
        "orbit (`CRNT.Planar.eq_orbitSet_of_minimal_invariant_subset`), so the omega-limit set "
        "contains no chaotic (fractal) minimal invariant set "
        "(`CRNT.Planar.omegaSet_not_chaotic`) -- no Solenoid, Plykin or horseshoe attractor, and "
        "no Devaney-chaotic or positive-topological-entropy minimal set. The rank-two "
        "mass-action application is `CRNT.Oscillation.rankTwo_noChaos`. Still missing: the "
        "Jordan refinement (the omega-limit set is a single periodic orbit or a finite union of "
        "them, and every omega-limit point is an equilibrium or on a periodic orbit).",
    ),
    "C3": (
        [
            "CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_setpoint",
            "CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_equilibrium",
            "CRNT.Design.GeneralPlant.LyapunovCertificate.antitheticLieDeriv_neg",
            "CRNT.Design.GeneralPlant.ergodic_of_fosterDrift",
            "CRNT.Design.GeneralPlant.geometric_ergodic_of_fosterDrift",
            "CRNT.Design.GeneralPlant.ProductionDegradationNetwork.closedLoop_mean_output_tendsto_via_general",
            "CRNT.Design.GeneralPlant.ProductionDegradationNetwork.ConcreteInstance.antithetic_equilibrium",
            "CRNT.Design.GeneralPlant.fosterDrift_of_certificate",
            "CRNT.Design.GeneralPlant.ergodic_of_certificate",
            "CRNT.Design.GeneralPlant.geometricErgodic_of_certificate",
            "CRNT.Design.GeneralPlant.fosterDrift_of_plant",
            "CRNT.Design.GeneralPlant.plant_lyapunov_equation",
        ],
        " The **general-plant** version of robust perfect adaptation is now formalized: a linear "
        "unimolecular plant `ẋ = A x + B u` with output `y = C x` closed by the antithetic "
        "internal model `u̇ = μ − θ(Cx)` has the setpoint `C x = μ/θ` at every equilibrium "
        "(`CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_setpoint`), a linear-quadratic "
        "Lyapunov certificate makes the closed-loop Lyapunov function decrease "
        "(`antitheticLieDeriv_neg`), and a **general Foster–Lyapunov transfer theorem** gives "
        "ergodicity (and geometric ergodicity) from a drift condition "
        "(`CRNT.Design.GeneralPlant.ergodic_of_fosterDrift`), which is then discharged for the "
        "production–degradation plant, recovering the mean-output convergence "
        "(`closedLoop_mean_output_tendsto_via_general`). Still missing: the construction of "
        "the drift condition for an *arbitrary* output-controllable unimolecular plant, which "
        "is the remaining Briat–Gupta–Khammash theorem. The **Foster drift condition is now "
        "constructed for a general plant**: a first-order (unimolecular) network together with a "
        "quadratic Lyapunov certificate (a symmetric positive-definite `P` solving the "
        "Lyapunov equation of the closed-loop drift matrix) yields the drift bound "
        "`QV(n) ≤ −(3/8)‖n − n*‖² + K` (`CRNT.Design.GeneralPlant.fosterDrift_of_certificate`), "
        "from which the Foster–Lyapunov transfer theorem gives ergodicity and geometric "
        "ergodicity (`ergodic_of_certificate`, `geometricErgodic_of_certificate`); the "
        "closed-loop matrix of a general linear plant is related to the network's drift matrix by "
        "`plant_lyapunov_equation`, so the certificate transfers to the plant "
        "(`LinearPlant.fosterDrift_of_plant`). Still missing: the *molecular* realization of "
        "the antithetic controller, whose annihilation reaction is bimolecular and contributes a "
        "cubic term to the drift of a quadratic Lyapunov function.",
    ),
    "M8": (
        [
            "CRNT.Network.adaFeasible_implies_capacity",
            "CRNT.Network.capacity_implies_adaFeasible",
            "CRNT.Network.hasMultistationarityCapacity_iff_adaFeasible",
            "CRNT.Network.adaFeasible_implies_adaAffirmsCapacity",
        ],
        " As for M7, the **Advanced Deficiency Algorithm** is now formalized: a shelf "
        "decomposition of the reaction set, a confluence vector per shelf carrying both the "
        "lower and the upper balance condition, and a sign-compatible log-ratio "
        "(`CRNT.Network.ADAFeasible`) give the multistationarity capacity "
        "(`adaFeasible_implies_capacity`), and in the one-shelf case the converse holds "
        "(`capacity_implies_adaFeasible`). The ADA refines the DOA "
        "(`adaFeasible_implies_doaFeasible`), and the repository's existing verdict "
        "(`CRNT.Network.ADAAffirmsCapacity`) is shown to follow from the new work "
        "(`adaFeasible_implies_adaAffirmsCapacity`). Still missing: the decomposition of an "
        "arbitrary capacity flux into a multi-shelf system of shelf-wise confluence vectors, "
        "which is the hard part of Ellison's algorithm.",
    ),
    "P9": (
        [
            "CRNT.Network.multivariate_clt_open_weak",
            "CRNT.Network.multivariate_clt_open_weak_integral",
            "CRNT.Network.fluctuation_uniform_concentration",
            "CRNT.JumpSystem.mass_outside_le_exitMass",
        ],
        " The **distributional** CLT for networks whose chains may explode is now formalized: "
        "the fluctuation law of the volume-scaled chain is a sub-probability measure of mass "
        "`P(no explosion)`, the mass tends to `1` as the volume grows, and completing the law "
        "at the origin changes its characteristic function by a vanishing amount; Lévy's "
        "continuity theorem then gives the weak convergence of the fluctuation laws to the "
        "linear-noise Gaussian "
        "(`CRNT.Network.multivariate_clt_open_weak`, "
        "`multivariate_clt_open_weak_integral`) with **no conservation, weight, stochasticity "
        "or non-explosion hypothesis**. The process-level statement is formalized in the "
        "path-free exit-mass form: the mass of the chain outside a set is bounded by the exit "
        "mass (`CRNT.JumpSystem.mass_outside_le_exitMass`, the rigorous reading of “the exit "
        "mass is the probability of leaving the set”), the exit mass is non-decreasing in "
        "time, and the resulting uniform-in-time bound is proved "
        "(`CRNT.Network.fluctuation_uniform_concentration`). Still missing: the "
        "fluctuation-scale (`O(1)`) uniform-in-time estimate and the path-space statement, "
        "which need martingale second-moment machinery that Mathlib lacks.",
    ),
    "D12": (
        [
            "CRNT.Network.conservationLawSpace_total_const_along_solution",
            "CRNT.Network.escape_in_orthogonalComplement",
            "CRNT.Network.projection_on_conservationLawSpace_const",
            "CRNT.Network.escape_to_infinity_in_escape_direction",
            "CRNT.Network.coordinate_le_of_positive_conservation_law",
            "CRNT.Network.no_escape_of_positive_conservation_law",
            "CRNT.Network.persistenceConjectureStrong_of_positive_conservation_law",
            "CRNT.Network.escape_confined_to_zero_face",
            "CRNT.Network.escapingSpecies_subset_escapeFace",
        ],
        " The **geometry of a possible escape to infinity** is now formalized: every conservation "
        "law is constant along a mass-action trajectory, so the displacement of an escaping "
        "trajectory lies in the orthogonal complement of the conservation-law space "
        "(`CRNT.Network.escape_in_orthogonalComplement`) and the projection onto the "
        "conservation-law space is constant "
        "(`projection_on_conservationLawSpace_const`); a species detected by a *nonnegative* "
        "conservation law has a bounded coordinate, so the escape is confined to a face "
        "(`escape_confined_to_zero_face`, `escapingSpecies_subset_escapeFace`). Consequently a "
        "network with a strictly positive conservation law cannot escape: its trajectories are "
        "bounded and uniformly bounded away from zero, and the strong persistence conjecture "
        "holds for it (`no_escape_of_positive_conservation_law`, "
        "`persistenceConjectureStrong_of_positive_conservation_law`). Instances: the reversible "
        "pair `A <-> B` and the autocatalytic network `A -> 2A` with a spectator `B`. Still "
        "missing: the unbounded case of the persistence conjecture for a weakly reversible "
        "network *without* a strictly positive conservation law (three or more species).",
    ),
    "M13": (
        [
            "CRNT.Network.reducedJacobian_det_sign_iff",
            "CRNT.Network.rankOne_multistationary_iff_det_pos",
            "CRNT.Network.rankOne_noPositiveCircuit_noSteadyState",
            "CRNT.Network.isOpen_multistationarityRegion",
            "CRNT.Network.inst_multistationary",
            "CRNT.Network.RateMultistationarityRegion",
            "CRNT.Network.rateMultistationarityRegion_iff_classIsMultistationary",
            "CRNT.Network.reducedDerivOf_eq_forward_sub_backward",
            "CRNT.Network.reducedDerivOf_pos_iff_two_reaction_circuit",
            "CRNT.Network.rankOne_circuit_is_pair",
            "CRNT.Network.not_eq_rateProduct_mul",
        ],
        " The **explicit description of the multistationarity region** is now formalized for "
        "rank-one networks: the sign of the reduced Jacobian determinant at a steady state "
        "equals the sign of the derivative of the scalar field along the class "
        "(`CRNT.Network.reducedJacobian_det_sign_iff`), so with all steady states "
        "nondegenerate the class is multistationary **iff** some steady state has a positive "
        "reduced determinant (`CRNT.Network.rankOne_multistationary_iff_det_pos`); the "
        "reduced determinant is a *signed sum of rate constants* "
        "(`CRNT.MultistationarityRegion.reducedDet_eq_sum_signedRates`), which is the "
        "circuit-based reading of the region, and a network whose reactions all run in the "
        "same direction along the class has no positive steady state at all "
        "(`CRNT.Network.rankOne_noPositiveCircuit_noSteadyState`). The region of parameters "
        "with `d` distinct nondegenerate positive steady states is open "
        "(`CRNT.Network.isOpen_multistationarityRegion`) and nonempty for the "
        "decorated-cell instance (`CRNT.Network.inst_multistationary`). Still missing: the product-of-rates "
        "reading of the determinant over a single circuit (the repository's circuit machinery "
        "covers the full Jacobian, not the rank-one reduced determinant). The region is now given "
        "**explicitly as a set of rate constants** (`CRNT.Network.RateMultistationarityRegion`: "
        "one linear equation, the reduced flux vanishing, plus one linear inequality, the "
        "reduced determinant being positive), and this set is proved to be exactly the set of "
        "parameters making the class multistationary "
        "(`rateMultistationarityRegion_iff_classIsMultistationary`). The correct circuit reading "
        "is proved: the reduced determinant is the difference of the two *directional fluxes* of "
        "the circuit (`reducedDerivOf_eq_forward_sub_backward`), the circuits of a rank-one "
        "network are *pairs* of oppositely oriented reactions (`rankOne_circuit_is_pair`), and "
        "the region condition is a comparison of two products of rate constants with "
        "monomial-derivative factors (`reducedDerivOf_pos_iff_two_reaction_circuit`). The "
        "proposed *single-product* reading is refuted by proof: the rank-one reduced determinant "
        "is an **affine** functional of the rate constants whereas a product is multilinear, so "
        "it is not a constant times a product of powers of the rates "
        "(`CRNT.Network.not_eq_rateProduct_mul`).",
    ),
    "C2": (
        [
            "CRNT.Computation.Semilinear",
            "CRNT.Computation.semilinear_of_affine",
            "CRNT.Computation.affineCRN_stablyComputes",
            "CRNT.Computation.output_conserving_semilinear",
            "CRNT.Computation.not_semilinear_pow2",
            "CRNT.Computation.MinAffine.minAffineCRN_stablyComputes",
            "CRNT.Computation.MinAffine.minList_semilinear",
        ],
        " The **semilinear characterization** is now formalized in the *piecewise affine over "
        "linear regions* form: a function `f : ℕ^d → ℕ` is **semilinear** if it is given by "
        "finitely many affine pieces on finitely many polyhedral regions "
        "(`CRNT.Computation.Semilinear`); the class is closed under `+`, `min` and `k·`; every "
        "affine function is semilinear **and stably computable** (an explicit reaction network "
        "`affineCRN_stablyComputes` computes `x ↦ a + ∑ m_j x_j`, proved with a new "
        "linear-invariant calculus on configurations); and `2^n` is **not** semilinear "
        "(`not_semilinear_pow2`). In the necessity direction: a stable computation pins the "
        "output of every terminal reachable configuration, and for an output-conserving "
        "network with affine input the computed function is affine, hence semilinear "
        "(`output_conserving_semilinear`). The full Chen–Doty–Soloveichik theorem (every "
        "semilinear function is stably computable, and every stably computable function is "
        "semilinear for arbitrary networks) remains open; the definition used here is weaker "
        "than Presburger semilinearity (no congruences) and this is stated in the module "
        "docstring. The **realization direction** is now proved for the min-of-affine class: the "
        "pointwise minimum of finitely many affine maps on `ℕ^d` is computed by an explicit "
        "reaction network (`CRNT.Computation.MinAffine.minAffineCRN_stablyComputes`), the "
        "selection being realized by consumption, with the correctness proof carried by the "
        "repository's linear-invariant calculus on configurations; the min of a list of affine "
        "maps is semilinear (`minList_semilinear`).",
    ),
    "A3": (
        [
            "CRNT.CircuitDescartes.signVariations",
            "CRNT.CircuitDescartes.card_zeros_exp_sum_le",
            "CRNT.CircuitDescartes.card_pos_roots_exp_le_signVariations",
            "CRNT.Circuit.card_circuit_solutions_le_signVariations",
            "CRNT.ExcludedCircuit.card_excludedCircuit_pos_le_one",
            "CRNT.ExcludedCircuit.card_circuitSystem_pos_le_one",
            "CRNT.ExcludedCircuit.card_ray_solutions_le_signVariations",
            "CRNT.ExcludedCircuit.card_common_pos_roots_le_mixedVolume",
        ],
        " The sign-variation count needed for the Bihan–Dickenstein refinement is now defined "
        "and proved to skip zeros (`CRNT.CircuitDescartes.signVariations`), and the "
        "**generalized Descartes rule is proved**: the number of distinct real zeros of an "
        "exponential sum `∑ c_k e^{w_k t}` with `w` strictly increasing is at most the number "
        "of sign variations of the coefficients "
        "(`CRNT.CircuitDescartes.card_zeros_exp_sum_le`), hence the number of positive roots of "
        "`∑ c_k y^{w_k}` is at most the sign variations "
        "(`card_pos_roots_exp_le_signVariations`). The proof is the classical "
        "Budan–Fourier/Rolle induction; the missing `−1` comes from the end signs of the "
        "shifted sum. Applied to circuits, the number of positive solutions of a circuit system "
        "is bounded by the sign variations of the numerator polynomial "
        "(`CRNT.Circuit.card_circuit_solutions_le_signVariations`), which is at most `n + 1` and "
        "strictly smaller when the numerator has few sign changes; the bound is attained "
        "(`1 + y − y²` has exactly one positive root). Still missing: the row-wise "
        "Bihan–Dickenstein bound and the BKK mixed volumes. The **excluded-circuit** bound is "
        "now proved: under the substitution `x_s = z_s^{σ_s}` the system becomes equivalent to a "
        "monotone one, the exclusion condition being exactly that all twisted reaction vectors "
        "have positive coordinate sum, and a square system supported on a circuit has **at most "
        "one positive solution** "
        "(`CRNT.ExcludedCircuit.card_excludedCircuit_pos_le_one`, "
        "`card_circuitSystem_pos_le_one`); the ray form gives the sign-variation bound "
        "(`card_ray_solutions_le_signVariations`). The **mixed volume** is introduced for "
        "intervals (`CRNT.ExcludedCircuit.mixedVolumeIntervals`, with the volume polynomial and "
        "the Minkowski-sum identity) and the BKK bound is proved in the one- and two-variable "
        "cases (`card_pos_roots_le_natDegree`, `card_common_pos_roots_le_mixedVolume`). A scope "
        "caveat is recorded in the module docstring: in the `n+2`-monomial framework the bound "
        "`1` does not hold (the repository's own example has two positive roots and its "
        "reaction vectors are excluded), so the bound is stated for the *linear* circuit system.",
    ),
    "S20": (
        [
            "CRNT.Network.nilpotent_jacobian_eq_zero_of_complexBalanced",
            "CRNT.Network.unique_complexBalanced_of_nilpotent_jacobian",
            "CRNT.Network.not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction",
            "CRNT.Network.exists_unique_isComplexBalanced_in_positiveClass_of_nilpotent_jacobian",
        ],
        " The **nilpotent-Jacobian criterion** is formalized: at a positive complex-balanced "
        "equilibrium the Horn–Jackson sum-of-squares identity makes the quadratic form of the "
        "Jacobian nonpositive, and a nilpotent matrix with everywhere nonpositive quadratic form "
        "is zero, so the Jacobian vanishes "
        "(`CRNT.Network.nilpotent_jacobian_eq_zero_of_complexBalanced`); the sum of squares then "
        "forces every reaction with positive flux to be stoichiometrically null, whence the "
        "uniqueness of the complex-balanced equilibrium in a class "
        "(`unique_complexBalanced_of_nilpotent_jacobian`) and the no-go theorem that a "
        "nontrivial weakly reversible network never has a nilpotent Jacobian at a positive "
        "complex-balanced equilibrium "
        "(`not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction`). The spectral form "
        "of the classical argument (the eigenvalues of the Jacobian being the negatives of the "
        "eigenvalues of the weighted adjacency matrix) is not formalized: the repository has no "
        "eigenvalue theory for mass-action Jacobians.",
    ),
    "M7": (
        [
            "CRNT.Network.doaFeasible_implies_capacity",
            "CRNT.Network.capacity_implies_doaFeasible",
            "CRNT.Network.hasMultistationarityCapacity_iff_doaFeasible",
            "CRNT.Network.rankOne_hasMultistationarityCapacity_iff",
            "CRNT.Network.oneRxn_doaFeasible_iff",
            "CRNT.Network.doaAffirmsCapacity_iff_nonempty_run",
            "CRNT.Network.doaRun_hasMultistationarityCapacity",
            "CRNT.Network.doaRun_doaFeasible",
            "CRNT.Network.capacity_implies_doaShelfFluxes",
        ],
        " The **correctness of the Deficiency One Algorithm is now proved in both directions**: "
        "the algorithm's system (`DOAFeasible`: a log-ratio `μ` and a flux `α` with the lower "
        "and upper balance equations and the sign compatibility with the stoichiometric "
        "subspace) is feasible **iff** the network has multistationarity capacity "
        "(`CRNT.Network.hasMultistationarityCapacity_iff_doaFeasible`), so the algorithm "
        "*decides* the capacity. For a rank-one network the two balance equations collapse to "
        "two scalar equations and the algorithm's linear inequality system reduces to the "
        "single inequality `⟨v, μ⟩ ≠ 0` "
        "(`CRNT.Network.rankOne_hasMultistationarityCapacity_iff`). For the fully open "
        "one-reaction network the test is feasible exactly when `∑_{b_i>a_i} a_i > 1` "
        "(`CRNT.Network.oneRxn_doaFeasible_iff`), a complete correctness statement for that "
        "family. Still missing: the *presentation* of the algorithm (the shelf/confluence "
        "enumeration of `CRNT.Deficiency.DeficiencyOneAlgorithm`) and its connection to the "
        "numerical version, and the analogous correctness of the Advanced Deficiency Algorithm "
        "(leaf M8). The **presentation** of the algorithm is now bridged to the semantic "
        "criterion: the repository's verdict `CRNT.Network.DOAAffirmsCapacity` is the "
        "existence of a run (a shelf partition, a cut-space confluence vector, a sign-compatible "
        "log-ratio) `CRNT.Network.doaAffirmsCapacity_iff_nonempty_run`, and a run together with "
        "the shelf-wise confluence vectors gives multistationarity "
        "(`CRNT.Network.doaRun_hasMultistationarityCapacity`), so the *presented* algorithm is "
        "correct in the algorithmic direction (`doaRun_doaFeasible`). Still missing: the "
        "multi-shelf converse (a capacity flux always decomposes into shelf-wise confluence "
        "vectors) and the numerical version of the algorithm.",
    ),
    "M11": (
        [
            "CRNT.Network.TwoRxnIsAtom",
            "CRNT.Network.twoRxnOpen_isAtom_iff",
            "CRNT.Network.twoRxnOpen_revPair_multistationary_iff",
            "CRNT.Network.twoRxnOpen_revPair_not_atom",
        ],
        " The **two-reaction atom criterion** is now formalized: for the fully open network "
        "with two non-flow reactions `a → b` and `c → d`, the network is an atom of "
        "multistationarity iff it is multistationary and neither reaction alone is "
        "(`CRNT.Network.twoRxnOpen_isAtom_iff`); the reversible-pair case is treated "
        "completely (multistationarity criterion and “never an atom”). Three concrete "
        "instances are checked, and *two proposed criteria are refuted by proof*: the "
        "“crossing reaction vectors” criterion is false in the fully open setting (a crossing "
        "pair can be monostationary) and so is its converse (a non-crossing pair can be "
        "multistationary). The remaining gap is a closed-form necessary-and-sufficient "
        "condition for two irreversible reactions, which does not exist in the literature "
        "(Joshi–Shiu settle it by computer-assisted enumeration).",
    ),
    "D16": (
        [
            "CRNT.Hopf.quadForm_expansion",
            "CRNT.Hopf.cubicForm_expansion",
            "CRNT.Hopf.cubicCombination_eq",
            "CRNT.Hopf.classical_lyapunov_formula",
            "CRNT.Hopf.classical_lyapunov",
            "CRNT.Hopf.hopf_lyapunov_calibration",
        ],
        " The **Guckenheimer–Holmes calibration is now proved**: the complex Taylor "
        "coefficients of a planar field are related to the real partial derivatives by "
        "explicit expansions (`CRNT.Hopf.quadForm_expansion`, `cubicForm_expansion`), the "
        "cubic combination satisfies `f_xxx + f_xyy + g_xxy + g_yyy = 16 Re c₂₁` "
        "(`cubicCombination_eq`), and the **classical first Lyapunov coefficient formula** "
        "with the *original* real partials is proved "
        "(`CRNT.Hopf.classical_lyapunov_formula`, `classical_lyapunov`); the repository's "
        "`lyapunovFromPartials_eq` is then applied to discharge the calibration "
        "(`CRNT.Hopf.hopf_lyapunov_calibration`). The remaining gap is the `O(R⁴)` remainder "
        "for a general reduced field and the mass-action verdict on a sustained periodic "
        "orbit.",
    ),
    "E2": (
        [
            "CRNT.ReactionDiffusion.exists_reactionDiffusion_solution",
            "CRNT.ReactionDiffusion.reactionDiffusionField_lipschitz",
            "CRNT.ReactionDiffusion.reactionDiffusionField_hasDerivAt_curve_matrix",
            "CRNT.ReactionDiffusion.brusselator_turing_instance",
            "CRNT.ReactionDiffusion.brusselator_turing_instance_mode",
        ],
        " The **semidiscrete (method of lines)** reading of the reaction–diffusion system is "
        "now formalized: the box Laplacian, the semidiscrete field "
        "`ẋ = D Δ_h x + f(x)`, its Lipschitz constant, **local existence** by "
        "Picard–Lindelöf (`CRNT.ReactionDiffusion.exists_reactionDiffusion_solution`), the "
        "semidiscrete Jacobian together with the identification of the Jacobian with the "
        "linearization (`reactionDiffusionField_hasDerivAt_curve_matrix`), the connection to "
        "the library's Turing criterion through the mode matrix, and a **genuine Brusselator "
        "instance** (`A = 3`, `B = 2`, diffusion ratio `64`) with the explicit unstable "
        "wavenumber `55/128` (`brusselator_turing_instance`, "
        "`brusselator_turing_instance_mode`). Still missing: PDE well-posedness, weak/strong "
        "solutions and pattern selection (Mathlib has no PDE theory); only the local existence "
        "of the semidiscrete ODE is proved.",
    ),
    "E3": (
        [
            "CRNT.Network.delayLyapunov_deriv_neg_of_not_steady",
            "CRNT.Network.delayLyapunov_deriv_eq_zero_iff",
            "CRNT.Network.delay_limit_isSteadyState",
            "CRNT.Network.delay_semistability",
        ],
        " The **semistability** of delay mass-action systems is now formalized: the exact zero "
        "set of the derivative of the Lyapunov–Krasovskii functional is the ratio condition "
        "(`CRNT.Network.delayLyapunov_deriv_eq_zero_iff`), the functional decreases strictly "
        "whenever that condition fails "
        "(`delayLyapunov_deriv_neg_of_not_steady`), every limit of a delay solution is a "
        "mass-action steady state (`delay_limit_isSteadyState`), and a precompact solution "
        "whose ω-limit set is a singleton converges to that steady state "
        "(`CRNT.Network.delay_semistability`). Still missing: existence theory for delay "
        "systems and the delayed-class LaSalle invariance principle (there is no semiflow in "
        "the library), and the uniqueness of the limiting equilibrium.",
    ),
    "A4": (
        [
            "CRNT.Network.tropicalOrder",
            "CRNT.Network.IsTropicalEquilibration",
            "CRNT.Network.tropicalReduced",
            "CRNT.Network.tropicalReduced_mem",
            "CRNT.Network.tropicalReduced_species_eq",
            "CRNT.Network.tropicalLeadingSystem",
            "CRNT.Network.leadingSystem_eq_reduced_of_equilibration",
            "CRNT.TropicalReductionInstance.ex_species_eq",
            "CRNT.tikhonov_local",
            "CRNT.tikhonov_local_attraction",
            "CRNT.exists_local_slow_manifold",
            "CRNT.hurwitz_linear_decay",
            "CRNT.fast_deviation_le_local",
        ],
        " The tropical reduction procedure of Samal et al. is now formalized: the tropical order "
        "of a reaction at a valuation (`tropicalOrder`), the equilibration condition "
        "(`IsTropicalEquilibration`), the reduced network consisting of the tropically minimal "
        "reactions (`tropicalReduced`), the fact that the reduction loses no species "
        "(`tropicalReduced_species_eq`), and that the leading system of the full network at an "
        "equilibration is the leading system of the reduced network "
        "(`leadingSystem_eq_reduced_of_equilibration`). Instance: a two-reaction network. "
        "**Tikhonov's theorem without a global contraction hypothesis** is now formalized "
        "for the local (Hurwitz) version: the exponential decay of the linearized fast system "
        "(`CRNT.hurwitz_linear_decay`), the local one-sided contraction of the nonlinear fast "
        "field implied by a Hurwitz linearization, the `ε`-scaled frozen system and its "
        "collapse to the slow manifold as `ε → 0⁺` (`CRNT.tikhonov_local_attraction`), the "
        "existence, uniqueness and `C¹` regularity of the local slow manifold by the implicit "
        "function theorem (`CRNT.exists_local_slow_manifold`), and the coupled estimate "
        "under a *local* contraction hypothesis (`CRNT.fast_deviation_le_local`). Instance: "
        "the Michaelis–Menten fast subsystem. Still missing: the passage from the frozen "
        "system to the full coupled system (the tube hypothesis), the slow error, and the "
        "`ε`-dependent Fenichel manifold.",
    ),
    "E3": (
        [
            "CRNT.NonIsothermal.isothermal_species_eq_massAction",
            "CRNT.NonIsothermal.isothermal_temperature_constant",
            "CRNT.NonIsothermal.coupledField_isothermal_restriction",
            "CRNT.NonIsothermal.temperatureEquation_eq_neg_sum_heat",
            "CRNT.NonIsothermal.heatRelease_nonneg_of_nonneg_enthalpies",
            "CRNT.NonIsothermal.totalMass_conserved",
            "CRNT.NonIsothermal.V_iso_derivative_nonpos",
            "CRNT.NonIsothermal.arrhenius_pos",
            "CRNT.NonIsothermal.arrhenius_isothermal_reduction",
            "CRNT.Network.gibbsFreeEnergy_rateOfChange",
            "CRNT.Network.chemicalAffinity_eq_zero_iff_conservationLaw",
            "CRNT.Network.gibbsFreeEnergy_dissipation_eq_sum_squares",
            "CRNT.Network.gibbsFreeEnergy_dissipation_nonneg_of_consistentChemicalPotentials",
        ],
        " Non-isothermal (temperature-dependent) kinetics are now formalized: the coupled "
        "species/temperature field (`coupledField`), the reduction to the isothermal mass-action "
        "system at a fixed temperature (`isothermal_species_eq_massAction`, "
        "coupledField_isothermal_restriction`), the energy balance "
        "(`temperatureEquation_eq_neg_sum_heat`) and its sign when the reaction enthalpies are "
        "nonnegative (`heatRelease_nonneg_of_nonneg_enthalpies`), the conservation of the "
        "total molecule number (`totalMass_conserved`), and an Arrhenius instance "
        "(`arrhenius_pos`, `arrhenius_isothermal_reduction`). The isothermal pseudo-Helmholtz "
        "function is nonincreasing along the isothermal flow of a detailed-balanced network "
        "(`V_iso_derivative_nonpos`). Still missing: the joint non-isothermal Lyapunov "
        "function, existence theory and semistability for the delayed systems. The **Gibbs free "
        "energy with standard chemical potentials** is now formalized: the chemical affinity of a "
        "reaction (`CRNT.Network.chemicalAffinity`), De Donder's identity for the rate of change "
        "of the free energy (`gibbsFreeEnergy_rateOfChange`), the equivalence between a vanishing "
        "affinity and a conservation law (`chemicalAffinity_eq_zero_iff_conservationLaw`), the "
        "stationarity of the free energy at a complex-balanced equilibrium for *every* choice of "
        "chemical potentials, and the classical dissipation formula "
        "`−dG/dt = ½ ∑_r κ_r A_r² x^{y_r}` under the local detailed-balance hypothesis "
        "(`gibbsFreeEnergy_dissipation_eq_sum_squares`), whose nonnegativity is linked to the "
        "entropy production of leaf E1 "
        "(`gibbsFreeEnergy_dissipation_nonneg_of_consistentChemicalPotentials`).",
    ),
}

NAME = re.compile(r"`([A-Za-z_][\w.']*)`")


def split_row(row: str) -> list[str]:
    """Split a table row into fragments, treating `|` inside code spans as text."""
    out: list[str] = []
    cur: list[str] = []
    in_code = False
    for ch in row:
        if ch == "`":
            in_code = not in_code
            cur.append(ch)
        elif ch == "|" and not in_code:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def main() -> int:
    lines = open(MAP, encoding="utf-8").read().split("\n")
    changed = False
    for i, line in enumerate(lines):
        if not line.startswith("|"):
            continue
        frags = split_row(line)
        if len(frags) < 6:
            continue
        leaf = frags[1].strip() if len(frags) > 1 else ""
        if leaf not in UPDATES:
            continue
        names, note = UPDATES[leaf]
        # The Lean column is the fragment holding the declaration names: it is the
        # third data cell (index 4 counting the leading empty fragment).
        lean_idx = 4
        while lean_idx < len(frags) and not NAME.search(frags[lean_idx]):
            lean_idx += 1
        if lean_idx >= len(frags):
            print(f"{leaf}: no Lean column found", file=sys.stderr)
            continue
        added = [n for n in names if f"`{n}`" not in frags[lean_idx]]
        if added:
            frags[lean_idx] = frags[lean_idx].rstrip() + ", " + ", ".join(f"`{n}`" for n in added)
            print(f"{leaf}: +{len(added)} declarations")
        note = note.strip()
        # Strip a previously inserted (mis-placed) copy of the note.  The note is keyed on
        # its first 60 characters, so that a later, longer version of the same note
        # replaces the earlier one instead of being appended to it.
        key = note[:60]
        frags = [f.replace(key, "") for f in frags]
        note = key + note[len(key):]
        row = "|".join(frags)
        row = row.rstrip()
        if not row.endswith("|"):
            row += " |"
        row = row[:-1].rstrip() + note + " |"
        lines[i] = row
        changed = True
    if not changed:
        print("no leaf rows updated")
        return 1
    open(MAP, "w", encoding="utf-8").write("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
