#!/usr/bin/env python3
"""Second round of field-map updates: the declarations of the campaign modules
integrated after the first round.

Same mechanism as `update_field_map.py`: append the new declarations to the
*Lean* column of the leaf and append a Notes paragraph.
"""
from __future__ import annotations

import re
from pathlib import Path

MAP = Path(__file__).resolve().parent.parent.parent / "docs" / "field-map.md"

UPDATES: dict[str, tuple[list[str], str]] = {
    "F13": ([
        "CRNT.Network.open_conservationLawSpace",
        "CRNT.Network.mem_orthSum_openStoichSubspace_iff",
        "CRNT.Network.open_weightedTotal_const_along_solution",
        "CRNT.Network.finrank_openConservationLawSpace",
        "CRNT.Network.open_conservationLaw_eq_bot_iff",
    ], """**2026-10-21 (campaign): the conservation laws of an open system with an arbitrary
inflow.**  The general theory is now formalized (Mizoguchi 2020; Feinberg 2019 ch. 10): the open
field is the mass-action field plus the constant inflow, the open stoichiometric subspace is
`S(N) ⊔ span{f}`, and the conservation laws of the opened network are exactly
`L(G_f) = L(G) ∩ f^⊥` (`CRNT.Network.open_conservationLawSpace`,
`mem_orthSum_openStoichSubspace_iff`); along a solution of the open system the pairing with such
a law is constant (`open_weightedTotal_const_along_solution`), and the dimension drops by the
rank of `w ↦ ⟨w, f⟩` (`finrank_openConservationLawSpace`). The *uniform* inflow case of the
original leaf is the special case `f` strictly positive in every species. A correction: the
statement "strictly positive inflow ⟹ the open conservation-law space is trivial" is **false**
(the counterexample is in the module: `A → B`, `C → D` with `f = (1,1,1,1)` carries the law
`(1,1,−1,−1)`); the correct criterion is `open_conservationLaw_eq_bot_iff`, and the *nonnegative*
version is true."""),
    "S17": ([
        "CRNT.Network.two_complexBalanced_differ_by_monomial_rescaling",
        "CRNT.Network.isComplexBalanced_of_monomial_rescaling",
        "CRNT.Network.unique_complexBalanced_of_nondegenerate",
        "CRNT.Network.isNondegenerate_iff_injective_reducedJacobian",
        "CRNT.Network.isNondegenerate_iff_strict_dissipation",
    ], """**2026-10-21 (campaign): the isolation criterion and the monomial-rescaling description of
the complex-balanced set.**  Two positive complex-balanced concentrations in one class differ by a
monomial rescaling `x ↦ x·e^u` with `u` in the orthogonal complement of the stoichiometric
subspace (`CRNT.Network.two_complexBalanced_differ_by_monomial_rescaling`), and conversely a
monomial rescaling of a complex-balanced state is complex balanced
(`isComplexBalanced_of_monomial_rescaling`). The nondegeneracy of a complex-balanced equilibrium
is the injectivity of the reduced Jacobian (`isNondegenerate_iff_injective_reducedJacobian`) and
is equivalent to the strict negativity of the dissipation on the stoichiometric subspace
(`isNondegenerate_iff_strict_dissipation`); a nondegenerate equilibrium is the unique
complex-balanced equilibrium of its class (`unique_complexBalanced_of_nondegenerate`). What
remains: the *polytope* form of the Horn–Jackson dichotomy (a finite union indexed by the faces
of a Newton polytope), which needs face combinatorics that Mathlib does not have."""),
    "D4": ([
        "CRNT.Network.relEntropy_ge_quadratic_of_complexBalanced",
        "CRNT.Network.relEntropy_ge_quadratic_in_ball",
        "CRNT.Network.relEntropy_expDecay_along_solution",
        "CRNT.Network.entropyHessianQuadratic_ge_minEigenvalue",
    ], """**2026-10-21 (campaign): the quantitative local stability.**  The relative entropy is
quadratic near a complex-balanced equilibrium (`CRNT.Network.relEntropy_ge_quadratic_of_complexBalanced`,
`relEntropy_ge_quadratic_in_ball`), with the constant given by the smallest eigenvalue of the
Hessian of the relative entropy (`entropyHessianQuadratic_ge_minEigenvalue`), and it therefore
decays exponentially along a solution (`relEntropy_expDecay_along_solution`). The decay carries a
prefactor: removing it needs the *sum-of-squares* form of the entropy dissipation, the
Horn–Jackson identity that the repository does not yet have."""),
    "D14": ([
        "CRNT.Dynamics.operatorNorm_contraction_of_jacobian",
        "CRNT.Dynamics.operatorNorm_unique_fixedPoint",
        "CRNT.Dynamics.markusYamabe_discrete",
        "CRNT.Network.massAction_operatorNorm_contraction",
        "CRNT.Network.massAction_flow_converges_of_operatorNormContraction",
        "CRNT.Network.massAction_kamkeOnSimplicialCone_of_criterion",
        "CRNT.Network.massAction_simplicialCone_preserving_of_criterion",
    ], """**2026-10-21 (campaign): the Markus–Yamabe criterion and the structural criterion for
simplicial-cone monotonicity.**  The operator-norm contraction criterion is now formalized
(`CRNT.Dynamics.operatorNorm_contraction_of_jacobian`), with the uniqueness of the fixed point
(`operatorNorm_unique_fixedPoint`) and the Markus–Yamabe theorem for the discrete map
(`markusYamabe_discrete`); for the mass-action field
(`CRNT.Network.massAction_operatorNorm_contraction`). A correction is recorded and proved by
counterexample: the *flow* version of the criterion (an operator-norm contraction alone forces
exponential attraction to a unique equilibrium) is **false** — the network `X → 2X` has
`‖J‖ = κ < 1` and its trajectory diverges — so the flow statement needs the one-sided
hypothesis that the repository already has (`massAction_flow_converges_of_operatorNormContraction`
carries both). The **structural criterion** for simplicial-cone monotonicity — the analogue of
`massAction_orthant_preserving` for a general cone — is now formalized
(`CRNT.Network.massAction_kamkeOnSimplicialCone_of_criterion`,
`massAction_simplicialCone_preserving_of_criterion`). What remains: the general
cone-monotonicity theory and a Harary-type graph criterion for cones."""),
    "E1": ([
        "CRNT.Network.entropyProduction_minimized_at_detailedBalanced",
        "CRNT.Network.entropyProduction_uniqueMinimizer_inClass",
        "CRNT.Network.gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction",
        "CRNT.Network.relEntropy_isLocalMin_of_complexBalanced",
        "CRNT.Network.relEntropy_isStrictLocalMin_of_complexBalanced",
        "CRNT.Network.complexBalanced_of_relEntropy_gradient_zero",
    ], """**2026-10-21 (campaign): Prigogine's principle in both of its readings.**  The
*entropy-production* form: the entropy production is nonnegative with equality exactly at the
reactionwise detailed-balanced states, and it is minimized — globally and class-wise — at a
detailed-balanced state (`CRNT.Network.entropyProduction_minimized_at_detailedBalanced`,
`entropyProduction_uniqueMinimizer_inClass`), with De Donder's identity
`dG/dt = −σ` (`gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction`). The *free-energy* form:
the pseudo-Helmholtz free energy has a strict local minimum at a complex-balanced equilibrium
(`CRNT.Network.relEntropy_isLocalMin_of_complexBalanced`,
`relEntropy_isStrictLocalMin_of_complexBalanced`), and the critical points of the free energy
along a compatibility class are exactly the complex-balanced states
(`complexBalanced_of_relEntropy_gradient_zero`). A correction: the *global* uniqueness of the
entropy-production minimizer is false — the minimizers form the toric manifold of detailed-balanced
states — so the statement is class-wise."""),
    "M11": ([
        "CRNT.Network.twoReaction_criterionTable_eq_criterion",
        "CRNT.Network.twoReaction_criterionTable_complete",
        "CRNT.Network.twoReaction_atomTable_eq_criterion",
        "CRNT.Network.twoReaction_atomTable_eq_atom",
        "CRNT.Network.twoRxnMultistationary_complete",
        "CRNT.Network.twoReaction_witness_iff_criterion",
    ], """**2026-10-21 (campaign): the criterion table is a proved complete enumeration.**  The
kernel-decided table and the closed-form criterion agree on every one of the 75 members
(`CRNT.Network.twoReaction_criterionTable_eq_criterion`), the table is exactly the set of
multistationary members (`twoReaction_criterionTable_complete`), the atom table is exactly the
set of atom members (`twoReaction_atomTable_eq_atom`), and the existence of two distinct positive
steady states is equivalent to the criterion holding (`twoReaction_witness_iff_criterion`). The
criterion is therefore a **proved exact decision procedure** for multistationarity on this
family. A correction: the table's verdict is a function of the member, not a `Bool`, and the
order of the list differs from the family's, so the correct relation is a permutation."""),
    "P9": ([
        "CRNT.JumpSystem.fluctuation_sq_le_uniform",
        "CRNT.JumpSystem.fluctuation_chebyshev_uniform",
        "CRNT.JumpSystem.fluctuation_sq_le_uniform_scaled",
        "CRNT.Network.fluctuation_uniform_concentration_and_second_moment",
    ], """**2026-10-21 (campaign): the fluctuation-scale uniform-in-time estimate.**  The
second-moment estimate for the jump system is now uniform in the starting state and in the time
(`CRNT.JumpSystem.fluctuation_sq_le_uniform`), with the Chebyshev form
(`fluctuation_chebyshev_uniform`) and the volume-scaled (fluctuation-scale) convention
(`fluctuation_sq_le_uniform_scaled`); the repository's uniform-in-time concentration bound is
recovered with the second-moment content
(`CRNT.Network.fluctuation_uniform_concentration_and_second_moment`). The exact degradation for
an unbounded Lyapunov function is recorded (`fluctuation_sq_le_uniform_unbounded`). What remains:
the path-space statement (the identification of the exit event with the exit mass and the
running-supremum bound), which needs an i.i.d.-exponential measure and the strong Markov
property."""),
    "A3": ([
        "CRNT.MixedVolume.mixedVolume_circuit",
        "CRNT.MixedVolume.card_circuit_solutions_le_mixedVolume",
        "CRNT.MixedVolume.card_common_positive_roots_le_mul_degrees",
        "CRNT.MixedVolume.card_solutions_le_mixedVolume_of_dense",
    ], """**2026-10-21 (campaign): the BKK bound for a circuit system in the mixed-volume form.**  The
mixed volume of the Newton polytopes of a circuit is the normalized volume of the circuit simplex
(`CRNT.MixedVolume.mixedVolume_circuit`), and the BKK bound holds in the case where the Newton
polytopes are simplices (`card_circuit_solutions_le_mixedVolume`); the product-of-degrees Bézout
bound for separated variables is proved (`card_common_positive_roots_le_mul_degrees`,
`card_solutions_le_mixedVolume_of_dense`), with a worked two-species instance where the bound is
attained. A correction is recorded: the naive reading of the BKK bound for an `n+2`-monomial
circuit system is **false** — the Newton polytope of such an equation is the *larger* polytope
`conv(0,w_1,…,w_{n+1})`, so the Bihan bound `n+1` and the mixed volume are different quantities
(the counterexample is in the module). What remains: the general BKK inequality for arbitrary
Newton polytopes, which needs the volume of a general convex body and the BKK inequality itself."""),
    "D18": ([
        "CRNT.Dynamics.fundamentalMatrixTarget",
        "CRNT.Dynamics.exists_variationalFundamental",
        "CRNT.Dynamics.exists_global_solution",
    ], """**2026-10-21 (campaign): the fundamental matrix of the mass-action variational
equation.**  The repository's smooth-dependence target was decomposed into three steps; the
middle one — the fundamental matrix — is now discharged: a linear ODE with continuous
coefficients has a global solution (`CRNT.Dynamics.exists_global_solution`) and the variational
equation of the mass-action flow has a solution (`exists_variationalFundamental`), so
`CRNT.Dynamics.fundamentalMatrixTarget` holds. What remains: the assembly of the Fréchet
derivative of the flow (`Network.DerivativeAssemblyTarget`), which needs the *uniform* modulus
of the Jacobian over the joining segment, and the Jordan separation theorem (out of Mathlib's
reach)."""),
    "C3": ([
        "CRNT.Antithetic.wLyapFamily_no_exponential_drift",
        "CRNT.Antithetic.wLyapSlope_no_exponential_drift",
        "CRNT.Antithetic.wLyap2_no_exponentialDrift_exists",
    ], """**2026-10-21 (campaign): the obstruction to the geometric ergodicity.**  The geometric
ergodicity of the antithetic closed loop would need a Lyapunov function with finite sublevel sets
*and* a strictly negative exponential drift. It is now **proved** that no Lyapunov function of the
piecewise-quadratic shape can have an exponential drift
(`CRNT.Antithetic.wLyapFamily_no_exponential_drift`), and that allowing the `z₂`-slope to depend
on `z₁` does not help (`wLyapSlope_no_exponential_drift`): on the line `z₁ = 0` the drift condition
forces the slope to drop, while on `z₁ = 1` the annihilation forces it not to drop. The
geometric ergodicity of this network is therefore **not** claimed."""),
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
        added = 0
        for d in decls:
            if f"`{d}`" not in lean_col:
                lean_col = lean_col.rstrip() + ", " + f"`{d}`"
                added += 1
        cols[3] = lean_col
        if len(cols) > 5:
            if "2026-10-21 (campaign)" not in cols[5]:
                cols[5] = cols[5].rstrip() + " " + note
        out.append("| " + " | ".join(cols) + " |")
        changed[leaf] = added
    MAP.write_text("\n".join(out), encoding="utf-8")
    for leaf, n in sorted(changed.items()):
        print(f"{leaf}: +{n} declarations")


if __name__ == "__main__":
    main()
