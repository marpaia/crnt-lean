import CRNT.Theorems.DeficiencyOne.JacobianKernel
import CRNT.Kinetics.MassActionJacobian

/-!
# The mass-action Jacobian on the stoichiometric subspace

This module packages the Jacobian restriction and its nonsingularity under the classical
deficiency-one hypotheses, independently of the degree construction.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restriction of the mass-action Jacobian to the stoichiometric tangent space.
The image lies in `S` because every reaction-vector contribution lies in `S`. -/
noncomputable def massActionJacobianOnStoich
    (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.stoichSubspace →ₗ[ℝ] N.stoichSubspace :=
  (N.massActionJacobianCLM κ x).toLinearMap.domRestrict N.stoichSubspace |>.codRestrict
    N.stoichSubspace (by
      intro v
      change N.massActionJacobianCLM κ x v.1 ∈ N.stoichSubspace
      simp only [massActionJacobianCLM, sum_apply,
        ContinuousLinearMap.smulRight_apply]
      exact Submodule.sum_mem _ (fun r _ =>
        Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)))

/-- Under the classical deficiency-one hypotheses, the Jacobian at any positive steady state
is injective on the stoichiometric subspace. -/
theorem deficiencyOne_jacobianOnStoich_injective
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    Function.Injective (N.massActionJacobianOnStoich κ x) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  apply N.massActionJacobianCLM_eq_zero_of_mem_stoich_of_deficiencyOne h κ hx hss v.2
  have hh := congrArg Subtype.val hv
  simpa [massActionJacobianOnStoich] using hh

/-- Equivalent kernel statement. -/
theorem deficiencyOne_jacobianOnStoich_ker_eq_bot
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    LinearMap.ker (N.massActionJacobianOnStoich κ x) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (N.deficiencyOne_jacobianOnStoich_injective h κ hx hss)

/-- The restricted Jacobian determinant is nonzero at every positive steady state. -/
theorem deficiencyOne_jacobianOnStoich_det_ne_zero
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    LinearMap.det (N.massActionJacobianOnStoich κ x) ≠ 0 := by
  have hinj : Function.Injective (N.massActionJacobianOnStoich κ x) :=
    N.deficiencyOne_jacobianOnStoich_injective h κ hx hss
  have hsurj : Function.Surjective (N.massActionJacobianOnStoich κ x) :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : N.stoichSubspace ≃ₗ[ℝ] N.stoichSubspace :=
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have hunit := e.isUnit_det'
  have hcoe : (e : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace)
      = N.massActionJacobianOnStoich κ x := rfl
  rw [hcoe] at hunit
  exact hunit.ne_zero

end Network
end CRNT
