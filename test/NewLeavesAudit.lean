import CRNT.Identifiability.RateConstants
import CRNT.Kinetics.Hill
import CRNT.Extensions.Turing
import CRNT.Equilibria.OneSpeciesDescartes
import CRNT.Equilibria.ToricSteadyStates
import CRNT.Computation.StableComputation
import CRNT.Design.Antithetic
import CRNT.Dynamics.Contraction
import CRNT.Kinetics.SignVectorCriterion
import CRNT.Translation.LinearConjugacyCharacterization

#print axioms CRNT.Complex.sum_massActionMonomial_eq_zero
#print axioms CRNT.Network.massActionVectorField_eqOn_positive_iff
#print axioms CRNT.Network.rateConstants_identifiable_iff
#print axioms CRNT.Network.hillKinetics
#print axioms CRNT.Network.hillKinetics_rate_le
#print axioms CRNT.Network.hillKinetics_rate_pos
#print axioms CRNT.Network.michaelisMentenKinetics_rate
#print axioms CRNT.Turing.diffusionDrivenInstability_iff
#print axioms CRNT.Turing.exists_nonHurwitz_mode_iff
#print axioms CRNT.Turing.no_instability_of_equal_diffusion
#print axioms CRNT.Turing.opposite_signs
#print axioms CRNT.Turing.exists_growing_mode
#print axioms CRNT.Turing.fourierMode_unbounded
#print axioms CRNT.Network.card_positiveSteadyStates_le_signVariations
#print axioms CRNT.Network.positiveSteadyState_unique_of_signVariations_le_one
#print axioms CRNT.Network.toricSteadyState_iff_log_orthogonal
#print axioms CRNT.Network.toricSteadyState_iff_exp_parametrization
#print axioms CRNT.Network.HasToricSteadyStates.geomMean
#print axioms CRNT.Computation.stablyComputes_of_terminating
#print axioms CRNT.Computation.minCRN_stablyComputes
#print axioms CRNT.Computation.addCRN_stablyComputes
#print axioms CRNT.Computation.scaleCRN_stablyComputes
#print axioms CRNT.Computation.maxCRN_stablyComputes

#print axioms Polynomial.signVariations_le_card_support_sub_one
#print axioms CRNT.Network.card_positiveSteadyStates_le_numSources
#print axioms CRNT.Network.positiveSteadyState_unique_of_numSources_le_two
#print axioms CRNT.logAffine_affine_injective_iff
#print axioms CRNT.signCondition_of_orthogonal
#print axioms CRNT.signCondition_iff_signCompatible
#print axioms CRNT.exists_two_points_of_not_signCompatible

#print axioms CRNT.Network.massActionLinearlyConjugate_iff
#print axioms CRNT.Network.massActionLinearlyConjugate_of_eqOn_positive
#print axioms CRNT.Network.dynamicallyEquivalent_iff_sourceWeightedSum_eq

/-! Non-vacuity of the Turing criterion: a concrete activator–inhibitor Jacobian
`J = [[1, -2], [3, -4]]` (trace `-3`, det `2`) with `d₁ = 1`, `d₂ = 20`. -/
example : 0 < (20:ℝ) * 1 + 1 * (-4) ∧
    4 * 1 * 20 * ((1:ℝ) * (-4) - (-2) * 3) < ((20:ℝ) * 1 + 1 * (-4)) ^ 2 := by norm_num

example : ∃ μ k v₁ v₂ : ℝ, 0 < μ ∧ (v₁ ≠ 0 ∨ v₂ ≠ 0) ∧ ∀ t x : ℝ,
    HasDerivAt (fun t => CRNT.Turing.fourierMode μ k v₁ t x)
        (1 * deriv (deriv (fun x => CRNT.Turing.fourierMode μ k v₁ t x)) x +
          1 * CRNT.Turing.fourierMode μ k v₁ t x + (-2) * CRNT.Turing.fourierMode μ k v₂ t x) t ∧
      HasDerivAt (fun t => CRNT.Turing.fourierMode μ k v₂ t x)
        (20 * deriv (deriv (fun x => CRNT.Turing.fourierMode μ k v₂ t x)) x +
          3 * CRNT.Turing.fourierMode μ k v₁ t x + (-4) * CRNT.Turing.fourierMode μ k v₂ t x) t :=
  CRNT.Turing.exists_growing_mode (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

#print axioms CRNT.Network.observableGenerator_maxRPACharge
#print axioms CRNT.Network.stochastic_maxRPA_mean
#print axioms CRNT.Antithetic.closedLoop_deterministic_setpoint
#print axioms CRNT.Antithetic.closedLoop_stochastic_setpoint
#print axioms CRNT.Contraction.dist_le_exp_of_contracting
#print axioms CRNT.Contraction.tendsto_of_contracting
#print axioms CRNT.Contraction.tendsto_equilibrium_of_contracting
#print axioms CRNT.Contraction.equilibrium_unique_of_contracting

/-! ## Non-vacuity: identifiability -/

namespace NewLeavesAudit
open CRNT

/-- Two parallel copies of `∅ → A`. -/
def parallelNet : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun _ => ⟨![0], ![1]⟩⟩

/-- Parallel reactions destroy identifiability. -/
example : ¬ (∀ κ κ' : parallelNet.RateConstants,
    (∀ x : Concentration (Fin 1), x.Positive →
      parallelNet.massActionVectorField κ x = parallelNet.massActionVectorField κ' x) →
      κ.k = κ'.k) := by
  rw [Network.rateConstants_identifiable_iff]
  intro h
  have hinj := (h ![0]).injective
  have h0 : (parallelNet.reaction (0 : Fin 2)).source = ![0] := rfl
  have h1 : (parallelNet.reaction (1 : Fin 2)).source = ![0] := rfl
  have := congrArg (fun r => (r.1 : Fin 2)) (@hinj ⟨(0 : Fin 2), h0⟩ ⟨(1 : Fin 2), h1⟩ rfl)
  have hne : ((0 : Fin 2) : Fin 2) ≠ 1 := by decide
  exact hne this

/-! ## Non-vacuity: toric steady states for `A ⇌ B` -/

/-- `A → B` (reaction `0`) and `B → A` (reaction `1`). -/
def revNet : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨![1, 0], ![0, 1]⟩
    else ⟨![0, 1], ![1, 0]⟩⟩

theorem revNet_r0 : revNet.reaction (0 : Fin 2) = ⟨![1, 0], ![0, 1]⟩ := rfl
theorem revNet_r1 : revNet.reaction (1 : Fin 2) = ⟨![0, 1], ![1, 0]⟩ := rfl
theorem revNet_sum (g : revNet.R → ℝ) : ∑ r, g r = g (0 : Fin 2) + g (1 : Fin 2) :=
  Fin.sum_univ_two g

theorem revNet_steady_iff (κ : revNet.RateConstants) (x : Concentration (Fin 2)) :
    revNet.IsMassActionSteadyState κ x ↔
      κ.k (0 : Fin 2) * x 0 = κ.k (1 : Fin 2) * x 1 := by
  rw [Network.isMassActionSteadyState_iff]
  simp only [revNet_sum, Network.massActionRate, Network.reactionVector_apply, revNet_r0,
    revNet_r1, Complex.massActionMonomial, Fin.prod_univ_two, Fin.forall_fin_two]
  simp
  constructor
  · intro h; linarith [h.1]
  · intro h; constructor <;> linarith

theorem revNet_toric (κ : revNet.RateConstants) : revNet.HasToricSteadyStates κ := by
  refine ⟨1, fun _ => ![1, 0], fun _ => ![0, 1], fun _ => κ.k (1 : Fin 2) / κ.k (0 : Fin 2),
    fun _ => div_pos (κ.positive _) (κ.positive _), fun x _ => ?_⟩
  rw [revNet_steady_iff]
  simp only [Complex.massActionMonomial, Fin.prod_univ_two, Fin.forall_fin_one]
  simp
  have h0 := (κ.positive (0 : Fin 2)).ne'
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

/-- A concrete use of the geometric-mean closure. -/
example (κ : revNet.RateConstants) {x z : Concentration (Fin 2)} (hx : x.Positive)
    (hz : z.Positive) (hxs : revNet.IsMassActionSteadyState κ x)
    (hzs : revNet.IsMassActionSteadyState κ z) :
    revNet.IsMassActionSteadyState κ (fun s => x s ^ (1/2 : ℝ) * z s ^ (1 - 1/2 : ℝ)) :=
  Network.HasToricSteadyStates.geomMean revNet κ (revNet_toric κ) hx hz hxs hzs _

end NewLeavesAudit
