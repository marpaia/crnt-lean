import CRNT.Design.EmergentConservation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear-response law of localization

This module formalizes the coordinate-free linear algebra behind the law of localization.
For an output-complete subnetwork `γ`, the local sensitivity system has

* unknowns: internal concentration responses and supported stoichiometric-cycle responses;
* equations: internal reaction-rate responses and projected conservation-law responses.

Its dimension defect is exactly the influence index `λ(γ)`.  Thus `λ = 0` says the
local response problem is square.  If its linearization is nonsingular, every internal
forcing has a unique internal response.  Output completeness guarantees that such an
internal concentration response cannot directly change reaction rates outside `Eγ`.

The analytic theorem in applications supplies nonsingularity of the steady-state
sensitivity operator; all topology and support statements are proved here independently.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A linearized reaction-rate map respects reactant support when a reaction has zero
first-order response to perturbations of species it does not read. -/
def RespectsReactantSupport {N : Network S}
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)) : Prop :=
  ∀ r dx, (∀ s, N.ReactionReadsSpecies r s → dx s = 0) → J dx r = 0

/-- The local response unknowns: internal concentration changes together with a globally
balanced reaction-cycle adjustment supported inside `Eγ`. -/
abbrev LocalSensitivityDomain (N : Network S) (γ : StructuralSubnetwork N) :=
  (↥γ.species → ℝ) × N.supportedCycleSubspace γ

/-- Linear functionals on the projected conservation-law space. -/
abbrev LocalConservationResponse (N : Network S) (γ : StructuralSubnetwork N) :=
  N.projectedConservationSubspace γ →ₗ[ℝ] ℝ

/-- The local response equations: selected reaction-rate equations together with selected
conservation-total equations. -/
abbrev LocalSensitivityCodomain (N : Network S) (γ : StructuralSubnetwork N) :=
  (↥γ.reactions → ℝ) × N.LocalConservationResponse γ

/-- Pair an internal concentration perturbation with each projected conservation law. -/
noncomputable def localConservationPairing (N : Network S)
    (γ : StructuralSubnetwork N) :
    (↥γ.species → ℝ) →ₗ[ℝ] N.LocalConservationResponse γ where
  toFun dx := {
    toFun := fun q => ∑ s : ↥γ.species, q.1 s * dx s
    map_add' := by
      intro q₁ q₂
      simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a q
      simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, mul_assoc,
        RingHom.id_apply, ← Finset.mul_sum] }
  map_add' dx dy := by
    ext q
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' a dx := by
    ext q
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- The local steady-state sensitivity operator associated with a reaction-rate
linearization `J`.  The upper block is `[J_γ  C_γ]`; the lower block is `[D_γ  0]` in
the traditional buffering-structure notation. -/
noncomputable def localSensitivityOperator {N : Network S}
    (γ : StructuralSubnetwork N) (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)) :
    N.LocalSensitivityDomain γ →ₗ[ℝ] N.LocalSensitivityCodomain γ where
  toFun z :=
    (fun r => J (speciesExtension γ.species z.1) r.1 + z.2.1 r.1,
      N.localConservationPairing γ z.1)
  map_add' z w := by
    apply Prod.ext
    · funext r
      change
        J (speciesExtension γ.species (z.1 + w.1)) r.1 +
            ((z.2 + w.2 : N.supportedCycleSubspace γ) : N.R → ℝ) r.1 =
          (J (speciesExtension γ.species z.1) r.1 + z.2.1 r.1) +
            (J (speciesExtension γ.species w.1) r.1 + w.2.1 r.1)
      rw [map_add, map_add]
      simp only [Pi.add_apply, Submodule.coe_add]
      ring
    · exact (N.localConservationPairing γ).map_add z.1 w.1
  map_smul' a z := by
    apply Prod.ext
    · funext r
      change
        J (speciesExtension γ.species (a • z.1)) r.1 +
            ((a • z.2 : N.supportedCycleSubspace γ) : N.R → ℝ) r.1 =
          a • (J (speciesExtension γ.species z.1) r.1 + z.2.1 r.1)
      rw [map_smul, map_smul]
      simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, smul_eq_mul, RingHom.id_apply]
      ring
    · exact (N.localConservationPairing γ).map_smul a z.1

/-- Dimension of the local response domain. -/
theorem finrank_localSensitivityDomain (N : Network S)
    (γ : StructuralSubnetwork N) :
    Module.finrank ℝ (N.LocalSensitivityDomain γ) =
      γ.species.card + N.supportedCycleDim γ := by
  simp [LocalSensitivityDomain, supportedCycleDim, Module.finrank_prod,
    Module.finrank_pi]

/-- Dimension of the local response codomain. -/
theorem finrank_localSensitivityCodomain (N : Network S)
    (γ : StructuralSubnetwork N) :
    Module.finrank ℝ (N.LocalSensitivityCodomain γ) =
      γ.reactions.card + N.projectedConservationDim γ := by
  rw [Module.finrank_prod]
  have hdual : Module.finrank ℝ (N.LocalConservationResponse γ) =
      Module.finrank ℝ (N.projectedConservationSubspace γ) := by
    exact Subspace.dual_finrank_eq
  rw [hdual]
  simp [LocalConservationResponse, projectedConservationDim, Module.finrank_pi]

/-- **Topological meaning of the influence index.**  It is exactly the dimension defect
`dim equations - dim unknowns` of the local sensitivity problem. -/
theorem influenceIndex_eq_sensitivity_dimension_defect (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.influenceIndex γ =
      (Module.finrank ℝ (N.LocalSensitivityCodomain γ) : ℤ) -
        (Module.finrank ℝ (N.LocalSensitivityDomain γ) : ℤ) := by
  rw [N.finrank_localSensitivityDomain γ, N.finrank_localSensitivityCodomain γ]
  simp [influenceIndex]
  ring

/-- Vanishing influence index iff the local sensitivity system is square. -/
theorem influenceIndex_eq_zero_iff_equal_sensitivity_dimensions
    (N : Network S) (γ : StructuralSubnetwork N) :
    N.influenceIndex γ = 0 ↔
      Module.finrank ℝ (N.LocalSensitivityDomain γ) =
        Module.finrank ℝ (N.LocalSensitivityCodomain γ) := by
  rw [N.influenceIndex_eq_sensitivity_dimension_defect γ]
  omega

/-- Under `λ=0`, injectivity of the local response operator is equivalent to bijectivity. -/
theorem localSensitivity_bijective_of_injective_of_influence_zero
    {N : Network S} {γ : StructuralSubnetwork N}
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (hzero : N.influenceIndex γ = 0)
    (hinj : Function.Injective (N.localSensitivityOperator γ J)) :
    Function.Bijective (N.localSensitivityOperator γ J) := by
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℝ (N.LocalSensitivityDomain γ) =
      Module.finrank ℝ (N.LocalSensitivityCodomain γ) :=
    (N.influenceIndex_eq_zero_iff_equal_sensitivity_dimensions γ).mp hzero
  have hrange : LinearMap.range (N.localSensitivityOperator γ J) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact (LinearMap.finrank_range_of_inj hinj).trans hdim
  exact LinearMap.range_eq_top.mp hrange

/-- Output completeness kills the exterior kinetic-coupling block: perturbing only
internal species cannot change the linearized rate of an exterior reaction. -/
theorem exterior_rate_response_zero_of_outputComplete
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hJ : N.RespectsReactantSupport J)
    (hout : N.IsOutputComplete γ)
    (dx : ↥γ.species → ℝ) {r : N.R} (hr : r ∉ γ.reactions) :
    J (speciesExtension γ.species dx) r = 0 := by
  apply hJ r
  intro s hread
  by_cases hs : s ∈ γ.species
  · exact False.elim (hr (hout r s hs hread))
  · simp [speciesExtension, hs]

/-- A local forcing consists of desired reaction-equation and conservation-equation
right-hand sides. -/
abbrev LocalForcing (N : Network S) (γ : StructuralSubnetwork N) :=
  N.LocalSensitivityCodomain γ

/-- **Linear law of localization.**  If `γ` is a buffering structure and the local
steady-state sensitivity operator is injective, every local forcing has a unique local
response.  Its concentration part produces zero direct rate response outside `γ`.

This is the algebraic core of the law of localization.  A differentiable steady-state
branch supplies `J` and interprets this local solution as the derivative with respect to
an internal parameter. -/
theorem lawOfLocalization_linear
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.localSensitivityOperator γ J))
    (b : N.LocalForcing γ) :
    ∃! z : N.LocalSensitivityDomain γ,
      N.localSensitivityOperator γ J z = b ∧
      ∀ r : N.R, r ∉ γ.reactions → J (speciesExtension γ.species z.1) r = 0 := by
  have hbij := N.localSensitivity_bijective_of_injective_of_influence_zero
    J hγ.2 hinj
  rcases hbij.2 b with ⟨z, hz⟩
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · intro r hr
    exact N.exterior_rate_response_zero_of_outputComplete hJ hγ.1 z.1 hr
  · intro w hw
    exact hinj (hw.1.trans hz.symm)

/-- Strong buffering makes the local equation count smaller by exactly the supported-cycle
space; equivalently, the ordinary local sensitivity defect is `-dim cycles`. -/
theorem strongBuffering_sensitivity_dimension_defect
    (N : Network S) {γ : StructuralSubnetwork N}
    (hγ : N.IsStrongBufferingStructure γ) :
    (Module.finrank ℝ (N.LocalSensitivityCodomain γ) : ℤ) -
      (Module.finrank ℝ (N.LocalSensitivityDomain γ) : ℤ) =
        -(N.supportedCycleDim γ : ℤ) := by
  rw [← N.influenceIndex_eq_sensitivity_dimension_defect γ]
  exact N.influenceIndex_eq_neg_supportedCycleDim_of_strong hγ

end Network
end CRNT
