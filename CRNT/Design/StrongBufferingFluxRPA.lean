import CRNT.Design.Localization
import CRNT.Design.MinimalForm

/-!
# Strong buffering structures and flux RPA

This module isolates the linear-response theorem behind the strong-buffering result of
Hong--Moon--Hirono--Kim.  The strong influence index

`λ_f(γ) = -|Vγ| + |Eγ| + dim P⁰_γ(coker S)`

is exactly the dimension defect of a response problem whose only unknowns are the
internal concentration perturbations.  There is no internal cycle variable: the output
of interest is the *total reaction-flux response* itself.

For a parameter perturbation supported on `Eγ`, solve

`J_γ δx = -δr_param`,      `D_γ δx = 0`.

When `λ_f = 0` and the local operator is nonsingular this has a unique solution.  Output
completeness kills `J δx` on exterior reactions, while the parameter forcing itself is
zero there.  Hence the total first-order flux response vanishes on **all** reactions.

This is the coordinate-free algebraic core of flux RPA.  A differentiable steady-state
branch supplies `J` and interprets the result as a derivative with respect to a kinetic
parameter.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The strong-buffering response unknowns are only internal concentration changes. -/
abbrev FluxSensitivityDomain (N : Network S) (γ : StructuralSubnetwork N) :=
  ↥γ.species → ℝ

/-- The equations are internal reaction-rate equations together with the projected
conservation-total equations. -/
abbrev FluxSensitivityCodomain (N : Network S) (γ : StructuralSubnetwork N) :=
  (↥γ.reactions → ℝ) × N.LocalConservationResponse γ

/-- Strong-buffering local response operator `[J_γ; D_γ]`. -/
noncomputable def fluxSensitivityOperator {N : Network S}
    (γ : StructuralSubnetwork N) (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)) :
    N.FluxSensitivityDomain γ →ₗ[ℝ] N.FluxSensitivityCodomain γ where
  toFun dx :=
    (fun r => J (speciesExtension γ.species dx) r.1,
      N.localConservationPairing γ dx)
  map_add' dx dy := by
    apply Prod.ext
    · funext r
      change J ((speciesExtension γ.species) (dx + dy)) r.1 =
        J ((speciesExtension γ.species) dx) r.1 +
          J ((speciesExtension γ.species) dy) r.1
      rw [map_add, map_add]
      rfl
    · ext q
      simp [localConservationPairing, mul_add, Finset.sum_add_distrib]
  map_smul' a dx := by
    apply Prod.ext
    · funext r
      change J ((speciesExtension γ.species) (a • dx)) r.1 =
        a • J ((speciesExtension γ.species) dx) r.1
      rw [map_smul, map_smul]
      rfl
    · ext q
      simp [localConservationPairing, Finset.mul_sum]

/-- Domain dimension of the strong-buffering response problem. -/
theorem finrank_fluxSensitivityDomain (N : Network S)
    (γ : StructuralSubnetwork N) :
    Module.finrank ℝ (N.FluxSensitivityDomain γ) = γ.species.card := by
  simp [FluxSensitivityDomain, Module.finrank_pi]

/-- Codomain dimension of the strong-buffering response problem. -/
theorem finrank_fluxSensitivityCodomain (N : Network S)
    (γ : StructuralSubnetwork N) :
    Module.finrank ℝ (N.FluxSensitivityCodomain γ) =
      γ.reactions.card + N.projectedConservationDim γ := by
  -- Same finite-dimensional duality used in `finrank_localSensitivityCodomain`.
  simpa [FluxSensitivityCodomain] using N.finrank_localSensitivityCodomain γ

/-- **Topological meaning of the strong influence index.** -/
theorem fluxInfluenceIndex_eq_sensitivity_dimension_defect (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.fluxInfluenceIndex γ =
      (Module.finrank ℝ (N.FluxSensitivityCodomain γ) : ℤ) -
        (Module.finrank ℝ (N.FluxSensitivityDomain γ) : ℤ) := by
  rw [N.finrank_fluxSensitivityCodomain γ, N.finrank_fluxSensitivityDomain γ]
  simp [fluxInfluenceIndex]
  ring

/-- `λ_f = 0` iff the strong-buffering response operator is square. -/
theorem fluxInfluenceIndex_eq_zero_iff_equal_sensitivity_dimensions
    (N : Network S) (γ : StructuralSubnetwork N) :
    N.fluxInfluenceIndex γ = 0 ↔
      Module.finrank ℝ (N.FluxSensitivityDomain γ) =
        Module.finrank ℝ (N.FluxSensitivityCodomain γ) := by
  rw [N.fluxInfluenceIndex_eq_sensitivity_dimension_defect γ]
  omega

/-- Under `λ_f = 0`, injectivity upgrades to bijectivity. -/
theorem fluxSensitivity_bijective_of_injective_of_fluxInfluence_zero
    {N : Network S} {γ : StructuralSubnetwork N}
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (hzero : N.fluxInfluenceIndex γ = 0)
    (hinj : Function.Injective (N.fluxSensitivityOperator γ J)) :
    Function.Bijective (N.fluxSensitivityOperator γ J) := by
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((N.fluxInfluenceIndex_eq_zero_iff_equal_sensitivity_dimensions γ).mp hzero)).mp hinj

/-- Embed a perturbation of the rates of reactions in `Eγ` into the full reaction space. -/
abbrev InternalRateForcing {N : Network S} (γ : StructuralSubnetwork N) :=
  ↥γ.reactions → ℝ

/-- Total first-order reaction-flux response: kinetic response to concentration change
plus the direct parameter forcing. -/
def totalFluxResponse {N : Network S} (γ : StructuralSubnetwork N)
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (dx : ↥γ.species → ℝ) (p : N.InternalRateForcing γ) : N.R → ℝ :=
  J (speciesExtension γ.species dx) + reactionExtension γ.reactions p

/-- On an internal reaction, zero local residual is exactly zero total flux response. -/
theorem totalFluxResponse_eq_zero_on_internal_of_local_equation
    {N : Network S} {γ : StructuralSubnetwork N}
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (dx : ↥γ.species → ℝ) (p : N.InternalRateForcing γ)
    (h : ∀ r : ↥γ.reactions,
      J (speciesExtension γ.species dx) r.1 = -p r) :
    ∀ r : ↥γ.reactions, N.totalFluxResponse γ J dx p r.1 = 0 := by
  intro r
  simp [totalFluxResponse, reactionExtension, r.property, h r]

/-- Outside an output-complete subnetwork both pieces of the total flux response vanish. -/
theorem totalFluxResponse_eq_zero_on_exterior
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hJ : N.RespectsReactantSupport J)
    (hout : N.IsOutputComplete γ)
    (dx : ↥γ.species → ℝ) (p : N.InternalRateForcing γ)
    {r : N.R} (hr : r ∉ γ.reactions) :
    N.totalFluxResponse γ J dx p r = 0 := by
  have hkin := N.exterior_rate_response_zero_of_outputComplete hJ hout dx hr
  simp [totalFluxResponse, reactionExtension, hr, hkin]

/-- The forcing vector corresponding to an internal direct rate perturbation, while
keeping conserved totals fixed. -/
def fluxRPAForcing {N : Network S} (γ : StructuralSubnetwork N)
    (p : N.InternalRateForcing γ) : N.FluxSensitivityCodomain γ :=
  (-p, 0)

/-- Solving the strong local response equation gives cancellation of the direct forcing
on every internal reaction. -/
theorem fluxSensitivity_solution_internal_cancellation
    {N : Network S} {γ : StructuralSubnetwork N}
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (p : N.InternalRateForcing γ) (dx : N.FluxSensitivityDomain γ)
    (hsol : N.fluxSensitivityOperator γ J dx = N.fluxRPAForcing γ p) :
    ∀ r : ↥γ.reactions,
      J (speciesExtension γ.species dx) r.1 = -p r := by
  intro r
  have h := congrArg (fun z : N.FluxSensitivityCodomain γ => z.1 r) hsol
  simpa [fluxSensitivityOperator, fluxRPAForcing] using h

/-- **Strong-buffering linear flux-RPA theorem.**

For an output-complete `γ` with `λ_f(γ)=0`, nonsingularity of `[J_γ;D_γ]` implies that
*every* direct kinetic perturbation supported on `Eγ` has a unique compensating internal
concentration response and the total reaction-flux derivative is zero globally.
-/
theorem strongBuffering_fluxRPA_linear
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsStrongBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.fluxSensitivityOperator γ J))
    (p : N.InternalRateForcing γ) :
    ∃! dx : N.FluxSensitivityDomain γ,
      N.fluxSensitivityOperator γ J dx = N.fluxRPAForcing γ p ∧
      N.totalFluxResponse γ J dx p = 0 := by
  have hbij := N.fluxSensitivity_bijective_of_injective_of_fluxInfluence_zero
    J hγ.2 hinj
  rcases hbij.2 (N.fluxRPAForcing γ p) with ⟨dx, hdx⟩
  refine ⟨dx, ⟨hdx, ?_⟩, ?_⟩
  · funext r
    by_cases hr : r ∈ γ.reactions
    · let rr : ↥γ.reactions := ⟨r, hr⟩
      exact N.totalFluxResponse_eq_zero_on_internal_of_local_equation J dx p
        (N.fluxSensitivity_solution_internal_cancellation J p dx hdx) rr
    · exact N.totalFluxResponse_eq_zero_on_exterior hJ hγ.1 dx p hr
  · intro dy hdy
    exact hinj (hdy.1.trans hdx.symm)

/-- The theorem specialized to a single perturbed internal reaction. -/
theorem strongBuffering_singleReaction_fluxRPA_linear
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsStrongBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.fluxSensitivityOperator γ J))
    (r₀ : ↥γ.reactions) (a : ℝ) :
    ∃! dx : N.FluxSensitivityDomain γ,
      N.fluxSensitivityOperator γ J dx =
        N.fluxRPAForcing γ (fun r => if r = r₀ then a else 0) ∧
      N.totalFluxResponse γ J dx (fun r => if r = r₀ then a else 0) = 0 :=
  N.strongBuffering_fluxRPA_linear hγ hJ hinj _

end Network
end CRNT
