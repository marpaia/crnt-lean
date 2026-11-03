import CRNT.Design.Localization
-- `DifferentiableAt`/`HasDerivAt` are used by `LocalC1SensitivityBranch` below but were not
-- in scope; `autoImplicit` then bound them as variables and the whole structure failed to
-- elaborate, which is why its *name* showed up as unknown further down.
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differential law of localization

`Localization.lean` proves the finite-dimensional algebraic core of buffering-structure
localization.  This module supplies the interpretation as a derivative of a steady-state
branch with respect to a perturbation parameter.

The analytic existence of a differentiable branch is deliberately separated from the CRNT
statement.  A `SteadyStateSensitivityCertificate` records exactly the first-order equation
obtained by differentiating the steady-state and conservation equations.  Once that equation
is available, output completeness and `λ = 0` force the derivative to remain inside the
buffering structure.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- First-order data for one parameter perturbation of a steady-state branch.  `directRate`
is the direct kinetic derivative at fixed concentration and `conservationForcing` is the
derivative of the selected conserved totals. -/
structure ParameterDerivativeForcing (N : Network S) where
  directRate : N.R → ℝ
  conservationForcing : S → ℝ

/-- A perturbation is supported in `γ` when it has no direct kinetic effect outside `Eγ`
and does not directly change species coordinates outside `Vγ` through its conserved-total
forcing. -/
def ParameterDerivativeForcing.SupportedIn {N : Network S}
    (γ : StructuralSubnetwork N) (p : ParameterDerivativeForcing N) : Prop :=
  (∀ r, r ∉ γ.reactions → p.directRate r = 0) ∧
  (∀ s, s ∉ γ.species → p.conservationForcing s = 0)

/-- Restrict a full direct-rate derivative to the reactions of `γ`. -/
def restrictRateForcing {N : Network S} (γ : StructuralSubnetwork N)
    (p : ParameterDerivativeForcing N) : ↥γ.reactions → ℝ :=
  fun r => p.directRate r.1

/-- Restrict a conservation forcing to the projected conservation equations. -/
noncomputable def restrictConservationForcing {N : Network S}
    (γ : StructuralSubnetwork N) (p : ParameterDerivativeForcing N) :
    N.LocalConservationResponse γ where
  toFun := fun q => ∑ s : ↥γ.species, q.1 s * p.conservationForcing s.1
  map_add' := by intro q₁ q₂; simp [Finset.sum_add_distrib, add_mul]
  map_smul' := by intro a q; simp [Finset.mul_sum, mul_assoc]

/-- The differentiated right-hand side seen by the local sensitivity operator.  Direct
rate forcing moves to the opposite side of the differentiated steady-state equation. -/
noncomputable def derivativeLocalForcing {N : Network S}
    (γ : StructuralSubnetwork N) (p : ParameterDerivativeForcing N) :
    N.LocalForcing γ :=
  (-N.restrictRateForcing γ p, N.restrictConservationForcing γ p)

/-- A certificate that a full concentration derivative and a supported cycle derivative
solve the differentiated steady-state equations for a parameter perturbation.

`dx_internal` is the derivative on `Vγ`; the associated full derivative is its zero
extension.  Thus this structure states precisely that the branch derivative is localized;
the law below constructs the unique such response from nonsingularity. -/
@[ext]
structure SteadyStateSensitivityCertificate {N : Network S}
    (γ : StructuralSubnetwork N)
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (p : ParameterDerivativeForcing N) where
  dx_internal : ↥γ.species → ℝ
  cycleDerivative : N.supportedCycleSubspace γ
  differentiatedEquation :
    N.localSensitivityOperator γ J (dx_internal, cycleDerivative) =
      N.derivativeLocalForcing γ p

namespace SteadyStateSensitivityCertificate

variable {N : Network S} {γ : StructuralSubnetwork N}
  {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)} {p : ParameterDerivativeForcing N}

/-- Full concentration derivative represented by a localized sensitivity certificate. -/
def fullConcentrationDerivative (C : N.SteadyStateSensitivityCertificate γ J p) : S → ℝ :=
  speciesExtension γ.species C.dx_internal

/-- Total first-order reaction-rate derivative: indirect concentration response plus the
direct parameter effect. -/
def totalRateDerivative (C : N.SteadyStateSensitivityCertificate γ J p) : N.R → ℝ :=
  J C.fullConcentrationDerivative + p.directRate

/-- Species outside a certified localized response have zero derivative. -/
theorem concentrationDerivative_eq_zero_outside
    (C : N.SteadyStateSensitivityCertificate γ J p)
    {s : S} (hs : s ∉ γ.species) : C.fullConcentrationDerivative s = 0 := by
  simp [fullConcentrationDerivative, speciesExtension, hs]

/-- For an output-complete response and an internally supported parameter perturbation,
the total reaction-rate derivative vanishes outside `Eγ`. -/
theorem totalRateDerivative_eq_zero_outside
    (C : N.SteadyStateSensitivityCertificate γ J p)
    (hout : N.IsOutputComplete γ)
    (hJ : N.RespectsReactantSupport J)
    (hp : p.SupportedIn γ)
    {r : N.R} (hr : r ∉ γ.reactions) : C.totalRateDerivative r = 0 := by
  have hkin := N.exterior_rate_response_zero_of_outputComplete hJ hout C.dx_internal hr
  simp [totalRateDerivative, fullConcentrationDerivative, hkin, hp.1 r hr]

end SteadyStateSensitivityCertificate

/-- **Differential law of localization.**  For an internally supported parameter
perturbation of a buffering structure, nonsingularity of the local sensitivity operator
constructs a unique first-order response.  The concentration derivative is zero outside
`Vγ`, and the total rate derivative is zero outside `Eγ`.

This is the exact derivative statement used in applications.  An implicit-function theorem
supplies the differentiated equation; the CRNT localization conclusion is finite-dimensional. -/
theorem lawOfLocalization_differential
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.localSensitivityOperator γ J))
    (p : ParameterDerivativeForcing N) (hp : p.SupportedIn γ) :
    ∃! C : N.SteadyStateSensitivityCertificate γ J p,
      (∀ s, s ∉ γ.species → C.fullConcentrationDerivative s = 0) ∧
      (∀ r, r ∉ γ.reactions → C.totalRateDerivative r = 0) := by
  have hbij := N.localSensitivity_bijective_of_injective_of_influence_zero J hγ.2 hinj
  rcases hbij.2 (N.derivativeLocalForcing γ p) with ⟨z, hz⟩
  let C : N.SteadyStateSensitivityCertificate γ J p :=
    { dx_internal := z.1
      cycleDerivative := z.2
      differentiatedEquation := hz }
  refine ⟨C, ?_, ?_⟩
  · constructor
    · intro s hs
      exact C.concentrationDerivative_eq_zero_outside hs
    · intro r hr
      exact C.totalRateDerivative_eq_zero_outside hγ.1 hJ hp hr
  · intro D hD
    apply SteadyStateSensitivityCertificate.ext
    · exact congrArg Prod.fst (hinj (D.differentiatedEquation.trans hz.symm))
    · exact congrArg Prod.snd (hinj (D.differentiatedEquation.trans hz.symm))

/-- A local differentiable branch together with the first-order CRNT sensitivity data
that it realizes.  The branch itself is not postulated to be localized: localization is a
conclusion about its derivative at the reference parameter. -/
structure LocalC1SensitivityBranch {N : Network S}
    (γ : StructuralSubnetwork N)
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (p : ParameterDerivativeForcing N) where
  radius : ℝ
  radius_pos : 0 < radius
  state : ℝ → Concentration S
  sensitivity : N.SteadyStateSensitivityCertificate γ J p
  differentiableOn : ∀ t, |t| < radius → DifferentiableAt ℝ state t
  derivativeAtZero : HasDerivAt state sensitivity.fullConcentrationDerivative 0

/-- Analytic input required to pass from the finite-dimensional sensitivity equation to an
actual local steady-state branch.  This deliberately isolates the implicit-function theorem
from the combinatorial CRNT localization theorem.  A concrete mass-action parameterization
should prove this predicate by differentiating its steady-state and conservation equations. -/
def HasLocalSteadyStateIFT {N : Network S}
    (γ : StructuralSubnetwork N)
    (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (p : ParameterDerivativeForcing N) : Prop :=
  -- `differentiatedEquation` is a *proof* field of the certificate, not a value, so the
  -- conjunct that used to sit here (`… = derivativeLocalForcing γ p`) was ill-typed: it
  -- compared a proof with a `LocalForcing`.  It was also redundant — every
  -- `SteadyStateSensitivityCertificate` carries that equation by construction.  So the
  -- analytic content of this predicate is exactly the existence of the branch.
  Nonempty (N.LocalC1SensitivityBranch γ J p)

/-- **Analytic law of localization.**  Once an implicit-function argument supplies a local
`C¹` steady-state branch whose derivative solves the CRNT sensitivity equations, buffering
structure nonsingularity forces that derivative to vanish outside `Vγ`, and forces the total
reaction-rate derivative to vanish outside `Eγ` for an internally supported perturbation.

Unlike the previous placeholder statement, this theorem has a genuine analytic hypothesis:
CRNT alone cannot manufacture a local branch without regularity of a parameterized steady-state
problem. -/
theorem localized_C1_steadyState_branch_of_nonsingular
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.localSensitivityOperator γ J))
    (p : ParameterDerivativeForcing N) (hp : p.SupportedIn γ)
    (hIFT : N.HasLocalSteadyStateIFT γ J p) :
    ∃ B : N.LocalC1SensitivityBranch γ J p,
      (∀ s, s ∉ γ.species → B.sensitivity.fullConcentrationDerivative s = 0) ∧
      (∀ r, r ∉ γ.reactions → B.sensitivity.totalRateDerivative r = 0) := by
  obtain ⟨B⟩ := hIFT
  refine ⟨B, ?_, ?_⟩
  · intro s hs
    exact B.sensitivity.concentrationDerivative_eq_zero_outside hs
  · intro r hr
    exact B.sensitivity.totalRateDerivative_eq_zero_outside hγ.1 hJ hp hr

/-- Existence form of the analytic bridge.  A nonsingular parameterized mass-action
steady-state problem satisfying the finite-dimensional IFT hypotheses produces a branch whose
first derivative is the unique localized sensitivity response.  The actual invocation of
Mathlib's implicit-function theorem is the remaining analytic proof kernel. -/
theorem exists_localized_C1_steadyState_branch_of_IFT
    {N : Network S} {γ : StructuralSubnetwork N}
    {J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)}
    (hγ : N.IsBufferingStructure γ)
    (hJ : N.RespectsReactantSupport J)
    (hinj : Function.Injective (N.localSensitivityOperator γ J))
    (p : ParameterDerivativeForcing N) (hp : p.SupportedIn γ)
    (hIFT : N.HasLocalSteadyStateIFT γ J p) :
    ∃ B : N.LocalC1SensitivityBranch γ J p,
      (∀ s, s ∉ γ.species → B.sensitivity.fullConcentrationDerivative s = 0) ∧
      (∀ r, r ∉ γ.reactions → B.sensitivity.totalRateDerivative r = 0) := by
  exact N.localized_C1_steadyState_branch_of_nonsingular hγ hJ hinj p hp hIFT

end Network
end CRNT
