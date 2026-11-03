import CRNT.Oscillation.FiedlerGlobalHopf
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Analyticity of the Vassena diagonal continuation

The Fiedler continuation theorem used by the mass-action oscillation criteria requires an analytic
parameterized vector field.  This file discharges that requirement for the concrete exponential
positive-diagonal continuation constructed in `VassenaContinuation`.

The proof is deliberately componentwise.  No analyticity is hidden in `RateConstants`, whose
positivity proof is irrelevant to the vector field.  We prove that

* every diagonal coordinate `d_i(mu)` is analytic;
* every reciprocal steady-state coordinate is analytic;
* every finite mass-action monomial along that state path is analytic and never zero;
* every proof-erased continuation rate is analytic;
* every state monomial is polynomial, hence analytic jointly in `(mu,x)`;
* finite reaction sums and finite species products assemble the analytic vector field.

This closes `FluxGlobalHopfAnalyticityTarget`; the remaining Vassena/Fiedler frontier is therefore
the global bifurcation theorem itself, not regularity of the CRN realization.
-/

namespace CRNT

open scoped BigOperators

namespace Complex

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Mass-action monomials are real analytic polynomial functions of the concentration vector. -/
theorem massActionMonomial_analyticOnNhd (y : Complex S) :
    AnalyticOnNhd ℝ (fun x : Concentration S => y.massActionMonomial x) Set.univ := by
  unfold Complex.massActionMonomial
  refine Finset.analyticOnNhd_fun_prod Finset.univ ?_
  intro s _
  have hs : AnalyticOnNhd ℝ (fun x : Concentration S => x s) Set.univ := by
    let L : Concentration S →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s
    have hL := L.analyticOnNhd Set.univ
    convert hL using 1
    funext x
    rfl
  exact hs.fun_pow (y s)

end Complex

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Each exponential-diagonal coordinate is analytic on the whole real parameter line. -/
theorem exponentialDiagonalPath_analyticOnNhd_apply
    {d₀ d₁ : S → ℝ} (s : S) :
    AnalyticOnNhd ℝ (fun μ : ℝ => exponentialDiagonalPath d₀ d₁ μ s) Set.univ := by
  unfold exponentialDiagonalPath
  have hid : AnalyticOnNhd ℝ (fun μ : ℝ => μ) Set.univ := by
    have hL := (1 : ℝ →L[ℝ] ℝ).analyticOnNhd Set.univ
    convert hL using 1
    funext μ
    rfl
  have hlin : AnalyticOnNhd ℝ
      (fun μ : ℝ => μ * Real.log (d₁ s / d₀ s)) Set.univ :=
    hid.mul analyticOnNhd_const
  exact analyticOnNhd_const.mul hlin.rexp

/-- The reciprocal state coordinate is analytic because the exponential diagonal never vanishes. -/
theorem exponentialDiagonalState_analyticOnNhd_apply
    {d₀ d₁ : S → ℝ} (hd₀ : ∀ s, 0 < d₀ s) (s : S) :
    AnalyticOnNhd ℝ (fun μ : ℝ => exponentialDiagonalState d₀ d₁ μ s) Set.univ := by
  change AnalyticOnNhd ℝ
    (fun μ : ℝ => (exponentialDiagonalPath d₀ d₁ μ s)⁻¹) Set.univ
  exact (exponentialDiagonalPath_analyticOnNhd_apply (d₀ := d₀) (d₁ := d₁) s).fun_inv
    (by
      intro μ _
      exact ne_of_gt (exponentialDiagonalPath_positive hd₀ μ s))

/-- The complete reciprocal steady-state branch is analytic as a finite Pi-valued map. -/
theorem exponentialDiagonalState_analyticOnNhd
    {d₀ d₁ : S → ℝ} (hd₀ : ∀ s, 0 < d₀ s) :
    AnalyticOnNhd ℝ (fun μ : ℝ => exponentialDiagonalState d₀ d₁ μ) Set.univ := by
  apply AnalyticOnNhd.pi
  intro s
  exact exponentialDiagonalState_analyticOnNhd_apply hd₀ s

/-- A source monomial evaluated along the reciprocal continuation state is analytic. -/
theorem exponentialDiagonal_sourceMonomial_analyticOnNhd
    {d₀ d₁ : S → ℝ} (hd₀ : ∀ s, 0 < d₀ s) (y : Complex S) :
    AnalyticOnNhd ℝ
      (fun μ : ℝ => y.massActionMonomial (exponentialDiagonalState d₀ d₁ μ)) Set.univ := by
  unfold Complex.massActionMonomial
  refine Finset.analyticOnNhd_fun_prod Finset.univ ?_
  intro s _
  exact (exponentialDiagonalState_analyticOnNhd_apply hd₀ s).fun_pow (y s)

namespace FluxJacobianStabilityTransition

variable {N : Network S}

/-- The proof-erased scalar rate used by the continuation is analytic for every reaction. -/
theorem continuationRateValue_analyticOnNhd
    (w : FluxJacobianStabilityTransition N) (r : N.R) :
    AnalyticOnNhd ℝ (fun μ : ℝ => w.continuationRateValue μ r) Set.univ := by
  unfold continuationRateValue continuationState
  have hden : AnalyticOnNhd ℝ
      (fun μ : ℝ =>
        (N.reaction r).source.massActionMonomial
          (exponentialDiagonalState w.transition.stableDiagonal
            w.transition.unstableDiagonal μ)) Set.univ :=
    exponentialDiagonal_sourceMonomial_analyticOnNhd w.transition.stablePositive _
  exact analyticOnNhd_const.div hden (by
    intro μ _
    exact (Complex.massActionMonomial_pos
      (exponentialDiagonalState_positive w.transition.stablePositive μ) _).ne')

/-- Coordinate projection from `(parameter,state)` to the parameter is analytic. -/
private theorem parameterProjection_analyticOnNhd :
    AnalyticOnNhd ℝ (fun p : ℝ × Concentration S => p.1) Set.univ := by
  let L : (ℝ × Concentration S) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ (Concentration S)
  have hL := L.analyticOnNhd Set.univ
  convert hL using 1
  funext p
  rfl

/-- Coordinate projection from `(parameter,state)` to one species concentration is analytic. -/
private theorem stateCoordinate_analyticOnNhd (s : S) :
    AnalyticOnNhd ℝ (fun p : ℝ × Concentration S => p.2 s) Set.univ := by
  let L₁ : (ℝ × Concentration S) →L[ℝ] Concentration S :=
    ContinuousLinearMap.snd ℝ ℝ (Concentration S)
  let L₂ : Concentration S →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s
  have hL := (L₂.comp L₁).analyticOnNhd Set.univ
  have h : AnalyticOnNhd ℝ
      (fun p : ℝ × Concentration S => (L₂.comp L₁) p) Set.univ := by
    exact hL
  simpa [L₁, L₂, ContinuousLinearMap.proj_apply] using h

/-- A state mass-action monomial is analytic jointly in `(parameter,state)`; it ignores the
parameter coordinate but lives on the same product domain as the continuation field. -/
private theorem jointStateMonomial_analyticOnNhd (y : Complex S) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × Concentration S => y.massActionMonomial p.2) Set.univ := by
  unfold Complex.massActionMonomial
  refine Finset.analyticOnNhd_fun_prod Finset.univ ?_
  intro s _
  exact (stateCoordinate_analyticOnNhd (S := S) s).fun_pow (y s)

/-- Each reaction contribution to one species coordinate of the continuation field is analytic. -/
private theorem reactionContribution_analyticOnNhd
    (w : FluxJacobianStabilityTransition N) (r : N.R) (s : S) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × Concentration S =>
        w.continuationRateValue p.1 r *
          (N.reaction r).source.massActionMonomial p.2 * N.reactionVector r s)
      Set.univ := by
  have hk : AnalyticOnNhd ℝ
      (fun p : ℝ × Concentration S => w.continuationRateValue p.1 r) Set.univ := by
    exact (w.continuationRateValue_analyticOnNhd r).comp
      parameterProjection_analyticOnNhd (by intro p hp; exact Set.mem_univ _)
  have hm := jointStateMonomial_analyticOnNhd (S := S) (N.reaction r).source
  exact (hk.mul hm).mul analyticOnNhd_const

/-- **Closed regularity theorem.**  The Vassena continuation vector field is jointly real analytic
in its continuation parameter and concentration vector. -/
theorem continuationField_analyticOnNhd
    (w : FluxJacobianStabilityTransition N) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × Concentration S => w.continuationField p.1 p.2) Set.univ := by
  apply AnalyticOnNhd.pi
  intro s
  unfold continuationField
  exact Finset.analyticOnNhd_fun_sum Finset.univ
    (fun r _ => reactionContribution_analyticOnNhd w r s)

end FluxJacobianStabilityTransition

/-- The former CRN-specific analyticity frontier is discharged for the concrete exponential
mass-action continuation. -/
theorem fluxGlobalHopfAnalyticity : FluxGlobalHopfAnalyticityTarget := by
  intro T _ _ N W
  exact W.toFluxJacobianStabilityTransition.continuationField_analyticOnNhd

namespace FluxGlobalHopfData

variable {N : Network S}

/-- Every `FluxGlobalHopfData` now upgrades canonically to the analytic continuation consumed by
Fiedler's theorem; no external regularity hypothesis remains. -/
noncomputable def toAnalyticEquilibriumContinuationClosed
    (W : N.FluxGlobalHopfData) : AnalyticEquilibriumContinuation S :=
  W.toAnalyticEquilibriumContinuation fluxGlobalHopfAnalyticity

/-- The Vassena/Fiedler route now needs only the actual analytic global-Hopf theorem. -/
theorem oscillatoryCapacity_of_fiedler_closed
    (hFiedler : FiedlerAnalyticGlobalHopfTarget)
    (W : N.FluxGlobalHopfData) : N.OscillatoryCapacity :=
  W.oscillatoryCapacity_of_fiedler fluxGlobalHopfAnalyticity hFiedler

end FluxGlobalHopfData

end Network

end CRNT
