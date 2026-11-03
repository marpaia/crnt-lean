import CRNT.Dynamics.FenichelMovingGeneralDrift

/-!
# Explicit base/fibre graph-transform examples

The displayed base and fibre flows supply graph-transform data and yield their
stated graph-invariance and fixed-point distance estimates. Michaelis–Menten
sections use a contracting comparison flow with frozen substrate where defined.
The hypotheses and actual flow in each theorem determine its scope. These
examples do not establish general normally hyperbolic manifold persistence or
transfer invariance to an unrelated coupled mass-action field.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section LogisticInjectivity

/-- **The time-`τ` map of the curved logistic base flow is injective.** Applying
`flow_toFun_injective` to the logistic field's Lipschitz bound and the retained integral-curve
witnesses of `logisticDriftFlowData`: two integral curves of `ε·sin y` agreeing at time `τ` agree at
time `0`, so they share a starting point. The base flows by a genuinely nonlinear field, yet its time
map is injective with no inverse supplied. -/
theorem logisticDriftFlow_injective (ε : ℝ) (τ : ℝ≥0) :
    Injective ((logisticDriftFlow ε).toFun τ) :=
  flow_toFun_injective (f := logisticField ε) (logisticField_lipschitz ε)
    (logisticDriftCurves_zero ε) (logisticDriftCurves_hasDerivAt ε)
    (logisticDriftFlow_eq_curves ε) τ

/-- **The injective curved logistic slow base flow.** Built via `InjectiveBaseFlow.ofInjective` from
the injectivity of the time-`τ` logistic base map: the left-inverse is
`Function.invFun (logisticDriftFlow ε |>.toFun τ)`, an honest abstract inverse — *no closed-form
back-translation*, in contrast to the affine base's `y ↦ y - τ·v`. -/
noncomputable def logisticInjectiveBase (ε : ℝ) (τ : ℝ≥0) : InjectiveBaseFlow ℝ :=
  InjectiveBaseFlow.ofInjective (logisticDriftFlow ε) τ (logisticDriftFlow_injective ε τ)

@[simp] theorem logisticInjectiveBase_τ (ε : ℝ) (τ : ℝ≥0) : (logisticInjectiveBase ε τ).τ = τ := rfl

@[simp] theorem logisticInjectiveBase_slowFlow (ε : ℝ) (τ : ℝ≥0) :
    (logisticInjectiveBase ε τ).slowFlow = logisticDriftFlow ε := rfl

end LogisticInjectivity

section Persistence

/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_logisticMovingBase (ε : ℝ) (rate : ℝ) (c : ℝ) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := ℝ) (E := ℝ) rate c τ hrate hτ
    let F := movingCoupled (logisticInjectiveBase ε τ) rate c
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  graphTransform_discrete_invariant_and_dist_le_movingGeneralDrift (logisticInjectiveBase ε τ) rate c hrate
    (by simpa using hτ)

/-- **All-time continuous-semiflow invariance of the slow manifold over the curved logistic base.**
The graph of the constant attracting fibre `{(y, c)}` is invariant under the *full continuous* product
semiflow over the logistic base for every `t ≥ 0`, not only at multiples of the horizon. The substrate
flows along the slow manifold under its genuine curved drift `ε·sin y`, the continuous-level residue of
`graphTransform_discrete_invariant_and_dist_le_logisticMovingBase`. -/
theorem logisticMovingBase_graphSet_isInvariant_allTime (ε : ℝ) (rate : ℝ) (c : ℝ) :
    IsInvariant (productContractFlow (logisticDriftFlow ε) rate c).toFun (graphSet (fun _ : ℝ => c)) :=
  generalDrift_graphSet_isInvariant_allTime (logisticDriftFlow ε) rate c

end Persistence

end ODE
