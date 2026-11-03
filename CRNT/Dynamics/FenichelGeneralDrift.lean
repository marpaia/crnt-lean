import CRNT.Dynamics.FenichelPersistenceContracting

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

section ProductFlow

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The product semiflow of the general-drift / contracting-fibre field** `ẏ = ε·g(y)`,
`ż = -rate·(z - c)` on `Y × E`: the base coordinate evolves under the general semiflow `slowFlow` and
the fast fibre relaxes onto the constant target `c` at rate `rate`,
`(y, z) ↦ (slowFlow t y, c + e^{-rate·t}·(z - c))`. The base motion is a genuine — possibly nonlinear —
flow, not a translation. Joint continuity comes from `slowFlow.cont'` and the fibre contraction; the
identity at time `0` and the semigroup law are coordinatewise. -/
noncomputable def productContractFlow (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) :
    Flow ℝ≥0 (Y × E) where
  toFun t p := (slowFlow.toFun t p.1, c + Real.exp (-rate * (t : ℝ)) • (p.2 - c))
  cont' := by
    refine Continuous.prodMk ?_ ?_
    · exact slowFlow.cont'.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · refine continuous_const.add ?_
      refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub continuous_const)
      exact Real.continuous_exp.comp (continuous_const.mul
        (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    refine Prod.ext ?_ ?_
    · exact slowFlow.map_add' t₁ t₂ p.1
    · show c + Real.exp (-rate * ((t₁ + t₂ : ℝ≥0) : ℝ)) • (p.2 - c)
        = c + Real.exp (-rate * (t₁ : ℝ)) • ((c + Real.exp (-rate * (t₂ : ℝ)) • (p.2 - c)) - c)
      rw [NNReal.coe_add, add_sub_cancel_left, smul_smul, mul_add, Real.exp_add,
        mul_comm (Real.exp (-rate * (t₁ : ℝ)))]
  map_zero' p := by
    refine Prod.ext ?_ ?_
    · exact slowFlow.map_zero' p.1
    · show c + Real.exp (-rate * ((0 : ℝ≥0) : ℝ)) • (p.2 - c) = p.2
      simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem productContractFlow_toFun (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (t : ℝ≥0)
    (p : Y × E) :
    (productContractFlow slowFlow rate c).toFun t p
      = (slowFlow.toFun t p.1, c + Real.exp (-rate * (t : ℝ)) • (p.2 - c)) := rfl

end ProductFlow

section ConstantFibre

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The product flow holds the constant-fibre graph at the target, whatever the base does.** The
time-`t` product flow carries each point `(y, c)` of `graphSet (fun _ => c)` to `(slowFlow t y, c)`,
again on the graph: the fibre contraction holds a fibre already at its own target `c`, so no
back-translation — and hence no base invertibility — is needed even though the base flows by a general
nonlinear field. -/
theorem productContract_const_mapsTo (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (t : ℝ≥0) :
    MapsTo ((productContractFlow slowFlow rate c).toFun t) (graphSet (fun _ : Y => c))
      (graphSet (fun _ : Y => c)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [productContractFlow_toFun, mem_graphSet]
  simp [hp]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem generalDrift_graphSet_isInvariant_allTime (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) :
    IsInvariant (productContractFlow slowFlow rate c).toFun (graphSet (fun _ : Y => c)) :=
  fun t => productContract_const_mapsTo slowFlow rate c t

end ConstantFibre

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- The constant-fibre graph is invariant under the iterate product semiflow sampling at multiples of
the horizon `τ`, the discrete-time restriction of `generalDrift_graphSet_isInvariant_allTime`. -/
theorem generalDrift_graphSet_isInvariant_iterate (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E)
    (τ : ℝ≥0) :
    IsInvariant (fun n : ℕ => (productContractFlow slowFlow rate c).toFun (n • τ))
      (graphSet (fun _ : Y => c)) :=
  fun n => generalDrift_graphSet_isInvariant_allTime slowFlow rate c (n • τ)

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_generalDrift (slowFlow : Flow ℝ≥0 Y) (rate : ℝ) (c : E) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c τ hrate hτ
    IsInvariant (fun n : ℕ => (productContractFlow slowFlow rate c).toFun (n • τ))
        (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G
  refine ⟨?_, G.manifold_dist_base_le⟩
  have hman : (G.manifold : Y → E) = fun _ : Y => c := by
    funext y
    have : (G.manifold : Y →ᵇ E) = BoundedContinuousFunction.const Y c :=
      contractGapData_manifold rate c τ hrate hτ
    rw [this, BoundedContinuousFunction.const_apply']
  rw [hman]
  exact generalDrift_graphSet_isInvariant_iterate slowFlow rate c τ

end Persistence

section LogisticInstance

/-- The saturating logistic-type slow field `y ↦ ε·sin y` on `ℝ`: a genuinely nonlinear drift,
bounded by `|ε|` and Lipschitz with constant `|ε|`. -/
noncomputable def logisticField (ε : ℝ) : ℝ → ℝ := fun y : ℝ => ε * Real.sin y

/-- The logistic field is Lipschitz with constant `|ε|`, since `sin` is `1`-Lipschitz. -/
theorem logisticField_lipschitz (ε : ℝ) :
    LipschitzWith ⟨|ε|, abs_nonneg ε⟩ (logisticField ε) :=
  LipschitzWith.of_dist_le_mul (fun a b => by
    have hsin : dist (Real.sin a) (Real.sin b) ≤ (1 : ℝ) * dist a b :=
      Real.lipschitzWith_sin.dist_le_mul a b
    rw [one_mul, Real.dist_eq] at hsin
    show dist (ε * Real.sin a) (ε * Real.sin b) ≤ |ε| * dist a b
    rw [Real.dist_eq, Real.dist_eq]
    calc |ε * Real.sin a - ε * Real.sin b|
        = |ε| * |Real.sin a - Real.sin b| := by rw [← mul_sub, abs_mul]
      _ ≤ |ε| * |a - b| := mul_le_mul_of_nonneg_left hsin (abs_nonneg ε))

/-- The logistic field is bounded by `|ε|`, since `|sin| ≤ 1`. -/
theorem logisticField_bound (ε : ℝ) (y : ℝ) : ‖logisticField ε y‖ ≤ (⟨|ε|, abs_nonneg ε⟩ : ℝ≥0) := by
  rw [Real.norm_eq_abs]
  show |ε * Real.sin y| ≤ |ε|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg ε) (abs_le.2 ⟨Real.neg_one_le_sin y, Real.sin_le_one y⟩)

/-- **The honest `exists_flow` witnesses for the logistic field**, retaining not only the forward
semiflow but also its integral-curve data `γ` (the starting-point identity and the `HasDerivAt` curve
spec) and the orbit identification `ϕ.toFun t x = γ x t`. Keeping the full witness — rather than
projecting only the `Flow` — makes the curve data available for downstream injectivity. -/
noncomputable def logisticDriftFlowData (ε : ℝ) :
    ∃ (ϕ : Flow ℝ≥0 ℝ) (γ : ℝ → ℝ → ℝ),
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (logisticField ε (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ t x = γ x (t : ℝ)) :=
  exists_flow (f := logisticField ε) (K := ⟨|ε|, abs_nonneg ε⟩) (M := ⟨|ε|, abs_nonneg ε⟩)
    (logisticField_lipschitz ε) (logisticField_bound ε)

/-- The genuine forward semiflow of the bounded Lipschitz nonlinear slow field `y ↦ ε·sin y` on `ℝ`,
obtained from `CRNT.Dynamics.FlowConstruction`'s `exists_flow`. The field is bounded by `|ε|` and
Lipschitz with constant `|ε|`, so it generates an honest `Flow ℝ≥0 ℝ`. Its base motion is genuinely
nonlinear — a saturating logistic-type drift — not a translation. -/
noncomputable def logisticDriftFlow (ε : ℝ) : Flow ℝ≥0 ℝ := (logisticDriftFlowData ε).choose

/-- The retained integral curves of the logistic base flow: the function `γ` whose orbits are the
solutions of `ẏ = ε·sin y`, paired with the orbit identification `logisticDriftFlow ε t x = γ x t`. -/
noncomputable def logisticDriftCurves (ε : ℝ) : ℝ → ℝ → ℝ := (logisticDriftFlowData ε).choose_spec.choose

/-- The retained curves start at their base point: `γ x 0 = x`. -/
theorem logisticDriftCurves_zero (ε : ℝ) (x : ℝ) : logisticDriftCurves ε x 0 = x :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.1 x

/-- The retained curves solve the logistic ODE: `γ x` has derivative `ε·sin (γ x t)` at every `t`. -/
theorem logisticDriftCurves_hasDerivAt (ε : ℝ) (x : ℝ) (t : ℝ) :
    HasDerivAt (logisticDriftCurves ε x) (logisticField ε (logisticDriftCurves ε x t)) t :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.2.1 x t

/-- The logistic base flow is its retained integral curves: `logisticDriftFlow ε t x = γ x t`. -/
theorem logisticDriftFlow_eq_curves (ε : ℝ) (x : ℝ) (t : ℝ≥0) :
    (logisticDriftFlow ε).toFun t x = logisticDriftCurves ε x (t : ℝ) :=
  (logisticDriftFlowData ε).choose_spec.choose_spec.2.2 x t

/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_logisticDrift (ε : ℝ) (rate : ℝ) (c : ℝ) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := ℝ) (E := ℝ) rate c τ hrate hτ
    IsInvariant (fun n : ℕ => (productContractFlow (logisticDriftFlow ε) rate c).toFun (n • τ))
        (graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  graphTransform_discrete_invariant_and_dist_le_generalDrift (logisticDriftFlow ε) rate c τ hrate hτ

end LogisticInstance

end ODE
