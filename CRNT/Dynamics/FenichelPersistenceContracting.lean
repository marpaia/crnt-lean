import CRNT.Dynamics.FenichelPersistenceConcrete

/-!
# A contracting fibre flow and its invariant graph

The base coordinate is frozen and the fibre relaxes exponentially to a supplied
centre. The explicit time-indexed regraph operators satisfy the graph-mapping
law and have a common fixed graph, proving all-time invariance. The example
illustrates the graph-transform API; it is not a general Fenichel theorem.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section Contracting

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The contracting fast-fibre field** `ẏ = 0`, `ż = -rate · (z - c)` on the product `Y × E`: the
slow base is frozen and the fast fibre is pulled toward the constant target `c` at exponential rate
`rate`. It is affine and unbounded in the fibre coordinate `z`, but its forward semiflow is globally
well-defined in closed form (`contractingFlow`). -/
def contractingField (rate : ℝ) (c : E) : Y × E → Y × E := fun p => (0, -rate • (p.2 - c))

omit [NormedSpace ℝ Y] in
@[simp] theorem contractingField_apply (rate : ℝ) (c : E) (p : Y × E) :
    contractingField rate c p = (0, -rate • (p.2 - c)) := rfl

/-- The closed-form exponential-contraction map at time `t`: `(y, z) ↦ (y, c + e^{-rate·t}·(z - c))`.
The slow base is fixed; the fast fibre relaxes toward the target `c` at rate `rate`. -/
noncomputable def contractingMap (rate : ℝ) (c : E) (t : ℝ) : Y × E → Y × E :=
  fun p => (p.1, c + Real.exp (-rate * t) • (p.2 - c))

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
@[simp] theorem contractingMap_fst (rate : ℝ) (c : E) (t : ℝ) (p : Y × E) :
    (contractingMap rate c t p).1 = p.1 := rfl

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
@[simp] theorem contractingMap_snd (rate : ℝ) (c : E) (t : ℝ) (p : Y × E) :
    (contractingMap rate c t p).2 = c + Real.exp (-rate * t) • (p.2 - c) := rfl

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
theorem contractingMap_zero (rate : ℝ) (c : E) (p : Y × E) :
    contractingMap rate c 0 p = p := by
  simp [contractingMap]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- The closed-form contraction is a semigroup in time:
`Φ (s + t) = Φ s ∘ Φ t` via `e^{-rate·(s+t)} = e^{-rate·s} · e^{-rate·t}`. -/
theorem contractingMap_add (rate : ℝ) (c : E) (s t : ℝ) (p : Y × E) :
    contractingMap rate c (s + t) p = contractingMap rate c s (contractingMap rate c t p) := by
  simp only [contractingMap, Prod.mk.injEq, true_and, add_sub_cancel_left, smul_smul]
  rw [mul_add, Real.exp_add, mul_comm (Real.exp (-rate * s))]

variable [CompleteSpace Y] [CompleteSpace E]

/-- **The forward semiflow of the contracting fast-fibre field.** The closed-form exponential
contraction `(y, z) ↦ (y, c + e^{-rate·t}·(z - c))` assembled into a genuine `Flow ℝ≥0 (Y × E)`: its
joint continuity is elementary, the identity at time `0` is `contractingMap_zero`, and the semigroup
law is `contractingMap_add`. No boundedness cutoff is needed — the exponential pull is a global
self-map at every forward time even though the field is unbounded in the fibre. -/
noncomputable def contractingFlow (rate : ℝ) (c : E) : Flow ℝ≥0 (Y × E) where
  toFun t p := contractingMap rate c (t : ℝ) p
  cont' := by
    show Continuous fun q : ℝ≥0 × (Y × E) =>
      ((q.2).1, c + Real.exp (-rate * (q.1 : ℝ)) • ((q.2).2 - c))
    refine (continuous_fst.comp continuous_snd).prodMk ?_
    refine continuous_const.add ?_
    refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub continuous_const)
    exact Real.continuous_exp.comp (continuous_const.mul
      (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    simp only [NNReal.coe_add]
    exact contractingMap_add rate c (t₁ : ℝ) (t₂ : ℝ) p
  map_zero' p := contractingMap_zero rate c p

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem contractingFlow_toFun (rate : ℝ) (c : E) (t : ℝ≥0) (p : Y × E) :
    (contractingFlow (Y := Y) rate c).toFun t p = contractingMap rate c (t : ℝ) p := rfl

end Contracting

section Regraph

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The regraph of a section under time `t` of the contracting flow: the section relaxed toward the
target `c` by the factor `e^{-rate·t}`. The time-`t` contraction carries `graphSet σ` to
`graphSet (contractRegraph rate c t σ)`. -/
noncomputable def contractRegraph (rate : ℝ) (c : E) (t : ℝ≥0) (σ : Y → E) : Y → E :=
  fun y => c + Real.exp (-rate * (t : ℝ)) • (σ y - c)

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The contracting flow regraphs at every time.** The time-`t` contraction carries the graph of
`σ` into the graph of `contractRegraph rate c t σ`, for every `t ≥ 0`. Read off the closed form of
the flow. -/
theorem contracting_allTimeRegraph (rate : ℝ) (c : E) (t : ℝ≥0) (σ : Y → E) :
    MapsTo ((contractingFlow (Y := Y) rate c).toFun t) (graphSet σ)
      (graphSet (contractRegraph rate c t σ)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [contractingFlow_toFun, mem_graphSet, contractingMap, contractRegraph, hp]

/-- The genuine contracting flow realizes an elapsed-time family of regraph operators. -/
noncomputable def contractingGraphTransformFamily (rate : ℝ) (c : E) :
    FlowGraphTransformFamily Y E where
  flow := contractingFlow rate c
  op := contractRegraph rate c
  flow_mapsTo := contracting_allTimeRegraph rate c

/-- The target section is fixed at every time, so its graph is continuously invariant. -/
theorem contracting_graph_invariant_allTime (rate : ℝ) (c : E) :
    IsInvariant (contractingFlow (Y := Y) rate c).toFun (graphSet (fun _ : Y => c)) := by
  apply (contractingGraphTransformFamily (Y := Y) rate c).graphSet_isInvariant_of_commonFixedPoint
  intro t
  funext y
  simp [contractingGraphTransformFamily, contractRegraph]

/-- **The concrete contracting fast-fibre coupled-flow graph transform.** Assembled from the genuine
closed-form contracting flow, with the graph-transform operator at horizon `τ` proved — not assumed —
to be the flow-then-regraph map `contractRegraph rate c τ`. This discharges the `flow_mapsTo`
hypothesis of `CoupledFlowGraphTransform` from the explicit contracting field. -/
noncomputable def contractingCoupled (rate : ℝ) (c : E) (τ : ℝ≥0) :
    CoupledFlowGraphTransform Y E where
  flow := contractingFlow rate c
  τ := τ
  op := contractRegraph rate c τ
  flow_mapsTo σ := contracting_allTimeRegraph rate c τ σ

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem contractingCoupled_op (rate : ℝ) (c : E) (τ : ℝ≥0) :
    (contractingCoupled (Y := Y) rate c τ).op = contractRegraph rate c τ := rfl

end Regraph

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The affine contraction operator on bounded sections `Y →ᵇ E`:
`op σ = const c + e^{-rate·τ} · (σ - const c)`. This is the bounded-section realization of the
flow-then-regraph map `contractRegraph rate c τ`. -/
noncomputable def contractOp (rate : ℝ) (c : E) (τ : ℝ≥0) (σ : Y →ᵇ E) : Y →ᵇ E :=
  BoundedContinuousFunction.const Y c
    + Real.exp (-rate * (τ : ℝ)) • (σ - BoundedContinuousFunction.const Y c)

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- The bounded-section operator evaluated pointwise equals the flow-then-regraph map. -/
@[simp] theorem contractOp_apply (rate : ℝ) (c : E) (τ : ℝ≥0) (σ : Y →ᵇ E) (y : Y) :
    contractOp rate c τ σ y = c + Real.exp (-rate * (τ : ℝ)) • (σ y - c) := by
  simp only [contractOp, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_sub, Pi.add_apply, Pi.sub_apply,
    BoundedContinuousFunction.const_apply']

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- The difference of two operator values is the scaled difference of the inputs:
`contractOp σ - contractOp ρ = e^{-rate·τ} • (σ - ρ)`. The target translation cancels. -/
theorem contractOp_sub (rate : ℝ) (c : E) (τ : ℝ≥0) (σ ρ : Y →ᵇ E) :
    contractOp rate c τ σ - contractOp rate c τ ρ
      = Real.exp (-rate * (τ : ℝ)) • (σ - ρ) := by
  simp only [contractOp]
  rw [add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right]

/-- **A genuine contraction on bounded sections with a moving fixed point.** The affine operator
`σ ↦ const c + e^{-rate·τ}·(σ - const c)` on `Y →ᵇ E` is an exact contraction with factor
`q = e^{-rate·τ} < 1` whenever `rate > 0` and `τ > 0`. Its unique Banach fixed point is the constant
section `c` — the genuinely attracting fibre, a non-trivial moving manifold. Packaged as
`GraphTransformData` with vanishing drift defect (the operator fixes the constant section exactly). -/
noncomputable def contractGapData (rate : ℝ) (c : E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) :
    GraphTransformData Y E where
  op := contractOp rate c τ
  factor := ⟨Real.exp (-rate * (τ : ℝ)), (Real.exp_pos _).le⟩
  factor_lt_one := by
    change Real.exp (-rate * (τ : ℝ)) < 1
    rw [Real.exp_lt_one_iff]
    have : 0 < rate * (τ : ℝ) := mul_pos hrate hτ
    linarith
  op_dist_le σ ρ := by
    rw [dist_eq_norm, contractOp_sub, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      dist_eq_norm]
    rfl
  base := BoundedContinuousFunction.const Y c
  defect := 0
  defect_le := by
    have hc : contractOp rate c τ (BoundedContinuousFunction.const Y c)
        = BoundedContinuousFunction.const Y c := by
      ext y
      rw [contractOp_apply, BoundedContinuousFunction.const_apply', sub_self, smul_zero, add_zero]
    rw [hc, dist_self]

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- The base section of `contractGapData` is the constant target section `c`. -/
@[simp] theorem contractGapData_base (rate : ℝ) (c : E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) :
    (contractGapData (Y := Y) rate c τ hrate hτ).base = BoundedContinuousFunction.const Y c := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- The operator of `contractGapData`. -/
@[simp] theorem contractGapData_op (rate : ℝ) (c : E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) :
    (contractGapData (Y := Y) rate c τ hrate hτ).op = contractOp rate c τ := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- **The persisted manifold of `contractGapData` is the constant target section.** The unique Banach
fixed point of the affine contraction `σ ↦ const c + e^{-rate·τ}·(σ - const c)` is the constant
section `c` — the genuinely attracting fibre, a non-trivial moving manifold rather than the zero
section. -/
theorem contractGapData_manifold (rate : ℝ) (c : E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) :
    (contractGapData (Y := Y) rate c τ hrate hτ).manifold = BoundedContinuousFunction.const Y c := by
  refine ((contractGapData (Y := Y) rate c τ hrate hτ).manifold_unique
    (σ := BoundedContinuousFunction.const Y c) ?_).symm
  rw [contractGapData_op]
  ext y
  rw [contractOp_apply, BoundedContinuousFunction.const_apply', sub_self, smul_zero, add_zero]

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_contracting (rate : ℝ) (c : E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c τ hrate hτ
    let F := contractingCoupled (Y := Y) (E := E) rate c τ
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G F
  refine graphTransform_discrete_invariant_and_dist_le G F ?_
  -- The bounded-section fixed point is the constant section `c`; the flow operator fixes it too,
  -- because the contraction holds the fibre on its own target.
  show F.op (G.manifold : Y → E) = (G.manifold : Y → E)
  rw [contractingCoupled_op]
  have hman : (G.manifold : Y →ᵇ E) = BoundedContinuousFunction.const Y c :=
    contractGapData_manifold rate c τ hrate hτ
  funext y
  rw [contractRegraph]
  simp only [G, hman, BoundedContinuousFunction.const_apply', sub_self, smul_zero, add_zero]

end Persistence

end ODE
