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

section CoupledDrift

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The coupled slow-drift / contracting-fibre field** `ẏ = ε·b`, `ż = -rate·(z - c)` on the
product `Y × E`: the slow base translates at the slow velocity `ε·b` and the fast fibre is pulled
toward the constant target `c` at exponential rate `rate`. The base coordinate genuinely moves — the
substrate drifts — unlike the frozen-base instances. -/
def coupledDriftField (ε : ℝ) (b : Y) (rate : ℝ) (c : E) : Y × E → Y × E :=
  fun p => (ε • b, -rate • (p.2 - c))

@[simp] theorem coupledDriftField_apply (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (p : Y × E) :
    coupledDriftField ε b rate c p = (ε • b, -rate • (p.2 - c)) := rfl

/-- The closed-form coupled drift map at time `t`: `(y, z) ↦ (y + (ε·t)·b, c + e^{-rate·t}·(z - c))`.
The slow base translates at velocity `ε·b`; the fast fibre relaxes toward the target `c` at rate
`rate`. -/
noncomputable def coupledDriftMap (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ) : Y × E → Y × E :=
  fun p => (p.1 + (ε * t) • b, c + Real.exp (-rate * t) • (p.2 - c))

@[simp] theorem coupledDriftMap_fst (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ) (p : Y × E) :
    (coupledDriftMap ε b rate c t p).1 = p.1 + (ε * t) • b := rfl

@[simp] theorem coupledDriftMap_snd (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ) (p : Y × E) :
    (coupledDriftMap ε b rate c t p).2 = c + Real.exp (-rate * t) • (p.2 - c) := rfl

theorem coupledDriftMap_zero (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (p : Y × E) :
    coupledDriftMap ε b rate c 0 p = p := by
  simp [coupledDriftMap]

/-- The closed-form coupled drift is a semigroup in time: `Φ (s + t) = Φ s ∘ Φ t`. The base
translations add (`(ε(s+t))·b = (εs)·b + (εt)·b`) and the fibre contractions multiply
(`e^{-rate(s+t)} = e^{-rate·s}·e^{-rate·t}`). -/
theorem coupledDriftMap_add (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (s t : ℝ) (p : Y × E) :
    coupledDriftMap ε b rate c (s + t) p
      = coupledDriftMap ε b rate c s (coupledDriftMap ε b rate c t p) := by
  simp only [coupledDriftMap, Prod.mk.injEq, add_sub_cancel_left, smul_smul]
  constructor
  · rw [mul_add, add_smul, add_assoc, add_comm ((ε * s) • b) ((ε * t) • b)]
  · rw [mul_add, Real.exp_add, mul_comm (Real.exp (-rate * s))]

variable [CompleteSpace Y] [CompleteSpace E]

/-- **The forward semiflow of the coupled slow-drift / contracting-fibre field.** The closed-form
product `(y, z) ↦ (y + (ε·t)·b, c + e^{-rate·t}·(z - c))` assembled into a genuine
`Flow ℝ≥0 (Y × E)`: joint continuity is elementary, the identity at time `0` is
`coupledDriftMap_zero`, and the semigroup law is `coupledDriftMap_add`. The base coordinate honestly
drifts under this flow — the substrate moves at speed `ε·‖b‖`. -/
noncomputable def coupledDriftFlow (ε : ℝ) (b : Y) (rate : ℝ) (c : E) : Flow ℝ≥0 (Y × E) where
  toFun t p := coupledDriftMap ε b rate c (t : ℝ) p
  cont' := by
    show Continuous fun q : ℝ≥0 × (Y × E) =>
      ((q.2).1 + (ε * (q.1 : ℝ)) • b, c + Real.exp (-rate * (q.1 : ℝ)) • ((q.2).2 - c))
    refine Continuous.prodMk ?_ ?_
    · refine (continuous_fst.comp continuous_snd).add ?_
      exact (continuous_const.mul (NNReal.continuous_coe.comp continuous_fst)).smul continuous_const
    · refine continuous_const.add ?_
      refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub continuous_const)
      exact Real.continuous_exp.comp (continuous_const.mul
        (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    simp only [NNReal.coe_add]
    exact coupledDriftMap_add ε b rate c (t₁ : ℝ) (t₂ : ℝ) p
  map_zero' p := coupledDriftMap_zero ε b rate c p

omit [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem coupledDriftFlow_toFun (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ≥0) (p : Y × E) :
    (coupledDriftFlow ε b rate c).toFun t p = coupledDriftMap ε b rate c (t : ℝ) p := rfl

end CoupledDrift

section Regraph

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The regraph of a section under time `t` of the coupled drifting-base flow. Because the base
translates by `(ε·t)·b`, a point of the image graph over base `y` came from base `y - (ε·t)·b`, so the
regraphed fibre value reads the section there and contracts it toward `c`:
`σ' y = c + e^{-rate·t}·(σ (y - (ε·t)·b) - c)`. The time-`t` map carries `graphSet σ` to
`graphSet (coupledDriftRegraph ε b rate c t σ)`. -/
noncomputable def coupledDriftRegraph (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ≥0) (σ : Y → E) :
    Y → E :=
  fun y => c + Real.exp (-rate * (t : ℝ)) • (σ (y - (ε * (t : ℝ)) • b) - c)

omit [CompleteSpace Y] [CompleteSpace E] in
/-- **The drifting-base flow regraphs at every time.** The time-`t` coupled flow carries the graph of
`σ` into the graph of `coupledDriftRegraph ε b rate c t σ`, for every `t ≥ 0`. Read off the closed
form of the flow: the base translation back-shifts the section argument and the fibre contraction
scales the fibre toward `c`. -/
theorem coupled_allTimeRegraph (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ≥0) (σ : Y → E) :
    MapsTo ((coupledDriftFlow (Y := Y) ε b rate c).toFun t) (graphSet σ)
      (graphSet (coupledDriftRegraph ε b rate c t σ)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [coupledDriftFlow_toFun, mem_graphSet, coupledDriftMap, coupledDriftRegraph]
  simp only [add_sub_cancel_right, hp]

/-- **The concrete drifting-base coupled-flow graph transform.** Assembled from the genuine
closed-form coupled flow whose base drifts, with the graph-transform operator at horizon `τ` proved —
not assumed — to be the flow-then-regraph map `coupledDriftRegraph ε b rate c τ`. This discharges the
`flow_mapsTo` hypothesis of `CoupledFlowGraphTransform` from the explicit drifting-base field. -/
noncomputable def coupledDriftCoupled (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (τ : ℝ≥0) :
    CoupledFlowGraphTransform Y E where
  flow := coupledDriftFlow ε b rate c
  τ := τ
  op := coupledDriftRegraph ε b rate c τ
  flow_mapsTo σ := coupled_allTimeRegraph ε b rate c τ σ

omit [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem coupledDriftCoupled_op (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (τ : ℝ≥0) :
    (coupledDriftCoupled (Y := Y) ε b rate c τ).op = coupledDriftRegraph ε b rate c τ := rfl

omit [CompleteSpace Y] [CompleteSpace E] in
/-- **The drifting-base flow fixes the constant-section graph at the target.** The
flow-then-regraph map sends the constant section `c` back to the constant section `c`: the base
back-translation acts trivially on a constant fibre, and the contraction holds the fibre on its own
target. So the graph `{(y, c)}` is regraphed onto itself even though the base drifts. -/
theorem coupledDriftRegraph_const (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (t : ℝ≥0) :
    coupledDriftRegraph (Y := Y) ε b rate c t (fun _ => c) = fun _ => c := by
  funext y
  rw [coupledDriftRegraph]
  simp

end Regraph

section AllTimeInvariance

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Y] [CompleteSpace E] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem coupledDrift_graphSet_isInvariant_allTime (ε : ℝ) (b : Y) (rate : ℝ) (c : E) :
    IsInvariant (coupledDriftFlow (Y := Y) ε b rate c).toFun (graphSet (fun _ : Y => c)) := by
  intro t p hp
  have hmap := coupled_allTimeRegraph ε b rate c t (fun _ : Y => c) hp
  rwa [coupledDriftRegraph_const ε b rate c t] at hmap

end AllTimeInvariance

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Y] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_coupledDrift (ε : ℝ) (b : Y) (rate : ℝ) (c : E) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c τ hrate hτ
    let F := coupledDriftCoupled (Y := Y) (E := E) ε b rate c τ
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G F
  refine graphTransform_discrete_invariant_and_dist_le G F ?_
  show F.op (G.manifold : Y → E) = (G.manifold : Y → E)
  have hman : (G.manifold : Y →ᵇ E) = BoundedContinuousFunction.const Y c :=
    contractGapData_manifold rate c τ hrate hτ
  have hman' : (G.manifold : Y → E) = fun _ : Y => c := by
    funext y; rw [hman]; rw [BoundedContinuousFunction.const_apply']
  rw [coupledDriftCoupled_op, hman']
  exact coupledDriftRegraph_const ε b rate c τ

end Persistence

end ODE
