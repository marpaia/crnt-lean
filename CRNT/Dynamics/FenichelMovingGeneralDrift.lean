import CRNT.Dynamics.FenichelGeneralDrift

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

section InjectiveBase

variable {Y : Type*}

/-- **An injective slow base flow with its time-`τ` left-inverse.** Bundles a forward semiflow
`slowFlow : Flow ℝ≥0 Y` of the slow base, the horizon `τ`, and a left-inverse `slowInv` of the
time-`τ` base map `slowFlow.toFun τ` as data: `slowInv (slowFlow.toFun τ y) = y`. The back-map
`slowInv` is what undoes the base motion when re-expressing the time-`τ` image of a non-constant graph
over the base. -/
structure InjectiveBaseFlow (Y : Type*) [TopologicalSpace Y] where
  /-- The forward semiflow of the slow base field. -/
  slowFlow : Flow ℝ≥0 Y
  /-- The horizon at which the graph transform is taken. -/
  τ : ℝ≥0
  /-- A left-inverse of the time-`τ` base map. -/
  slowInv : Y → Y
  /-- `slowInv` undoes the time-`τ` base motion: `slowInv (slowFlow τ y) = y`. -/
  leftInverse : LeftInverse slowInv (slowFlow.toFun τ)

variable [TopologicalSpace Y]

/-- Build an `InjectiveBaseFlow` from an injectivity proof of the time-`τ` base map: the left-inverse
is `Function.invFun (slowFlow.toFun τ)`, honest for any injective base flow. -/
noncomputable def InjectiveBaseFlow.ofInjective (slowFlow : Flow ℝ≥0 Y) (τ : ℝ≥0)
    (hinj : Injective (slowFlow.toFun τ)) [Nonempty Y] : InjectiveBaseFlow Y where
  slowFlow := slowFlow
  τ := τ
  slowInv := Function.invFun (slowFlow.toFun τ)
  leftInverse := Function.leftInverse_invFun hinj

end InjectiveBase

section InjectivityFromCurves

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Time maps of an ODE flow are injective.** For a flow whose orbits `γ x` are the integral curves
of an autonomous Lipschitz field `f` — the `CRNT.Dynamics.FlowConstruction`'s `exists_flow` output —
the time-`t` map `ϕ t` is injective: two integral curves that agree at time `t` are the same global
curve by two-sided uniqueness, so they agree at time `0`, i.e. have the same starting point. No base
smoothness beyond the Lipschitz field is needed. -/
theorem flow_toFun_injective {f : Y → Y} {K : ℝ≥0} (hl : LipschitzWith K f)
    {ϕ : Flow ℝ≥0 Y} {γ : Y → ℝ → Y} (hγ0 : ∀ x, γ x 0 = x)
    (hγd : ∀ x t, HasDerivAt (γ x) (f (γ x t)) t) (hϕ : ∀ x (t : ℝ≥0), ϕ.toFun t x = γ x (t : ℝ))
    (t : ℝ≥0) : Injective (ϕ.toFun t) := by
  intro x₁ x₂ hx
  rw [hϕ, hϕ] at hx
  -- two integral curves agreeing at time `t` agree everywhere (two-sided uniqueness)
  have heq : γ x₁ = γ x₂ :=
    ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => Set.univ)
      (fun _ => hl.lipschitzOnWith) (fun s => ⟨hγd x₁ s, Set.mem_univ _⟩)
      (fun s => ⟨hγd x₂ s, Set.mem_univ _⟩) hx
  have := congrFun heq 0
  rwa [hγ0 x₁, hγ0 x₂] at this

end InjectivityFromCurves

section MovingRegraph

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The moving-target regraph of a section under the time-`τ` product flow over an injective general
base: `op h y = c + e^{-rate·τ}·(h (slowInv y) - c)`. The base back-map `slowInv` undoes the base
motion — a point of the image graph over base `y` came from base `slowInv y` — and the fibre
contraction scales the read-off section value toward `c`. -/
noncomputable def movingRegraph (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) (h : Y → E) : Y → E :=
  fun y => c + Real.exp (-rate * (B.τ : ℝ)) • (h (B.slowInv y) - c)

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The product flow regraphs a non-constant section at the horizon.** The time-`τ` product
semiflow over the injective general base carries the graph of *any* section `h` into the graph of
`movingRegraph B rate c h`: a point `(y, h y)` lands over the moved base point `slowFlow τ y`, where
the back-map reads `slowInv (slowFlow τ y) = y` so the regraphed fibre value `c + e^{-rate·τ}·(h y - c)`
matches the flowed fibre exactly. This discharges `flow_mapsTo` for a genuinely moving target over a
genuinely nonlinear base. -/
theorem movingFlow_mapsTo (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) (h : Y → E) :
    MapsTo ((productContractFlow B.slowFlow rate c).toFun B.τ) (graphSet h)
      (graphSet (movingRegraph B rate c h)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [productContractFlow_toFun, mem_graphSet, movingRegraph, B.leftInverse p.1, hp]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The moving regraph fixes the constant-section graph at the target.** Over the constant section
`c` the base back-map reads a value already equal to `c`, so the contraction holds it: the moving
regraph sends the constant section back to itself. The Banach fixed point of the fibre contraction is
this constant section, so the moving machinery collapses to constant-fibre invariance over the
nonlinear base on the persisted manifold. -/
theorem movingRegraph_const (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    movingRegraph B rate c (fun _ : Y => c) = fun _ : Y => c := by
  funext y
  rw [movingRegraph]
  simp

/-- **The concrete moving-target coupled-flow graph transform over an injective general base.**
Assembled from the genuine product semiflow whose base flows by the general — possibly nonlinear —
field `B.slowFlow`, with the graph-transform operator at horizon `τ` proved — not assumed — to be the
flow-then-regraph map `movingRegraph B rate c`. This discharges the `flow_mapsTo` hypothesis of
`CoupledFlowGraphTransform` for a non-constant fibre over a nonlinear base. -/
noncomputable def movingCoupled (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    CoupledFlowGraphTransform Y E where
  flow := productContractFlow B.slowFlow rate c
  τ := B.τ
  op := movingRegraph B rate c
  flow_mapsTo h := movingFlow_mapsTo B rate c h

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem movingCoupled_op (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    (movingCoupled B rate c).op = movingRegraph B rate c := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem movingCoupled_τ (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    (movingCoupled B rate c).τ = B.τ := rfl

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
@[simp] theorem movingCoupled_flow (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    (movingCoupled B rate c).flow = productContractFlow B.slowFlow rate c := rfl

end MovingRegraph

section Persistence

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_movingGeneralDrift (B : InjectiveBaseFlow Y) (rate : ℝ) (c : E)
    (hrate : 0 < rate) (hτ : 0 < (B.τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c B.τ hrate hτ
    let F := movingCoupled B rate c
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G F
  refine graphTransform_discrete_invariant_and_dist_le G F ?_
  show F.op (G.manifold : Y → E) = (G.manifold : Y → E)
  have hman : (G.manifold : Y →ᵇ E) = BoundedContinuousFunction.const Y c :=
    contractGapData_manifold rate c B.τ hrate hτ
  have hman' : (G.manifold : Y → E) = fun _ : Y => c := by
    funext y; rw [hman, BoundedContinuousFunction.const_apply']
  rw [movingCoupled_op, hman']
  exact movingRegraph_const B rate c

end Persistence

section AffineInstance

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The genuine forward semiflow of the constant-velocity slow field `ẏ = v` on a normed space `Y`:
`(y, t) ↦ y + t·v`. Its base motion is a genuine translation flow with an explicit time-`τ`
left-inverse `y ↦ y - τ·v`. -/
noncomputable def affineBaseFlow (v : Y) : Flow ℝ≥0 Y where
  toFun t y := y + (t : ℝ) • v
  cont' := by
    refine continuous_snd.add ?_
    exact (NNReal.continuous_coe.comp continuous_fst).smul continuous_const
  map_add' t₁ t₂ y := by
    show y + ((t₁ + t₂ : ℝ≥0) : ℝ) • v = (y + (t₂ : ℝ) • v) + (t₁ : ℝ) • v
    rw [NNReal.coe_add, add_smul, add_assoc, add_comm ((t₂ : ℝ) • v) ((t₁ : ℝ) • v)]
  map_zero' y := by show y + ((0 : ℝ≥0) : ℝ) • v = y; simp

omit [CompleteSpace Y] in
@[simp] theorem affineBaseFlow_toFun (v : Y) (t : ℝ≥0) (y : Y) :
    (affineBaseFlow v).toFun t y = y + (t : ℝ) • v := rfl

omit [CompleteSpace Y] in
/-- The time-`τ` map of the affine base flow is injective: it is the translation `y ↦ y + τ·v`. -/
theorem affineBaseInjective (v : Y) (τ : ℝ≥0) : Injective ((affineBaseFlow v).toFun τ) := by
  intro y₁ y₂ h
  simpa using h

/-- The injective affine slow base flow with its explicit translation left-inverse `y ↦ y - τ·v`. -/
noncomputable def affineInjectiveBase (v : Y) (τ : ℝ≥0) : InjectiveBaseFlow Y where
  slowFlow := affineBaseFlow v
  τ := τ
  slowInv := fun y => y - (τ : ℝ) • v
  leftInverse := fun y => by simp

omit [CompleteSpace Y] in
@[simp] theorem affineInjectiveBase_τ (v : Y) (τ : ℝ≥0) : (affineInjectiveBase v τ).τ = τ := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Y] in
/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem graphTransform_discrete_invariant_and_dist_le_affineBase (v : Y) (rate : ℝ) (c : E) (τ : ℝ≥0)
    (hrate : 0 < rate) (hτ : 0 < (τ : ℝ)) :
    let G := contractGapData (Y := Y) (E := E) rate c τ hrate hτ
    IsInvariant (fun n : ℕ => (productContractFlow (affineBaseFlow v) rate c).toFun (n • τ))
        (graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) := by
  intro G
  exact graphTransform_discrete_invariant_and_dist_le_movingGeneralDrift (affineInjectiveBase v τ) rate c hrate hτ

end AffineInstance

end ODE
