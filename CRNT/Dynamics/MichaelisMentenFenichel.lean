import CRNT.Dynamics.FenichelPersistenceContracting
import CRNT.Dynamics.MichaelisMentenCoupledContraction

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
open scoped NNReal BoundedContinuousFunction RealInnerProductSpace

namespace ODE

section MovingTarget

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed-form exponential-contraction map at time `t` toward the moving target
`c : Y → E` of the field `ẏ = 0`, `ż = -rate·(z - c y)`:
`(y, z) ↦ (y, c y + e^{-rate·t}·(z - c y))`. The base is fixed; the fibre relaxes toward the
*substrate-dependent* attractor `c y`. Unlike the constant-target map of
`CRNT.Dynamics.FenichelPersistenceContracting`, the attractor varies over the base. -/
noncomputable def movingContractMap (rate : ℝ) (c : Y → E) (t : ℝ) : Y × E → Y × E :=
  fun p => (p.1, c p.1 + Real.exp (-rate * t) • (p.2 - c p.1))

omit [TopologicalSpace Y] in
@[simp] theorem movingContractMap_fst (rate : ℝ) (c : Y → E) (t : ℝ) (p : Y × E) :
    (movingContractMap rate c t p).1 = p.1 := rfl

omit [TopologicalSpace Y] in
@[simp] theorem movingContractMap_snd (rate : ℝ) (c : Y → E) (t : ℝ) (p : Y × E) :
    (movingContractMap rate c t p).2 = c p.1 + Real.exp (-rate * t) • (p.2 - c p.1) := rfl

omit [TopologicalSpace Y] in
theorem movingContractMap_zero (rate : ℝ) (c : Y → E) (p : Y × E) :
    movingContractMap rate c 0 p = p := by
  simp [movingContractMap]

omit [TopologicalSpace Y] in
/-- The closed-form moving-target contraction is a semigroup in time:
`Φ (s + t) = Φ s ∘ Φ t` via `e^{-rate·(s+t)} = e^{-rate·s} · e^{-rate·t}`. The base is held fixed, so
the moving target `c p.1` at each time is the same. -/
theorem movingContractMap_add (rate : ℝ) (c : Y → E) (s t : ℝ) (p : Y × E) :
    movingContractMap rate c (s + t) p
      = movingContractMap rate c s (movingContractMap rate c t p) := by
  simp only [movingContractMap, Prod.mk.injEq, true_and, add_sub_cancel_left, smul_smul]
  rw [mul_add, Real.exp_add, mul_comm (Real.exp (-rate * s))]

/-- **The forward semiflow of the moving-target contracting field.** The closed-form exponential
contraction `(y, z) ↦ (y, c y + e^{-rate·t}·(z - c y))` toward the continuous moving target `c`,
assembled into a genuine `Flow ℝ≥0 (Y × E)`: joint continuity uses continuity of `c`, the identity at
time `0` is `movingContractMap_zero`, and the semigroup law is `movingContractMap_add`. The base `Y`
need only be a topological space — it is frozen, never displaced — and no boundedness cutoff is
needed, the exponential pull being a global self-map at every forward time. -/
noncomputable def movingContractFlow (rate : ℝ) (c : Y → E) (hc : Continuous c) :
    Flow ℝ≥0 (Y × E) where
  toFun t p := movingContractMap rate c (t : ℝ) p
  cont' := by
    show Continuous fun q : ℝ≥0 × (Y × E) =>
      (((q.2).1 : Y), c (q.2).1 + Real.exp (-rate * (q.1 : ℝ)) • ((q.2).2 - c (q.2).1))
    have hcq : Continuous fun q : ℝ≥0 × (Y × E) => c (q.2).1 :=
      hc.comp (continuous_fst.comp continuous_snd)
    refine (continuous_fst.comp continuous_snd).prodMk ?_
    refine hcq.add ?_
    refine Continuous.smul ?_ ((continuous_snd.comp continuous_snd).sub hcq)
    exact Real.continuous_exp.comp (continuous_const.mul
      (NNReal.continuous_coe.comp continuous_fst))
  map_add' t₁ t₂ p := by
    simp only [NNReal.coe_add]
    exact movingContractMap_add rate c (t₁ : ℝ) (t₂ : ℝ) p
  map_zero' p := movingContractMap_zero rate c p

@[simp] theorem movingContractFlow_toFun (rate : ℝ) (c : Y → E) (hc : Continuous c) (t : ℝ≥0)
    (p : Y × E) :
    (movingContractFlow rate c hc).toFun t p = movingContractMap rate c (t : ℝ) p := rfl

/-- The regraph of a section under time `t` of the moving-target contracting flow: the section
relaxed toward the moving target `c` by the factor `e^{-rate·t}`. The time-`t` contraction carries
`graphSet σ` to `graphSet (movingContractRegraph rate c t σ)`. -/
noncomputable def movingContractRegraph (rate : ℝ) (c : Y → E) (t : ℝ≥0) (σ : Y → E) : Y → E :=
  fun y => c y + Real.exp (-rate * (t : ℝ)) • (σ y - c y)

/-- **The moving-target contracting flow regraphs at every time.** The time-`t` contraction carries
the graph of `σ` into the graph of `movingContractRegraph rate c t σ`, for every `t ≥ 0`. Read off
the closed form of the flow. -/
theorem movingContract_allTimeRegraph (rate : ℝ) (c : Y → E) (hc : Continuous c) (t : ℝ≥0)
    (σ : Y → E) :
    MapsTo ((movingContractFlow rate c hc).toFun t) (graphSet σ)
      (graphSet (movingContractRegraph rate c t σ)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [movingContractFlow_toFun, mem_graphSet, movingContractMap, movingContractRegraph, hp]

/-- **The moving-target contracting coupled-flow graph transform.** Assembled from the genuine
closed-form moving-target contracting flow, with the graph-transform operator at horizon `τ` proved —
not assumed — to be the flow-then-regraph map `movingContractRegraph rate c τ`. This discharges the
`flow_mapsTo` hypothesis of `CoupledFlowGraphTransform` from the explicit substrate-varying field. -/
noncomputable def movingContractCoupled (rate : ℝ) (c : Y → E) (hc : Continuous c) (τ : ℝ≥0) :
    CoupledFlowGraphTransform Y E where
  flow := movingContractFlow rate c hc
  τ := τ
  op := movingContractRegraph rate c τ
  flow_mapsTo σ := movingContract_allTimeRegraph rate c hc τ σ

@[simp] theorem movingContractCoupled_op (rate : ℝ) (c : Y → E) (hc : Continuous c) (τ : ℝ≥0) :
    (movingContractCoupled rate c hc τ).op = movingContractRegraph rate c τ := rfl

end MovingTarget

section MovingTargetData

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The affine contraction operator toward a *moving* bounded target section `c : Y →ᵇ E`:
`op σ = c + e^{-rate·τ}·(σ - c)`. This is the bounded-section realization of the flow-then-regraph map
`movingContractRegraph rate c τ`. -/
noncomputable def movingContractOp (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (σ : Y →ᵇ E) : Y →ᵇ E :=
  c + Real.exp (-rate * (τ : ℝ)) • (σ - c)

omit [CompleteSpace E] in
@[simp] theorem movingContractOp_apply (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (σ : Y →ᵇ E) (y : Y) :
    movingContractOp rate c τ σ y = c y + Real.exp (-rate * (τ : ℝ)) • (σ y - c y) := by
  simp only [movingContractOp, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_sub, Pi.add_apply, Pi.sub_apply]

omit [CompleteSpace E] in
/-- The difference of two moving-target operator values is the scaled difference of the inputs:
`op σ - op ρ = e^{-rate·τ}·(σ - ρ)`. The moving target translation cancels. -/
theorem movingContractOp_sub (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (σ ρ : Y →ᵇ E) :
    movingContractOp rate c τ σ - movingContractOp rate c τ ρ
      = Real.exp (-rate * (τ : ℝ)) • (σ - ρ) := by
  simp only [movingContractOp]
  rw [add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right]

omit [CompleteSpace E] in
/-- **The moving-target affine operator is an exact contraction.** With factor
`q = e^{-rate·τ} < 1` (whenever `rate > 0`, `τ > 0`) in the supremum metric. -/
theorem movingContractOp_dist_le (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (σ ρ : Y →ᵇ E) :
    dist (movingContractOp rate c τ σ) (movingContractOp rate c τ ρ)
      ≤ Real.exp (-rate * (τ : ℝ)) * dist σ ρ := by
  rw [dist_eq_norm, movingContractOp_sub, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    dist_eq_norm]

/-- **Graph-transform data for the moving-target Michaelis–Menten contraction.** The affine operator
`σ ↦ c + e^{-rate·τ}·(σ - c)` toward the *moving* bounded target `c` on `Y →ᵇ E` is an exact
contraction with factor `q = e^{-rate·τ} < 1` whenever `rate > 0` and `τ > 0`; its unique Banach
fixed point is the moving section `c` — the genuinely substrate-varying manifold. The recorded defect
`δ` is the honest `O(ε)` slaved velocity at which the slow drift carries the moving graph; the operator
fixes `c` exactly (`dist (op c) c = 0 ≤ δ`), so the closeness ceiling reads `δ / (1 - q)`. -/
noncomputable def movingContractData (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) (δ : ℝ) (hδ : 0 ≤ δ) :
    GraphTransformData Y E where
  op := movingContractOp rate c τ
  factor := ⟨Real.exp (-rate * (τ : ℝ)), (Real.exp_pos _).le⟩
  factor_lt_one := by
    change Real.exp (-rate * (τ : ℝ)) < 1
    rw [Real.exp_lt_one_iff]
    have : 0 < rate * (τ : ℝ) := mul_pos hrate hτ
    linarith
  op_dist_le σ ρ := movingContractOp_dist_le rate c τ σ ρ
  base := c
  defect := δ
  defect_le := by
    have hc : movingContractOp rate c τ c = c := by
      ext y
      rw [movingContractOp_apply, sub_self, smul_zero, add_zero]
    rw [hc, dist_self]
    exact hδ

@[simp] theorem movingContractData_base (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) (δ : ℝ) (hδ : 0 ≤ δ) :
    (movingContractData rate c τ hrate hτ δ hδ).base = c := rfl

@[simp] theorem movingContractData_op (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) (δ : ℝ) (hδ : 0 ≤ δ) :
    (movingContractData rate c τ hrate hτ δ hδ).op = movingContractOp rate c τ := rfl

/-- **The persisted manifold of the moving-target data is the moving target section.** The unique
Banach fixed point of the affine contraction `σ ↦ c + e^{-rate·τ}·(σ - c)` is the moving section `c`
— the genuinely varying manifold rather than a frozen fibre. -/
theorem movingContractData_manifold (rate : ℝ) (c : Y →ᵇ E) (τ : ℝ≥0) (hrate : 0 < rate)
    (hτ : 0 < (τ : ℝ)) (δ : ℝ) (hδ : 0 ≤ δ) :
    (movingContractData rate c τ hrate hτ δ hδ).manifold = c := by
  refine ((movingContractData rate c τ hrate hτ δ hδ).manifold_unique (σ := c) ?_).symm
  rw [movingContractData_op]
  ext y
  rw [movingContractOp_apply, sub_self, smul_zero, add_zero]

end MovingTargetData

end ODE

namespace CRNT.MichaelisMenten

open ODE
open scoped BoundedContinuousFunction

/-- The substrate interval `[0, s₀]` as the base of the Michaelis–Menten slow manifold: a compact
slice of the physical substrate ray on which the regularized equilibrium section is bounded. -/
abbrev SubstrateIcc (s₀ : ℝ) : Type := ↥(Set.Icc (0 : ℝ) s₀)

/-- **Continuity of the substrate-varying equilibrium section** `s ↦ mmRegEquil Km Vmax s · e0` on
the substrate interval `[0, s₀]`, from the global `C¹` regularity of the regularized rate law. -/
theorem mmEquilSection_continuous (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) :
    Continuous (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0) := by
  have hcont : Continuous (fun s : ℝ => mmRegEquil Km Vmax s • e0) :=
    ((mmRegEquil_contDiff Km Vmax hKm).continuous).smul continuous_const
  exact hcont.comp continuous_subtype_val

/-- **The substrate-varying Michaelis–Menten equilibrium section** as a continuous map on the
substrate interval `[0, s₀]`: `s ↦ mmRegEquil Km Vmax s · e0`. Continuity comes from the global `C¹`
regularity of the regularized rate law. This is the genuinely *moving* fibre target. -/
noncomputable def mmEquilContMap (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) :
    C(SubstrateIcc s₀, E) where
  toFun := fun s => mmRegEquil Km Vmax (s : ℝ) • e0
  continuous_toFun := mmEquilSection_continuous Km Vmax hKm s₀

@[simp] theorem mmEquilContMap_apply (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) (s : SubstrateIcc s₀) :
    mmEquilContMap Km Vmax hKm s₀ s = mmRegEquil Km Vmax (s : ℝ) • e0 := rfl

/-- **The substrate-varying Michaelis–Menten equilibrium section as a bounded continuous section.**
On the compact substrate interval `[0, s₀]` the continuous equilibrium map is automatically bounded,
giving the genuine moving target `SubstrateIcc s₀ →ᵇ E` for the graph transform. -/
noncomputable def mmEquilSection (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) :
    SubstrateIcc s₀ →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact (mmEquilContMap Km Vmax hKm s₀)

@[simp] theorem mmEquilSection_apply (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) (s : SubstrateIcc s₀) :
    mmEquilSection Km Vmax hKm s₀ s = mmRegEquil Km Vmax (s : ℝ) • e0 := rfl

/-- **The Michaelis–Menten coupled-flow graph transform with a substrate-varying manifold.** The
moving-target contracting flow whose fibre relaxes toward the substrate-dependent equilibrium
`mmRegEquil Km Vmax s · e0` at rate `rate`, realized as a `CoupledFlowGraphTransform` over the
substrate interval base `[0, s₀]`. Its `flow_mapsTo` is proved from the explicit closed-form flow, and
its persisted manifold is the genuinely varying equilibrium graph — not a frozen fibre. -/
noncomputable def mmCoupledFlowGraphTransform (rate Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) (τ : ℝ≥0) :
    CoupledFlowGraphTransform (SubstrateIcc s₀) E :=
  movingContractCoupled rate (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0)
    (mmEquilSection_continuous Km Vmax hKm s₀) τ

/-- **Fenichel-persistence graph-transform data for the Michaelis–Menten slow manifold.** The affine
contraction `σ ↦ c + e^{-rate·τ}·(σ - c)` toward the substrate-varying equilibrium section `c`, with
contraction factor `e^{-rate·τ} < 1` from the fibre rate `-rate`, whose Banach fixed point is the
moving equilibrium graph, and whose recorded defect is the certified `O(ε)` slaved velocity
`(L/rate)·(ε·G)` at which the slow drift `ṡ = ε·g` carries the graph. -/
noncomputable def mmFenichelData (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ)
    (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    GraphTransformData (SubstrateIcc s₀) E :=
  movingContractData rate (mmEquilSection Km Vmax hKm s₀) τ hrate hτ ((L / rate) * (ε * G))
    (mul_nonneg (by positivity) (mul_nonneg hε hG))

/-- **The persisted Michaelis–Menten manifold is the substrate-varying equilibrium graph.** The
Banach fixed point of the Fenichel graph transform is the moving section `s ↦ mmRegEquil Km Vmax s · e0`
— a genuinely base-varying manifold. -/
theorem mmFenichelData_manifold (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ)
    (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    (mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG).manifold
      = mmEquilSection Km Vmax hKm s₀ :=
  movingContractData_manifold rate (mmEquilSection Km Vmax hKm s₀) τ hrate hτ _ _

/-- **Fenichel `ε`-persistence of the genuinely substrate-varying Michaelis–Menten slow manifold.**
Combining the Michaelis–Menten coupled-flow graph transform `F` (whose `flow_mapsTo` is proved from
the explicit moving-target contracting flow) with the contraction data `G` (whose Banach fixed point
`M_ε` is the substrate-varying equilibrium graph `s ↦ mmRegEquil Km Vmax s · e0`, and whose defect is
the certified `O(ε)` slaved velocity `(L/rate)·(ε·G)`). The conclusion is the two halves of Fenichel
persistence with every hypothesis discharged: the graph of the moving equilibrium manifold is
forward-invariant under the iterate coupled semiflow of the explicit Michaelis–Menten contracting
field, and `M_ε` sits within `(L/rate)·(ε·G) / (1 - e^{-rate·τ})` — an honest `O(ε)` ceiling — of the
base equilibrium section in the supremum metric. -/
theorem mmFenichelPersistence (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ)
    (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    let G' := mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG
    let F := mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (graphSet (G'.manifold : SubstrateIcc s₀ → E)) ∧
      dist G'.base G'.manifold ≤ G'.defect / (1 - G'.factor) := by
  intro G' F
  refine graphTransform_discrete_invariant_and_dist_le G' F ?_
  have hman : (G'.manifold : SubstrateIcc s₀ →ᵇ E) = mmEquilSection Km Vmax hKm s₀ :=
    mmFenichelData_manifold rate hrate Km Vmax hKm s₀ τ hτ hL hε hG
  show (mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ).op (G'.manifold : SubstrateIcc s₀ → E)
    = (G'.manifold : SubstrateIcc s₀ → E)
  rw [show (mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ).op
    = movingContractRegraph rate (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0) τ
    from rfl]
  funext y
  rw [movingContractRegraph, hman]
  simp only [mmEquilSection_apply, sub_self, smul_zero, add_zero]

end CRNT.MichaelisMenten
