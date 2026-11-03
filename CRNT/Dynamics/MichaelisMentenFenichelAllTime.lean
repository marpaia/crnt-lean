import CRNT.Dynamics.MichaelisMentenFenichel

/-!
# All-time invariance for a frozen-base Michaelis–Menten graph

The closed-form contracting comparison flow freezes the substrate coordinate and
relaxes the enzyme fibre to its prescribed graph. It provides an explicit invariant
graph example. Tracking the genuine coupled Michaelis–Menten dynamics requires
the separate contraction/error hypotheses in the corresponding tracking modules.
General normally hyperbolic manifold persistence is not supplied by this example.
-/

open Function Set
open scoped NNReal BoundedContinuousFunction

namespace ODE

section MovingTargetAllTime

variable {Y : Type*} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [TopologicalSpace Y] in
/-- The moving target `c` is fixed by the time-`t` regraph of the moving-target contracting flow, for
*every* `t`: `movingContractRegraph rate c t c = c`, since `c y + e^{-rate·t}·(c y - c y) = c y`. -/
theorem movingContractRegraph_self (rate : ℝ) (c : Y → E) (t : ℝ≥0) :
    movingContractRegraph rate c t c = c := by
  funext y
  rw [movingContractRegraph, sub_self, smul_zero, add_zero]

/-- **Continuous-semiflow invariance of the moving equilibrium graph.** The graph of the moving target
`c` is forward-invariant under the *full continuous* moving-target contracting semiflow `Φ t` at every
forward time `t ≥ 0` — not only at multiples of any horizon. The time-`t` flow regraphs `graphSet c`
into `graphSet (movingContractRegraph rate c t c)`, and the moving target is fixed by its own regraph
at every time, so this is `graphSet c` again. -/
theorem movingContractFlow_isInvariant_graphSet (rate : ℝ) (c : Y → E) (hc : Continuous c) :
    IsInvariant (movingContractFlow rate c hc).toFun (graphSet c) := by
  intro t
  have h := movingContract_allTimeRegraph rate c hc t c
  rwa [movingContractRegraph_self rate c t] at h

end MovingTargetAllTime

end ODE

namespace CRNT.MichaelisMenten

open ODE
open scoped BoundedContinuousFunction

/-- **All-time continuous-semiflow invariance of the Michaelis–Menten slow manifold.** The graph of
the substrate-varying equilibrium section `s ↦ mmRegEquil Km Vmax s · e0` is forward-invariant under
the *full continuous* coupled semiflow `Φ t` of the Michaelis–Menten moving-target contracting flow,
at every forward time `t ≥ 0` — upgrading the iterate-semiflow invariance of `mmFenichelPersistence`
to the continuous semiflow. The flow regraphs `graphSet c` into `graphSet (movingContractRegraph rate c t c)`
at every `t`, and the moving equilibrium target is fixed by its own regraph at every time. -/
theorem mmFenichelInvariant_allTime (rate Km Vmax : ℝ) (hKm : 0 < Km) (s₀ : ℝ) (τ : ℝ≥0) :
    IsInvariant (mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ).flow.toFun
      (graphSet (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0)) :=
  movingContractFlow_isInvariant_graphSet rate
    (fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0)
    (mmEquilSection_continuous Km Vmax hKm s₀)

/-- Graph invariance and/or a distance estimate for the displayed explicit flow
and supplied contraction data. This does not assert general perturbed NHIM persistence. -/
theorem mmFenichelPersistence_allTime (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    (s₀ : ℝ) (τ : ℝ≥0) (hτ : 0 < (τ : ℝ)) {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    let G' := mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG
    let F := mmCoupledFlowGraphTransform rate Km Vmax hKm s₀ τ
    IsInvariant F.flow.toFun (graphSet (G'.manifold : SubstrateIcc s₀ → E)) ∧
      dist G'.base G'.manifold ≤ G'.defect / (1 - G'.factor) := by
  intro G' F
  refine ⟨?_, (mmFenichelPersistence rate hrate Km Vmax hKm s₀ τ hτ hL hε hG).2⟩
  have hman : (G'.manifold : SubstrateIcc s₀ → E)
      = fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0 := by
    show ((mmFenichelData rate hrate Km Vmax hKm s₀ τ hτ hL hε hG).manifold : SubstrateIcc s₀ → E)
      = fun s : SubstrateIcc s₀ => mmRegEquil Km Vmax (s : ℝ) • e0
    rw [mmFenichelData_manifold rate hrate Km Vmax hKm s₀ τ hτ hL hε hG]
    funext y
    rw [mmEquilSection_apply]
  rw [hman]
  exact mmFenichelInvariant_allTime rate Km Vmax hKm s₀ τ

end CRNT.MichaelisMenten
