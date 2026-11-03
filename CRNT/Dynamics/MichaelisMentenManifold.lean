import CRNT.Dynamics.FenichelManifold
import CRNT.Dynamics.MichaelisMenten
import CRNT.Dynamics.QSSA
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Michaelis–Menten reduction on the constructed slow manifold

This module upgrades the flat-fibre quasi-steady-state reduction of `CRNT.Dynamics.MichaelisMenten`
to a genuinely **substrate-dependent** reduction whose reduced complex coordinate tracks the
Michaelis–Menten quasi-equilibrium `z = h(s)` as a function of substrate `s`, rather than a fixed
fibre. It consumes the constructed slow-manifold map of `CRNT.Dynamics.FenichelManifold`
(`ODE.SlowManifoldSeed`, `manifoldMap`, `manifoldMap_eq_of_stationary`, `continuous_manifoldMap`)
and the compact-time Grönwall envelope of `CRNT.Dynamics.QSSA`. It lives in the
`CRNT.MichaelisMenten` namespace, a sibling of the flat reduction, reusing the enzyme-kinetics
state space `E := EuclideanSpace ℝ (Fin 2)`.

**Substrate-dependent fast field** (`mmFastField`). Over substrate `s`, the fast field
`mmFastField rate Km Vmax s z = -rate • (z - mmComplexEquil Km Vmax s • e0)` relaxes the complex
coordinate linearly toward `mmComplexEquil Km Vmax s • e0`, where
`mmComplexEquil Km Vmax s = Vmax * s / (Km + s)` is the substrate-dependent Michaelis–Menten
complex level and `e0 := EuclideanSpace.single 0 1`. Each fibre is stationary at that level
(`mmFastField_stat`) and, for `0 ≤ rate`, one-sided contracting toward it at `rate`
(`mmFastField_oneSidedContraction`) — the genuine slow-variable dependence, not a fixed point.

**The seed and the constructed map** (`mmSlowManifoldSeed`, `mmManifoldMap_eq`). Bundling the
field, rate, and per-fibre stationarity/contraction yields an `ODE.SlowManifoldSeed ℝ E`. Its
constructed `manifoldMap` (defined via `Classical.choose`) is pinned to the explicit
Michaelis–Menten curve `mmManifoldMap_eq : manifoldMap s = mmComplexEquil Km Vmax s • e0` through
the canonicity lemma `SlowManifoldSeed.manifoldMap_eq_of_stationary`: this is what makes the
reduction *true* — the abstract constructed graph equals the substrate-dependent MM equilibrium.
Rewriting along this identity gives continuity on `{s | 0 ≤ s}` under `0 < Km`
(`continuousOn_mmManifoldMap`).

**Reduction error theorem** (`michaelisMenten_manifold_qssa_error`,
`michaelisMenten_manifold_qssa_error_const`). For a `K`-Lipschitz full mass-action field `full`,
an exact integral curve `γ`, and a substrate path `σ` whose lifted reduced curve
`t ↦ manifoldMap (σ t)` is continuous on `[0, T]`, has right derivative `γᵣ'`, and carries
slaving defect at most `εf`, the exact trajectory stays within `gronwallBound δ K εf T` of the
substrate-dependent reduced curve on `[0, T]`, and that bound tends to `0` as the initial mismatch
and the defect jointly vanish (a direct application of `ODE.qssa_error_tendsto_zero`). The
convenience corollary rewrites the bound against the explicit curve
`t ↦ mmComplexEquil Km Vmax (σ t) • e0`, exhibiting that the manifold tracks the MM rate law.

**Scope.** The reduction here is substrate-dependent and
compact-time; it is not a fully ε-quantified Fenichel reduction. (1) The slaving defect
`εf` and initial mismatch `δ` are hypotheses, not quantities derived from a singular-perturbation
small parameter `ε`: making `εf = O(ε)` needs the slow drift along the manifold to be genuinely
`O(ε)` and derived from a coupled slow ODE `ṡ = ε g(s, z)` with a uniform-in-`ε` estimate. (2)
ε-positive normally-hyperbolic invariant-manifold persistence is absent from Mathlib v4.31: there is
no construction perturbing the exact `ε = 0` invariant graph `{(s, manifoldMap s)}` to a nearby
invariant manifold for `ε > 0`, so `manifoldMap`'s `C¹` regularity is also unavailable (it needs an
invertible fibre-derivative and the implicit function theorem) — only Lipschitz/continuous is
reachable. (3) Infinite-horizon shadowing is unavailable: `gronwallBound δ K εf T` diverges as
`T → ∞` for `K > 0`, so all claims stay on compact `[0, T]`. (4) The substrate path `σ` and its
slaving (the right-derivative and defect hypotheses) are inputs; closing the loop — proving the full
trajectory's substrate component actually solves the reduced scalar MM ODE `ṡ = -Vmax·s/(Km+s)` —
needs a parametrised slow-drift field coupled to `manifoldMap` and its own scalar Grönwall closure.

Depends on: CRNT.Dynamics.FenichelManifold,
CRNT.Dynamics.MichaelisMenten, CRNT.Dynamics.QSSA, Mathlib.Analysis.InnerProductSpace.PiL2.
-/

open Filter Set
open scoped Topology RealInnerProductSpace NNReal

namespace CRNT.MichaelisMenten

-- The enzyme-kinetics state space `E` (the slow/fast reduced coordinates of `E + S ⇌ ES → E + P`)
-- is reused from `CRNT.Dynamics.MichaelisMenten`.

/-- A fixed basis direction carrying the complex coordinate. -/
noncomputable def e0 : E := EuclideanSpace.single 0 1

/-- The substrate-dependent Michaelis–Menten quasi-equilibrium complex level
`Vmax * s / (Km + s)` as a function of substrate `s`. -/
noncomputable def mmComplexEquil (Km Vmax s : ℝ) : ℝ := Vmax * s / (Km + s)

/-- The substrate-dependent fast (enzyme-complex) field over substrate `s`:
`mmFastField rate Km Vmax s z = -rate • (z - mmComplexEquil Km Vmax s • e0)`. It relaxes the
complex coordinate linearly toward the substrate-dependent quasi-equilibrium `mmComplexEquil … s`
at uniform rate `rate`. -/
noncomputable def mmFastField (rate Km Vmax : ℝ) : ℝ → E → E :=
  fun s z => -rate • (z - mmComplexEquil Km Vmax s • e0)

/-- The fast field is stationary at the substrate-dependent equilibrium fibre. -/
lemma mmFastField_stat (rate Km Vmax s : ℝ) :
    mmFastField rate Km Vmax s (mmComplexEquil Km Vmax s • e0) = 0 := by
  simp [mmFastField]

/-- The substrate fast field is one-sided contracting toward its equilibrium fibre at rate
`rate ≥ 0`: `⟪-rate • (z - q), z - q⟫ = -rate * ‖z - q‖²`, where `q = mmComplexEquil … s • e0`. -/
lemma mmFastField_oneSidedContraction (rate Km Vmax s : ℝ) (_h : 0 ≤ rate) :
    ODE.OneSidedContraction (mmFastField rate Km Vmax s) (mmComplexEquil Km Vmax s • e0) rate := by
  intro z
  set q : E := mmComplexEquil Km Vmax s • e0 with hq
  have hstat : mmFastField rate Km Vmax s q = 0 := mmFastField_stat rate Km Vmax s
  show ⟪mmFastField rate Km Vmax s z - mmFastField rate Km Vmax s q, z - q⟫
      ≤ -rate * ‖z - q‖ ^ 2
  rw [hstat, sub_zero]
  show ⟪-rate • (z - q), z - q⟫ ≤ -rate * ‖z - q‖ ^ 2
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The Michaelis–Menten slow-manifold **seed**: the parametrised substrate fast field, its
positive contraction rate, per-fibre existence of the equilibrium, and per-fibre one-sided
contraction toward any equilibrium. This is the central consumption of the constructed
slow-manifold machinery. -/
noncomputable def mmSlowManifoldSeed (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    ODE.SlowManifoldSeed ℝ E where
  fast := mmFastField rate Km Vmax
  rate := rate
  rate_pos := hrate
  exists_stat := fun s => ⟨mmComplexEquil Km Vmax s • e0, mmFastField_stat rate Km Vmax s⟩
  contraction := by
    intro s zstar hzs
    -- Stationarity of the linear field forces `zstar` to be the equilibrium fibre.
    have hzeq : zstar = mmComplexEquil Km Vmax s • e0 := by
      have h : -rate • (zstar - mmComplexEquil Km Vmax s • e0) = 0 := hzs
      rcases smul_eq_zero.1 h with hr | hd
      · exact absurd (neg_eq_zero.1 hr) hrate.ne'
      · exact sub_eq_zero.1 hd
    rw [hzeq]
    exact mmFastField_oneSidedContraction rate Km Vmax s hrate.le

@[simp] lemma mmSlowManifoldSeed_fast (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    (mmSlowManifoldSeed rate hrate Km Vmax).fast = mmFastField rate Km Vmax := rfl

@[simp] lemma mmSlowManifoldSeed_rate (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) :
    (mmSlowManifoldSeed rate hrate Km Vmax).rate = rate := rfl

/-- **Canonicity of the reduction.** The constructed `manifoldMap` of the Michaelis–Menten seed
equals the explicit substrate-dependent complex curve `mmComplexEquil Km Vmax s • e0`. This pins
the abstract `Classical.choose`-constructed graph to the genuine Michaelis–Menten rate law. -/
theorem mmManifoldMap_eq (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap s = mmComplexEquil Km Vmax s • e0 :=
  ((mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap_eq_of_stationary
    (mmFastField_stat rate Km Vmax s)).symm

/-- **Continuity of the constructed manifold map** on the physical substrate domain `s ≥ 0` under
`0 < Km`. Rewriting along `mmManifoldMap_eq` reduces this to continuity of the explicit MM rate
law `s ↦ Vmax * s / (Km + s) • e0`, whose denominator stays positive on `[0, ∞)`. -/
theorem continuousOn_mmManifoldMap (rate : ℝ) (hrate : 0 < rate) {Km : ℝ} (Vmax : ℝ)
    (hKm : 0 < Km) :
    ContinuousOn (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (Ici 0) := by
  have hfun : (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap
      = fun s => mmComplexEquil Km Vmax s • e0 :=
    funext fun s => mmManifoldMap_eq rate hrate Km Vmax s
  rw [hfun]
  refine ContinuousOn.smul (f := fun s => mmComplexEquil Km Vmax s)
    (g := fun _ => e0) ?_ continuousOn_const
  have : mmComplexEquil Km Vmax = fun s => Vmax * s / (Km + s) := rfl
  rw [this]
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro s hs
    have : (0 : ℝ) ≤ s := hs
    positivity

/-- **Substrate-dependent Michaelis–Menten reduction with a compact-time error bound.** Let `full`
be a `K`-Lipschitz full mass-action field and `γ` an exact integral curve of `full`. Let `σ` be a
substrate path whose lifted reduced curve `t ↦ manifoldMap (σ t)` — the genuine substrate-dependent
Michaelis–Menten quasi-equilibrium curve — is continuous on `[0, T]`, has right derivative `γᵣ'`,
and carries slaving defect at most `εf`, with initial mismatch `δ`. Then on every compact interval
`[0, T]` the exact trajectory stays within `gronwallBound δ K εf T` of the reduced curve, and that
Grönwall bound tends to `0` as the initial mismatch and the slaving defect jointly vanish. Unlike
the flat reduction, the reduced curve here tracks `manifoldMap (σ t)`, not a constant fibre. -/
theorem michaelisMenten_manifold_qssa_error (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {σ : ℝ → ℝ} {γ γᵣ' : ℝ → E} {T εf δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hσc : ContinuousOn (fun t => (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ t))
      (Icc 0 T))
    (hσ' : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun t => (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ t))
        (γᵣ' t) (Ici t) t)
    (hdef : ODE.QssaDefect full
      (fun t => (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ t)) γᵣ' 0 T εf)
    (h0 : dist (γ 0) ((mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ 0)) ≤ δ) :
    (∀ t ∈ Icc 0 T,
        dist (γ t) ((mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ t))
          ≤ gronwallBound δ K εf T) ∧
      Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) :=
  ODE.qssa_error_tendsto_zero hl hT hδ hεf hγd hσc hσ' hdef h0

/-- **The reduction tracks the explicit Michaelis–Menten rate law.** Rewriting the
substrate-dependent error bound along `mmManifoldMap_eq`, the exact trajectory stays within
`gronwallBound δ K εf T` of the explicit curve `t ↦ mmComplexEquil Km Vmax (σ t) • e0` on `[0, T]`,
demonstrating that the constructed slow manifold is the genuine Michaelis–Menten complex law. -/
theorem michaelisMenten_manifold_qssa_error_const (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ)
    (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {σ : ℝ → ℝ} {γ γᵣ' : ℝ → E} {T εf δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hσc : ContinuousOn (fun t => mmComplexEquil Km Vmax (σ t) • e0) (Icc 0 T))
    (hσ' : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun t => mmComplexEquil Km Vmax (σ t) • e0) (γᵣ' t) (Ici t) t)
    (hdef : ODE.QssaDefect full (fun t => mmComplexEquil Km Vmax (σ t) • e0) γᵣ' 0 T εf)
    (h0 : dist (γ 0) (mmComplexEquil Km Vmax (σ 0) • e0) ≤ δ) :
    (∀ t ∈ Icc 0 T,
        dist (γ t) (mmComplexEquil Km Vmax (σ t) • e0) ≤ gronwallBound δ K εf T) ∧
      Tendsto (fun p : ℝ × ℝ => gronwallBound p.1 K p.2 T) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  have heq : (fun t => (mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap (σ t))
      = fun t => mmComplexEquil Km Vmax (σ t) • e0 :=
    funext fun t => mmManifoldMap_eq rate hrate Km Vmax (σ t)
  rw [← heq] at hσc hσ' hdef
  rw [← mmManifoldMap_eq rate hrate Km Vmax (σ 0)] at h0
  have key := michaelisMenten_manifold_qssa_error rate hrate Km Vmax full hl hT hδ hεf hγd
    hσc hσ' hdef h0
  refine ⟨fun t ht => ?_, key.2⟩
  have ht' := key.1 t ht
  rwa [mmManifoldMap_eq rate hrate Km Vmax (σ t)] at ht'

end CRNT.MichaelisMenten
