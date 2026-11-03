import CRNT.Dynamics.FenichelLogisticInstance

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

section AllTimeInjectiveBase

variable {Y : Type*}

/-- **A slow base flow injective at every time, with its running left-inverse family.** Bundles a
forward semiflow `slowFlow : Flow ℝ≥0 Y` together with a `t`-indexed left-inverse family
`slowInvAt : ℝ≥0 → Y → Y` of the time-`t` base map: `slowInvAt t (slowFlow.toFun t y) = y` for every
`t`. The family `slowInvAt t` is what undoes the base motion when re-expressing the time-`t` image of
a non-constant graph over the base — at every continuous time, not only at a fixed horizon. -/
structure AllTimeInjectiveBaseFlow (Y : Type*) [TopologicalSpace Y] where
  /-- The forward semiflow of the slow base field. -/
  slowFlow : Flow ℝ≥0 Y
  /-- A left-inverse of the time-`t` base map, indexed by `t`. -/
  slowInvAt : ℝ≥0 → Y → Y
  /-- `slowInvAt t` undoes the time-`t` base motion: `slowInvAt t (slowFlow t y) = y`, for every `t`. -/
  leftInverseAt : ∀ t : ℝ≥0, LeftInverse (slowInvAt t) (slowFlow.toFun t)

variable [TopologicalSpace Y]

/-- Build an `AllTimeInjectiveBaseFlow` from injectivity of the time-`t` base map at *every* `t`: the
running left-inverse family is `fun t => Function.invFun (slowFlow.toFun t)`, honest at each time. -/
noncomputable def AllTimeInjectiveBaseFlow.ofInjective (slowFlow : Flow ℝ≥0 Y)
    (hinj : ∀ t : ℝ≥0, Injective (slowFlow.toFun t)) [Nonempty Y] :
    AllTimeInjectiveBaseFlow Y where
  slowFlow := slowFlow
  slowInvAt t := Function.invFun (slowFlow.toFun t)
  leftInverseAt t := Function.leftInverse_invFun (hinj t)

end AllTimeInjectiveBase

section MovingRegraphAt

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The time-`t` moving-target regraph of a section under the time-`t` product flow over a base
injective at every time: `op t h y = c + e^{-rate·t}·(h (slowInvAt t y) - c)`. The running back-map
`slowInvAt t` undoes the base motion — a point of the image graph over base `y` came from base
`slowInvAt t y` — and the running fibre contraction `e^{-rate·t}` scales the read-off section value
toward `c`. -/
noncomputable def movingRegraphAt (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (c : E) (t : ℝ≥0)
    (h : Y → E) : Y → E :=
  fun y => c + Real.exp (-rate * (t : ℝ)) • (h (B.slowInvAt t y) - c)

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The product flow regraphs a non-constant section at every time.** For *every* `t` and *every*
section `h`, the time-`t` product semiflow over the all-time-injective general base carries the graph
of `h` into the graph of `movingRegraphAt B rate c t h`: a point `(y, h y)` lands over the moved base
point `slowFlow t y`, where the running back-map reads `slowInvAt t (slowFlow t y) = y` so the
regraphed fibre value `c + e^{-rate·t}·(h y - c)` matches the flowed fibre exactly. This is the
genuinely non-constant, all-time moving-target mapping property — the `τ`-restriction removed. -/
theorem movingFlowAt_mapsTo (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (c : E) (t : ℝ≥0)
    (h : Y → E) :
    MapsTo ((productContractFlow B.slowFlow rate c).toFun t) (graphSet h)
      (graphSet (movingRegraphAt B rate c t h)) := by
  intro p hp
  rw [mem_graphSet] at hp
  rw [productContractFlow_toFun, mem_graphSet, movingRegraphAt, B.leftInverseAt t p.1, hp]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **The moving regraph fixes the constant-section graph at every time.** Over the constant section
`c` the running back-map reads a value already equal to `c`, so the running contraction holds it: at
*every* `t` the time-`t` moving regraph sends the constant section back to itself. The Banach fixed
point of the fibre contraction is this constant section, so the all-time moving machinery collapses to
constant-fibre invariance along the whole forward semiflow. -/
theorem movingRegraphAt_const (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (c : E) (t : ℝ≥0) :
    movingRegraphAt B rate c t (fun _ : Y => c) = fun _ : Y => c := by
  funext y
  rw [movingRegraphAt]
  simp

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **All-time non-constant moving-target mapping property.** Packaging `movingFlowAt_mapsTo` as a
single statement quantified over *every* time `t` and *every* candidate section `h`: the continuous
product semiflow regraphs the graph of `h` into the graph of the time-`t` moving target
`movingRegraphAt B rate c t h` at all `t ≥ 0`. The genuinely non-constant continuous-time mapping
property with the "only at multiples of `τ`" restriction removed. -/
theorem movingTarget_mapsTo_allTime (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ) (c : E) :
    ∀ (t : ℝ≥0) (h : Y → E),
      MapsTo ((productContractFlow B.slowFlow rate c).toFun t) (graphSet h)
        (graphSet (movingRegraphAt B rate c t h)) :=
  fun t h => movingFlowAt_mapsTo B rate c t h

end MovingRegraphAt

section ContinuousInvariance

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ Y] [CompleteSpace Y] [CompleteSpace E] in
/-- **Continuous-time invariance of the persisted slow manifold over the moving base.** The constant
attracting fibre `c` is the time-`t` moving target of itself at every `t` (`movingRegraphAt_const`),
so the product flow maps its graph into itself at every `t`: the slow manifold `{(y, c)}` is invariant
under the *full continuous* product semiflow `Φ t` for every `t ≥ 0`. This removes the
multiples-of-`τ` restriction from the moving-target invariance statement — the persisted manifold is
invariant along the whole forward semiflow, with the genuinely non-constant back-map exercised on
every candidate section through `movingFlowAt_mapsTo`. -/
theorem fenichel_continuousMovingTarget_isInvariant (B : AllTimeInjectiveBaseFlow Y) (rate : ℝ)
    (c : E) :
    IsInvariant (productContractFlow B.slowFlow rate c).toFun (graphSet (fun _ : Y => c)) := by
  intro t
  have hmap := movingFlowAt_mapsTo B rate c t (fun _ : Y => c)
  rwa [movingRegraphAt_const B rate c t] at hmap

end ContinuousInvariance

section AffineInstance

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The all-time-injective affine slow base flow `ẏ = v`, with its explicit running left-inverse
family `slowInvAt t : y ↦ y - t·v`. The time-`t` map `y ↦ y + t·v` is injective at every `t`. -/
noncomputable def affineAllTimeBase (v : Y) : AllTimeInjectiveBaseFlow Y where
  slowFlow := affineBaseFlow v
  slowInvAt t := fun y => y - (t : ℝ) • v
  leftInverseAt t := fun y => by simp

omit [CompleteSpace Y] in
@[simp] theorem affineAllTimeBase_slowFlow (v : Y) :
    (affineAllTimeBase v).slowFlow = affineBaseFlow v := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Y] [CompleteSpace E] in
/-- **Continuous-time moving-target persistence over the affine translation base.** Specializing
`fenichel_continuousMovingTarget_isInvariant` to the constant-velocity base `affineBaseFlow`: the
slow manifold `{(y, c)}` is invariant under the *full continuous* product semiflow over the moving
base for every `t ≥ 0`, with the genuinely non-constant time-`t` back-map `y ↦ y - t·v` exercised on
every candidate section through `movingFlowAt_mapsTo`. -/
theorem affineMovingTarget_isInvariant_allTime (v : Y) (rate : ℝ) (c : E) :
    IsInvariant (productContractFlow (affineBaseFlow v) rate c).toFun (graphSet (fun _ : Y => c)) :=
  fenichel_continuousMovingTarget_isInvariant (affineAllTimeBase v) rate c

end AffineInstance

section LogisticInstance

/-- The all-time-injective curved logistic slow base flow `ẏ = ε·sin y`, built from time-`t`
injectivity of the nonlinear base map at every `t` via `AllTimeInjectiveBaseFlow.ofInjective`. The
running left-inverse family is `fun t => Function.invFun (logisticDriftFlow ε |>.toFun t)` — honest,
abstract, with *no closed-form inverse supplied* at any time. -/
noncomputable def logisticAllTimeBase (ε : ℝ) : AllTimeInjectiveBaseFlow ℝ :=
  AllTimeInjectiveBaseFlow.ofInjective (logisticDriftFlow ε) (logisticDriftFlow_injective ε)

@[simp] theorem logisticAllTimeBase_slowFlow (ε : ℝ) :
    (logisticAllTimeBase ε).slowFlow = logisticDriftFlow ε := rfl

/-- **Continuous-time moving-target persistence over the curved logistic base.** Specializing
`fenichel_continuousMovingTarget_isInvariant` to the genuinely nonlinear `ε·sin y` base, whose time-`t`
left-inverse comes from injectivity alone with no closed-form inverse: the slow manifold `{(y, c)}` is
invariant under the *full continuous* product semiflow over the curved base for every `t ≥ 0`. The
non-constant moving-target machinery is honest at every continuous time on a concrete curved example,
the multiples-of-`τ` restriction removed. -/
theorem logisticMovingTarget_isInvariant_allTime (ε : ℝ) (rate : ℝ) (c : ℝ) :
    IsInvariant (productContractFlow (logisticDriftFlow ε) rate c).toFun
      (graphSet (fun _ : ℝ => c)) :=
  fenichel_continuousMovingTarget_isInvariant (logisticAllTimeBase ε) rate c

end LogisticInstance

end ODE
