import CRNT.Dynamics.FlowConstruction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# The transversal-crossing-time function

The Poincaré first-return map of a planar flow is built from a more primitive object: the
**first crossing time** of a transversal section. Given the flow line `Φ x : ℝ → E` of an
autonomous field `ẋ = f(x)` through a state `x`, and an affine codimension-one section
`S = { y | ⟪y − p₀, n⟫ = 0 }` that the field crosses transversally at `p₀` (so the
transversal speed `⟪f p₀, n⟫` is nonzero), the crossing time at `x` is the time `τ(x)` with
`Φ x (τ x) ∈ S`. This module constructs `τ` for states near a known transversal crossing and
establishes its existence, local uniqueness, and `C¹` dependence on the initial state.

`Mathlib` carries flows (`Mathlib.Dynamics.Flow`) and the implicit function theorem
(`Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`) but no Poincaré section or
first-return primitive; this is the foundational piece those need.

## The signed section coordinate

The crossing condition `Φ x t ∈ S` is the scalar equation
`g(x, t) = ⟪Φ x t − p₀, n⟫ = 0`. Two partials govern it:

* The **temporal** partialDeriv is the transversal speed `∂_t g(x, t) = ⟪f(Φ x t), n⟫`. It comes
  for free from the integral-curve law `HasDerivAt (Φ x) (f (Φ x t)) t` and is proved here
  (`TransversalSection.hasDeriv_time`). At the crossing it equals `⟪f p₀, n⟫ ≠ 0`, which is the
  nondegeneracy the implicit function theorem requires.
* The **spatial** partialDeriv `∂_x g(x, t)` is the inner product of the section normal with the
  flow's spatial derivative `D_x Φ x t` (the variational/monodromy operator). The spatial
  regularity of a flow is the differentiable dependence on initial conditions, which `Mathlib`
  does not provide for a general Lipschitz field; it is recorded here as DATA on the section,
  mirroring `CRNT.Dynamics.HopfPersistentOrbit.FullRadialField`, whose averaged-field
  regularity is likewise carried as data because the underlying reduction is outside `Mathlib`.

## The crossing time

With both partials in hand, the bivariate implicit function theorem
(`implicitFunctionOfBivariate`) solves `g(x, t) = 0` for `t` as a function of `x` near the
crossing: `crossingTime` is the resulting `τ`, with `τ x → t₀` as `x → x₀`
(`crossingTime_tendsto`), `g(x, τ x) = 0` near `x₀` (`crossingTime_isCrossing`) — i.e. the
flow line of `x` meets `S` at time `τ x` — and a strict Fréchet derivative
(`hasStrictFDerivAt_crossingTime`), hence continuity (`crossingTime_continuousAt`). The strict
derivative is the `C¹` dependence on the initial state.

This abstracts to the planar case used by the Hopf return map: take `E` two-dimensional,
`p₀` the seed crossing of the persisting orbit, `n` the section normal, and the transversal
speed nonzero because the field rotates across the section. The first-return map is then
`x ↦ Φ x (crossingTime x)` restricted to `S`, the composition this module is stated to support.

(Poincaré, *Les méthodes nouvelles de la mécanique céleste*, vol. I, on the section map;
Hartman, *Ordinary Differential Equations*, IX.10, on the differentiable first-return time.)

Depends on: `CRNT.Dynamics.FlowConstruction`,
`Mathlib.Analysis.InnerProductSpace.Calculus`,
`Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate`.
-/

namespace CRNT

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **A nonzero scalar derivative is invertible.** Scaling `ℝ →L[ℝ] ℝ` by a nonzero constant
`c`, the continuous linear map `toSpanSingleton ℝ c : r ↦ r · c`, is a continuous linear
automorphism of `ℝ` — the nondegeneracy the implicit function theorem requires of the temporal
partialDeriv. -/
theorem toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  refine ContinuousLinearMap.ext fun r => ?_
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- **A transversal Poincaré section for a flow line family.**

The data of an autonomous field `field`, a family of flow lines `flow : E → ℝ → E` (one
through each state, `flow x` solving `ẏ = field y` with `flow x 0 = x`), an affine section
`S = { y | ⟪y − point, normal⟫ = 0 }`, a base state `base`, and a base crossing time `time`
at which `base` meets `S` **transversally**.

The temporal regularity (the integral-curve law `hasDeriv_flow`) is intrinsic and supplies the
transversal-speed partialDeriv. The spatial regularity of the flow — its differentiable dependence
on the initial state, recorded by `spaceDeriv` together with `hasFDeriv_space` and
`cont_spaceDeriv` — is the variational structure `Mathlib` does not furnish for a general
field, so it is carried as DATA, exactly as `FullRadialField` carries the averaged-field
regularity. `transversal` records that the field is not tangent to `S` at the crossing. -/
structure TransversalSection where
  /-- The autonomous vector field. -/
  field : E → E
  /-- The flow line through each state: `flow x` solves `ẏ = field y` with `flow x 0 = x`. -/
  flow : E → ℝ → E
  /-- A point on the affine section `S`. -/
  point : E
  /-- The (nonzero) normal of the affine section `S = { y | ⟪y − point, normal⟫ = 0 }`. -/
  normal : E
  /-- The base state whose flow line crosses `S`. -/
  base : E
  /-- The time at which the base state crosses `S`. -/
  time : ℝ
  /-- The field is continuous (the regularity making the transversal speed vary continuously). -/
  cont_field : Continuous field
  /-- The integral-curve law: each flow line solves the field's ODE. -/
  hasDeriv_flow : ∀ x t, HasDerivAt (flow x) (field (flow x t)) t
  /-- The flow is jointly continuous in state and time. -/
  cont_flow : Continuous (Function.uncurry flow)
  /-- The spatial derivative of the flow at fixed time — the variational operator `D_x Φ`. -/
  spaceDeriv : E → ℝ → (E →L[ℝ] E)
  /-- `spaceDeriv` is the spatial Fréchet derivative near the base crossing. -/
  hasFDeriv_space : ∀ᶠ v in 𝓝 (base, time), HasFDerivAt (flow · v.2) (spaceDeriv v.1 v.2) v.1
  /-- The spatial derivative is continuous at the base crossing. -/
  cont_spaceDeriv : ContinuousAt (Function.uncurry spaceDeriv) (base, time)
  /-- The **joint** Fréchet derivative of the flow in state and time, `D Φ : E × ℝ →L[ℝ] E`. Its
  restriction to the `E` factor is the spatial variational operator `spaceDeriv` and its
  restriction to the `ℝ` factor is the field along the flow; the assembled joint operator is the
  variational datum the differentiable first-return map consumes, which `Mathlib` does not furnish
  for a general field. -/
  jointFlowDeriv : E → ℝ → (E × ℝ →L[ℝ] E)
  /-- `jointFlowDeriv` is the joint Fréchet derivative of the flow at the base crossing. -/
  hasFDeriv_flow_joint :
    HasFDerivAt (fun p : E × ℝ => flow p.1 p.2) (jointFlowDeriv base time) (base, time)
  /-- The flow of the base state meets `S` at `time`. -/
  isCrossing : flow base time = point
  /-- The crossing is **transversal**: the field is not tangent to `S` there. -/
  transversal : ⟪field point, normal⟫ ≠ 0

namespace TransversalSection

variable (S : TransversalSection (E := E))

/-- **The signed section coordinate.** `sectionCoord x t = ⟪Φ x t − point, normal⟫` measures
the signed distance of the flow line of `x` to the affine section `S` at time `t`. The crossing
condition `Φ x t ∈ S` is `sectionCoord x t = 0`, and the base crossing is `sectionCoord base
time = 0`. -/
def sectionCoord (x : E) (t : ℝ) : ℝ := ⟪S.flow x t - S.point, S.normal⟫

omit [CompleteSpace E] in
@[simp] theorem sectionCoord_base : S.sectionCoord S.base S.time = 0 := by
  simp [sectionCoord, S.isCrossing]

omit [CompleteSpace E] in
/-- **The temporal partialDeriv is the transversal speed.** Differentiating
`sectionCoord x · = ⟪Φ x · − point, normal⟫` in time, the integral-curve law gives
`∂_t sectionCoord x t = ⟪field (Φ x t), normal⟫`: the rate at which the flow line pierces `S`.
At the base crossing this is the nonzero transversal speed `⟪field point, normal⟫`. -/
theorem hasDeriv_time (x : E) (t : ℝ) :
    HasDerivAt (S.sectionCoord x) ⟪S.field (S.flow x t), S.normal⟫ t := by
  have hsub : HasDerivAt (fun s => S.flow x s - S.point) (S.field (S.flow x t)) t :=
    (S.hasDeriv_flow x t).sub_const S.point
  have h := hsub.inner ℝ (hasDerivAt_const t S.normal)
  simp only [inner_zero_right, zero_add] at h
  exact h

omit [CompleteSpace E] in
/-- The temporal partialDeriv, packaged as a continuous linear map `ℝ →L[ℝ] ℝ` for the implicit
function theorem: scaling by the transversal speed `⟪field (Φ x t), normal⟫`. -/
theorem hasFDeriv_time :
    ∀ᶠ v in 𝓝 (S.base, S.time),
      HasFDerivAt (S.sectionCoord v.1 ·)
        (ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow v.1 v.2), S.normal⟫) v.2 := by
  filter_upwards with v using (S.hasDeriv_time v.1 v.2).hasFDerivAt

/-- The spatial partialDeriv of `sectionCoord`, packaged for the implicit function theorem: the
section normal composed with the flow's variational operator, `r ↦ ⟪D_x Φ x t · r, normal⟫`. -/
noncomputable def spaceCoordDeriv (x : E) (t : ℝ) : E →L[ℝ] ℝ :=
  (innerSL ℝ S.normal).comp (S.spaceDeriv x t)

omit [CompleteSpace E] in
/-- **The spatial partialDeriv of `sectionCoord`.** Near the base crossing,
`sectionCoord · t = ⟪Φ · t − point, normal⟫` has Fréchet derivative
`spaceCoordDeriv x t = ⟪D_x Φ x t · , normal⟫` — the section normal read against the flow's
variational operator, the data the section carries. -/
theorem hasFDeriv_space_coord :
    ∀ᶠ v in 𝓝 (S.base, S.time),
      HasFDerivAt (S.sectionCoord · v.2) (S.spaceCoordDeriv v.1 v.2) v.1 := by
  filter_upwards [S.hasFDeriv_space] with v hv
  have h := (hv.sub_const S.point).inner ℝ (hasFDerivAt_const S.normal v.1)
  refine h.congr_fderiv ?_
  ext y
  simp [spaceCoordDeriv, fderivInnerCLM_apply, real_inner_comm]

omit [CompleteSpace E] in
/-- **Continuity of the transversal speed.** The temporal partialDeriv — scaling by
`⟪field (Φ x t), normal⟫` — is continuous at the base crossing, since `field`, the flow, and the
inner product are continuous there. This is the continuity the implicit function theorem needs
for the temporal partialDeriv. -/
theorem continuousAt_timeDeriv :
    ContinuousAt
      (↿fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
      (S.base, S.time) := by
  have hcomp : Continuous fun v : E × ℝ => S.field (S.flow v.1 v.2) :=
    S.cont_field.comp (S.cont_flow.comp (continuous_fst.prodMk continuous_snd))
  have hspeed : Continuous fun v : E × ℝ => (⟪S.field (S.flow v.1 v.2), S.normal⟫ : ℝ) :=
    hcomp.inner continuous_const
  exact ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp
    hspeed).continuousAt

omit [CompleteSpace E] in
/-- Continuity of the spatial partialDeriv `spaceCoordDeriv` at the base crossing: composing the
section normal `innerSL ℝ normal` with the continuous variational operator `spaceDeriv`. -/
theorem continuousAt_spaceCoordDeriv :
    ContinuousAt (↿S.spaceCoordDeriv) (S.base, S.time) := by
  have hcomp : Continuous fun L : E →L[ℝ] E => (innerSL ℝ S.normal).comp L :=
    (ContinuousLinearMap.compL ℝ E E ℝ (innerSL ℝ S.normal)).continuous
  exact (hcomp.continuousAt).comp S.cont_spaceDeriv

/-! ## The crossing time -/

/-- **The transversal first-crossing time.** The implicit function `τ : E → ℝ` solving the
section equation `sectionCoord x t = 0` for the crossing time `t` as a function of the initial
state `x`, near the base crossing `(base, time)`, furnished by the curried bivariate implicit
function theorem with the temporal partialDeriv (the nonzero transversal speed) inverted. By
construction `τ base = time` (limit) and `Φ x (τ x) ∈ S` for `x` near `base`. -/
noncomputable def crossingTime : E → ℝ :=
  implicitFunctionOfBivariate
    (u := (S.base, S.time))
    (f := S.sectionCoord)
    (f₁ := fun x t => S.spaceCoordDeriv x t)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
    S.hasFDeriv_space_coord
    S.hasFDeriv_time
    S.continuousAt_spaceCoordDeriv
    S.continuousAt_timeDeriv
    (by
      simpa [S.isCrossing] using
        toSpanSingleton_isInvertible S.transversal)

/-- **The crossing time meets the section.** For every initial state `x` near `base`, the flow
line of `x` meets the section `S` at the crossing time: `sectionCoord x (τ x) = 0`, i.e.
`Φ x (τ x) ∈ S`. This is the defining property of the first-crossing time, propagated off the
base crossing by the implicit function theorem. -/
theorem crossingTime_isCrossing :
    ∀ᶠ x in 𝓝 S.base, S.sectionCoord x (S.crossingTime x) = 0 := by
  have h := eventually_apply_implicitFunctionOfBivariate
    (u := (S.base, S.time)) (f := S.sectionCoord)
    (f₁ := fun x t => S.spaceCoordDeriv x t)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
    S.hasFDeriv_space_coord S.hasFDeriv_time
    S.continuousAt_spaceCoordDeriv S.continuousAt_timeDeriv
    (by simpa [S.isCrossing] using toSpanSingleton_isInvertible S.transversal)
  filter_upwards [h] with x hx
  rw [crossingTime, hx, S.sectionCoord_base]

/-- **The crossing time starts at the base.** As `x → base`, the crossing time `τ x` tends to
the base crossing time `time`. So the crossing time emerges continuously from the known
crossing, and for states near `base` it stays near `time`. -/
theorem crossingTime_tendsto :
    Tendsto S.crossingTime (𝓝 S.base) (𝓝 S.time) := by
  have h := tendsto_implicitFunctionOfBivariate
    (u := (S.base, S.time)) (f := S.sectionCoord)
    (f₁ := fun x t => S.spaceCoordDeriv x t)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
    S.hasFDeriv_space_coord S.hasFDeriv_time
    S.continuousAt_spaceCoordDeriv S.continuousAt_timeDeriv
    (by simpa [S.isCrossing] using toSpanSingleton_isInvertible S.transversal)
  simpa [crossingTime] using h

/-- **`C¹` dependence of the crossing time on the initial state.** The crossing time has a
strict Fréchet derivative at the base state, namely `−(∂_t)⁻¹ ∘ ∂_x` evaluated at the crossing:
`−(transversal speed)⁻¹ • spaceCoordDeriv`. A strict Fréchet derivative is the differentiable
(in particular continuous) dependence of the first-crossing time on the initial state — the
analytic input a differentiable Poincaré return map requires. -/
theorem hasStrictFDerivAt_crossingTime :
    HasStrictFDerivAt S.crossingTime
      (-(ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field S.point, S.normal⟫).inverse ∘L
          S.spaceCoordDeriv S.base S.time)
      S.base := by
  have h := hasStrictFDerivAt_implicitFunctionOfBivariate
    (u := (S.base, S.time)) (f := S.sectionCoord)
    (f₁ := fun x t => S.spaceCoordDeriv x t)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ ⟪S.field (S.flow x t), S.normal⟫)
    S.hasFDeriv_space_coord S.hasFDeriv_time
    S.continuousAt_spaceCoordDeriv S.continuousAt_timeDeriv
    (by simpa [S.isCrossing] using toSpanSingleton_isInvertible S.transversal)
  simpa only [crossingTime, S.isCrossing] using h

/-- **Continuous dependence of the crossing time on the initial state.** A corollary of the
strict Fréchet derivative: the first-crossing time is continuous at the base state. -/
theorem crossingTime_continuousAt : ContinuousAt S.crossingTime S.base :=
  S.hasStrictFDerivAt_crossingTime.continuousAt

end TransversalSection

end CRNT
