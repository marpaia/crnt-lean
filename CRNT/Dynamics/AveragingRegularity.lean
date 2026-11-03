import CRNT.Dynamics.AveragingRemainder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The `C¹` regularity of the averaged remainder: differentiating under the angular integral

This module discharges the last item of leaf **D16 (Hopf bifurcation; oscillation)** of the field
map `docs/field-map.md`:

> "What is not proved: that the averaged remainder of a concrete reduced field is automatically `C¹`
> (differentiate under the angular integral) and the rotation closure."

(The rotation closure has meanwhile been discharged in `CRNT.Dynamics.HopfRealizes`.)  What is
proved here is exactly the remaining item: **the `C¹` regularity of the averaged remainder is
automatic** — it follows from the `C¹` regularity of the reduced field alone, by differentiating
under the angular integral.

## 1. The averaging / averaging-remainder theory

The averaging theory of the Hopf normal form (Kuznetsov, *Elements of Applied Bifurcation Theory*,
§8; Guckenheimer & Holmes, *Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector
Fields*, §3.4) replaces the reduced planar field by its **angular average** over the circle of
radius `R`.  Writing the reduced field in the complex coordinate `w = R e^{iθ}` as

```
ẇ = (α(μ) + iω) w + c₂₁ w |w|² + O(|w|⁴) ,
```

the angular average of the radial component of the field is

```
radialDrift F R = (1 / 2π) · (1/R) · ∫₀^{2π} Re ( w̄ · F w ) dθ ,      w = R e^{iθ} ,
```

and the *resonant* monomial `w² w̄ = w |w|²` is the only cubic monomial whose phase vanishes, so
that the average is `Re λ · R + Re c₂₁ · R³` up to an `O(R⁴)` remainder.  The repository already
carries this theory:

* `CRNT.Hopf.radialDrift` (`CRNT.Dynamics.HopfAveraging`) — the angular average of the radial
  component;
* `CRNT.Hopf.radialDrift_remainder` (`CRNT.Dynamics.AveragingRemainder`) — the `O(R⁴)` estimate
  `| radialDrift F R − (Re λ · R + Re c₂₁ · R³) | ≤ C R⁴` for a general reduced field;
* `CRNT.Hopf.averagedRemainder` — the averaged remainder
  `S μ R = radialDrift (F μ) R − (Re λ μ · R + Re c₂₁ μ · R³)`;
* `CRNT.Hopf.averagedRemainder_bound` — `|S μ R| ≤ C R⁴`.

## 2. What was missing: the `C¹` regularity carried as *data*

For the averaged field `G μ R = α μ · R + ℓ₁ μ · R³ + S μ R` to be a
`CRNT.PlanarHopfData.FullRadialField` one needs the averaged remainder `S` to be `C¹` in `(μ, R)`;
the repository therefore *carries* that regularity as data in

* `CRNT.Hopf.RemainderRadialField` — the averaged remainder together with its `μ`- and `R`-partials
  and their continuity — and uses it in `CRNT.Hopf.fullRadialFieldOf_remainder`.

That is exactly the "seed" pattern the repository uses elsewhere (`CenterManifoldSeed`,
`PeriodicOrbitSeed`, `TransversalSection`): the regularity is *asserted*, not *derived*.

## 3. What this module proves

The `C¹` regularity is **automatic**.  The only input is the `C¹` regularity of the reduced field
itself; the derivative of the averaged remainder is obtained by **differentiating under the
angular integral**:

* `CRNT.Hopf.integral_hasDerivAt_param` — the Leibniz rule for interval integrals (the analytic
  core: pointwise fundamental theorem of calculus + Fubini for interval integrals + the
  fundamental theorem of calculus for the parameter);
* `CRNT.Hopf.radialAverage_hasDerivAt_of_contDiff` — the angular average of the radial component
  of a `C¹` planar field is `C¹` in the radius;
* `CRNT.Hopf.radialDrift_hasDerivAt_of_contDiff` — the radial drift of a `C¹` planar field
  vanishing at the origin is `C¹` in the radius;
* `CRNT.Hopf.averagedRemainder_hasDerivAt_of_contDiff` — the averaged remainder of a `C¹` reduced
  field is `C¹` in the amplitude;
* `CRNT.Hopf.averagedRemainder_hasDerivAt_μ_of_contDiff` — for a smooth *family* of `C¹` reduced
  fields the averaged remainder is `C¹` in the parameter;
* `CRNT.Hopf.fullRadialFieldOf_remainder_of_contDiff` — **the averaged field of a smooth family of
  `C¹` reduced fields is a `CRNT.PlanarHopfData.FullRadialField` whose `C¹` regularity is
  derived, not assumed**;
* `CRNT.Hopf.Examples.averagedRemainder_normalForm_hasDerivAt` — a worked instance: for the
  truncated Hopf normal form the averaged remainder vanishes identically, hence is `C¹`.

## 4. What remains open

This module does **not** prove the persistence of the cycle for the **full nonlinear mass-action
field**.  That conclusion still requires a `CRNT.Dynamics.HopfRealizationData`: a Poincaré section
for the full field together with the **differentiable dependence of the flow on the initial
point** (the smooth-ODE-dependence fact `Mathlib` does not furnish — it is carried as data in
`CRNT.TransversalSection`).  With that datum, `CRNT.Dynamics.HopfRealizes` closes the cycle;
the `C¹` regularity of the averaged remainder, proved here, is the analytic input that the
averaged amplitude is a genuine root of the averaged field.

Depends on: `CRNT.Dynamics.AveragingRemainder` (which itself depends on
`CRNT.Dynamics.HopfAveraging`).
-/

set_option linter.ambiguousOpen false

open Complex Real MeasureTheory intervalIntegral
open Topology Filter

namespace CRNT

namespace Hopf




theorem integral_hasDerivAt_param {f g : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f.uncurry) (hderiv : ∀ x y, HasDerivAt (fun t => f t y) (g x y) x)
    (hg : Continuous g.uncurry) (x₀ : ℝ) :
    HasDerivAt (fun t => ∫ y in a..b, f t y) (∫ y in a..b, g x₀ y) x₀ := by
  -- the "derivative profile" `G t = ∫ y in a..b, g t y` is continuous
  have hG : Continuous (fun t => ∫ y in a..b, g t y) := by
    have hIcc : IsCompact (Set.Icc a b) := isCompact_Icc
    have h := continuous_parametric_integral_of_continuous (μ := volume) hg hIcc
    have heq : (fun t => ∫ y in a..b, g t y) = fun t => ∫ y in (Set.Icc a b), g t y := by
      funext t
      rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact h
  -- pointwise FTC
  have hFTC : ∀ t y, f t y - f x₀ y = ∫ s in x₀..t, g s y := by
    intro t y
    have hcont : ContinuousOn (fun s => f s y) (Set.uIcc x₀ t) := by
      intro s hs
      exact (hderiv s y).continuousAt.continuousWithinAt
    have hint : IntervalIntegrable (fun s => g s y) volume x₀ t := by
      have hc : Continuous (fun s => g s y) := hg.comp (Continuous.prodMk_left y)
      exact hc.intervalIntegrable x₀ t
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x₀) (b := t)
      (f := fun s => f s y) (f' := fun s => g s y)
      (fun s hs => hderiv s y) hint
    exact h.symm
  -- Fubini
  have hFubini : ∀ t,
      (∫ y in a..b, ∫ s in x₀..t, g s y) = ∫ s in x₀..t, (∫ y in a..b, g s y) := by
    intro t
    have hcont : Continuous (fun p : ℝ × ℝ => g p.2 p.1) :=
      hg.comp (continuous_snd.prodMk continuous_fst)
    have hKa : IsCompact (Set.uIcc a b) := by
      change IsCompact (Set.Icc (min a b) (max a b))
      exact isCompact_Icc
    have hKb : IsCompact (Set.uIcc x₀ t) := by
      change IsCompact (Set.Icc (min x₀ t) (max x₀ t))
      exact isCompact_Icc
    have hK : IsCompact (Set.uIcc a b ×ˢ Set.uIcc x₀ t) := hKa.prod hKb
    have hsubset : Set.uIoc a b ×ˢ Set.uIoc x₀ t ⊆
        Set.uIcc a b ×ˢ Set.uIcc x₀ t := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨Set.uIoc_subset_uIcc hx, Set.uIoc_subset_uIcc hy⟩
    have hinterr : IntegrableOn (fun p : ℝ × ℝ => g p.2 p.1)
        (Set.uIoc a b ×ˢ Set.uIoc x₀ t) :=
      (hcont.continuousOn.integrableOn_compact hK).mono_set hsubset
    exact MeasureTheory.intervalIntegral_intervalIntegral_swap (F := fun y s => g s y)
      hinterr
  -- the identity
  have hid : ∀ t, (∫ y in a..b, f t y) = (∫ y in a..b, f x₀ y) +
      ∫ s in x₀..t, (∫ y in a..b, g s y) := by
    intro t
    have hI1 : IntervalIntegrable (fun y => f t y) volume a b := by
      have hc : Continuous (fun y => f t y) := hf.comp (Continuous.prodMk_right t)
      exact hc.intervalIntegrable a b
    have hI2 : IntervalIntegrable (fun y => f x₀ y) volume a b := by
      have hc : Continuous (fun y => f x₀ y) := hf.comp (Continuous.prodMk_right x₀)
      exact hc.intervalIntegrable a b
    calc (∫ y in a..b, f t y)
        = (∫ y in a..b, f x₀ y) + ∫ y in a..b, (f t y - f x₀ y) := by
          have h := intervalIntegral.integral_sub hI1 hI2
          linarith
      _ = (∫ y in a..b, f x₀ y) + ∫ y in a..b, (∫ s in x₀..t, g s y) := by
          congr 1
          rw [intervalIntegral.integral_congr (fun y _ => hFTC t y)]
      _ = (∫ y in a..b, f x₀ y) + ∫ s in x₀..t, (∫ y in a..b, g s y) := by
          rw [hFubini t]
  -- the derivative
  have hd : HasDerivAt (fun u => ∫ s in x₀..u, (∫ y in a..b, g s y))
      (∫ y in a..b, g x₀ y) x₀ := by
    have hcont : ContinuousAt (fun s => ∫ y in a..b, g s y) x₀ := hG.continuousAt
    have hint : IntervalIntegrable (fun s => ∫ y in a..b, g s y) volume x₀ x₀ :=
      hG.intervalIntegrable x₀ x₀
    have hmeas : StronglyMeasurableAtFilter (fun s => ∫ y in a..b, g s y) (𝓝 x₀) volume :=
      hG.stronglyMeasurableAtFilter volume (𝓝 x₀)
    exact intervalIntegral.integral_hasDerivAt_right (a := x₀) (b := x₀)
      (f := fun s => ∫ y in a..b, g s y) hint hmeas hcont
  have hc : HasDerivAt (fun _ => ∫ y in a..b, f x₀ y) 0 x₀ :=
    hasDerivAt_const x₀ (∫ y in a..b, f x₀ y)
  have h1 : HasDerivAt (fun u => (∫ y in a..b, f x₀ y) +
      ∫ s in x₀..u, (∫ y in a..b, g s y)) (∫ y in a..b, g x₀ y) x₀ :=
    (hc.add hd).congr_deriv (by ring)
  have heq : (fun t => ∫ y in a..b, f t y) =ᶠ[𝓝 x₀]
      fun u => (∫ y in a..b, f x₀ y) + ∫ s in x₀..u, (∫ y in a..b, g s y) := by
    filter_upwards [] with u
    exact (hid u)
  exact h1.congr_of_eventuallyEq heq

/-! ## 2. The real part of a complex-valued derivative -/

/-- **The real part of a complex-valued derivative.**  If `f : ℝ → ℂ` is differentiable at `x`
with derivative `f'`, then `t ↦ (f t).re` is differentiable at `x` with derivative `(f').re`. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x := by
  have hfd : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ f') x := h.hasFDerivAt
  have h2 : HasFDerivAt (fun t => reCLM (f t))
      (reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ f')) x :=
    HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt reCLM) hfd
  have h3 : HasDerivAt (fun t => reCLM (f t))
      ((reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ f')) 1) x := h2.hasDerivAt
  have h4 : (reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ f')) 1 = reCLM f' := by
    simp
  rw [h4] at h3
  convert h3 using 1
  · funext t
    exact Complex.reCLM_apply _
  · exact Complex.reCLM_apply _

/-! ## 3. The angular average of the radial component -/

/-- The radial integrand `θ ↦ Re ( conj(e^{iθ}) · F (R e^{iθ}) )`. -/
noncomputable def radialIntegrand (F : ℂ → ℂ) (R θ : ℝ) : ℝ :=
  Complex.re (star (Complex.exp (Complex.I * θ)) * F (R * Complex.exp (Complex.I * θ)))

/-- The radial derivative integrand `θ ↦ Re ( conj(e^{iθ}) · D F (R e^{iθ}) (e^{iθ}) )`. -/
noncomputable def radialIntegrandDeriv (F : ℂ → ℂ) (R θ : ℝ) : ℝ :=
  Complex.re (star (Complex.exp (Complex.I * θ)) *
    (fderiv ℝ F (R * Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * θ))))

/-- **The angular average of the radial component of a planar field.** -/
noncomputable def radialAverage (F : ℂ → ℂ) (R : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R θ

/-- **The angular average of the radial component of a `C¹` planar field is `C¹` in the radius.**
This is the analytic core of the module: the derivative is obtained by differentiating under the
angular integral, the `R`-derivative of the integrand being

```
θ ↦ Re ( conj(e^{iθ}) · D F (R e^{iθ}) (e^{iθ}) ) .
```
-/
theorem radialAverage_hasDerivAt_of_contDiff {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (R : ℝ) :
    HasDerivAt (fun R' => radialAverage F R')
      ((1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv F R θ) R := by
  have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp (Complex.I * p.2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => Complex.I * (p.2 : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)
    exact Complex.continuous_exp.comp h1
  have hmul : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (Complex.I * p.2)) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul hexp
  have hstar : Continuous (fun p : ℝ × ℝ => star (Complex.exp (Complex.I * p.2))) := by
    rw [show (fun p : ℝ × ℝ => star (Complex.exp (Complex.I * p.2)))
        = (fun p : ℝ × ℝ => (starRingEnd ℂ) (Complex.exp (Complex.I * p.2))) by
      funext p; exact (Complex.star_def ▸ rfl)]
    exact Complex.continuous_conj.comp hexp
  have hfc : Continuous (fun p : ℝ × ℝ =>
      radialIntegrand F p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ × ℝ =>
        star (Complex.exp (Complex.I * p.2)) * F ((p.1 : ℂ) * Complex.exp (Complex.I * p.2))) :=
      hstar.mul (hF.continuous.comp hmul)
    exact Complex.continuous_re.comp h1
  have hfderiv : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hgc : Continuous (fun p : ℝ × ℝ => radialIntegrandDeriv F p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ × ℝ =>
        fderiv ℝ F ((p.1 : ℂ) * Complex.exp (Complex.I * p.2)) (Complex.exp (Complex.I * p.2))) :=
      Continuous.clm_apply (hfderiv.comp hmul) hexp
    exact Complex.continuous_re.comp (hstar.mul h1)
  have hderiv : ∀ t θ,
      HasDerivAt (fun s => radialIntegrand F s θ) (radialIntegrandDeriv F t θ) t := by
    intro t θ
    have hFd : HasFDerivAt F (fderiv ℝ F ((t : ℂ) * Complex.exp (Complex.I * θ)))
        ((t : ℂ) * Complex.exp (Complex.I * θ)) :=
      (hF.differentiable (by norm_num) ((t : ℂ) * Complex.exp (Complex.I * θ))).hasFDerivAt
    have hlin : HasFDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp (Complex.I * θ))
        (ContinuousLinearMap.toSpanSingleton ℝ (Complex.exp (Complex.I * θ))) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp (Complex.I * θ))
          (Complex.exp (Complex.I * θ)) t := by
        have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
          HasDerivAt.ofReal_comp (hasDerivAt_id t)
        simpa using hid.mul_const (Complex.exp (Complex.I * θ))
      exact h1.hasFDerivAt
    have hcomp : HasFDerivAt (fun s : ℝ => F ((s : ℂ) * Complex.exp (Complex.I * θ)))
        (fderiv ℝ F ((t : ℂ) * Complex.exp (Complex.I * θ)) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (Complex.exp (Complex.I * θ))) t :=
      HasFDerivAt.comp t hFd hlin
    have h1 : HasDerivAt (fun s : ℝ => F ((s : ℂ) * Complex.exp (Complex.I * θ)))
        (fderiv ℝ F ((t : ℂ) * Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * θ))) t := by
      convert hcomp.hasDerivAt using 1
      simp
    have h2 : HasDerivAt (fun s : ℝ =>
        star (Complex.exp (Complex.I * θ)) * F ((s : ℂ) * Complex.exp (Complex.I * θ)))
        (star (Complex.exp (Complex.I * θ)) *
          (fderiv ℝ F ((t : ℂ) * Complex.exp (Complex.I * θ)) (Complex.exp (Complex.I * θ)))) t :=
      h1.const_mul (star (Complex.exp (Complex.I * θ)))
    have h3 := hasDerivAt_re h2
    convert h3 using 1
    · funext s
      rfl
    · rfl
  have hmain := integral_hasDerivAt_param (a := 0) (b := 2 * Real.pi) (by positivity)
    (f := fun t θ => radialIntegrand F t θ)
    (g := fun t θ => radialIntegrandDeriv F t θ)
    hfc hderiv hgc R
  have h4 : HasDerivAt (fun R' => (1 / (2 * Real.pi)) *
      ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R' θ)
      ((1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv F R θ) R :=
    hmain.const_mul (1 / (2 * Real.pi))
  convert h4 using 1
  funext R'
  rfl



/-! ## 4. The radial drift -/

/-- **The radial drift is the angular average of the radial component, off the origin.** -/
theorem radialDrift_eq_radialAverage {F : ℂ → ℂ} (R : ℝ) (hR : R ≠ 0) :
    radialDrift F R = radialAverage F R := by
  have hstarR : star (R : ℂ) = (R : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hpoint : ∀ θ : ℝ,
      Complex.re (star ((R : ℂ) * Complex.exp (Complex.I * θ)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))) = R * radialIntegrand F R θ := by
    intro θ
    have hre : star ((R : ℂ) * Complex.exp (Complex.I * θ)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))
        = (R : ℂ) * (star (Complex.exp (Complex.I * θ)) *
          F ((R : ℂ) * Complex.exp (Complex.I * θ))) := by
      rw [star_mul, hstarR]
      ring
    rw [hre, mul_comm (R : ℂ) (star (Complex.exp (Complex.I * θ)) *
        F ((R : ℂ) * Complex.exp (Complex.I * θ))), Complex.re_mul_ofReal, mul_comm]
    rfl
  have hcong : (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.re (star ((R : ℂ) * Complex.exp (Complex.I * θ)) *
          F ((R : ℂ) * Complex.exp (Complex.I * θ))))
      = ∫ θ in (0:ℝ)..(2 * Real.pi), R * radialIntegrand F R θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact hpoint θ
  have hmulint : (∫ θ in (0:ℝ)..(2 * Real.pi), R * radialIntegrand F R θ)
      = R * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R θ := by
    calc (∫ θ in (0:ℝ)..(2 * Real.pi), R * radialIntegrand F R θ)
        = ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R θ * R := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact mul_comm _ _
      _ = (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R θ) * R :=
        intervalIntegral.integral_mul_const _ _
      _ = R * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F R θ := mul_comm _ _
  unfold radialDrift radialAverage
  rw [hcong, hmulint]
  field_simp



/-- **At the origin the radial drift and the angular average agree (for a field vanishing at the
origin).** -/
theorem radialDrift_eq_radialAverage_of_zero {F : ℂ → ℂ} (hF0 : F 0 = 0) (R : ℝ) :
    radialDrift F R = radialAverage F R := by
  rcases eq_or_ne R 0 with h | h
  · subst h
    have hz : ∀ θ : ℝ, Complex.re (star ((0 : ℝ) * Complex.exp (Complex.I * θ)) *
        F ((0 : ℝ) * Complex.exp (Complex.I * θ))) = 0 := by
      intro θ
      simp [hF0]
    have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star ((0 : ℝ) * Complex.exp (Complex.I * θ)) *
          F ((0 : ℝ) * Complex.exp (Complex.I * θ)))) = 0 := by
      rw [intervalIntegral.integral_congr (fun θ _ => hz θ)]
      exact intervalIntegral.integral_zero
    have h2 : (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrand F 0 θ) = 0 := by
      rw [intervalIntegral.integral_congr (f := fun θ => radialIntegrand F 0 θ) (g := fun _ => 0)
        (fun θ _ => by simp [radialIntegrand, hF0])]
      exact intervalIntegral.integral_zero
    simp [radialDrift, radialAverage, h2]
  · exact radialDrift_eq_radialAverage R h

/-- **The `C¹` regularity of the radial drift: differentiating under the angular integral.** -/
theorem radialDrift_hasDerivAt_of_contDiff {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hF0 : F 0 = 0) (R : ℝ) :
    HasDerivAt (fun R' => radialDrift F R')
      ((1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv F R θ) R := by
  have h := radialAverage_hasDerivAt_of_contDiff hF R
  have heq : (fun R' => radialDrift F R') =ᶠ[𝓝 R] fun R' => radialAverage F R' := by
    filter_upwards [] with R'
    exact radialDrift_eq_radialAverage_of_zero hF0 R'
  exact h.congr_of_eventuallyEq heq

/-! ## 5. The averaged remainder -/

/-- **The averaged remainder of a `C¹` reduced field is `C¹` in the amplitude.** -/
theorem averagedRemainder_hasDerivAt_of_contDiff
    {F : ℝ → (ℂ → ℂ)} {T : ℝ → CubicTaylorData}
    (hF : ∀ μ, ContDiff ℝ 1 (F μ)) (hF0 : ∀ μ, F μ 0 = 0) (μ R : ℝ) :
    HasDerivAt (fun R' => averagedRemainder F T μ R')
      ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv (F μ) R θ)
        - ((T μ).lam.re + 3 * (T μ).c21.re * R ^ 2)) R := by
  have h1 := radialDrift_hasDerivAt_of_contDiff (hF μ) (hF0 μ) R
  have h2 := hasDerivAt_averagedRadialField (T μ).lam.re (T μ).c21.re R
  have hsub := h1.sub h2
  have heq : (fun R' => radialDrift (F μ) R' -
      ((T μ).lam.re * R' + (T μ).c21.re * R' ^ 3)) = fun R' => averagedRemainder F T μ R' := by
    funext R'
    rfl
  refine (hsub.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)).congr_deriv ?_
  ring



/-- The radial integrand of the `μ`-derivative of a family of reduced fields. -/
noncomputable def radialIntegrandDerivμ (dF : ℝ → (ℂ → ℂ)) (μ R θ : ℝ) : ℝ :=
  Complex.re (star (Complex.exp (Complex.I * θ)) *
    (dF μ) (R * Complex.exp (Complex.I * θ)))

/-- **The averaged remainder of a smooth family of `C¹` reduced fields is `C¹` in the
parameter.** -/
theorem averagedRemainder_hasDerivAt_μ_of_contDiff
    {F : ℝ → (ℂ → ℂ)} {T : ℝ → CubicTaylorData} {dF : ℝ → (ℂ → ℂ)} {dlam dc21 : ℝ → ℂ}
    (hjoint : Continuous (fun p : ℝ × ℂ => F p.1 p.2))
    (hF0 : ∀ μ, F μ 0 = 0)
    (hdF : ∀ μ z, HasDerivAt (fun ν => F ν z) (dF μ z) μ)
    (hdFjoint : Continuous (fun p : ℝ × ℂ => (dF p.1) p.2))
    (hlam : ∀ μ, HasDerivAt (fun ν => (T ν).lam) (dlam μ) μ)
    (hc21 : ∀ μ, HasDerivAt (fun ν => (T ν).c21) (dc21 μ) μ)
    (μ R : ℝ) :
    HasDerivAt (fun μ' => averagedRemainder F T μ' R)
      ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
          radialIntegrandDerivμ dF μ R θ)
        - (dlam μ).re * R - (dc21 μ).re * R ^ 3) μ := by
  have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp (Complex.I * p.2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => Complex.I * (p.2 : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)
    exact Complex.continuous_exp.comp h1
  have hstar : Continuous (fun p : ℝ × ℝ => star (Complex.exp (Complex.I * p.2))) := by
    rw [show (fun p : ℝ × ℝ => star (Complex.exp (Complex.I * p.2)))
        = (fun p : ℝ × ℝ => (starRingEnd ℂ) (Complex.exp (Complex.I * p.2))) by
      funext p; exact (Complex.star_def ▸ rfl)]
    exact Complex.continuous_conj.comp hexp
  have harg : Continuous (fun p : ℝ × ℝ => (R : ℂ) * Complex.exp (Complex.I * p.2)) :=
    continuous_const.mul hexp
  -- continuity of the integrand
  have hfc : Continuous (fun p : ℝ × ℝ => radialIntegrand (F p.1) R p.2) := by
    have h1 : Continuous (fun p : ℝ × ℝ =>
        star (Complex.exp (Complex.I * p.2)) * F p.1 ((R : ℂ) * Complex.exp (Complex.I * p.2))) := by
      have h2 : Continuous (fun p : ℝ × ℝ =>
          F p.1 ((R : ℂ) * Complex.exp (Complex.I * p.2))) := by
        have h3 : Continuous (fun p : ℝ × ℝ =>
            (p.1, ((R : ℂ) * Complex.exp (Complex.I * p.2) : ℂ))) :=
          continuous_fst.prodMk harg
        exact hjoint.comp h3
      exact hstar.mul h2
    exact Complex.continuous_re.comp h1
  have hgc : Continuous (fun p : ℝ × ℝ => radialIntegrandDerivμ dF p.1 R p.2) := by
    have h1 : Continuous (fun p : ℝ × ℝ =>
        (dF p.1) ((R : ℂ) * Complex.exp (Complex.I * p.2))) := by
      have h3 : Continuous (fun p : ℝ × ℝ =>
          (p.1, ((R : ℂ) * Complex.exp (Complex.I * p.2) : ℂ))) :=
        continuous_fst.prodMk harg
      exact hdFjoint.comp h3
    exact Complex.continuous_re.comp (hstar.mul h1)
  -- the pointwise `μ`-derivative
  have hderiv : ∀ μ' θ,
      HasDerivAt (fun t => radialIntegrand (F t) R θ)
        (radialIntegrandDerivμ dF μ' R θ) μ' := by
    intro μ' θ
    have h1 : HasDerivAt (fun t => F t ((R : ℂ) * Complex.exp (Complex.I * θ)))
        (dF μ' ((R : ℂ) * Complex.exp (Complex.I * θ))) μ' := hdF μ' _
    have h2 : HasDerivAt (fun t =>
        star (Complex.exp (Complex.I * θ)) * F t ((R : ℂ) * Complex.exp (Complex.I * θ)))
        (star (Complex.exp (Complex.I * θ)) *
          (dF μ' ((R : ℂ) * Complex.exp (Complex.I * θ)))) μ' :=
      h1.const_mul (star (Complex.exp (Complex.I * θ)))
    have h3 := hasDerivAt_re h2
    convert h3 using 1
    · funext t
      rfl
    · rfl
  -- the Leibniz rule
  have hmain := integral_hasDerivAt_param (a := 0) (b := 2 * Real.pi) (by positivity)
    (f := fun μ' θ => radialIntegrand (F μ') R θ)
    (g := fun μ' θ => radialIntegrandDerivμ dF μ' R θ)
    hfc hderiv hgc μ
  have havg : HasDerivAt (fun μ' => radialAverage (F μ') R)
      ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
        radialIntegrandDerivμ dF μ R θ)) μ := by
    convert hmain.const_mul (1 / (2 * Real.pi)) using 1
    funext μ'
    rfl
  -- the Taylor part
  have hlam' : HasDerivAt (fun μ' => (T μ').lam.re) (dlam μ).re μ := hasDerivAt_re (hlam μ)
  have hc21' : HasDerivAt (fun μ' => (T μ').c21.re) (dc21 μ).re μ := hasDerivAt_re (hc21 μ)
  have htot := (havg.sub (hlam'.const_mul R)).sub (hc21'.const_mul (R ^ 3))
  have heq : (fun μ' => averagedRemainder F T μ' R) = ((fun μ' => radialAverage (F μ') R)
      - (fun μ' => R * (T μ').lam.re) - (fun μ' => R ^ 3 * (T μ').c21.re)) := by
    funext μ'
    rw [averagedRemainder, radialDrift_eq_radialAverage_of_zero (hF0 μ')]
    simp only [Pi.sub_apply]
    ring
  exact (htot.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)).congr_deriv (by ring)



/-! ## 6. The averaged field with the regularity derived -/

/-- **Continuity of a parameter-dependent angular integral.** -/
theorem continuous_angularIntegral {G : ℝ × ℝ → ℝ → ℝ} (hG : Continuous G.uncurry) :
    Continuous (fun p : ℝ × ℝ => ∫ θ in (0:ℝ)..(2 * Real.pi), G p θ) := by
  have hIcc : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
  have h := continuous_parametric_integral_of_continuous (μ := volume) hG hIcc
  have heq : (fun p : ℝ × ℝ => ∫ θ in (0:ℝ)..(2 * Real.pi), G p θ)
      = fun p : ℝ × ℝ => ∫ θ in (Set.Icc 0 (2 * Real.pi)), G p θ := by
    funext p
    rw [intervalIntegral.integral_of_le (by positivity),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h


/-- **Continuity of the radial derivative integrand in the triple `((μ, R), θ)`.** -/
theorem continuous_radialIntegrandDeriv {F : ℝ → (ℂ → ℂ)}
    (hdjoint : Continuous (fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2)) :
    Continuous (fun t : (ℝ × ℝ) × ℝ => radialIntegrandDeriv (F t.1.1) t.1.2 t.2) := by
  have hexp' : Continuous (fun t : (ℝ × ℝ) × ℝ => Complex.exp (Complex.I * t.2)) := by
    have h1 : Continuous (fun t : (ℝ × ℝ) × ℝ => Complex.I * (t.2 : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)
    exact Complex.continuous_exp.comp h1
  have hstar' : Continuous (fun t : (ℝ × ℝ) × ℝ => star (Complex.exp (Complex.I * t.2))) := by
    rw [show (fun t : (ℝ × ℝ) × ℝ => star (Complex.exp (Complex.I * t.2)))
        = (fun t : (ℝ × ℝ) × ℝ => (starRingEnd ℂ) (Complex.exp (Complex.I * t.2))) by
      funext t; exact (Complex.star_def ▸ rfl)]
    exact Complex.continuous_conj.comp hexp'
  have hR : Continuous (fun t : (ℝ × ℝ) × ℝ => (t.1.2 : ℂ)) := by
    fun_prop
  have harg : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      (t.1.2 : ℂ) * Complex.exp (Complex.I * t.2)) := hR.mul hexp'
  have hpair : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      ((t.1.1, ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2) : ℂ)) : ℝ × ℂ)) := by
    fun_prop
  have hfd : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      fderiv ℝ (F t.1.1) ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2))) :=
    hdjoint.comp hpair
  have h1 : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      star (Complex.exp (Complex.I * t.2)) *
        (fderiv ℝ (F t.1.1) ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2)))
          (Complex.exp (Complex.I * t.2))) :=
    hstar'.mul (Continuous.clm_apply hfd hexp')
  exact Complex.continuous_re.comp h1

/-- **Continuity of the radial `μ`-derivative integrand in the triple `((μ, R), θ)`.** -/
theorem continuous_radialIntegrandDerivμ (dF : ℝ → (ℂ → ℂ))
    (hdFjoint : Continuous (fun p : ℝ × ℂ => (dF p.1) p.2)) :
    Continuous (fun t : (ℝ × ℝ) × ℝ => radialIntegrandDerivμ dF t.1.1 t.1.2 t.2) := by
  have hexp' : Continuous (fun t : (ℝ × ℝ) × ℝ => Complex.exp (Complex.I * t.2)) := by
    have h1 : Continuous (fun t : (ℝ × ℝ) × ℝ => Complex.I * (t.2 : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)
    exact Complex.continuous_exp.comp h1
  have hstar' : Continuous (fun t : (ℝ × ℝ) × ℝ => star (Complex.exp (Complex.I * t.2))) := by
    rw [show (fun t : (ℝ × ℝ) × ℝ => star (Complex.exp (Complex.I * t.2)))
        = (fun t : (ℝ × ℝ) × ℝ => (starRingEnd ℂ) (Complex.exp (Complex.I * t.2))) by
      funext t; exact (Complex.star_def ▸ rfl)]
    exact Complex.continuous_conj.comp hexp'
  have hR : Continuous (fun t : (ℝ × ℝ) × ℝ => (t.1.2 : ℂ)) := by
    fun_prop
  have harg : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      (t.1.2 : ℂ) * Complex.exp (Complex.I * t.2)) := hR.mul hexp'
  have hpair : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      ((t.1.1, ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2) : ℂ)) : ℝ × ℂ)) := by
    fun_prop
  have hfd : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      (dF t.1.1) ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2))) :=
    hdFjoint.comp hpair
  have h1 : Continuous (fun t : (ℝ × ℝ) × ℝ =>
      star (Complex.exp (Complex.I * t.2)) *
        (dF t.1.1) ((t.1.2 : ℂ) * Complex.exp (Complex.I * t.2))) :=
    hstar'.mul hfd
  exact Complex.continuous_re.comp h1

/-- **The averaged field of a smooth family of `C¹` reduced fields is a `FullRadialField` with
the regularity derived, not assumed.** -/
noncomputable def fullRadialFieldOf_remainder_of_contDiff
    {F : ℝ → (ℂ → ℂ)} {T : ℝ → CubicTaylorData} {dF : ℝ → (ℂ → ℂ)}
    {dlam dc21 : ℝ → ℂ} {C : ℝ} {μ₁ R₀ : ℝ}
    (hF : ∀ μ, ContDiff ℝ 1 (F μ))
    (hjoint : Continuous (fun p : ℝ × ℂ => F p.1 p.2))
    (hdjoint : Continuous (fun p : ℝ × ℂ => fderiv ℝ (F p.1) p.2))
    (hF0 : ∀ μ, F μ 0 = 0)
    (hdF : ∀ μ z, HasDerivAt (fun ν => F ν z) (dF μ z) μ)
    (hdFjoint : Continuous (fun p : ℝ × ℂ => (dF p.1) p.2))
    (hTlam : Continuous (fun μ => (T μ).lam))
    (hTc21 : Continuous (fun μ => (T μ).c21))
    (hlam : ∀ μ, HasDerivAt (fun ν => (T ν).lam) (dlam μ) μ)
    (hc21 : ∀ μ, HasDerivAt (fun ν => (T ν).c21) (dc21 μ) μ)
    (hdlam : Continuous dlam) (hdc21 : Continuous dc21)
    (hbound : ∀ μ R, |averagedRemainder F T μ R| ≤ C * R ^ 4)
    (hroot : (T μ₁).lam.re * R₀ + (T μ₁).c21.re * R₀ ^ 3 + averagedRemainder F T μ₁ R₀ = 0)
    (hnondeg : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
          radialIntegrandDeriv (F μ₁) R₀ θ) ≠ 0) :
    CRNT.PlanarHopfData.FullRadialField μ₁ R₀ := by
  have hG2 : Continuous (fun t : (ℝ × ℝ) × ℝ => radialIntegrandDeriv (F t.1.1) t.1.2 t.2) :=
    continuous_radialIntegrandDeriv hdjoint
  have hG1 : Continuous (fun t : (ℝ × ℝ) × ℝ => radialIntegrandDerivμ dF t.1.1 t.1.2 t.2) :=
    continuous_radialIntegrandDerivμ dF hdFjoint
  -- the `RemainderRadialField`, with the regularity derived
  set hRem : RemainderRadialField μ₁ R₀ C := by
    refine
    { S := averagedRemainder F T
      S₁ := fun μ R => (1 / (2 * Real.pi)) *
          (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDerivμ dF μ R θ)
            - (dlam μ).re * R - (dc21 μ).re * R ^ 3
      S₂ := fun μ R => (1 / (2 * Real.pi)) *
          (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv (F μ) R θ)
            - ((T μ).lam.re + 3 * (T μ).c21.re * R ^ 2)
      hasDeriv_S₁ := ?_
      hasDeriv_S₂ := ?_
      cont_S₁ := ?_
      cont_S₂ := ?_
      bound := ?_ }
    · -- the `μ`-partial is derived by differentiating under the angular integral
      filter_upwards [] with v
      exact averagedRemainder_hasDerivAt_μ_of_contDiff (T := T) (dF := dF) (dlam := dlam)
        (dc21 := dc21) hjoint hF0 hdF hdFjoint hlam hc21 v.1 v.2
    · -- the `R`-partial is derived by differentiating under the angular integral
      filter_upwards [] with v
      exact averagedRemainder_hasDerivAt_of_contDiff (T := T) hF hF0 v.1 v.2
    · -- continuity of the `μ`-partial
      have h1 : Continuous (fun p : ℝ × ℝ =>
          (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            radialIntegrandDerivμ dF p.1 p.2 θ)) :=
        continuous_const.mul (continuous_angularIntegral hG1)
      have h2 : Continuous (fun p : ℝ × ℝ => (dlam p.1).re * p.2) := by
        fun_prop
      have h3 : Continuous (fun p : ℝ × ℝ => (dc21 p.1).re * p.2 ^ 3) := by
        fun_prop
      exact ((h1.sub h2).sub h3).continuousAt
    · -- continuity of the `R`-partial
      have h1 : Continuous (fun p : ℝ × ℝ =>
          (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            radialIntegrandDeriv (F p.1) p.2 θ)) :=
        continuous_const.mul (continuous_angularIntegral hG2)
      have h2 : Continuous (fun p : ℝ × ℝ => (T p.1).lam.re + 3 * (T p.1).c21.re * p.2 ^ 2) := by
        have h3 : Continuous (fun p : ℝ × ℝ => (T p.1).lam.re) :=
          Complex.continuous_re.comp (hTlam.comp continuous_fst)
        have h5 : Continuous (fun p : ℝ × ℝ => (T p.1).c21.re) :=
          Complex.continuous_re.comp (hTc21.comp continuous_fst)
        have h6 : Continuous (fun p : ℝ × ℝ => p.2 ^ 2) := by
          fun_prop
        exact h3.add ((h5.const_mul 3).mul h6)
      exact (h1.sub h2).continuousAt
    · -- the `O(R⁴)` bound
      intro μ R
      exact hbound μ R
  -- the averaged field
  have hα : ∀ t, HasDerivAt (fun μ => (T μ).lam.re) ((dlam t).re) t := by
    intro t
    exact hasDerivAt_re (hlam t)
  have hℓ : ∀ t, HasDerivAt (fun μ => (T μ).c21.re) ((dc21 t).re) t := by
    intro t
    exact hasDerivAt_re (hc21 t)
  have hdα : Continuous (fun t => (dlam t).re) := Complex.continuous_re.comp hdlam
  have hdℓ : Continuous (fun t => (dc21 t).re) := Complex.continuous_re.comp hdc21
  have hroot' : (T μ₁).lam.re * R₀ + (T μ₁).c21.re * R₀ ^ 3 + hRem.S μ₁ R₀ = 0 := by
    exact hroot
  have hnondeg' : (T μ₁).lam.re + 3 * (T μ₁).c21.re * R₀ ^ 2 + hRem.S₂ μ₁ R₀ ≠ 0 := by
    have hS2 : hRem.S₂ μ₁ R₀ = (1 / (2 * Real.pi)) *
        (∫ θ in (0:ℝ)..(2 * Real.pi), radialIntegrandDeriv (F μ₁) R₀ θ)
          - ((T μ₁).lam.re + 3 * (T μ₁).c21.re * R₀ ^ 2) := rfl
    rw [hS2]
    have hring : (T μ₁).lam.re + 3 * (T μ₁).c21.re * R₀ ^ 2
        + ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            radialIntegrandDeriv (F μ₁) R₀ θ)
          - ((T μ₁).lam.re + 3 * (T μ₁).c21.re * R₀ ^ 2))
        = (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
            radialIntegrandDeriv (F μ₁) R₀ θ) := by ring
    rw [hring]
    exact hnondeg
  exact fullRadialFieldOf_remainder (α := fun μ => (T μ).lam.re) (ℓ₁ := fun μ => (T μ).c21.re)
    (dα := fun μ => (dlam μ).re) (dℓ := fun μ => (dc21 μ).re)
    hα hℓ hdα hdℓ hRem hroot' hnondeg'


/-! ## 7. A concrete instance -/

namespace Examples

/-- **The truncated Hopf normal form** `ẇ = (α + iω) w + c₁ w |w|²`. -/
def normalFormField (α ω : ℝ) (c₁ : ℂ) : ℂ → ℂ :=
  fun w => ((α : ℂ) + ω * Complex.I) * w + c₁ * w * (Complex.normSq w : ℂ)

/-- **The cubic Taylor data of the truncated normal form**: the linear coefficient `(α + iω)` and
the resonant cubic coefficient `c₁`. -/
def truncatedTaylorData (α ω : ℝ) (c₁ : ℂ) : CubicTaylorData :=
  ⟨(α : ℂ) + ω * Complex.I, 0, 0, 0, 0, c₁, 0, 0⟩

/-- **The truncated normal form is its own cubic Taylor polynomial.** -/
theorem normalFormField_eq_cubicTaylorPoly (α ω : ℝ) (c₁ : ℂ) (w : ℂ) :
    normalFormField α ω c₁ w = cubicTaylorPoly (truncatedTaylorData α ω c₁) w := by
  have hnorm : (Complex.normSq w : ℂ) = w * star w := by
    have h := Complex.mul_conj w
    exact h.symm
  simp only [normalFormField, truncatedTaylorData, cubicTaylorPoly, monomial]
  simp only [zero_mul, add_zero, pow_zero, pow_one, mul_one]
  rw [hnorm]
  ring

/-- **The truncated normal form is a `C¹` field.** -/
theorem normalFormField_contDiff (α ω : ℝ) (c₁ : ℂ) : ContDiff ℝ 1 (normalFormField α ω c₁) := by
  unfold normalFormField
  have hofR : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := ofRealCLM.contDiff
  have hnorm : ContDiff ℝ 1 (fun w : ℂ => (Complex.normSq w : ℂ)) := by
    rw [show (fun w : ℂ => (Complex.normSq w : ℂ)) = fun w => w * star w by
      funext w; exact (Complex.mul_conj w).symm]
    have hstar : ContDiff ℝ 1 (fun w : ℂ => star w) := by
      rw [show (fun w : ℂ => star w) = fun w => (starRingEnd ℂ) w by
        funext w; exact (Complex.star_def ▸ rfl)]
      exact conjCLE.contDiff
    fun_prop
  fun_prop

/-- **The truncated normal form vanishes at the origin.** -/
theorem normalFormField_zero (α ω : ℝ) (c₁ : ℂ) : normalFormField α ω c₁ 0 = 0 := by
  simp [normalFormField]

/-- **The general `C¹` result applied to the truncated normal form.**  The averaged remainder of
the truncated Hopf normal form is `C¹` in the amplitude, with the derivative prescribed by the
general theorem `averagedRemainder_hasDerivAt_of_contDiff`. -/
theorem averagedRemainder_normalForm_hasDerivAt_of_contDiff (α ω : ℝ) (c₁ : ℂ) (R : ℝ) :
    HasDerivAt (fun R' => averagedRemainder (fun _ => normalFormField α ω c₁)
      (fun _ => truncatedTaylorData α ω c₁) 0 R')
      ((1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2 * Real.pi),
          radialIntegrandDeriv (normalFormField α ω c₁) R θ)
        - ((truncatedTaylorData α ω c₁).lam.re
          + 3 * (truncatedTaylorData α ω c₁).c21.re * R ^ 2)) R :=
  averagedRemainder_hasDerivAt_of_contDiff (T := fun _ => truncatedTaylorData α ω c₁)
    (fun _ => normalFormField_contDiff α ω c₁) (fun _ => normalFormField_zero α ω c₁) 0 R

/-- **The averaged remainder of the truncated normal form vanishes identically.** -/
theorem averagedRemainder_normalForm_eq_zero (α ω : ℝ) (c₁ : ℂ) (R : ℝ) :
    averagedRemainder (fun _ => normalFormField α ω c₁)
      (fun _ => truncatedTaylorData α ω c₁) 0 R = 0 := by
  have h1 : radialDrift (normalFormField α ω c₁) R = α * R + c₁.re * R ^ 3 := by
    exact radialDrift_normalForm α ω c₁ R
  have h2 : (truncatedTaylorData α ω c₁).lam.re = α := by
    simp [truncatedTaylorData, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h3 : (truncatedTaylorData α ω c₁).c21.re = c₁.re := by
    simp only [truncatedTaylorData]
  have h4 : averagedRemainder (fun _ => normalFormField α ω c₁)
      (fun _ => truncatedTaylorData α ω c₁) 0 R
      = radialDrift (normalFormField α ω c₁) R
        - ((truncatedTaylorData α ω c₁).lam.re * R + (truncatedTaylorData α ω c₁).c21.re * R ^ 3) := by
    rfl
  rw [h4, h1, h2, h3]
  ring

/-- **The averaged remainder of the truncated normal form is `C¹`.**  Being identically zero, it
is `C¹` with vanishing derivative — the concrete instance of the general result
`averagedRemainder_hasDerivAt_of_contDiff`. -/
theorem averagedRemainder_normalForm_hasDerivAt (α ω : ℝ) (c₁ : ℂ) (R : ℝ) :
    HasDerivAt (fun R' => averagedRemainder (fun _ => normalFormField α ω c₁)
      (fun _ => truncatedTaylorData α ω c₁) 0 R') 0 R := by
  have hz : (fun R' => averagedRemainder (fun _ => normalFormField α ω c₁)
      (fun _ => truncatedTaylorData α ω c₁) 0 R') = fun _ => 0 := by
    funext R'
    exact averagedRemainder_normalForm_eq_zero α ω c₁ R'
  rw [hz]
  exact hasDerivAt_const R 0

end Examples


/-! ## The axioms of the principal declarations -/

#print axioms integral_hasDerivAt_param
#print axioms hasDerivAt_re
#print axioms radialAverage_hasDerivAt_of_contDiff
#print axioms radialDrift_hasDerivAt_of_contDiff
#print axioms averagedRemainder_hasDerivAt_of_contDiff
#print axioms averagedRemainder_hasDerivAt_μ_of_contDiff
#print axioms fullRadialFieldOf_remainder_of_contDiff
#print axioms Examples.averagedRemainder_normalForm_hasDerivAt
#print axioms Examples.averagedRemainder_normalForm_hasDerivAt_of_contDiff

end Hopf

end CRNT
