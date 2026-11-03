import CRNT.Oscillation.PlanarDivergenceRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Green's divergence identity on axis-aligned rectangles

This file proves the analytic base case of the planar Green theorem directly from the one-variable
fundamental theorem of calculus and Fubini.  No Jordan topology is involved.
-/

namespace CRNT
namespace Planar

open MeasureTheory Set intervalIntegral

/-- Turn a coordinate pair into the `WithLp` representation of the planar phase space. -/
def rectPoint (x y : ℝ) : Phase2 := WithLp.toLp 2 ![x, y]

private noncomputable def rectXAxis : Phase2 := EuclideanSpace.single 0 1
private noncomputable def rectYAxis : Phase2 := EuclideanSpace.single 1 1

private theorem rectPoint_affine (x y : ℝ) :
    rectPoint x y = x • rectXAxis + y • rectYAxis := by
  ext i
  fin_cases i <;>
    simp [rectPoint, rectXAxis, rectYAxis, EuclideanSpace.single_apply,
      WithLp.ofLp_toLp]

private theorem rectPoint_curve_contDiff_x (y : ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => rectPoint x y) := by
  have h : ContDiff ℝ 1 (fun x : ℝ => x • rectXAxis + y • rectYAxis) := by
    fun_prop
  have heq : (fun x : ℝ => rectPoint x y) =
      fun x => x • rectXAxis + y • rectYAxis := by
    funext x
    exact rectPoint_affine x y
  rw [heq]
  exact h

private theorem rectPoint_curve_contDiff_y (x : ℝ) :
    ContDiff ℝ 1 (fun y : ℝ => rectPoint x y) := by
  have h : ContDiff ℝ 1 (fun y : ℝ => x • rectXAxis + y • rectYAxis) := by
    fun_prop
  have heq : (fun y : ℝ => rectPoint x y) =
      fun y => x • rectXAxis + y • rectYAxis := by
    funext y
    exact rectPoint_affine x y
  rw [heq]
  exact h

private theorem partialDeriv_continuous
    (G : Phase2 → Phase2) (hG : ContDiff ℝ 1 G) (i j : Fin 2) :
    Continuous (fun p => partialDeriv (fun x => G x i) j p) := by
  let g : Phase2 → ℝ := fun x => G x i
  have hg : ContDiff ℝ 1 g :=
    ContDiff.continuousLinearMap_comp (coordinateProjection i) hG
  have hc : Continuous (fun p => fderiv ℝ g p (EuclideanSpace.single j 1)) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  convert hc using 1
  funext p
  exact partial_eq_fderiv_apply_basis (hg.differentiable (by norm_num) p)

private theorem contDiff_partial_integrable
    (G : Phase2 → Phase2) (hG : ContDiff ℝ 1 G) (i j : Fin 2)
    (a b c d : ℝ) :
    IntegrableOn
      (fun z : ℝ × ℝ => partialDeriv (fun p => G p i) j (rectPoint z.2 z.1))
      (Set.uIoc a b ×ˢ Set.uIoc c d) := by
  have hpartial := partialDeriv_continuous G hG i j
  have hrect : Continuous (fun z : ℝ × ℝ => rectPoint z.2 z.1) := by
    have h : Continuous (fun z : ℝ × ℝ => z.2 • rectXAxis + z.1 • rectYAxis) := by
      fun_prop
    have heq : (fun z : ℝ × ℝ => rectPoint z.2 z.1) =
        fun z => z.2 • rectXAxis + z.1 • rectYAxis := by
      funext z
      exact rectPoint_affine z.2 z.1
    rw [heq]
    exact h
  have hcont : Continuous
      (fun z : ℝ × ℝ => partialDeriv (fun p => G p i) j (rectPoint z.2 z.1)) :=
    hpartial.comp hrect
  have hKa : IsCompact (Set.uIcc a b) := by
    change IsCompact (Set.Icc (min a b) (max a b))
    exact isCompact_Icc
  have hKb : IsCompact (Set.uIcc c d) := by
    change IsCompact (Set.Icc (min c d) (max c d))
    exact isCompact_Icc
  have hK : IsCompact (Set.uIcc a b ×ˢ Set.uIcc c d) := hKa.prod hKb
  have hsubset : Set.uIoc a b ×ˢ Set.uIoc c d ⊆
      Set.uIcc a b ×ˢ Set.uIcc c d := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨Set.uIoc_subset_uIcc hx, Set.uIoc_subset_uIcc hy⟩
  exact (hcont.continuousOn.integrableOn_compact hK).mono_set hsubset

private theorem continuous_intervalIntegral_param
    {F : ℝ → ℝ → ℝ} (hF : Continuous F.uncurry)
    {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun y => ∫ x in a..b, F y x) := by
  have hparam : Continuous (fun y => ∫ x in Set.Icc a b, F y x) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  have heq : (fun y => ∫ x in a..b, F y x) =
      fun y => ∫ x in Set.Icc a b, F y x := by
    funext y
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hparam

private theorem partialRect_continuous
    (G : Phase2 → Phase2) (hG : ContDiff ℝ 1 G) (i j : Fin 2) :
    Continuous (fun z : ℝ × ℝ =>
      partialDeriv (fun p => G p i) j (rectPoint z.2 z.1)) := by
  have hpartial := partialDeriv_continuous G hG i j
  have hrect : Continuous (fun z : ℝ × ℝ => rectPoint z.2 z.1) := by
    have h : Continuous (fun z : ℝ × ℝ => z.2 • rectXAxis + z.1 • rectYAxis) := by
      fun_prop
    have heq : (fun z : ℝ × ℝ => rectPoint z.2 z.1) =
        fun z => z.2 • rectXAxis + z.1 • rectYAxis := by
      funext z
      exact rectPoint_affine z.2 z.1
    rw [heq]
    exact h
  exact hpartial.comp hrect

private theorem rectPoint_eq_setCoord_x (x y s : ℝ) :
    rectPoint s y = setCoord (rectPoint x y) 0 s := by
  ext i
  fin_cases i <;> simp [rectPoint, setCoord, WithLp.ofLp_toLp]

private theorem rectPoint_eq_setCoord_y (x y s : ℝ) :
    rectPoint x s = setCoord (rectPoint x y) 1 s := by
  ext i
  fin_cases i <;> simp [rectPoint, setCoord, WithLp.ofLp_toLp]

private theorem deriv_rectPoint_x (g : Phase2 → ℝ) (x y : ℝ) :
    deriv (fun s => g (rectPoint s y)) x = partialDeriv g 0 (rectPoint x y) := by
  have hfun : (fun s => g (rectPoint s y)) =
      fun s => g (setCoord (rectPoint x y) 0 s) := by
    funext s
    rw [rectPoint_eq_setCoord_x]
  rw [hfun]
  simp [partialDeriv, rectPoint]

private theorem deriv_rectPoint_y (g : Phase2 → ℝ) (x y : ℝ) :
    deriv (fun s => g (rectPoint x s)) y = partialDeriv g 1 (rectPoint x y) := by
  have hfun : (fun s => g (rectPoint x s)) =
      fun s => g (setCoord (rectPoint x y) 1 s) := by
    funext s
    rw [rectPoint_eq_setCoord_y]
  rw [hfun]
  simp [partialDeriv, rectPoint]

/-- Coordinate FTC along a horizontal line. -/
theorem coordinate_FTC_x (a b : ℝ) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) (y : ℝ) :
    (∫ x in a..b, partialDeriv (fun p => G p 0) 0 (rectPoint x y)) =
      (G (rectPoint b y)) 0 - (G (rectPoint a y)) 0 := by
  let f : ℝ → ℝ := fun x => (G (rectPoint x y)) 0
  have hcurve : ContDiff ℝ 1 (fun x : ℝ => rectPoint x y) :=
    rectPoint_curve_contDiff_x y
  have hline : ContDiff ℝ 1 (fun x : ℝ => G (rectPoint x y)) := hG.comp hcurve
  have hf : ContDiff ℝ 1 f := by
    dsimp [f]
    change ContDiff ℝ 1 ((coordinateProjection 0) ∘ fun x : ℝ => G (rectPoint x y))
    exact ContDiff.continuousLinearMap_comp (coordinateProjection 0) hline
  have hderiv : deriv f =
      (fun x => partialDeriv (fun p => G p 0) 0 (rectPoint x y)) := by
    funext x
    exact deriv_rectPoint_x (fun p => G p 0) x y
  rw [← hderiv]
  simpa [f] using intervalIntegral.integral_deriv_eq_sub
    (a := a) (b := b) (f := f)
    (fun x _ => hf.differentiable (by norm_num) x)
    (hf.continuous_deriv_one.intervalIntegrable a b)

/-- Coordinate FTC along a vertical line. -/
theorem coordinate_FTC_y (a b : ℝ) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) (x : ℝ) :
    (∫ y in a..b, partialDeriv (fun p => G p 1) 1 (rectPoint x y)) =
      (G (rectPoint x b)) 1 - (G (rectPoint x a)) 1 := by
  let f : ℝ → ℝ := fun y => (G (rectPoint x y)) 1
  have hcurve : ContDiff ℝ 1 (fun y : ℝ => rectPoint x y) :=
    rectPoint_curve_contDiff_y x
  have hline : ContDiff ℝ 1 (fun y : ℝ => G (rectPoint x y)) := hG.comp hcurve
  have hf : ContDiff ℝ 1 f := by
    dsimp [f]
    change ContDiff ℝ 1 ((coordinateProjection 1) ∘ fun y : ℝ => G (rectPoint x y))
    exact ContDiff.continuousLinearMap_comp (coordinateProjection 1) hline
  have hderiv : deriv f =
      (fun y => partialDeriv (fun p => G p 1) 1 (rectPoint x y)) := by
    funext y
    exact deriv_rectPoint_y (fun p => G p 1) x y
  rw [← hderiv]
  simpa [f] using intervalIntegral.integral_deriv_eq_sub
    (a := a) (b := b) (f := f)
    (fun y _ => hf.differentiable (by norm_num) y)
    (hf.continuous_deriv_one.intervalIntegrable a b)

/-- Closed axis-aligned rectangle. -/
structure AxisRectangle where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ
  hx : x0 ≤ x1
  hy : y0 ≤ y1

namespace AxisRectangle

/-- Rectangle as a subset of `R²`. -/
def carrier (R : AxisRectangle) : Set Phase2 :=
  {p | p 0 ∈ Set.Icc R.x0 R.x1 ∧ p 1 ∈ Set.Icc R.y0 R.y1}

/-- Four-edge outward flux with positive (counterclockwise) boundary orientation. -/
noncomputable def boundaryFlux (R : AxisRectangle) (G : Phase2 → Phase2) : ℝ :=
    (∫ x in R.x0..R.x1, -(G (rectPoint x R.y0)) 1) +
    (∫ y in R.y0..R.y1,  (G (rectPoint R.x1 y)) 0) +
    (∫ x in R.x1..R.x0, -(G (rectPoint x R.y1)) 1) +
    (∫ y in R.y1..R.y0,  (G (rectPoint R.x0 y)) 0)

/-- Area integral of divergence on the rectangle. -/
noncomputable def divergenceIntegral (R : AxisRectangle) (G : Phase2 → Phase2) : ℝ :=
  ∫ y in R.y0..R.y1, ∫ x in R.x0..R.x1, divergence G (rectPoint x y)

/-- Horizontal FTC identity for the first component. -/
theorem integral_partial0_eq_boundary
    (R : AxisRectangle) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) :
    (∫ x in R.x0..R.x1, partialDeriv (fun p => G p 0) 0 (rectPoint x R.y0)) =
      (G (rectPoint R.x1 R.y0)) 0 - (G (rectPoint R.x0 R.y0)) 0 := by
  exact coordinate_FTC_x R.x0 R.x1 G hG R.y0

/-- For each fixed `y`, integrating the x-part of divergence gives the right-minus-left flux. -/
theorem integral_partial0_slice
    (R : AxisRectangle) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) (y : ℝ) :
    (∫ x in R.x0..R.x1, partialDeriv (fun p => G p 0) 0 (rectPoint x y)) =
      (G (rectPoint R.x1 y)) 0 - (G (rectPoint R.x0 y)) 0 := by
  exact coordinate_FTC_x R.x0 R.x1 G hG y

/-- For each fixed `x`, integrating the y-part gives top-minus-bottom. -/
theorem integral_partial1_slice
    (R : AxisRectangle) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) (x : ℝ) :
    (∫ y in R.y0..R.y1, partialDeriv (fun p => G p 1) 1 (rectPoint x y)) =
      (G (rectPoint x R.y1)) 1 - (G (rectPoint x R.y0)) 1 := by
  exact coordinate_FTC_y R.y0 R.y1 G hG x

/-- **Green/divergence theorem on a rectangle.** -/
theorem boundaryFlux_eq_divergenceIntegral
    (R : AxisRectangle) (G : Phase2 → Phase2)
    (hG : ContDiff ℝ 1 G) :
    R.boundaryFlux G = R.divergenceIntegral G := by
  have hx := fun y => R.integral_partial0_slice G hG y
  have hy := fun x => R.integral_partial1_slice G hG x
  have hP0 : Continuous (Function.uncurry (fun y x =>
      partialDeriv (fun p => G p 0) 0 (rectPoint x y))) :=
    partialRect_continuous G hG 0 0
  have hP1 : Continuous (Function.uncurry (fun y x =>
      partialDeriv (fun p => G p 1) 1 (rectPoint x y))) :=
    partialRect_continuous G hG 1 1
  have hFubini1 := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun y x => partialDeriv (fun p => G p 1) 1 (rectPoint x y))
    (contDiff_partial_integrable G hG 1 1 R.y0 R.y1 R.x0 R.x1)
  let F0 : ℝ → ℝ := fun y =>
    ∫ x in R.x0..R.x1, partialDeriv (fun p => G p 0) 0 (rectPoint x y)
  let F1 : ℝ → ℝ := fun y =>
    ∫ x in R.x0..R.x1, partialDeriv (fun p => G p 1) 1 (rectPoint x y)
  have hF0 : Continuous F0 := continuous_intervalIntegral_param hP0 R.hx
  have hF1 : Continuous F1 := continuous_intervalIntegral_param hP1 R.hx
  have hF0i : IntervalIntegrable F0 volume R.y0 R.y1 :=
    hF0.intervalIntegrable R.y0 R.y1
  have hF1i : IntervalIntegrable F1 volume R.y0 R.y1 :=
    hF1.intervalIntegrable R.y0 R.y1
  have hP0x : ∀ y, IntervalIntegrable
      (fun x => partialDeriv (fun p => G p 0) 0 (rectPoint x y)) volume R.x0 R.x1 := by
    intro y
    exact ((partialDeriv_continuous G hG 0 0).comp
      (rectPoint_curve_contDiff_x y).continuous).intervalIntegrable R.x0 R.x1
  have hP1x : ∀ y, IntervalIntegrable
      (fun x => partialDeriv (fun p => G p 1) 1 (rectPoint x y)) volume R.x0 R.x1 := by
    intro y
    exact ((partialDeriv_continuous G hG 1 1).comp
      (rectPoint_curve_contDiff_x y).continuous).intervalIntegrable R.x0 R.x1
  unfold divergenceIntegral divergence
  symm
  calc
    _ = ∫ y in R.y0..R.y1, (F0 y + F1 y) := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [F0, F1]
      exact intervalIntegral.integral_add (hP0x y) (hP1x y)
    _ = (∫ y in R.y0..R.y1, F0 y) + (∫ y in R.y0..R.y1, F1 y) :=
      intervalIntegral.integral_add hF0i hF1i
    _ = (∫ y in R.y0..R.y1,
          (G (rectPoint R.x1 y)) 0 - (G (rectPoint R.x0 y)) 0) +
        (∫ x in R.x0..R.x1,
          (G (rectPoint x R.y1)) 1 - (G (rectPoint x R.y0)) 1) := by
      rw [show (∫ y in R.y0..R.y1, F0 y) =
          ∫ y in R.y0..R.y1,
            ((G (rectPoint R.x1 y)) 0 - (G (rectPoint R.x0 y)) 0) by
          apply intervalIntegral.integral_congr
          intro y _
          exact hx y]
      calc
        _ = (∫ y in R.y0..R.y1,
              (G (rectPoint R.x1 y)) 0 - (G (rectPoint R.x0 y)) 0) +
            (∫ y in R.y0..R.y1, F1 y) := by rfl
        _ = (∫ y in R.y0..R.y1,
              (G (rectPoint R.x1 y)) 0 - (G (rectPoint R.x0 y)) 0) +
            (∫ x in R.x0..R.x1,
              (G (rectPoint x R.y1)) 1 - (G (rectPoint x R.y0)) 1) := by
          congr 1
          calc
            ∫ y in R.y0..R.y1, F1 y =
                ∫ y in R.y0..R.y1, ∫ x in R.x0..R.x1,
                  partialDeriv (fun p => G p 1) 1 (rectPoint x y) := by rfl
            _ = ∫ x in R.x0..R.x1, ∫ y in R.y0..R.y1,
                  partialDeriv (fun p => G p 1) 1 (rectPoint x y) := hFubini1
            _ = ∫ x in R.x0..R.x1,
                  (G (rectPoint x R.y1)) 1 - (G (rectPoint x R.y0)) 1 := by
              apply intervalIntegral.integral_congr
              intro x _
              exact hy x
    _ = R.boundaryFlux G := by
      have hbottom : (∫ x in R.x0..R.x1, -(G (rectPoint x R.y0)) 1) =
          -(∫ x in R.x0..R.x1, (G (rectPoint x R.y0)) 1) :=
        intervalIntegral.integral_neg
      have htop : (∫ x in R.x1..R.x0, -(G (rectPoint x R.y1)) 1) =
          ∫ x in R.x0..R.x1, (G (rectPoint x R.y1)) 1 := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm]
        ring
      have hleft : (∫ y in R.y1..R.y0, (G (rectPoint R.x0 y)) 0) =
          -(∫ y in R.y0..R.y1, (G (rectPoint R.x0 y)) 0) := by
        rw [intervalIntegral.integral_symm]
      have hrightCont : Continuous (fun y => (G (rectPoint R.x1 y)) 0) := by
        exact (ContDiff.continuousLinearMap_comp (coordinateProjection 0)
          (hG.comp (rectPoint_curve_contDiff_y R.x1))).continuous
      have hleftCont : Continuous (fun y => (G (rectPoint R.x0 y)) 0) := by
        exact (ContDiff.continuousLinearMap_comp (coordinateProjection 0)
          (hG.comp (rectPoint_curve_contDiff_y R.x0))).continuous
      have htopCont : Continuous (fun x => (G (rectPoint x R.y1)) 1) := by
        exact (ContDiff.continuousLinearMap_comp (coordinateProjection 1)
          (hG.comp (rectPoint_curve_contDiff_x R.y1))).continuous
      have hbottomCont : Continuous (fun x => (G (rectPoint x R.y0)) 1) := by
        exact (ContDiff.continuousLinearMap_comp (coordinateProjection 1)
          (hG.comp (rectPoint_curve_contDiff_x R.y0))).continuous
      have hrightI : IntervalIntegrable (fun y => (G (rectPoint R.x1 y)) 0)
          volume R.y0 R.y1 := hrightCont.intervalIntegrable R.y0 R.y1
      have hleftI : IntervalIntegrable (fun y => (G (rectPoint R.x0 y)) 0)
          volume R.y0 R.y1 := hleftCont.intervalIntegrable R.y0 R.y1
      have htopI : IntervalIntegrable (fun x => (G (rectPoint x R.y1)) 1)
          volume R.x0 R.x1 := htopCont.intervalIntegrable R.x0 R.x1
      have hbottomI : IntervalIntegrable (fun x => (G (rectPoint x R.y0)) 1)
          volume R.x0 R.x1 := hbottomCont.intervalIntegrable R.x0 R.x1
      unfold AxisRectangle.boundaryFlux
      rw [hbottom, htop, hleft,
        intervalIntegral.integral_sub hrightI hleftI,
        intervalIntegral.integral_sub htopI hbottomI]
      ring

end AxisRectangle

end Planar
end CRNT
