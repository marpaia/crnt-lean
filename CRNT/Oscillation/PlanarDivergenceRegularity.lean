import CRNT.Oscillation.GreenJordanFoundations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularity of planar divergence

The public Dulac API defines divergence through classical one-dimensional coordinate derivatives.
For a C1 vector field on an open set these derivatives are the diagonal entries of the Frechet
Jacobian.  This file records that bridge and derives continuity/integrability of divergence on a
bounded Jordan interior.
-/

namespace CRNT
namespace Planar

open MeasureTheory Set

/-- Coordinate line through `x` in direction `e_i`. -/
def coordinateLine (x : Phase2) (i : Fin 2) (a : ℝ) : Phase2 := setCoord x i a

/-- Continuous linear projection onto coordinate `i`. -/
def coordinateProjection (i : Fin 2) : Phase2 →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

/-- Replacing one Euclidean coordinate has the expected one-dimensional derivative. -/
theorem hasDerivAt_setCoord (x : Phase2) (i : Fin 2) :
    HasDerivAt (fun a : ℝ => setCoord x i a)
      (EuclideanSpace.single i 1) (x i) := by
  have hformula : (fun a : ℝ => setCoord x i a) =
      fun a => x + (a - x i) • EuclideanSpace.single i 1 := by
    funext a
    ext j
    by_cases hji : j = i
    · subst j
      simp [setCoord, EuclideanSpace.single, PiLp.single_apply, WithLp.ofLp_toLp]
    · simp [setCoord, EuclideanSpace.single, PiLp.single_apply, WithLp.ofLp_toLp, hji]
  have hscalar : HasDerivAt (fun a : ℝ => a - x i) 1 (x i) := by
    simpa using (hasDerivAt_id (x i)).sub_const (x i)
  simpa only [hformula, one_smul] using
    (hscalar.smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x

/-- For a differentiable scalar function, the classical coordinate partial equals the Frechet
derivative applied to the coordinate basis vector. -/
theorem partial_eq_fderiv_apply_basis
    {g : Phase2 → ℝ} {x : Phase2} {i : Fin 2}
    (hg : DifferentiableAt ℝ g x) :
    partialDeriv g i x = fderiv ℝ g x (EuclideanSpace.single i 1) := by
  unfold partialDeriv
  have hself : setCoord x i (x i) = x := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [setCoord, WithLp.ofLp_toLp]
    · simp [setCoord, WithLp.ofLp_toLp, hji]
  have hline : HasDerivAt (fun a => g (setCoord x i a))
      (fderiv ℝ g x (EuclideanSpace.single i 1)) (x i) := by
    have hcoord : HasDerivAt (fun a : ℝ => setCoord x i a)
        (EuclideanSpace.single i 1) (x i) := by
      exact hasDerivAt_setCoord x i
    have hg' : HasFDerivAt g (fderiv ℝ g x) (setCoord x i (x i)) := by
      rw [hself]
      exact hg.hasFDerivAt
    exact hg'.comp_hasDerivAt (x i) hcoord
  exact hline.deriv

/-- Divergence of a differentiable planar vector field is the sum of the two diagonal Frechet
Jacobian entries. -/
theorem divergence_eq_fderiv_diag
    {G : Phase2 → Phase2} {x : Phase2}
    (hG : DifferentiableAt ℝ G x) :
    divergence G x =
      (fderiv ℝ G x (EuclideanSpace.single 0 1)) 0 +
      (fderiv ℝ G x (EuclideanSpace.single 1 1)) 1 := by
  unfold divergence
  have hcoordDiff (i : Fin 2) : DifferentiableAt ℝ (fun y => G y i) x := by
    change DifferentiableAt ℝ ((coordinateProjection i) ∘ G) x
    exact (coordinateProjection i).differentiableAt.comp x hG
  have hcoordFDeriv (i : Fin 2) : HasFDerivAt (fun y => G y i)
      ((coordinateProjection i).comp (fderiv ℝ G x)) x := by
    convert (coordinateProjection i).hasFDerivAt.comp x hG.hasFDerivAt using 1
    · funext y
      rfl
  rw [partial_eq_fderiv_apply_basis (hcoordDiff 0),
    partial_eq_fderiv_apply_basis (hcoordDiff 1)]
  rw [(hcoordFDeriv 0).fderiv, (hcoordFDeriv 1).fderiv]
  simp [coordinateProjection, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, EuclideanSpace.single, PiLp.single_apply]

/-- Divergence is continuous on an open set where the vector field is C1. -/
theorem continuousOn_divergence_of_contDiffOn
    {G : Phase2 → Phase2} {U : Set Phase2}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) :
    ContinuousOn (divergence G) U := by
  intro x hx
  have hdiff : DifferentiableAt ℝ G x :=
    (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hfder : ContinuousWithinAt (fun y => fderiv ℝ G y) U x :=
    (hG.continuousOn_fderiv_of_isOpen hU (by norm_num)) x hx
  have hcandidate : ContinuousWithinAt
      (fun y => (fderiv ℝ G y (EuclideanSpace.single 0 1)) 0 +
        (fderiv ℝ G y (EuclideanSpace.single 1 1)) 1) U x := by
    fun_prop
  have hEq : ∀ y ∈ U, divergence G y =
      (fderiv ℝ G y (EuclideanSpace.single 0 1)) 0 +
        (fderiv ℝ G y (EuclideanSpace.single 1 1)) 1 := by
    intro y hy
    exact divergence_eq_fderiv_diag
      ((hG.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  exact (continuousWithinAt_congr hEq (hEq x hx)).mpr hcandidate

/-- Scalar multiplication of C1 planar functions is C1 on the same region. -/
theorem contDiffOn_smul_field
    {B : Phase2 → ℝ} {G : Phase2 → Phase2} {U : Set Phase2}
    (hB : ContDiffOn ℝ 1 B U) (hG : ContDiffOn ℝ 1 G U) :
    ContDiffOn ℝ 1 (fun x => B x • G x) U := by
  exact hB.smul hG

/-- Continuous divergence on a bounded finite-measure set is integrable. -/
theorem integrableOn_divergence_of_bounded
    {G : Phase2 → Phase2} {U K : Set Phase2}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hK : closure K ⊆ U)
    (hKbounded : Bornology.IsBounded K) :
    IntegrableOn (divergence G) K := by
  have hcont : ContinuousOn (divergence G) (closure K) :=
    (continuousOn_divergence_of_contDiffOn hU hG).mono hK
  have hcpt : IsCompact (closure K) := hKbounded.isCompact_closure
  exact (hcont.integrableOn_compact hcpt).mono_set subset_closure

/-- The Jordan/Dulac regularity target is therefore an internal consequence of the packaged C1
hypotheses, once the closure of the interior stays inside the open Dulac region. -/
theorem jordanDulacRegularity_proved : JordanDulacRegularityTarget := by
  intro field D P J hclosure
  let G : Phase2 → Phase2 := fun x => D.dulac x • field x
  have hG : ContDiffOn ℝ 1 G D.region :=
    contDiffOn_smul_field D.smooth_dulac D.smooth_field
  have hcont : ContinuousOn (divergence G) J.interior :=
    (continuousOn_divergence_of_contDiffOn D.open_region hG).mono
      (subset_trans subset_closure hclosure)
  have hint : IntegrableOn (divergence G) J.interior := by
    exact integrableOn_divergence_of_bounded D.open_region hG
      hclosure J.bounded
  have hC1 : ContDiffOn ℝ 1 G (closure J.interior) := hG.mono hclosure
  exact ⟨hcont, hint, hC1⟩

end Planar
end CRNT
