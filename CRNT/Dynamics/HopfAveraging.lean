import CRNT.Dynamics.HopfNormalForm
import CRNT.Dynamics.HopfPersistentOrbit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

set_option linter.ambiguousOpen false

namespace CRNT

namespace Hopf

open Complex Real MeasureTheory intervalIntegral

/-! ## Angular integrals -/

theorem integral_exp_one_I :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (1 * Complex.I * θ) = 0 := by
  have hc : (1 * Complex.I : ℂ) ≠ 0 := by simp
  rw [integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) (c := 1 * Complex.I) hc]
  have hexp : Complex.exp (Complex.I * (2 * Real.pi)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (1 : ℤ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  simp [hexp]

theorem integral_exp_two_I :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (2 * Complex.I * θ) = 0 := by
  have hc : (2 * Complex.I : ℂ) ≠ 0 := by simp
  rw [integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) (c := 2 * Complex.I) hc]
  have hexp : Complex.exp (2 * Complex.I * (2 * Real.pi)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (2 : ℤ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  simp [hexp]

theorem integral_exp_three_I :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (3 * Complex.I * θ) = 0 := by
  have hc : (3 * Complex.I : ℂ) ≠ 0 := by simp
  rw [integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) (c := 3 * Complex.I) hc]
  have hexp : Complex.exp (3 * Complex.I * (2 * Real.pi)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (3 : ℤ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  simp [hexp]

theorem integral_exp_neg_two_I :
    ∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp (-2 * Complex.I * θ) = 0 := by
  have hc : (-2 * Complex.I : ℂ) ≠ 0 := by simp
  rw [integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) (c := -2 * Complex.I) hc]
  have hexp2 : Complex.exp (2 * Complex.I * (2 * Real.pi)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (2 : ℤ)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hexp : Complex.exp (-(2 * Complex.I * (2 * Real.pi))) = 1 := by
    rw [Complex.exp_neg]
    rw [hexp2]
    simp
  simp [hexp]

theorem integral_one_complex :
    ∫ _θ in (0:ℝ)..(2*Real.pi), (1 : ℂ) = 2 * Real.pi := by
  simp [intervalIntegral.integral_const]

/-! ## Averaged radial drift -/

noncomputable def radialDrift (F : ℂ → ℂ) (R : ℝ) : ℝ :=
  ((1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi),
      Complex.re (star (R * Complex.exp (Complex.I * θ)) * F (R * Complex.exp (Complex.I * θ)))) / R

theorem radialDrift_normalForm (α ω : ℝ) (c₁ : ℂ) (R : ℝ) :
    radialDrift (fun w => ((α : ℂ) + ω * Complex.I) * w + c₁ * w * (Complex.normSq w : ℂ)) R =
      α * R + c₁.re * R ^ 3 := by
  unfold radialDrift
  by_cases hR : R = 0
  · simp [hR]
  · -- The integrand is pointwise constant in θ.
    have hpoint : ∀ θ : ℝ,
        Complex.re (star (R * Complex.exp (Complex.I * θ)) *
          (((α : ℂ) + ω * Complex.I) * (R * Complex.exp (Complex.I * θ)) +
            c₁ * (R * Complex.exp (Complex.I * θ)) *
              (Complex.normSq (R * Complex.exp (Complex.I * θ)) : ℂ))) =
        α * R ^ 2 + c₁.re * R ^ 4 := by
      intro θ
      set w := (R : ℂ) * Complex.exp (Complex.I * θ)
      have hwstar : star w * w = (Complex.normSq w : ℂ) := by
        have h := RCLike.mul_conj w
        rw [mul_comm] at h
        calc star w * w = ↑‖w‖ ^ 2 := h
          _ = ↑(‖w‖ ^ 2) := (Complex.ofReal_pow (‖w‖) 2).symm
          _ = ↑(Complex.normSq w) := by rw [Complex.normSq_eq_norm_sq w]
      have hnorm : Complex.normSq w = R ^ 2 := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal R]
        have hexp : Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
          rw [Complex.normSq_eq_norm_sq]
          rw [Complex.norm_exp_I_mul_ofReal θ]
          norm_num
        rw [hexp]
        ring
      have hprod : star w *
          (((α : ℂ) + ω * Complex.I) * w + c₁ * w * (Complex.normSq w : ℂ)) =
        ((α : ℂ) + ω * Complex.I) * ↑(R ^ 2) + c₁ * (↑(R ^ 2) * ↑(R ^ 2)) := by
        rw [mul_add]
        have t1 : star w * (((α : ℂ) + ω * Complex.I) * w) =
            ((α : ℂ) + ω * Complex.I) * ↑(R ^ 2) := by
          have : star w * (((α : ℂ) + ω * Complex.I) * w) =
              ((α : ℂ) + ω * Complex.I) * (star w * w) := by ring
          rw [this, hwstar, hnorm]
        have t2 : star w * (c₁ * w * (Complex.normSq w : ℂ)) =
            c₁ * (↑(R ^ 2) * ↑(R ^ 2)) := by
          have : star w * (c₁ * w * (Complex.normSq w : ℂ)) =
              c₁ * (star w * w) * (Complex.normSq w : ℂ) := by ring
          rw [this, hwstar, hnorm]
          ring
        rw [t1, t2]
      have hre : Complex.re (star w *
          (((α : ℂ) + ω * Complex.I) * w + c₁ * w * (Complex.normSq w : ℂ))) =
        α * R ^ 2 + c₁.re * R ^ 4 := by
        rw [hprod]
        rw [Complex.add_re]
        have h1 : Complex.re (((α : ℂ) + ω * Complex.I) * ↑(R ^ 2)) = α * R ^ 2 := by
          rw [Complex.re_mul_ofReal]
          simp
        have h2 : Complex.re (c₁ * (↑(R ^ 2) * ↑(R ^ 2))) = c₁.re * (R ^ 2 * R ^ 2) := by
          rw [← Complex.ofReal_mul]
          rw [Complex.re_mul_ofReal]
        rw [h1, h2]
        ring
      simpa [w] using hre
    -- Integral of the constant.
    have hcong : ∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.re (star (R * Complex.exp (Complex.I * θ)) *
          (((α : ℂ) + ω * Complex.I) * (R * Complex.exp (Complex.I * θ)) +
            c₁ * (R * Complex.exp (Complex.I * θ)) *
              (Complex.normSq (R * Complex.exp (Complex.I * θ)) : ℂ))) =
        ∫ θ in (0:ℝ)..(2 * Real.pi), (α * R ^ 2 + c₁.re * R ^ 4) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hpoint θ
    rw [hcong]
    rw [intervalIntegral.integral_const]
    -- Simplify the division by R.
    field_simp [hR, Real.pi_ne_zero]
    ring





/-! ## Averaged radial field and C¹ regularity -/

noncomputable def averagedRadialField (α ℓ₁ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun μ R => α μ * R + ℓ₁ μ * R ^ 3

theorem hasDerivAt_averagedRadialField (α ℓ₁ R : ℝ) :
    HasDerivAt (fun R' : ℝ => α * R' + ℓ₁ * R' ^ 3) (α + 3 * ℓ₁ * R ^ 2) R := by
  have h1 : HasDerivAt (fun x => α * x) α R := hasDerivAt_const_mul (x := R) α
  have hp : HasDerivAt (fun x => x ^ 3) (3 * R ^ 2) R := hasDerivAt_pow 3 R
  have h2 : HasDerivAt (fun x => ℓ₁ * x ^ 3) (ℓ₁ * (3 * R ^ 2)) R :=
    HasDerivAt.const_mul ℓ₁ hp
  have hsum : HasDerivAt (fun x => α * x + ℓ₁ * x ^ 3) (α + ℓ₁ * (3 * R ^ 2)) R :=
    HasDerivAt.add h1 h2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsum

theorem hasDerivAt_averagedRadialField_μ {α ℓ₁ : ℝ → ℝ} {μ α' ℓ₁' R : ℝ}
    (hα : HasDerivAt α α' μ) (hℓ : HasDerivAt ℓ₁ ℓ₁' μ) :
    HasDerivAt (fun t => α t * R + ℓ₁ t * R ^ 3) (α' * R + ℓ₁' * R ^ 3) μ := by
  have h1 : HasDerivAt (fun t => α t * R) (α' * R) μ := by
    have := hα.const_mul R
    simpa [mul_comm] using this
  have h2 : HasDerivAt (fun t => ℓ₁ t * R ^ 3) (ℓ₁' * R ^ 3) μ := by
    have := hℓ.const_mul (R ^ 3)
    simpa [mul_comm] using this
  exact HasDerivAt.add h1 h2

theorem hasDerivAt_averagedRadialField_RR (α ℓ₁ R : ℝ) :
    HasDerivAt (fun R' : ℝ => α + 3 * ℓ₁ * R' ^ 2) (6 * ℓ₁ * R) R := by
  have hp : HasDerivAt (fun x => x ^ 2) (2 * R) R := by simpa using hasDerivAt_pow 2 R
  have hc : HasDerivAt (fun x => (3 * ℓ₁) * x ^ 2) ((3 * ℓ₁) * (2 * R)) R :=
    HasDerivAt.const_mul (3 * ℓ₁) hp
  have h0 : HasDerivAt (fun _ => α) 0 R := hasDerivAt_const (c := α) (x := R)
  have hsum : HasDerivAt (fun x => α + (3 * ℓ₁) * x ^ 2) (0 + (3 * ℓ₁) * (2 * R)) R :=
    HasDerivAt.add h0 hc
  exact HasDerivAt.congr_deriv hsum (by ring)

theorem averagedRadialField_amplitude {α ℓ₁ : ℝ → ℝ} (μ : ℝ) (R : ℝ)
    (hR : R ≠ 0) (hℓ : ℓ₁ μ ≠ 0) :
    averagedRadialField α ℓ₁ μ R = 0 ↔ R ^ 2 = - α μ / ℓ₁ μ := by
  unfold averagedRadialField
  constructor
  · intro h
    have hfactor : R * (α μ + ℓ₁ μ * R ^ 2) = 0 := by linear_combination h
    have hsum : α μ + ℓ₁ μ * R ^ 2 = 0 := (mul_eq_zero.mp hfactor).resolve_left hR
    have hprod : ℓ₁ μ * R ^ 2 = - α μ := by linear_combination hsum
    exact (eq_div_iff hℓ).mpr (by simpa [mul_comm] using hprod)
  · intro hsq
    have hprod : ℓ₁ μ * R ^ 2 = - α μ := by simpa [mul_comm] using (eq_div_iff hℓ).mp hsq
    have hsum : α μ + ℓ₁ μ * R ^ 2 = 0 := by linear_combination hprod
    have hfactor : R * α μ + ℓ₁ μ * R ^ 3 = 0 := by linear_combination R * hsum
    simpa [mul_add, mul_assoc, mul_comm, mul_left_comm] using hfactor

/-! ## Instantiating FullRadialField -/

noncomputable def fullRadialFieldOf
    (α ℓ₁ : ℝ → ℝ) (dα dℓ : ℝ → ℝ)
    (hα : ∀ t, HasDerivAt α (dα t) t)
    (hℓ : ∀ t, HasDerivAt ℓ₁ (dℓ t) t)
    (hdα : Continuous dα) (hdℓ : Continuous dℓ)
    (μ₁ R₀ : ℝ) (hroot : α μ₁ * R₀ + ℓ₁ μ₁ * R₀ ^ 3 = 0)
    (hnondeg : ℓ₁ μ₁ ≠ 0) (hR : R₀ ≠ 0) :
    CRNT.PlanarHopfData.FullRadialField μ₁ R₀ := by
  -- continuity of α, ℓ₁ from differentiability
  have cα : Continuous α := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hα x).differentiableAt.continuousAt
  have cℓ : Continuous ℓ₁ := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hℓ x).differentiableAt.continuousAt
  refine
    { G := fun μ R => α μ * R + ℓ₁ μ * R ^ 3
      G₁ := fun μ R => dα μ * R + dℓ μ * R ^ 3
      G₂ := fun μ R => α μ + 3 * ℓ₁ μ * R ^ 2
      hasDeriv_G₁ := ?_
      hasDeriv_G₂ := ?_
      cont_G₁ := ?_
      cont_G₂ := ?_
      isRoot := ?_
      nondegenerate := ?_ }
  · -- hasDeriv_G₁
    filter_upwards [Filter.univ_mem] with v _
    exact hasDerivAt_averagedRadialField_μ (hα v.1) (hℓ v.1)
  · -- hasDeriv_G₂
    filter_upwards [Filter.univ_mem] with v _
    exact hasDerivAt_averagedRadialField (α v.1) (ℓ₁ v.1) v.2
  · -- cont_G₁
    have : ContinuousAt (Function.uncurry (fun μ R => dα μ * R + dℓ μ * R ^ 3)) (μ₁, R₀) := by
      -- from continuity of dα,dℓ
      have hdαc : Continuous dα := hdα
      have hdℓc : Continuous dℓ := hdℓ
      -- product and sum of continuous functions on product
      have h1 : Continuous (fun p : ℝ × ℝ => dα p.1 * p.2) := by
        have hc : Continuous (fun p : ℝ × ℝ => dα p.1) := hdα.comp continuous_fst
        exact hc.mul continuous_snd
      have h2 : Continuous (fun p : ℝ × ℝ => dℓ p.1 * p.2 ^ 3) := by
        have hc : Continuous (fun p : ℝ × ℝ => dℓ p.1) := hdℓ.comp continuous_fst
        exact hc.mul (continuous_snd.pow 3)
      exact (h1.add h2).continuousAt
    exact this
  · -- cont_G₂
    have : ContinuousAt (Function.uncurry (fun μ R => α μ + 3 * ℓ₁ μ * R ^ 2)) (μ₁, R₀) := by
      have hαc : Continuous α := cα
      have hℓc : Continuous ℓ₁ := cℓ
      have h1 : Continuous (fun p : ℝ × ℝ => α p.1) := hαc.comp continuous_fst
      have h2 : Continuous (fun p : ℝ × ℝ => 3 * ℓ₁ p.1 * p.2 ^ 2) := by
        have hc : Continuous (fun p : ℝ × ℝ => ℓ₁ p.1) := hℓc.comp continuous_fst
        exact (by simpa [mul_assoc, mul_comm, mul_left_comm] using (hc.mul (continuous_snd.pow 2)).const_mul 3)
      exact (h1.add h2).continuousAt
    exact this
  · -- isRoot
    exact hroot
  · -- nondegenerate
    have hαeq : α μ₁ = - ℓ₁ μ₁ * R₀ ^ 2 := by
      have : R₀ * (α μ₁ + ℓ₁ μ₁ * R₀ ^ 2) = 0 := by linear_combination hroot
      have : α μ₁ + ℓ₁ μ₁ * R₀ ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left hR
      linear_combination this
    have : α μ₁ + 3 * ℓ₁ μ₁ * R₀ ^ 2 = 2 * ℓ₁ μ₁ * R₀ ^ 2 := by
      rw [hαeq]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hnondeg) (pow_ne_zero 2 hR)

noncomputable def truncatedFullRadialField
    (H : CRNT.PlanarHopfData)
    (unfold : ∀ μ, H.α μ = H.α' * (μ - H.μ₀))
    (hℓ : H.firstLyapunov ≠ 0)
    (μ₁ R₀ : ℝ) (hroot : H.radialField μ₁ R₀ = 0) (hR : 0 < R₀) :
    CRNT.PlanarHopfData.FullRadialField μ₁ R₀ := by
  -- derivative of α everywhere
  have hαderiv : ∀ t, HasDerivAt H.α H.α' t := by
    intro t
    have h1 : HasDerivAt (fun s => H.α' * s) H.α' t := hasDerivAt_const_mul (x := t) H.α'
    have h2 : HasDerivAt (fun s => H.α' * s - H.α' * H.μ₀) H.α' t := h1.sub_const (H.α' * H.μ₀)
    have hfun : H.α = fun s => H.α' * (s - H.μ₀) := by
      funext s; exact unfold s
    rw [hfun]
    simpa [mul_sub] using h2
  have hroot' : H.α μ₁ * R₀ + H.firstLyapunov * R₀ ^ 3 = 0 := by
    simpa [CRNT.PlanarHopfData.radialField, CRNT.PlanarHopfData.radialField_apply] using hroot
  exact fullRadialFieldOf H.α (fun _ => H.firstLyapunov)
    (fun _ => H.α') (fun _ => 0)
    hαderiv (fun t => hasDerivAt_const (c := H.firstLyapunov) (x := t))
    continuous_const continuous_const
    μ₁ R₀ hroot' hℓ (ne_of_gt hR)

end Hopf

end CRNT