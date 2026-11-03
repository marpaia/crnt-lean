import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Slow–fast reduction (a quantitative Tikhonov theorem)

For the singularly perturbed system

`ẋ = f(x, y)`,  `ε ẏ = g(x, y)`

with a slow manifold `y = h(x)` (`g(x, h(x)) = 0`) along which the fast subsystem is uniformly
contracting,

`⟨g(x, y) − g(x, y'), y − y'⟩ ≤ −μ |y − y'|²`,

every solution is close to the reduced system `Ẋ = f(X, h(X))` started at the same slow state:

* the fast deviation `E(t) = |y(t) − h(x(t))|²` satisfies
  `E(t) ≤ e^{−μt/ε} E(0) + (ε G/μ)²` (`fast_deviation_le`), where `G` bounds the speed
  `|Dh(x) f(x, y)|` of the slow manifold along the flow;
* the slow error `Q(t) = |x(t) − X(t)|²` satisfies
  `Q(t) ≤ e^{(2 + L²) t} L_f² (E(0) ε/μ + (εG/μ)² t)` (`slow_error_le`), where `L_f` is the
  Lipschitz constant of `f` in `y` and `L` that of the reduced field.

With the initial deviation `E(0)` bounded, the right-hand sides are `O(ε)` uniformly on
`[0, T]`, so `x_ε → X` uniformly and `y_ε(t) − h(x_ε(t)) → 0` for every `t > 0` as `ε → 0`.
All norms are Euclidean, written as sums of squares; both estimates come from monotonicity of
`e^{±ct}`-weighted quantities (termwise AM–GM, no Cauchy–Schwarz). Instance: the
quasi-steady-state approximation for Michaelis–Menten kinetics in the Segel–Slemrod scaling
(`MichaelisMenten.qssa`).
-/

open Set Filter
open scoped Topology BigOperators

namespace CRNT
namespace SlowFast

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Termwise AM–GM: `2 u v ≤ a u² + v²/a`. -/
theorem two_mul_le (a : ℝ) (ha : 0 < a) (u v : ℝ) : 2 * u * v ≤ a * u ^ 2 + v ^ 2 / a := by
  rw [← sub_nonneg]
  have h : a * u ^ 2 + v ^ 2 / a - 2 * u * v = (a * u - v) ^ 2 / a := by field_simp; ring
  rw [h]; positivity

section

variable (f : (A → ℝ) → (B → ℝ) → (A → ℝ)) (g : (A → ℝ) → (B → ℝ) → (B → ℝ))
  (h : (A → ℝ) → (B → ℝ)) (Dh : (A → ℝ) → ((A → ℝ) →L[ℝ] (B → ℝ)))
  {Kx : Set (A → ℝ)} {Ky : Set (B → ℝ)} {μ G ε T : ℝ}
  (x : ℝ → A → ℝ) (y : ℝ → B → ℝ)

/-- The fast deviation. -/
noncomputable def fastDev (t : ℝ) : ℝ := ∑ b, (y t b - h (x t) b) ^ 2

/-- **The fast deviation decays to `O(ε²)`.** -/
theorem fast_deviation_le (hμ : 0 < μ) (hε : 0 < ε) (hT : 0 ≤ T)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z) (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b, (g z u b - g z v b) * (u b - v b) ≤ -μ * ∑ b, (u b - v b) ^ 2)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky, ∑ b, (Dh z (f z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, fastDev h x y t ≤
      Real.exp (-(μ / ε * t)) * fastDev h x y 0 + (ε * G / μ) ^ 2 := by
  set E := fastDev h x y with hE
  set c := μ / ε with hc
  have hc0 : 0 < c := div_pos hμ hε
  set C := ε / μ * G ^ 2 with hC
  -- the weighted quantity `φ(t) = e^{ct} E(t) − (C/c) e^{ct}`
  set φ : ℝ → ℝ := fun t => Real.exp (c * t) * E t - C / c * Real.exp (c * t) with hφ
  have hEder : ∀ t ∈ Ioo 0 T, HasDerivAt E
      (∑ b, 2 * (y t b - h (x t) b) * ((1 / ε) * g (x t) (y t) b - Dh (x t) (f (x t) (y t)) b)) t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hhx : HasDerivAt (fun t => h (x t)) (Dh (x t) (f (x t) (y t))) t :=
      (hh (x t) (hxK t htI)).comp_hasDerivAt t (hx t ht)
    have hyb := hasDerivAt_pi.mp (hy t ht)
    have hhb := hasDerivAt_pi.mp hhx
    refine HasDerivAt.fun_sum fun b _ => ?_
    have h1 := ((hyb b).sub (hhb b)).pow 2
    convert h1 using 1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    push_cast; ring
  have hEbound : ∀ t ∈ Ioo 0 T, (∑ b, 2 * (y t b - h (x t) b) *
      ((1 / ε) * g (x t) (y t) b - Dh (x t) (f (x t) (y t)) b)) ≤ -c * E t + C := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hz := hxK t htI
    have hu := hyK t htI
    have hm := hmono (x t) hz (y t) hu (h (x t)) (hhK _ hz)
    rw [hzero _ hz] at hm
    simp only [Pi.zero_apply, sub_zero] at hm
    have hg := hG (x t) hz (y t) hu
    have hsplit : ∑ b, 2 * (y t b - h (x t) b) *
        ((1 / ε) * g (x t) (y t) b - Dh (x t) (f (x t) (y t)) b) =
        2 / ε * ∑ b, g (x t) (y t) b * (y t b - h (x t) b) -
          ∑ b, 2 * (y t b - h (x t) b) * Dh (x t) (f (x t) (y t)) b := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by field_simp <;> ring
    have hcross : -∑ b, 2 * (y t b - h (x t) b) * Dh (x t) (f (x t) (y t)) b ≤
        c * E t + 1 / c * G ^ 2 := by
      have : ∀ b, -(2 * (y t b - h (x t) b) * Dh (x t) (f (x t) (y t)) b) ≤
          c * (y t b - h (x t) b) ^ 2 + (Dh (x t) (f (x t) (y t)) b) ^ 2 / c := fun b => by
        have h1 := two_mul_le c hc0 (y t b - h (x t) b) (-(Dh (x t) (f (x t) (y t)) b))
        rw [neg_sq] at h1
        have e : 2 * (y t b - h (x t) b) * -(Dh (x t) (f (x t) (y t)) b) =
            -(2 * (y t b - h (x t) b) * Dh (x t) (f (x t) (y t)) b) := by ring
        linarith
      have hs := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => this b
      rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hs
      have : (∑ b, (Dh (x t) (f (x t) (y t)) b) ^ 2) / c ≤ G ^ 2 / c :=
        div_le_div_of_nonneg_right hg hc0.le
      have e : 1 / c * G ^ 2 = G ^ 2 / c := by ring
      simp only [hE, fastDev] at *
      linarith
    rw [hsplit]
    have h2 : 2 / ε * ∑ b, g (x t) (y t) b * (y t b - h (x t) b) ≤ 2 / ε * (-μ * E t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [hE, fastDev] using hm
    have e1 : 2 / ε * (-μ * E t) = -(2 * c) * E t := by rw [hc]; ring
    have e2 : 1 / c * G ^ 2 = C := by rw [hc, hC]; field_simp
    linarith
  -- φ is antitone
  have hEc : ContinuousOn E (Icc 0 T) := by
    simp only [hE, fastDev]
    refine continuousOn_finsetSum _ fun b _ => ?_
    exact (((continuous_apply b).comp_continuousOn hyc).sub
      ((continuous_apply b).comp_continuousOn hhc)).pow 2
  have hφanti : AntitoneOn φ (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) ?_ (fun t ht => ?_) (fun t ht => ?_)
      (f' := fun t => Real.exp (c * t) * c * E t + Real.exp (c * t) *
        (∑ b, 2 * (y t b - h (x t) b) * ((1 / ε) * g (x t) (y t) b - Dh (x t) (f (x t) (y t)) b)) -
        C / c * (Real.exp (c * t) * c))
    · simp only [hφ]
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hEc).sub
        (continuousOn_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    · rw [interior_Icc] at ht ⊢
      have he : HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * t) * c) t := by
        simpa using ((hasDerivAt_id t).const_mul c).exp
      exact ((he.mul (hEder t ht)).sub (he.const_mul (C / c))).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have hb := hEbound t ht
      have hex := Real.exp_pos (c * t)
      have : Real.exp (c * t) * c * E t + Real.exp (c * t) *
          (∑ b, 2 * (y t b - h (x t) b) * ((1 / ε) * g (x t) (y t) b - Dh (x t) (f (x t) (y t)) b)) -
          C / c * (Real.exp (c * t) * c) =
          Real.exp (c * t) * ((∑ b, 2 * (y t b - h (x t) b) * ((1 / ε) * g (x t) (y t) b -
            Dh (x t) (f (x t) (y t)) b)) + c * E t - C) := by
        field_simp; ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hex.le (by linarith)
  intro t ht
  have h1 := hφanti ⟨le_rfl, hT⟩ ht ht.1
  simp only [hφ, mul_zero, Real.exp_zero, one_mul] at h1
  -- `e^{ct} E t ≤ E 0 + (C/c)(e^{ct} − 1)`
  have hex := Real.exp_pos (c * t)
  have hCc : C / c = (ε * G / μ) ^ 2 := by rw [hC, hc]; field_simp
  have hE0 : 0 ≤ E 0 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have key : E t ≤ Real.exp (-(c * t)) * E 0 + C / c * (1 - Real.exp (-(c * t))) := by
    have hinv : Real.exp (-(c * t)) = (Real.exp (c * t))⁻¹ := Real.exp_neg _
    rw [hinv]
    rw [← mul_le_mul_iff_of_pos_left hex]
    have : Real.exp (c * t) * ((Real.exp (c * t))⁻¹ * E 0 + C / c * (1 - (Real.exp (c * t))⁻¹)) =
        E 0 + C / c * (Real.exp (c * t) - 1) := by
      field_simp
    rw [this]
    linarith
  have hexn : 0 < Real.exp (-(c * t)) := Real.exp_pos _
  have hneg : (-(μ / ε * t)) = -(c * t) := by rw [hc]
  rw [hneg]
  have hCc0 : 0 ≤ C / c := by positivity
  nlinarith


/-- The slow error. -/
noncomputable def slowErr (X : ℝ → A → ℝ) (t : ℝ) : ℝ := ∑ a, (x t a - X t a) ^ 2

/-- **The slow error is `O(ε)`.** -/
theorem slow_error_le (hμ : 0 < μ) (hε : 0 < ε) (hT : 0 ≤ T) {Lf L : ℝ}
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z) (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky,
      ∑ b, (g z u b - g z v b) * (u b - v b) ≤ -μ * ∑ b, (u b - v b) ^ 2)
    (hG : ∀ z ∈ Kx, ∀ u ∈ Ky, ∑ b, (Dh z (f z u) b) ^ 2 ≤ G ^ 2)
    (hhK : ∀ z ∈ Kx, h z ∈ Ky)
    (hf1 : ∀ z ∈ Kx, ∀ u ∈ Ky, ∀ v ∈ Ky, ∑ a, (f z u a - f z v a) ^ 2 ≤ Lf ^ 2 * ∑ b, (u b - v b) ^ 2)
    (hf2 : ∀ z ∈ Kx, ∀ z' ∈ Kx,
      ∑ a, (f z (h z) a - f z' (h z') a) ^ 2 ≤ L ^ 2 * ∑ a, (z a - z' a) ^ 2)
    (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ Kx) (hyK : ∀ t ∈ Icc 0 T, y t ∈ Ky)
    (hhc : ContinuousOn (fun t => h (x t)) (Icc 0 T))
    (X : ℝ → A → ℝ) (hXc : ContinuousOn X (Icc 0 T))
    (hX : ∀ t ∈ Ioo 0 T, HasDerivAt X (f (X t) (h (X t))) t)
    (hXK : ∀ t ∈ Icc 0 T, X t ∈ Kx) (hX0 : X 0 = x 0) :
    ∀ t ∈ Icc 0 T, slowErr x X t ≤
      Real.exp ((2 + L ^ 2) * t) * Lf ^ 2 *
        (fastDev h x y 0 * (ε / μ) + (ε * G / μ) ^ 2 * t) := by
  have hfast := fast_deviation_le f g h Dh x y hμ hε hT hh hzero hmono hG hhK hxc hyc hx hy hxK hyK hhc
  set E := fastDev h x y with hE
  set Q := slowErr x X with hQ
  set K := 2 + L ^ 2 with hK
  set c := μ / ε with hc
  have hc0 : 0 < c := div_pos hμ hε
  set D := (ε * G / μ) ^ 2 with hD
  have hE0 : 0 ≤ E 0 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hEnn : ∀ t, 0 ≤ E t := fun t => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hLf2 : 0 ≤ Lf ^ 2 := sq_nonneg _
  -- derivative of Q and its bound
  have hQder : ∀ t ∈ Ioo 0 T, HasDerivAt Q
      (∑ a, 2 * (x t a - X t a) * (f (x t) (y t) a - f (X t) (h (X t)) a)) t := by
    intro t ht
    have hxa := hasDerivAt_pi.mp (hx t ht)
    have hXa := hasDerivAt_pi.mp (hX t ht)
    refine HasDerivAt.fun_sum fun a _ => ?_
    have h1 := ((hxa a).sub (hXa a)).pow 2
    convert h1 using 1
    simp only [Pi.sub_apply]
    push_cast; ring
  have hQbound : ∀ t ∈ Ioo 0 T,
      (∑ a, 2 * (x t a - X t a) * (f (x t) (y t) a - f (X t) (h (X t)) a)) ≤ K * Q t + Lf ^ 2 * E t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have h1 := hf1 (x t) (hxK t htI) (y t) (hyK t htI) (h (x t)) (hhK _ (hxK t htI))
    have h2 := hf2 (x t) (hxK t htI) (X t) (hXK t htI)
    have hterm : ∀ a, 2 * (x t a - X t a) * (f (x t) (y t) a - f (X t) (h (X t)) a) ≤
        2 * (x t a - X t a) ^ 2 + (f (x t) (y t) a - f (x t) (h (x t)) a) ^ 2 +
          (f (x t) (h (x t)) a - f (X t) (h (X t)) a) ^ 2 := fun a => by
      nlinarith [sq_nonneg (x t a - X t a - (f (x t) (y t) a - f (x t) (h (x t)) a)),
        sq_nonneg (x t a - X t a - (f (x t) (h (x t)) a - f (X t) (h (X t)) a))]
    have hs := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hterm a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    simp only [hQ, slowErr, hE, fastDev, hK]
    nlinarith [h1, h2]
  -- the weighted quantity
  set Bint : ℝ → ℝ := fun t => E 0 * (1 - Real.exp (-(c * t))) / c + D * t with hBint
  set φ : ℝ → ℝ := fun t => Real.exp (-(K * t)) * Q t - Lf ^ 2 * Bint t with hφ
  have hQc : ContinuousOn Q (Icc 0 T) := by
    simp only [hQ, slowErr]
    refine continuousOn_finsetSum _ fun a _ => ?_
    exact (((continuous_apply a).comp_continuousOn hxc).sub
      ((continuous_apply a).comp_continuousOn hXc)).pow 2
  have hφanti : AntitoneOn φ (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) ?_ (fun t ht => ?_) (fun t ht => ?_)
      (f' := fun t => Real.exp (-(K * t)) * (-K) * Q t + Real.exp (-(K * t)) *
        (∑ a, 2 * (x t a - X t a) * (f (x t) (y t) a - f (X t) (h (X t)) a)) -
        Lf ^ 2 * (E 0 * (Real.exp (-(c * t)) * c) / c + D))
    · simp only [hφ, hBint]
      refine ContinuousOn.sub ?_ ?_
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul hQc
      · refine continuousOn_const.mul ?_
        refine ContinuousOn.add ?_ (continuousOn_const.mul continuousOn_id)
        refine ContinuousOn.div_const ?_ _
        exact continuousOn_const.mul (continuousOn_const.sub
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn)
    · rw [interior_Icc] at ht ⊢
      have he : HasDerivAt (fun t => Real.exp (-(K * t))) (Real.exp (-(K * t)) * (-K)) t := by
        have := ((hasDerivAt_id t).const_mul K).neg.exp
        simpa using this
      have hec : HasDerivAt (fun t => Real.exp (-(c * t))) (Real.exp (-(c * t)) * (-c)) t := by
        have := ((hasDerivAt_id t).const_mul c).neg.exp
        simpa using this
      have hB : HasDerivAt Bint (E 0 * (Real.exp (-(c * t)) * c) / c + D) t := by
        have h1 := ((hec.const_sub 1).const_mul (E 0)).div_const c
        have h2 := (hasDerivAt_id t).const_mul D
        convert h1.add h2 using 1
        · funext t'; simp [hBint]
        · simp
      exact ((he.mul (hQder t ht)).sub (hB.const_mul (Lf ^ 2))).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have htI := Ioo_subset_Icc_self ht
      have hb := hQbound t ht
      have hEt := hfast t htI
      have hexK := Real.exp_pos (-(K * t))
      have hexK1 : Real.exp (-(K * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ K := by positivity
        nlinarith [ht.1])
      have hneg : (-(μ / ε * t)) = -(c * t) := by rw [hc]
      rw [hneg] at hEt
      have hBt : E 0 * (Real.exp (-(c * t)) * c) / c + D = Real.exp (-(c * t)) * E 0 + D := by
        field_simp
      rw [hBt]
      have h1 : Real.exp (-(K * t)) * (-K) * Q t + Real.exp (-(K * t)) *
          (∑ a, 2 * (x t a - X t a) * (f (x t) (y t) a - f (X t) (h (X t)) a)) ≤
          Real.exp (-(K * t)) * (Lf ^ 2 * E t) := by
        have := mul_le_mul_of_nonneg_left hb hexK.le
        nlinarith
      have h2 : Real.exp (-(K * t)) * (Lf ^ 2 * E t) ≤ Lf ^ 2 * E t := by
        have : 0 ≤ Lf ^ 2 * E t := mul_nonneg hLf2 (hEnn t)
        nlinarith
      have h3 : Lf ^ 2 * E t ≤ Lf ^ 2 * (Real.exp (-(c * t)) * E 0 + D) :=
        mul_le_mul_of_nonneg_left hEt hLf2
      linarith
  intro t ht
  have h1 := hφanti ⟨le_rfl, hT⟩ ht ht.1
  have hQ0 : Q 0 = 0 := by
    simp only [hQ, slowErr, hX0, sub_self]
    simp
  simp only [hφ, hBint, mul_zero, neg_zero, Real.exp_zero, one_mul, hQ0, sub_self, zero_div,
    zero_add] at h1
  have hexK := Real.exp_pos (K * t)
  have hBle : Bint t ≤ E 0 * (ε / μ) + D * t := by
    simp only [hBint]
    have h2 : E 0 * (1 - Real.exp (-(c * t))) / c ≤ E 0 * (ε / μ) := by
      rw [div_le_iff₀ hc0]
      have : 0 ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
      have e : E 0 * (ε / μ) * c = E 0 := by rw [hc]; field_simp
      nlinarith
    linarith
  have hQt : Q t ≤ Real.exp (K * t) * (Lf ^ 2 * Bint t) := by
    have hinv : Real.exp (-(K * t)) = (Real.exp (K * t))⁻¹ := Real.exp_neg _
    rw [hinv] at h1
    have : (Real.exp (K * t))⁻¹ * Q t ≤ Lf ^ 2 * Bint t := by linarith
    rw [inv_mul_le_iff₀ hexK] at this
    linarith
  calc Q t ≤ Real.exp (K * t) * (Lf ^ 2 * Bint t) := hQt
    _ ≤ Real.exp (K * t) * (Lf ^ 2 * (E 0 * (ε / μ) + D * t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBle hLf2) hexK.le
    _ = Real.exp (K * t) * Lf ^ 2 * (E 0 * (ε / μ) + D * t) := by ring

end

end SlowFast
end CRNT

namespace CRNT
namespace SlowFast
namespace MichaelisMenten

/-! ### The quasi-steady-state approximation for Michaelis–Menten kinetics

In the Segel–Slemrod scaling, `ṡ = −s + (s + K − λ) c`, `ε ċ = s − (s + K) c` (`0 < λ ≤ K`).
The slow manifold is `c = s/(s + K)` and the reduced system is the Michaelis–Menten law
`Ṡ = −λ S/(S + K)`. On `s, c ∈ [0, 1]` the fast subsystem contracts at rate `K`, so the full
solutions stay within `O(√ε)` of the reduced one (`qssa`). -/

variable {K lam : ℝ}

/-- The slow field. -/
def fMM (K lam : ℝ) (s : Fin 1 → ℝ) (c : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => -s 0 + (s 0 + K - lam) * c 0

/-- The fast field. -/
def gMM (K : ℝ) (s : Fin 1 → ℝ) (c : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => s 0 - (s 0 + K) * c 0

/-- The slow manifold. -/
noncomputable def hMM (K : ℝ) (s : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => s 0 / (s 0 + K)

/-- Its derivative. -/
noncomputable def DhMM (K : ℝ) (s : Fin 1 → ℝ) : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => (K / (s 0 + K) ^ 2) • ContinuousLinearMap.proj 0

/-- The region `[0, 1]`. -/
def box : Set (Fin 1 → ℝ) := {s | 0 ≤ s 0 ∧ s 0 ≤ 1}

theorem hasFDerivAt_hMM (hK : 0 < K) {z : Fin 1 → ℝ} (hz : z ∈ box) :
    HasFDerivAt (hMM K) (DhMM K z) z := by
  show HasFDerivAt (fun x (_ : Fin 1) => x 0 / (x 0 + K))
    (ContinuousLinearMap.pi fun _ => (K / (z 0 + K) ^ 2) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) z
  rw [hasFDerivAt_pi]
  intro i
  have hne : z 0 + K ≠ 0 := by have := hz.1; linarith
  have h1 : HasDerivAt (fun u : ℝ => u / (u + K)) (K / (z 0 + K) ^ 2) (z 0) := by
    have hd := (hasDerivAt_id' (z 0)).div ((hasDerivAt_id' (z 0)).add_const K) hne
    convert hd using 1
    field_simp
    ring
  have h2 := HasDerivAt.comp_hasFDerivAt
    (f := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) z h1
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  convert h2 using 1
  ext v
  simp [DhMM]

theorem zero_hMM (hK : 0 < K) {z : Fin 1 → ℝ} (hz : z ∈ box) : gMM K z (hMM K z) = 0 := by
  funext i
  have hne : z 0 + K ≠ 0 := by have := hz.1; linarith
  simp [gMM, hMM]
  field_simp
  ring

theorem mono_gMM (hK : 0 < K) {z : Fin 1 → ℝ} (hz : z ∈ box) (u v : Fin 1 → ℝ) :
    ∑ b, (gMM K z u b - gMM K z v b) * (u b - v b) ≤ -K * ∑ b, (u b - v b) ^ 2 := by
  simp only [gMM, Fin.sum_univ_one]
  have := hz.1
  nlinarith [sq_nonneg (u 0 - v 0)]

theorem hMM_mem (hK : 0 < K) {z : Fin 1 → ℝ} (hz : z ∈ box) : hMM K z ∈ box := by
  have h1 : 0 < z 0 + K := by have := hz.1; linarith
  refine ⟨div_nonneg hz.1 h1.le, ?_⟩
  show z 0 / (z 0 + K) ≤ 1
  rw [div_le_one h1]; linarith

theorem speed_bound (hK : 0 < K) (hlam : 0 < lam) (hlK : lam ≤ K) {z : Fin 1 → ℝ} (hz : z ∈ box)
    {u : Fin 1 → ℝ} (hu : u ∈ box) :
    ∑ b, (DhMM K z (fMM K lam z u) b) ^ 2 ≤ ((2 + K) / K) ^ 2 := by
  simp only [DhMM, fMM, Fin.sum_univ_one, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have h1 : 0 < z 0 + K := by have := hz.1; linarith
  have hfb : |-z 0 + (z 0 + K - lam) * u 0| ≤ 2 + K := by
    rw [abs_le]
    have := hz.1; have := hz.2; have := hu.1; have := hu.2
    constructor <;> nlinarith
  have hD : K / (z 0 + K) ^ 2 ≤ 1 / K := by
    rw [div_le_div_iff₀ (by positivity) hK]
    nlinarith [hz.1]
  have hD0 : 0 ≤ K / (z 0 + K) ^ 2 := by positivity
  have habs : |K / (z 0 + K) ^ 2 * (-z 0 + (z 0 + K - lam) * u 0)| ≤ (2 + K) / K := by
    rw [abs_mul, abs_of_nonneg hD0]
    calc K / (z 0 + K) ^ 2 * |-z 0 + (z 0 + K - lam) * u 0| ≤ 1 / K * (2 + K) :=
          mul_le_mul hD hfb (abs_nonneg _) (by positivity)
      _ = (2 + K) / K := by ring
  calc (K / (z 0 + K) ^ 2 * (-z 0 + (z 0 + K - lam) * u 0)) ^ 2
      = |K / (z 0 + K) ^ 2 * (-z 0 + (z 0 + K - lam) * u 0)| ^ 2 := (sq_abs _).symm
    _ ≤ ((2 + K) / K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2

theorem lip_y (hK : 0 < K) (hlam : 0 < lam) (hlK : lam ≤ K) {z : Fin 1 → ℝ} (hz : z ∈ box)
    (u v : Fin 1 → ℝ) :
    ∑ a, (fMM K lam z u a - fMM K lam z v a) ^ 2 ≤ (1 + K) ^ 2 * ∑ b, (u b - v b) ^ 2 := by
  simp only [fMM, Fin.sum_univ_one]
  have h1 : 0 ≤ z 0 + K - lam := by have := hz.1; linarith
  have h2 : z 0 + K - lam ≤ 1 + K := by have := hz.2; linarith
  have e : (-z 0 + (z 0 + K - lam) * u 0 - (-z 0 + (z 0 + K - lam) * v 0)) ^ 2 =
      (z 0 + K - lam) ^ 2 * (u 0 - v 0) ^ 2 := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1 h2 2) (sq_nonneg _)

theorem lip_reduced (hK : 0 < K) (hlam : 0 < lam) {z z' : Fin 1 → ℝ} (hz : z ∈ box)
    (hz' : z' ∈ box) :
    ∑ a, (fMM K lam z (hMM K z) a - fMM K lam z' (hMM K z') a) ^ 2 ≤
      (lam / K) ^ 2 * ∑ a, (z a - z' a) ^ 2 := by
  simp only [fMM, hMM, Fin.sum_univ_one]
  have h1 : 0 < z 0 + K := by have := hz.1; linarith
  have h2 : 0 < z' 0 + K := by have := hz'.1; linarith
  have e : -z 0 + (z 0 + K - lam) * (z 0 / (z 0 + K)) -
      (-z' 0 + (z' 0 + K - lam) * (z' 0 / (z' 0 + K))) =
      -(lam * K * (z 0 - z' 0)) / ((z 0 + K) * (z' 0 + K)) := by
    field_simp; ring
  have hP : K ^ 2 ≤ (z 0 + K) * (z' 0 + K) := by nlinarith [hz.1, hz'.1]
  have hP4 : K ^ 4 ≤ ((z 0 + K) * (z' 0 + K)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hP 2
    nlinarith
  rw [e, div_pow, neg_sq, div_le_iff₀ (by positivity)]
  have key : (lam * K * (z 0 - z' 0)) ^ 2 = (lam / K) ^ 2 * (z 0 - z' 0) ^ 2 * K ^ 4 := by
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left hP4 (by positivity)

/-- **QSSA for Michaelis–Menten kinetics.** Solutions `(s, c)` of the scaled Michaelis–Menten
system in `[0, 1]²` and the solution `S` of the reduced law `Ṡ = −λ S/(S + K)` in `[0, 1]` with
`S(0) = s(0)` satisfy `|s(t) − S(t)|² ≤ e^{(2 + (λ/K)²)t} (1 + K)² (E(0) ε/K + (ε(2 + K)/K²)² t)`,
`E(0) = (c(0) − s(0)/(s(0) + K))²`. -/
theorem qssa (hK : 0 < K) (hlam : 0 < lam) (hlK : lam ≤ K) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (s c S : ℝ → Fin 1 → ℝ) (hsc : ContinuousOn s (Icc 0 T)) (hcc : ContinuousOn c (Icc 0 T))
    (hs : ∀ t ∈ Ioo 0 T, HasDerivAt s (fMM K lam (s t) (c t)) t)
    (hc : ∀ t ∈ Ioo 0 T, HasDerivAt c ((1 / ε) • gMM K (s t) (c t)) t)
    (hsK : ∀ t ∈ Icc 0 T, s t ∈ box) (hcK : ∀ t ∈ Icc 0 T, c t ∈ box)
    (hSc : ContinuousOn S (Icc 0 T))
    (hS : ∀ t ∈ Ioo 0 T, HasDerivAt S (fMM K lam (S t) (hMM K (S t))) t)
    (hSK : ∀ t ∈ Icc 0 T, S t ∈ box) (hS0 : S 0 = s 0) :
    ∀ t ∈ Icc 0 T, slowErr s S t ≤
      Real.exp ((2 + (lam / K) ^ 2) * t) * (1 + K) ^ 2 *
        (fastDev (hMM K) s c 0 * (ε / K) + (ε * ((2 + K) / K) / K) ^ 2 * t) := by
  have hhc : ContinuousOn (fun t => hMM K (s t)) (Icc 0 T) := by
    refine continuousOn_pi.mpr fun i => ?_
    show ContinuousOn (fun t => s t 0 / (s t 0 + K)) (Icc 0 T)
    refine ContinuousOn.div ((continuous_apply 0).comp_continuousOn hsc)
      (((continuous_apply 0).comp_continuousOn hsc).add continuousOn_const) fun t ht => ?_
    have := (hsK t ht).1
    show s t 0 + K ≠ 0
    linarith
  exact slow_error_le (fMM K lam) (gMM K) (hMM K) (DhMM K) s c hK hε hT
    (fun z hz => hasFDerivAt_hMM hK hz) (fun z hz => zero_hMM hK hz)
    (fun z hz u _ v _ => mono_gMM hK hz u v) (fun z hz u hu => speed_bound hK hlam hlK hz hu)
    (fun z hz => hMM_mem hK hz) (fun z hz u _ v _ => lip_y hK hlam hlK hz u v)
    (fun z hz z' hz' => lip_reduced hK hlam hz hz') hsc hcc hs hc hsK hcK hhc S hSc hS hSK hS0

end MichaelisMenten
end SlowFast
end CRNT
