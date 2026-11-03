import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Contraction of ODE flows under a one-sided Lipschitz condition

A vector field `f` on a real inner product space is **contracting with rate `c`** when
`⟪f a - f b, a - b⟫ ≤ -c ‖a - b‖²` for all `a, b` in a set `K` (a one-sided Lipschitz /
negative logarithmic norm condition; Lohmiller–Slotine 1998, and for reaction networks
Russo–di Bernardo–Sontag 2010, Angeli–Sontag 2008 for the monotone counterpart). Then any two
solutions remaining in `K` approach each other exponentially:
`‖x(t) - y(t)‖ ≤ e^{-c t} ‖x(0) - y(0)‖`.

Main results:
* `CRNT.Contraction.dist_le_exp_of_contracting`: the contraction estimate.
* `CRNT.Contraction.tendsto_of_contracting`: for `c > 0`, two solutions defined for all
  `t ≥ 0` converge to each other.
* `CRNT.Contraction.tendsto_equilibrium_of_contracting`: every solution converges to any
  equilibrium in `K`, which is therefore unique and globally attracting in `K`.
-/

namespace CRNT

namespace Contraction

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" a ", " b "⟫" => @inner ℝ E _ a b

/-- `f` is contracting with rate `c` on `K`. -/
def IsContracting (f : E → E) (K : Set E) (c : ℝ) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, ⟪f a - f b, a - b⟫ ≤ -c * ‖a - b‖ ^ 2

/-- **Contraction estimate.** Two solutions of `ẋ = f(x)` on `[0, T]` that stay in a set on
which `f` is contracting with rate `c` satisfy `‖x t - y t‖ ≤ e^{-c t} ‖x 0 - y 0‖`. -/
theorem dist_le_exp_of_contracting {f : E → E} {K : Set E} {c T : ℝ}
    (hf : IsContracting f K c) {x y : ℝ → E}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (f (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (f (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖x t - y t‖ ≤ Real.exp (-c * t) * ‖x 0 - y 0‖ := by
  set D := Set.Icc (0 : ℝ) T
  have h0 : (0 : ℝ) ∈ D := ⟨le_rfl, ht.1.trans ht.2⟩
  let g : ℝ → ℝ := fun s => Real.exp (2 * c * s) * ‖x s - y s‖ ^ 2
  have hd : ∀ s ∈ D, HasDerivWithinAt g
      (2 * c * Real.exp (2 * c * s) * ‖x s - y s‖ ^ 2 +
        Real.exp (2 * c * s) * (2 * ⟪x s - y s, f (x s) - f (y s)⟫)) D s := by
    intro s hs
    have hexp : HasDerivWithinAt (fun s => Real.exp (2 * c * s))
        (Real.exp (2 * c * s) * (2 * c)) D s := by
      have := ((hasDerivAt_id s).const_mul (2 * c)).exp
      simpa using this.hasDerivWithinAt
    have hn := ((hx s hs).sub (hy s hs)).norm_sq
    convert hexp.mul hn using 1
    simp only [Pi.sub_apply]
    ring
  have hcont : ContinuousOn g D := fun s hs => (hd s hs).continuousWithinAt
  have hanti : AntitoneOn g D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont
      (fun s hs => (hd s (interior_subset hs)).mono interior_subset) ?_
    intro s hs
    have hsD := interior_subset hs
    have hin := hf _ (hxK s hsD) _ (hyK s hsD)
    rw [real_inner_comm] at hin
    have he := Real.exp_pos (2 * c * s)
    nlinarith [mul_le_mul_of_nonneg_left hin he.le]
  have hle : g t ≤ g 0 := hanti h0 ht ht.1
  simp only [g, mul_zero, Real.exp_zero, one_mul] at hle
  have hsq : ‖x t - y t‖ ^ 2 ≤ (Real.exp (-c * t) * ‖x 0 - y 0‖) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (2 * c * t) * Real.exp (↑2 * (-c * t)) = 1 := by
      rw [← Real.exp_add, show 2 * c * t + 2 * (-c * t) = 0 by ring,
        Real.exp_zero]
    have hpos : 0 < Real.exp (↑2 * (-c * t)) := Real.exp_pos _
    calc ‖x t - y t‖ ^ 2 = (Real.exp (2 * c * t) * ‖x t - y t‖ ^ 2) *
          Real.exp (↑2 * (-c * t)) := by rw [mul_comm (Real.exp _), mul_assoc, he, mul_one]
      _ ≤ ‖x 0 - y 0‖ ^ 2 * Real.exp (↑2 * (-c * t)) :=
          mul_le_mul_of_nonneg_right hle hpos.le
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) two_ne_zero).mp hsq

/-- **Convergence of solutions.** For `c > 0`, two global forward solutions in the
contracting region converge to each other. -/
theorem tendsto_of_contracting {f : E → E} {K : Set E} {c : ℝ} (hc : 0 < c)
    (hf : IsContracting f K c) {x y : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (f (x t)) (Set.Ici 0) t)
    (hy : ∀ t, 0 ≤ t → HasDerivWithinAt y (f (y t)) (Set.Ici 0) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K) (hyK : ∀ t, 0 ≤ t → y t ∈ K) :
    Tendsto (fun t => ‖x t - y t‖) atTop (𝓝 0) := by
  have hbound : ∀ t, 0 ≤ t → ‖x t - y t‖ ≤ Real.exp (-c * t) * ‖x 0 - y 0‖ := by
    intro t ht
    exact dist_le_exp_of_contracting (T := t) hf
      (fun s hs => (hx s hs.1).mono Set.Icc_subset_Ici_self)
      (fun s hs => (hy s hs.1).mono Set.Icc_subset_Ici_self)
      (fun s hs => hxK s hs.1) (fun s hs => hyK s hs.1) ⟨ht, le_rfl⟩
  have hlim : Tendsto (fun t => Real.exp (-c * t) * ‖x 0 - y 0‖) atTop (𝓝 0) := by
    have : Tendsto (fun t => Real.exp (-c * t)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hc) (l := atTop))
      simpa [Function.comp_def] using h
    simpa using this.mul_const ‖x 0 - y 0‖
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact hbound t ht

/-- **Global attraction of an equilibrium.** If `f` is contracting with rate `c > 0` on `K`
and `xe ∈ K` is an equilibrium, every global forward solution in `K` converges to `xe`. -/
theorem tendsto_equilibrium_of_contracting {f : E → E} {K : Set E} {c : ℝ} (hc : 0 < c)
    (hf : IsContracting f K c) {xe : E} (hxe : xe ∈ K) (heq : f xe = 0) {x : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (f (x t)) (Set.Ici 0) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K) :
    Tendsto x atTop (𝓝 xe) := by
  have := tendsto_of_contracting hc hf hx (y := fun _ => xe)
    (fun t _ => by rw [heq]; exact hasDerivWithinAt_const _ _ _) hxK (fun _ _ => hxe)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact this

/-- In a contracting region with `c > 0` there is at most one equilibrium. -/
theorem equilibrium_unique_of_contracting {f : E → E} {K : Set E} {c : ℝ} (hc : 0 < c)
    (hf : IsContracting f K c) {a b : E} (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 0)
    (hfb : f b = 0) : a = b := by
  have h := hf a ha b hb
  rw [hfa, hfb, sub_zero, inner_zero_left] at h
  have : ‖a - b‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖a - b‖]
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Contraction

end CRNT
