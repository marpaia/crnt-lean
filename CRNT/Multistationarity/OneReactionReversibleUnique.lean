import CRNT.Multistationarity.OneReactionReversible
import CRNT.Analysis.NegDerivAtZeros
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fully open networks with one reversible non-flow reaction: uniqueness (Joshi 2013, Thm 4.1(2))

`revPair_unique_steadyState`: if `∑_{i : b_i > a_i} a_i ≤ 1` and `∑_{i : a_i > b_i} b_i ≤ 1`, the
fully open network with `a ⇌ b` has at most one positive steady state for every choice of rates.
With `revPair_exists_two_steadyStates` this gives Joshi's Theorem 4.1(2) as an iff
(`revPair_multistationary_iff`).

Proof (direct; Joshi uses the Deficiency One Algorithm).  Steady states correspond to zeros of
`G(w) = k_f ∏ x_i(w)^{a_i} - k_r ∏ x_i(w)^{b_i} - w` on the interval where
`x_i(w) = (k_i + d_i w)/l_i > 0`.  At a zero `w₀` (`α - β = w₀`, `α = k_f x^a`, `β = k_r x^b`),
`G'(w₀) + 1 = ∑ (α a_i - β b_i) d_i/(k_i + d_i w₀)`; each term is bounded by
`a_i · (w₀ d_i /(k_i + d_i w₀)) < a_i` on `b_i > a_i` and `≤ 0` elsewhere if `w₀ ≥ 0`, and
symmetrically with `b_i` on `a_i > b_i` if `w₀ < 0`; so `G'(w₀) < 0`, and a function with
negative derivative at each zero has at most one zero (`no_two_zeros_of_deriv_neg`).

Nothing here is an axiom or a `sorry`.
-/

open Finset Filter Topology Set

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `∑ c_s t_s < 1` when `0 ≤ t_s < 1` and `∑ c_s ≤ 1` (natural weights). -/
theorem weighted_sum_lt_one {F : Finset S} {c : S → ℕ} {t : S → ℝ}
    (ht0 : ∀ s ∈ F, 0 ≤ t s) (ht1 : ∀ s ∈ F, t s < 1) (hc : ∑ s ∈ F, c s ≤ 1) :
    ∑ s ∈ F, (c s : ℝ) * t s < 1 := by
  by_cases hex : ∃ s ∈ F, 0 < c s
  · have hlt : ∑ s ∈ F, (c s : ℝ) * t s < ∑ s ∈ F, (c s : ℝ) := by
      obtain ⟨s₀, hs₀, hpos⟩ := hex
      refine sum_lt_sum (fun s hs => ?_) ⟨s₀, hs₀, ?_⟩
      · have := ht1 s hs; have := ht0 s hs
        nlinarith [(Nat.cast_nonneg (c s) : (0:ℝ) ≤ c s)]
      · have : (0 : ℝ) < c s₀ := by exact_mod_cast hpos
        nlinarith [ht1 s₀ hs₀]
    have : (∑ s ∈ F, (c s : ℝ)) ≤ 1 := by exact_mod_cast hc
    linarith
  · push Not at hex
    rw [sum_eq_zero fun s hs => by rw [Nat.le_zero.mp (hex s hs), Nat.cast_zero, zero_mul]]
    norm_num

/-- **Negative slope at zeros.** -/
theorem revPair_slope_neg (a b : Complex S)
    (hP : ∑ s ∈ univ.filter (fun s => a s < b s), a s ≤ 1)
    (hN : ∑ s ∈ univ.filter (fun s => b s < a s), b s ≤ 1)
    {kin : S → ℝ} (hkin : ∀ s, 0 < kin s) {w₀ α β : ℝ}
    (hI : ∀ s, 0 < kin s + ((b s : ℝ) - a s) * w₀) (hα : 0 < α) (hβ : 0 < β)
    (hw : α - β = w₀) :
    α * (∑ s, (a s : ℝ) * (((b s : ℝ) - a s) / (kin s + ((b s : ℝ) - a s) * w₀))) -
      β * (∑ s, (b s : ℝ) * (((b s : ℝ) - a s) / (kin s + ((b s : ℝ) - a s) * w₀))) < 1 := by
  classical
  set d : S → ℝ := fun s => (b s : ℝ) - a s with hd
  set q : S → ℝ := fun s => d s / (kin s + d s * w₀) with hq
  have hT : α * (∑ s, (a s : ℝ) * q s) - β * (∑ s, (b s : ℝ) * q s) =
      ∑ s, (α * a s - β * b s) * q s := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
  show α * (∑ s, (a s : ℝ) * q s) - β * (∑ s, (b s : ℝ) * q s) < 1
  rw [hT]
  have hqsign : ∀ s, (a s < b s → 0 < q s) ∧ (b s < a s → q s < 0) ∧
      (¬ a s < b s → ¬ b s < a s → q s = 0) := by
    intro s
    refine ⟨fun h => div_pos ?_ (hI s), fun h => div_neg_of_neg_of_pos ?_ (hI s), fun h1 h2 => ?_⟩
    · have : (a s : ℝ) < b s := by exact_mod_cast h
      simp only [hd]; linarith
    · have : (b s : ℝ) < a s := by exact_mod_cast h
      simp only [hd]; linarith
    · have : a s = b s := by omega
      simp [hq, hd, this]
  have hwq : ∀ s, w₀ * q s < 1 := by
    intro s
    rw [show w₀ * q s = (d s * w₀) / (kin s + d s * w₀) by simp only [hq]; ring,
      div_lt_one (hI s)]
    linarith [hkin s]
  have hab : ∀ s, ((a s : ℝ) ≤ b s ∨ (b s : ℝ) ≤ a s) := fun s => le_total _ _
  rcases le_or_gt 0 w₀ with hw0 | hw0
  · -- `α ≥ β`
    have hαβ : β ≤ α := by linarith
    have hU : ∀ s, (α * a s - β * b s) * q s ≤
        if a s < b s then (a s : ℝ) * (w₀ * q s) else 0 := by
      intro s
      obtain ⟨h1, h2, h3⟩ := hqsign s
      split_ifs with hlt
      · have hq0 := h1 hlt
        have : (a s : ℝ) ≤ b s := by exact_mod_cast hlt.le
        have : α * a s - β * b s ≤ (α - β) * a s := by nlinarith [(Nat.cast_nonneg (a s) : (0:ℝ) ≤ a s)]
        rw [← hw]; nlinarith
      · by_cases hgt : b s < a s
        · have hq0 := h2 hgt
          have : (b s : ℝ) ≤ a s := by exact_mod_cast hgt.le
          have : 0 ≤ α * a s - β * b s := by nlinarith [(Nat.cast_nonneg (b s) : (0:ℝ) ≤ b s)]
          nlinarith
        · rw [h3 hlt hgt, mul_zero]
    calc ∑ s, (α * a s - β * b s) * q s
        ≤ ∑ s, (if a s < b s then (a s : ℝ) * (w₀ * q s) else 0) := sum_le_sum fun s _ => hU s
      _ = ∑ s ∈ univ.filter (fun s => a s < b s), (a s : ℝ) * (w₀ * q s) := by rw [sum_filter]
      _ < 1 := weighted_sum_lt_one (fun s hs => mul_nonneg hw0 ((hqsign s).1 (mem_filter.mp hs).2).le)
          (fun s _ => hwq s) hP
  · -- `α < β`
    have hαβ : α < β := by linarith
    have hU : ∀ s, (α * a s - β * b s) * q s ≤
        if b s < a s then (b s : ℝ) * (w₀ * q s) else 0 := by
      intro s
      obtain ⟨h1, h2, h3⟩ := hqsign s
      split_ifs with hgt
      · have hq0 := h2 hgt
        have : (b s : ℝ) ≤ a s := by exact_mod_cast hgt.le
        have : β * b s - α * a s ≤ (β - α) * b s := by nlinarith [(Nat.cast_nonneg (b s) : (0:ℝ) ≤ b s)]
        have hbw : β - α = -w₀ := by linarith
        rw [hbw] at this
        nlinarith
      · by_cases hlt : a s < b s
        · have hq0 := h1 hlt
          have : (a s : ℝ) ≤ b s := by exact_mod_cast hlt.le
          have : α * a s - β * b s ≤ 0 := by nlinarith [(Nat.cast_nonneg (a s) : (0:ℝ) ≤ a s)]
          nlinarith
        · rw [h3 hlt hgt, mul_zero]
    calc ∑ s, (α * a s - β * b s) * q s
        ≤ ∑ s, (if b s < a s then (b s : ℝ) * (w₀ * q s) else 0) := sum_le_sum fun s _ => hU s
      _ = ∑ s ∈ univ.filter (fun s => b s < a s), (b s : ℝ) * (w₀ * q s) := by rw [sum_filter]
      _ < 1 := weighted_sum_lt_one
          (fun s hs => mul_nonneg_of_nonpos_of_nonpos hw0.le ((hqsign s).2.1 (mem_filter.mp hs).2).le)
          (fun s _ => hwq s) hN

/-- `exp (∑ c_s log x_s(w))`, equal to `∏ x_s(w)^{c_s}` where all `x_s(w) > 0`. -/
noncomputable def logMono (c : Complex S) (kin l d : S → ℝ) (w : ℝ) : ℝ :=
  Real.exp (∑ s, (c s : ℝ) * Real.log ((kin s + d s * w) / l s))

theorem logMono_eq (c : Complex S) {kin l d : S → ℝ} (hl : ∀ s, 0 < l s) {w : ℝ}
    (hw : ∀ s, 0 < kin s + d s * w) :
    logMono c kin l d w = c.massActionMonomial (fun s => (kin s + d s * w) / l s) := by
  unfold logMono Complex.massActionMonomial
  rw [Real.exp_sum]
  refine prod_congr rfl fun s _ => ?_
  rw [Real.exp_nat_mul, Real.exp_log (div_pos (hw s) (hl s))]

theorem logMono_hasDerivAt (c : Complex S) {kin l d : S → ℝ} (hl : ∀ s, 0 < l s) {w : ℝ}
    (hw : ∀ s, 0 < kin s + d s * w) :
    HasDerivAt (logMono c kin l d)
      (logMono c kin l d w * ∑ s, (c s : ℝ) * (d s / (kin s + d s * w))) w := by
  have hin : HasDerivAt (fun w => ∑ s, (c s : ℝ) * Real.log ((kin s + d s * w) / l s))
      (∑ s, (c s : ℝ) * (d s / (kin s + d s * w))) w := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun w => (kin s + d s * w) / l s) (d s / l s) w := by
      have := (((hasDerivAt_id w).const_mul (d s)).const_add (kin s)).div_const (l s)
      simpa using this
    have h2 := (h1.log (div_pos (hw s) (hl s)).ne').const_mul (c s : ℝ)
    convert h2 using 1
    have := (hl s).ne'; have := (hw s).ne'
    field_simp
  exact hin.exp

/-- **Joshi 2013, Theorem 4.1(2) ("only if").** -/
theorem revPair_unique_steadyState (a b : Complex S)
    (hP : ∑ s ∈ univ.filter (fun s => a s < b s), a s ≤ 1)
    (hN : ∑ s ∈ univ.filter (fun s => b s < a s), b s ≤ 1)
    (κ : (revPair a b).fullyOpen.RateConstants) {x z : Concentration S}
    (hx : x.Positive) (hz : z.Positive)
    (hxs : (revPair a b).fullyOpen.IsMassActionSteadyState κ x)
    (hzs : (revPair a b).fullyOpen.IsMassActionSteadyState κ z) : x = z := by
  classical
  set kf := κ.k (Sum.inl 0)
  set kr := κ.k (Sum.inl 1)
  set kin : S → ℝ := fun s => κ.k (Sum.inr (Sum.inl s)) with hkin
  set l : S → ℝ := fun s => κ.k (Sum.inr (Sum.inr s)) with hl
  set d : S → ℝ := fun s => (b s : ℝ) - a s with hd
  have hkinpos : ∀ s, 0 < kin s := fun s => κ.positive _
  have hlpos : ∀ s, 0 < l s := fun s => κ.positive _
  have hkf : 0 < kf := κ.positive _
  have hkr : 0 < kr := κ.positive _
  set W : Concentration S → ℝ := fun y => kf * a.massActionMonomial y - kr * b.massActionMonomial y
    with hW
  have hrel : ∀ y : Concentration S, (revPair a b).fullyOpen.IsMassActionSteadyState κ y →
      ∀ s, l s * y s = kin s + d s * W y := by
    intro y hy s
    have := hy s
    rw [revPair_fullyOpen_field] at this
    simp only [hl, hkin, hd, hW]
    linarith
  have hX : ∀ y : Concentration S, (revPair a b).fullyOpen.IsMassActionSteadyState κ y →
      (fun s => (kin s + d s * W y) / l s) = y := by
    intro y hy; funext s; rw [← hrel y hy s]; field_simp [(hlpos s).ne']
  set I : Set ℝ := {w | ∀ s, 0 < kin s + d s * w} with hIdef
  have hIoc : I.OrdConnected := by
    refine ⟨fun w₁ h₁ w₂ h₂ w hw s => ?_⟩
    rcases le_total 0 (d s) with hds | hds
    · have := h₁ s; nlinarith [hw.1]
    · have := h₂ s; nlinarith [hw.2]
  have hyI : ∀ y : Concentration S, y.Positive →
      (revPair a b).fullyOpen.IsMassActionSteadyState κ y → W y ∈ I := by
    intro y hyp hy s
    rw [← hrel y hy s]; exact mul_pos (hlpos s) (hyp s)
  set G : ℝ → ℝ := fun w => kf * logMono a kin l d w - kr * logMono b kin l d w - w with hG
  set G' : ℝ → ℝ := fun w => kf * logMono a kin l d w * (∑ s, (a s : ℝ) * (d s / (kin s + d s * w)))
    - kr * logMono b kin l d w * (∑ s, (b s : ℝ) * (d s / (kin s + d s * w))) - 1 with hG'
  have hderiv : ∀ w ∈ I, HasDerivAt G (G' w) w := by
    intro w hw
    have h := (((logMono_hasDerivAt a hlpos hw).const_mul kf).sub
      ((logMono_hasDerivAt b hlpos hw).const_mul kr)).sub (hasDerivAt_id w)
    convert h using 1
    · funext v; simp only [hG, Pi.sub_apply, id]
    · simp only [hG']; ring
  have hneg : ∀ w ∈ I, G w = 0 → G' w < 0 := by
    intro w hw hGw
    have hα : 0 < kf * logMono a kin l d w := mul_pos hkf (Real.exp_pos _)
    have hβ : 0 < kr * logMono b kin l d w := mul_pos hkr (Real.exp_pos _)
    have hαβ : kf * logMono a kin l d w - kr * logMono b kin l d w = w := by
      simp only [hG] at hGw; linarith
    have := revPair_slope_neg a b hP hN hkinpos hw hα hβ hαβ
    simp only [hG']
    have e : kf * logMono a kin l d w * (∑ s, (a s : ℝ) * (d s / (kin s + d s * w))) -
        kr * logMono b kin l d w * (∑ s, (b s : ℝ) * (d s / (kin s + d s * w))) =
        kf * logMono a kin l d w * (∑ s, (a s : ℝ) * (((b s : ℝ) - a s) /
          (kin s + ((b s : ℝ) - a s) * w))) -
        kr * logMono b kin l d w * (∑ s, (b s : ℝ) * (((b s : ℝ) - a s) /
          (kin s + ((b s : ℝ) - a s) * w))) := rfl
    linarith
  have hzero : ∀ y : Concentration S, y.Positive →
      (revPair a b).fullyOpen.IsMassActionSteadyState κ y → G (W y) = 0 := by
    intro y hyp hy
    have hIy := hyI y hyp hy
    simp only [hG]
    rw [logMono_eq a hlpos hIy, logMono_eq b hlpos hIy, hX y hy]
    simp only [hW]; ring
  by_cases heq : W x = W z
  · rw [← hX x hxs, ← hX z hzs, heq]
  · exfalso
    rcases lt_or_gt_of_ne heq with hlt | hlt
    · exact no_two_zeros_of_deriv_neg hIoc hderiv hneg (hyI x hx hxs) (hyI z hz hzs)
        (hzero x hx hxs) (hzero z hz hzs) hlt
    · exact no_two_zeros_of_deriv_neg hIoc hderiv hneg (hyI z hz hzs) (hyI x hx hxs)
        (hzero z hz hzs) (hzero x hx hxs) hlt

/-- **Joshi 2013, Theorem 4.1(2).** The fully open network with the reversible non-flow reaction
`a ⇌ b` admits two distinct positive steady states for some rates iff
`∑_{i : b_i > a_i} a_i > 1` or `∑_{i : a_i > b_i} b_i > 1`. -/
theorem revPair_multistationary_iff (a b : Complex S) :
    (∃ (κ : (revPair a b).fullyOpen.RateConstants) (x z : Concentration S),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ (revPair a b).fullyOpen.IsMassActionSteadyState κ x ∧
        (revPair a b).fullyOpen.IsMassActionSteadyState κ z) ↔
      (1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s ∨
        1 < ∑ s ∈ univ.filter (fun s => b s < a s), b s) := by
  constructor
  · rintro ⟨κ, x, z, hx, hz, hne, hxs, hzs⟩
    by_contra h; push Not at h
    exact hne (revPair_unique_steadyState a b h.1 h.2 κ hx hz hxs hzs)
  · exact revPair_exists_two_steadyStates a b

end Network
end CRNT
