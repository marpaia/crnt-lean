import CRNT.Dynamics.TierScaleTruncation
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative asymptotics from a tier scale decomposition

The truncation argument selects the correct descending partner structurally. Lemma 4.5 also needs
one quantitative fact: if `i` is the first scale separating two complexes, their log-monomial ratio
is asymptotic to `mᵢ` times the first nonzero direction gap. Bounded residuals disappear after
division by `mᵢ`, as do all later scales.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Residual contribution to a complex log-ratio. -/
noncomputable def TierScaleDecomposition.residualGap
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (y y' : Complex S) (n : ℕ) : ℝ :=
  ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s)

/-- The bounded residual divided by any divergent scale tends to zero. -/
theorem TierScaleDecomposition.residualGap_div_scale_tendsto_zero
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (y y' : Complex S) (i : Fin D.levels) :
    Tendsto (fun n => D.residualGap y y' n / D.scale i n) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := D.residualGap_bounded y y'
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun n => D.residualGap y y' n) := by
    refine Filter.isBoundedUnder_of ⟨C, fun (n : ℕ) => ?_⟩
    simpa [Real.norm_eq_abs, Function.comp_apply, TierScaleDecomposition.residualGap]
      using hbound n
  have hinv : Tendsto (fun n => (D.scale i n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (D.scale_escape i)
  have hmul := Filter.isBoundedUnder_le_mul_tendsto_zero hbdd hinv
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun n => by simp [div_eq_mul_inv]

/-- After normalization by the first separating scale, all later scale contributions vanish. -/
theorem TierScaleDecomposition.laterGapSum_div_scale_tendsto_zero
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (i : Fin D.levels) (y y' : Complex S) :
    Tendsto
      (fun n =>
        (∑ j : Fin D.levels with i < j,
          D.scale j n * tierDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 0) := by
  classical
  let A : Finset (Fin D.levels) := Finset.univ.filter (fun j => i < j)
  have hsum : Tendsto
      (fun n => ∑ j ∈ A,
        (D.scale j n * tierDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 0) := by
    have hterms := tendsto_finset_sum A (fun j hj => by
      have hij : i < j := by simpa [A] using (Finset.mem_filter.mp hj).2
      exact D.later_mul_div_earlier_tendsto_zero hij
        (tierDirectionGap (D.direction j) y y'))
    rw [Finset.sum_const_zero] at hterms
    exact hterms
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [A]
    rw [Finset.sum_div]

/-- **First-scale asymptotic.** -/
theorem TierScaleDecomposition.logRatio_div_first_tendsto_gap
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0) :
    Tendsto
      (fun n =>
        Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n)
      atTop (𝓝 (tierDirectionGap (D.direction i) y y')) := by
  classical
  let g := tierDirectionGap (D.direction i) y y'
  have hlater := D.laterGapSum_div_scale_tendsto_zero i y y'
  have hres := D.residualGap_div_scale_tendsto_zero y y' i
  have hlead : Tendsto (fun n => (D.scale i n * g) / D.scale i n) atTop (𝓝 g) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [D.scale_pos i] with n hn
    simp [hn.ne']
  have hsum := (hlead.add hlater).add hres
  rw [add_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [D.scale_pos i] with n hsi
  rw [D.logRatio_eq_from_first hpos n y y' i hbefore]
  classical
  have hsplit :
      (∑ j : Fin D.levels with i ≤ j,
        D.scale j n * tierDirectionGap (D.direction j) y y') =
        D.scale i n * g +
          ∑ j : Fin D.levels with i < j,
            D.scale j n * tierDirectionGap (D.direction j) y y' := by
    have hset : (Finset.univ.filter (fun j : Fin D.levels => i ≤ j))
        = insert i (Finset.univ.filter (fun j : Fin D.levels => i < j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · intro h
        rcases h with h | h
        · exact h ▸ le_rfl
        · exact le_of_lt h
    rw [hset, Finset.sum_insert (by simp)]
  rw [hsplit]
  dsimp [TierScaleDecomposition.residualGap]
  field_simp [hsi.ne']

/-- A strict first gap gives an eventual negative linear bound. -/
theorem TierScaleDecomposition.eventually_logRatio_le_negative_scale
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0)
    (hgap : tierDirectionGap (D.direction i) y y' < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') ≤ -c * D.scale i n := by
  let g := tierDirectionGap (D.direction i) y y'
  let c : ℝ := -g / 2
  have hc : 0 < c := by dsimp [c, g]; linarith
  refine ⟨c, hc, ?_⟩
  have hnorm := D.logRatio_div_first_tendsto_gap hpos y y' i hbefore
  have hlt : ∀ᶠ n in atTop,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n < -c := by
    have : g < -c := by dsimp [c, g]; linarith
    exact (tendsto_order.1 hnorm).2 (-c) this
  filter_upwards [hlt, D.scale_pos i] with n hn hs
  have hmul := mul_le_mul_of_nonneg_left hn.le hs.le
  rw [mul_div_cancel₀ _ hs.ne'] at hmul
  simpa [mul_comm] using hmul

/-- A log-ratio whose first relevant scale is `i` grows at most linearly in that scale. -/
theorem TierScaleDecomposition.eventually_abs_logRatio_le_scale
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| ≤ C * D.scale i n := by
  let g := tierDirectionGap (D.direction i) y y'
  let C : ℝ := |g| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hnorm := D.logRatio_div_first_tendsto_gap hpos y y' i hbefore
  have hev : ∀ᶠ n in atTop,
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n| < C := by
    have hball := hnorm (Metric.ball_mem_nhds g zero_lt_one)
    filter_upwards [hball] with n hn
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hn
    calc
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n|
          ≤ |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') /
              D.scale i n - g| + |g| := by
            simpa [sub_add_cancel] using abs_add_le
              (Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') /
                D.scale i n - g) g
      _ < 1 + |g| := by linarith
      _ = C := by dsimp [C]; ring
  filter_upwards [hev, D.scale_pos i] with n hn hs
  have hmul := mul_le_mul_of_nonneg_right hn.le hs.le
  rw [abs_div, abs_of_pos hs, div_mul_cancel₀ _ hs.ne'] at hmul
  simpa [mul_comm] using hmul

/-- An exponentially suppressed source-tier ratio dominates the logarithmic growth of a
reaction whose first separating scale is no earlier than the source gap. This is the quantitative
estimate needed to control a tier-upward reaction against a strictly descending top-tier reaction. -/
theorem TierScaleDecomposition.scale_suppressed_log_ratio_tendsto_zero
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (hpos : PositiveSequence xs)
    (ysrc ydst ytop : Complex S) (isrc ibad : Fin D.levels)
    (hisrc : isrc ≤ ibad)
    (hsrcBefore : ∀ j : Fin D.levels, j < isrc →
      tierDirectionGap (D.direction j) ysrc ytop = 0)
    (hsrcGap : tierDirectionGap (D.direction isrc) ysrc ytop < 0)
    (hbadBefore : ∀ j : Fin D.levels, j < ibad →
      tierDirectionGap (D.direction j) ydst ysrc = 0) :
    Tendsto (fun n =>
      (tierMonomial (xs n) ysrc / tierMonomial (xs n) ytop) *
        |Real.log (tierMonomial (xs n) ydst / tierMonomial (xs n) ysrc)|)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hdecay⟩ :=
    D.eventually_logRatio_le_negative_scale hpos ysrc ytop isrc hsrcBefore hsrcGap
  obtain ⟨C, hC, hlog⟩ :=
    D.eventually_abs_logRatio_le_scale hpos ydst ysrc ibad hbadBefore
  have hscale : ∀ᶠ n in atTop, D.scale ibad n ≤ D.scale isrc n := by
    rcases hisrc.eq_or_lt with rfl | hlt
    · exact Filter.Eventually.of_forall fun _ => le_rfl
    · have hratio := D.scale_separated isrc ibad hlt
      have hle : ∀ᶠ n in atTop, D.scale ibad n / D.scale isrc n < 1 :=
        (tendsto_order.1 hratio).2 1 zero_lt_one
      filter_upwards [hle, D.scale_pos isrc] with n hn hpos
      exact (div_le_one hpos).mp hn.le
  have hbase : Tendsto (fun n => D.scale isrc n *
      Real.exp (-c * D.scale isrc n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
      (D.scale_escape isrc)
    have heq : (fun n => (D.scale isrc n) ^ (1 : ℝ) *
        Real.exp (-c * D.scale isrc n)) =
        (fun n => D.scale isrc n * Real.exp (-c * D.scale isrc n)) := by
      funext n
      simp
    rw [← heq]
    exact h
  have hupper : Tendsto (fun n => C *
      (D.scale isrc n * Real.exp (-c * D.scale isrc n))) atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
    (div_nonneg (le_of_lt (tierMonomial_pos_of_positiveSequence hpos n ysrc))
      (le_of_lt (tierMonomial_pos_of_positiveSequence hpos n ytop))) (abs_nonneg _))
    ?_ hupper
  filter_upwards [hdecay, hlog, hscale, D.scale_pos isrc] with n hdecayN hlogN hscaleN hposN
  have hratioPos : 0 < tierMonomial (xs n) ysrc / tierMonomial (xs n) ytop :=
    div_pos (tierMonomial_pos_of_positiveSequence hpos n ysrc)
      (tierMonomial_pos_of_positiveSequence hpos n ytop)
  have hratio : tierMonomial (xs n) ysrc / tierMonomial (xs n) ytop ≤
      Real.exp (-c * D.scale isrc n) := by
    have he := Real.exp_le_exp.mpr hdecayN
    rw [Real.exp_log hratioPos] at he
    exact he
  calc
    (tierMonomial (xs n) ysrc / tierMonomial (xs n) ytop) *
        |Real.log (tierMonomial (xs n) ydst / tierMonomial (xs n) ysrc)|
      ≤ Real.exp (-c * D.scale isrc n) * (C * D.scale ibad n) := by
        calc
          _ ≤ Real.exp (-c * D.scale isrc n) *
              |Real.log (tierMonomial (xs n) ydst / tierMonomial (xs n) ysrc)| :=
            mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
          _ ≤ Real.exp (-c * D.scale isrc n) * (C * D.scale ibad n) :=
            mul_le_mul_of_nonneg_left hlogN (Real.exp_pos _).le
    _ ≤ C * (D.scale isrc n * Real.exp (-c * D.scale isrc n)) := by
      have hscaleN' : D.scale ibad n ≤ D.scale isrc n := hscaleN
      have hexp : 0 ≤ Real.exp (-c * D.scale isrc n) := (Real.exp_pos _).le
      calc
        Real.exp (-c * D.scale isrc n) * (C * D.scale ibad n)
          ≤ Real.exp (-c * D.scale isrc n) * (C * D.scale isrc n) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscaleN' hC.le) hexp
        _ = C * (D.scale isrc n * Real.exp (-c * D.scale isrc n)) := by ring

/-- Later scales are eventually no larger than earlier scales. -/
theorem TierScaleDecomposition.eventually_scale_le_of_le
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) {j i : Fin D.levels} (hji : j ≤ i) :
    ∀ᶠ n in atTop, D.scale i n ≤ D.scale j n := by
  rcases hji.eq_or_lt with rfl | hlt
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · have hratio := D.scale_separated j i hlt
    have hle : ∀ᶠ n in atTop, D.scale i n / D.scale j n < 1 :=
      (tendsto_order.1 hratio).2 1 zero_lt_one
    filter_upwards [hle, D.scale_pos j] with n hn hjpos
    exact (div_le_one hjpos).mp hn.le

end Network
end CRNT
