import CRNT.Dynamics.TierScaleDecomposition
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Truncating a multiscale tier decomposition

This module formalizes the truncation used in the strict-upward case of Lemma 4.5.  Given a
multiscale decomposition of `log xₙ`, retain only the first `k+1` divergent scales and exponentiate.
The resulting positive sequence preserves every tier comparison whose first separating scale is at
most `k`.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable def TierScaleDecomposition.truncatedLog
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) (n : ℕ) (s : S) : ℝ :=
  ∑ j : Fin D.levels with j ≤ k, D.scale j n * D.direction j s

noncomputable def TierScaleDecomposition.truncatedSequence
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) : ℕ → Concentration S :=
  fun n s => Real.exp (D.truncatedLog k n s)

@[simp] theorem TierScaleDecomposition.truncatedSequence_pos
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) (n : ℕ) (s : S) :
    0 < D.truncatedSequence k n s := by
  simp [TierScaleDecomposition.truncatedSequence, Real.exp_pos]

theorem TierScaleDecomposition.truncatedSequence_positive
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) :
    PositiveSequence (D.truncatedSequence k) := by
  intro n s
  exact D.truncatedSequence_pos k n s

@[simp] theorem TierScaleDecomposition.log_truncatedSequence
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) (n : ℕ) (s : S) :
    Real.log (D.truncatedSequence k n s) = D.truncatedLog k n s := by
  simp [TierScaleDecomposition.truncatedSequence]

theorem TierScaleDecomposition.logRatio_truncated_eq
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels)
    (n : ℕ) (y y' : Complex S) :
    Real.log (tierMonomial (D.truncatedSequence k n) y /
      tierMonomial (D.truncatedSequence k n) y') =
      ∑ j : Fin D.levels with j ≤ k,
        D.scale j n * tierDirectionGap (D.direction j) y y' := by
  have hpos := D.truncatedSequence_positive k n
  rw [Real.log_div]
  · rw [log_tierMonomial hpos y, log_tierMonomial hpos y', ← Finset.sum_sub_distrib]
    simp only [D.log_truncatedSequence]
    calc
      (∑ s : S, ((y s : ℝ) * D.truncatedLog k n s -
          (y' s : ℝ) * D.truncatedLog k n s))
          = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.truncatedLog k n s) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) *
          (∑ j : Fin D.levels with j ≤ k, D.scale j n * D.direction j s)) := by
              rfl
      _ = ∑ j : Fin D.levels with j ≤ k,
          D.scale j n * tierDirectionGap (D.direction j) y y' := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j hj
              simp only [tierDirectionGap, complexWValue, dotProduct, exponentVector]
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
  · exact (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y).ne'
  · exact (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y').ne'

theorem TierScaleDecomposition.later_mul_div_earlier_tendsto_zero
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) {i j : Fin D.levels} (hij : i < j) (a : ℝ) :
    Tendsto (fun n => (D.scale j n * a) / D.scale i n) atTop (𝓝 0) := by
  have h := (D.scale_separated i j hij).mul_const a
  rw [zero_mul] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by ring

theorem TierScaleDecomposition.normalized_truncatedLogRatio_tendsto_firstGap
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k i : Fin D.levels) (hik : i ≤ k)
    (y y' : Complex S)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0) :
    Tendsto
      (fun n =>
        (∑ j : Fin D.levels with j ≤ k,
          D.scale j n * tierDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 (tierDirectionGap (D.direction i) y y')) := by
  classical
  let A : Finset (Fin D.levels) := Finset.univ.filter (fun j => j ≤ k)
  have hsum : Tendsto
      (fun n => ∑ j ∈ A,
        (D.scale j n * tierDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 (tierDirectionGap (D.direction i) y y')) := by
    have hiA : i ∈ A := by simp [A, hik]
    have hterms : ∀ j ∈ A,
        Tendsto (fun n => (D.scale j n * tierDirectionGap (D.direction j) y y') /
          D.scale i n) atTop
          (𝓝 (if j = i then tierDirectionGap (D.direction i) y y' else 0)) := by
      intro j hj
      by_cases hji : j = i
      · subst j
        have hpos := D.scale_pos i
        apply tendsto_const_nhds.congr'
        filter_upwards [hpos] with n hn
        simp [hn.ne']
      · have hle : j ≤ k := by simpa [A] using hj
        rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
        · have hzero := hbefore j hji_lt
          simp [hzero, hji]
        · simpa [hji] using D.later_mul_div_earlier_tendsto_zero hij_lt
            (tierDirectionGap (D.direction j) y y')
    have hall := tendsto_finset_sum A (fun j hj => hterms j hj)
    have hval : (∑ c ∈ A, if c = i then tierDirectionGap (D.direction i) y y' else 0)
        = tierDirectionGap (D.direction i) y y' := by
      rw [Finset.sum_ite_eq' A i (fun _ => tierDirectionGap (D.direction i) y y')]
      simp [hiA]
    rw [← hval]
    exact hall
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [A]
    rw [Finset.sum_div]

theorem TierScaleDecomposition.truncatedLogRatio_tendsto_atBot_of_firstGap
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k i : Fin D.levels) (hik : i ≤ k)
    (y y' : Complex S)
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0)
    (hgap : tierDirectionGap (D.direction i) y y' < 0) :
    Tendsto
      (fun n => ∑ j : Fin D.levels with j ≤ k,
        D.scale j n * tierDirectionGap (D.direction j) y y')
      atTop atBot := by
  let g := tierDirectionGap (D.direction i) y y'
  let c : ℝ := -g / 2
  have hc : 0 < c := by dsimp [c, g]; linarith
  have hnorm := D.normalized_truncatedLogRatio_tendsto_firstGap k i hik y y' hbefore
  have hq : ∀ᶠ n in atTop,
      (∑ j : Fin D.levels with j ≤ k,
        D.scale j n * tierDirectionGap (D.direction j) y y') / D.scale i n < -c := by
    have hlim : g < -c := by dsimp [c, g]; linarith
    exact (tendsto_order.1 hnorm).2 (-c) hlim
  rw [tendsto_atBot]
  intro B
  have hscale : ∀ᶠ n in atTop, (-B / c) + 1 < D.scale i n :=
    (tendsto_atTop.1 (D.scale_escape i) ((-B / c) + 2)).mono fun _ h => by linarith
  have hpos := D.scale_pos i
  filter_upwards [hq, hscale, hpos] with n hqn hsn hpin
  let L := ∑ j : Fin D.levels with j ≤ k,
    D.scale j n * tierDirectionGap (D.direction j) y y'
  have hmul : L < (-c) * D.scale i n := by
    have hmul0 := mul_lt_mul_of_pos_right hqn hpin
    rw [div_mul_cancel₀ _ hpin.ne'] at hmul0
    simpa [L, mul_comm] using hmul0
  have hbound : (-c) * D.scale i n < B := by
    have hcne : c ≠ 0 := hc.ne'
    have hsmall : -B / c < D.scale i n := by linarith
    have hmul0 := mul_lt_mul_of_neg_left hsmall (neg_neg_of_pos hc)
    field_simp [hcne] at hmul0 ⊢
    linarith
  exact (hmul.trans hbound).le

theorem TierScaleDecomposition.strictBelow_truncated_of_first
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k i : Fin D.levels) (hik : i ≤ k)
    {y y' : Complex S}
    (hbefore : ∀ j : Fin D.levels, j < i →
      tierDirectionGap (D.direction j) y y' = 0)
    (hgap : tierDirectionGap (D.direction i) y y' < 0) :
    TierStrictBelow (D.truncatedSequence k) y y' := by
  have hlogsum := D.truncatedLogRatio_tendsto_atBot_of_firstGap k i hik y y' hbefore hgap
  have hlog : Tendsto
      (fun n => Real.log (tierMonomial (D.truncatedSequence k n) y /
        tierMonomial (D.truncatedSequence k n) y')) atTop atBot := by
    apply hlogsum.congr'
    exact Filter.Eventually.of_forall fun n => (D.logRatio_truncated_eq k n y y').symm
  have hexp := Real.tendsto_exp_atBot.comp hlog
  apply hexp.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hratio : 0 < tierMonomial (D.truncatedSequence k n) y /
        tierMonomial (D.truncatedSequence k n) y' :=
      div_pos (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y)
        (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y')
    dsimp only [Function.comp_apply]
    exact Real.exp_log hratio

theorem TierScaleDecomposition.same_truncated_of_gaps_zero
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels) {y y' : Complex S}
    (hzero : ∀ j : Fin D.levels, j ≤ k → tierDirectionGap (D.direction j) y y' = 0) :
    TierSame (D.truncatedSequence k) y y' := by
  refine ⟨1, zero_lt_one, ?_⟩
  apply tendsto_const_nhds.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hlog := D.logRatio_truncated_eq k n y y'
    have hsum : (∑ j : Fin D.levels with j ≤ k,
        D.scale j n * tierDirectionGap (D.direction j) y y') = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hzero j (by simpa using (Finset.mem_filter.mp hj).2)]
    rw [hsum] at hlog
    have hratio : 0 < tierMonomial (D.truncatedSequence k n) y /
        tierMonomial (D.truncatedSequence k n) y' :=
      div_pos (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y)
        (tierMonomial_pos_of_positiveSequence (D.truncatedSequence_positive k) n y')
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_log hratio, Real.exp_zero] at hexp
    exact hexp.symm

theorem TierScaleDecomposition.strictBelow_truncated
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (k : Fin D.levels)
    {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (h : TierStrictBelow xs y y')
    (hfirst_le : (Classical.choose (D.strict_first hy hy' h)) ≤ k) :
    TierStrictBelow (D.truncatedSequence k) y y' := by
  let i : Fin D.levels := Classical.choose (D.strict_first hy hy' h)
  have hi := Classical.choose_spec (D.strict_first hy hy' h)
  exact D.strictBelow_truncated_of_first k i hfirst_le hi.1 hi.2

/-- Any positive sequence carrying one strict tier comparison escapes in logarithmic coordinates. -/
theorem logEscapes_of_strictTierComparison
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y y' : Complex S} (hstrict : TierStrictBelow xs y y') : LogEscapes xs := by
  let C : ℝ := ∑ s : S, |(y s : ℝ) - (y' s : ℝ)|
  have hlog := hstrict.log_tendsto_atBot hpos
  intro R
  let A : ℝ := (C + 1) * (|R| + 1)
  have hlarge : ∀ᶠ n in atTop,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') < -A :=
    (tendsto_atBot.1 hlog (-A - 1)).mono fun _ h => by linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hlarge
  refine ⟨N0, ?_⟩
  intro n hn
  have hln := hN0 n hn
  have habslog : A < |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| := by
    have hneg : Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') < 0 := by
      exact hln.trans_le (neg_nonpos.mpr (mul_nonneg (by dsimp [C]; positivity) (by positivity)))
    rw [abs_of_neg hneg]
    linarith
  have hratioLog :
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
        ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * Real.log (xs n s)) := by
    have hy := tierMonomial_pos_of_positiveSequence hpos n y
    have hy' := tierMonomial_pos_of_positiveSequence hpos n y'
    rw [Real.log_div hy.ne' hy'.ne', log_tierMonomial (hpos n), log_tierMonomial (hpos n),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hupper :
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| ≤
        C * (∑ s : S, |Real.log (xs n s)|) := by
    rw [hratioLog]
    calc
      |∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * Real.log (xs n s))|
          ≤ ∑ s : S, |((y s : ℝ) - (y' s : ℝ)) * Real.log (xs n s)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| * |Real.log (xs n s)| := by
            apply Finset.sum_congr rfl
            intro s _
            rw [abs_mul]
      _ ≤ ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| *
          (∑ t : S, |Real.log (xs n t)|) := by
            apply Finset.sum_le_sum
            intro s _
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (f := fun t : S => |Real.log (xs n t)|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ s)) (abs_nonneg _)
      _ = C * (∑ s : S, |Real.log (xs n s)|) := by simp [C, Finset.sum_mul]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum_nonneg : 0 ≤ ∑ s : S, |Real.log (xs n s)| := by positivity
  have hbig : (|R| + 1) < ∑ s : S, |Real.log (xs n s)| := by
    have hC1 : 0 < C + 1 := by linarith
    have hA_le : A < (C + 1) * (∑ s : S, |Real.log (xs n s)|) := by
      calc
        A < |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| := habslog
        _ ≤ C * (∑ s : S, |Real.log (xs n s)|) := hupper
        _ ≤ (C + 1) * (∑ s : S, |Real.log (xs n s)|) := by
              gcongr
              linarith
    dsimp [A] at hA_le
    exact lt_of_mul_lt_mul_left hA_le hC1.le
  exact (le_abs_self R).trans (by linarith)

/-- Tier order survives truncation: a strict comparison is preserved if its first separating scale
is retained, and otherwise collapses to a same-tier comparison. -/
theorem TierScaleDecomposition.tierLE_truncated
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (htier : N.IsTierSequence xs)
    (k : Fin D.levels) {y y' : Complex S} (hy : y ∈ N.complexes) (hy' : y' ∈ N.complexes)
    (hle : TierLE xs y y') : TierLE (D.truncatedSequence k) y y' := by
  rcases hle with hstrict | hsame
  · obtain ⟨i, hbefore, hgap⟩ := D.strict_first hy hy' hstrict
    by_cases hik : i ≤ k
    · exact Or.inl (D.strictBelow_truncated_of_first k i hik hbefore hgap)
    · apply Or.inr
      apply D.same_truncated_of_gaps_zero k
      intro j hjk
      exact hbefore j (lt_of_le_of_lt hjk (lt_of_not_ge hik))
  · apply Or.inr
    apply D.same_truncated_of_gaps_zero k
    intro j _
    exact D.same_gap_zero hy hy' hsame j

/-- Truncating at the first separating scale of one strict reaction gives a transversal tier
sequence. -/
theorem TierScaleDecomposition.truncated_isTransversalTierSequence_at_reaction
    {N : Network S} {xs : ℕ → Concentration S}
    (D : N.TierScaleDecomposition xs) (htier : N.IsTierSequence xs)
    (r : N.R)
    (hup : TierStrictBelow xs (N.reaction r).source (N.reaction r).target) :
    let i : Fin D.levels := Classical.choose
      (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
    N.IsTransversalTierSequence (D.truncatedSequence i) := by
  classical
  let i : Fin D.levels := Classical.choose
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have hi := Classical.choose_spec
    (D.strict_first (N.source_mem_complexes r) (N.target_mem_complexes r) hup)
  have hstrictTr : TierStrictBelow (D.truncatedSequence i)
      (N.reaction r).source (N.reaction r).target :=
    D.strictBelow_truncated_of_first i i le_rfl hi.1 hi.2
  have hpos := D.truncatedSequence_positive i
  have hcomp : N.TierComparable (D.truncatedSequence i) := by
    intro y hy y' hy'
    have horig := htier.2.2 y hy y' hy'
    rcases horig with hle | hrev
    · exact Or.inl (D.tierLE_truncated htier i hy hy' hle)
    · have hrevle : TierLE xs y' y := Or.inl hrev
      have htr := D.tierLE_truncated htier i hy' hy hrevle
      rcases htr with htrstrict | htrsame
      · exact Or.inr htrstrict
      · exact Or.inl (Or.inr (htrsame.symm hpos))
  have hesc : LogEscapes (D.truncatedSequence i) :=
    logEscapes_of_strictTierComparison hpos hstrictTr
  exact ⟨⟨hpos, hesc, hcomp⟩, ⟨r, Or.inl hstrictTr⟩⟩

end Network
end CRNT
