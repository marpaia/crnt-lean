import CRNT.Dynamics.TierLyapunov
import CRNT.Dynamics.TierStrictUpwardPartner
import CRNT.Dynamics.TierScaleExtractionLemma44

/-!
# Tier dissipation on a decomposed escaping sequence

For a tier-descending network, upward reactions are negligible at the top-source scale, while a
top-tier descending reaction contributes an unbounded negative logarithm. This file records the
finite-sum step of the tier Lyapunov argument for a sequence already equipped with its multiscale
decomposition.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

private noncomputable def normalizedTierReactionTerm (N : Network S)
    (κ : N.RateConstants) (xs : ℕ → Concentration S) (rtop r : N.R) (n : ℕ) : ℝ :=
  κ.k r *
    (tierMonomial (xs n) (N.reaction r).source /
      tierMonomial (xs n) (N.reaction rtop).source) *
    Real.log (tierMonomial (xs n) (N.reaction r).target /
      tierMonomial (xs n) (N.reaction r).source)

private theorem normalizedTierReactionTerm_eventually_bounded_above
    {N : Network S} (htd : N.TierDescending)
    {xs : ℕ → Concentration S} (htrans : N.IsTransversalTierSequence xs)
    (D : N.TierScaleDecomposition xs) (κ : N.RateConstants) (rtop r : N.R)
    (htop : N.IsTopSourceTier xs rtop) :
    r ≠ rtop → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, normalizedTierReactionTerm N κ xs rtop r n ≤ C := by
  intro hr
  classical
  let srcTop : ℕ → ℝ := fun n =>
    tierMonomial (xs n) (N.reaction rtop).source
  let src : ℕ → ℝ := fun n => tierMonomial (xs n) (N.reaction r).source
  let trg : ℕ → ℝ := fun n => tierMonomial (xs n) (N.reaction r).target
  let logRatio : ℕ → ℝ := fun n => Real.log (trg n / src n)
  have hpos := htrans.1.1
  have hsrcTopPos (n : ℕ) : 0 < srcTop n := by
    exact tierMonomial_pos_of_positiveSequence hpos n (N.reaction rtop).source
  have hsrcPos (n : ℕ) : 0 < src n := by
    exact tierMonomial_pos_of_positiveSequence hpos n (N.reaction r).source
  have htrgPos (n : ℕ) : 0 < trg n := by
    exact tierMonomial_pos_of_positiveSequence hpos n (N.reaction r).target
  have hsourceLe : TierLE xs (N.reaction r).source (N.reaction rtop).source := htop r
  obtain ⟨Csrc, hCsrc, hsrcBound⟩ :=
    TierLE.eventually_ratio_le_const hpos hsourceLe
  have hreactionOrder := htrans.1.2.2
    (N.reaction r).source (N.source_mem_complexes r)
    (N.reaction r).target (N.target_mem_complexes r)
  rcases hreactionOrder with hsourceTargetLe | htargetSource
  · rcases hsourceTargetLe with hup | hsame
    · have hsupp := htd.upwardContribution_suppressed_by_topSource
        htrans D r rtop hup htop
      have hsuppLt : ∀ᶠ n in atTop,
          (src n / srcTop n) * |logRatio n| < 1 := by
        have h := (tendsto_order.1 hsupp).2 1 zero_lt_one
        exact h
      refine ⟨κ.k r + 1, by linarith [κ.positive r], ?_⟩
      filter_upwards [hsuppLt] with n hn
      have hfactor : 0 ≤ κ.k r * (src n / srcTop n) :=
        mul_nonneg (κ.positive r).le (div_nonneg (hsrcPos n).le (hsrcTopPos n).le)
      have hlogle : logRatio n ≤ |logRatio n| := le_abs_self _
      change κ.k r * (src n / srcTop n) * logRatio n ≤ κ.k r + 1
      calc
        κ.k r * (src n / srcTop n) * logRatio n
            ≤ κ.k r * ((src n / srcTop n) * |logRatio n|) := by
              calc
                κ.k r * (src n / srcTop n) * logRatio n
                    = (κ.k r * (src n / srcTop n)) * logRatio n := rfl
                _ ≤ (κ.k r * (src n / srcTop n)) * |logRatio n| :=
                  mul_le_mul_of_nonneg_left hlogle hfactor
                _ = κ.k r * ((src n / srcTop n) * |logRatio n|) := by ring
        _ ≤ κ.k r * 1 := mul_le_mul_of_nonneg_left hn.le (κ.positive r).le
        _ ≤ κ.k r + 1 := by linarith
    · obtain ⟨Clog, hClog, hlogBound⟩ := (hsame.symm hpos).eventually_abs_log_le hpos
      refine ⟨κ.k r * Csrc * Clog,
        mul_nonneg (mul_nonneg (κ.positive r).le hCsrc.le) hClog, ?_⟩
      filter_upwards [hsrcBound, hlogBound] with n hsn hln
      have hratioNonneg : 0 ≤ src n / srcTop n :=
        div_nonneg (hsrcPos n).le (hsrcTopPos n).le
      have hkpos : 0 ≤ κ.k r := (κ.positive r).le
      have hpref : 0 ≤ κ.k r * (src n / srcTop n) :=
        mul_nonneg hkpos hratioNonneg
      have hprefBound : κ.k r * (src n / srcTop n) ≤ κ.k r * Csrc :=
        mul_le_mul_of_nonneg_left hsn hkpos
      change κ.k r * (src n / srcTop n) * logRatio n ≤ κ.k r * Csrc * Clog
      calc
        κ.k r * (src n / srcTop n) * logRatio n
            ≤ κ.k r * (src n / srcTop n) * |logRatio n| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hpref
        _ ≤ κ.k r * Csrc * |logRatio n| := by
              calc
                κ.k r * (src n / srcTop n) * |logRatio n|
                    ≤ (κ.k r * Csrc) * |logRatio n| :=
                      mul_le_mul_of_nonneg_right hprefBound (abs_nonneg _)
                _ = κ.k r * Csrc * |logRatio n| := rfl
        _ ≤ κ.k r * Csrc * Clog :=
              mul_le_mul_of_nonneg_left hln (mul_nonneg hkpos hCsrc.le)
  · have hlogAtBot : Tendsto logRatio atTop atBot := by
      simpa [logRatio, trg, src] using htargetSource.log_tendsto_atBot hpos
    have hratioLt : ∀ᶠ n in atTop, trg n / src n < 1 :=
      (tendsto_order.1 htargetSource).2 1 zero_lt_one
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards [hratioLt] with n hn
    have hlogNeg : logRatio n < 0 := by
      exact Real.log_neg (div_pos (htrgPos n) (hsrcPos n)) hn
    have hfactor : 0 ≤ κ.k r * (src n / srcTop n) :=
      mul_nonneg (κ.positive r).le (div_nonneg (hsrcPos n).le (hsrcTopPos n).le)
    change κ.k r * (src n / srcTop n) * logRatio n ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hfactor hlogNeg.le

/-- **Tier dissipation is eventually negative on a decomposed transversal tier sequence.** The
selected top-tier descending reaction contributes a term tending to `-∞` after normalization by
its source monomial. Every other downward reaction is eventually nonpositive; same-tier terms stay
bounded; and every upward term tends to zero by the partner estimate. -/
theorem TierDescending.tierDissipation_eventually_negative_of_scaleDecomposition
    {N : Network S} (htd : N.TierDescending)
    {xs : ℕ → Concentration S} (htrans : N.IsTransversalTierSequence xs)
    (D : N.TierScaleDecomposition xs) (κ : N.RateConstants) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → N.tierDissipation κ (xs n) < 0 := by
  classical
  obtain ⟨_, rtop, htop, htopDown⟩ := htd xs htrans
  let sourceTop : ℕ → ℝ := fun n =>
    tierMonomial (xs n) (N.reaction rtop).source
  have hsourceTopPos (n : ℕ) : 0 < sourceTop n :=
    tierMonomial_pos_of_positiveSequence htrans.1.1 n (N.reaction rtop).source
  have htopLogAtBot : Tendsto
      (fun n => Real.log (tierMonomial (xs n) (N.reaction rtop).target / sourceTop n))
      atTop atBot := by
    simpa [sourceTop] using htopDown.log_tendsto_atBot htrans.1.1
  have htopRatio : Tendsto (fun n => sourceTop n / sourceTop n) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    simp [ne_of_gt (hsourceTopPos n)]
  have hrate : Tendsto (fun _ : ℕ => κ.k rtop) atTop (𝓝 (κ.k rtop)) := tendsto_const_nhds
  have htopTermAtBot : Tendsto
      (fun n => normalizedTierReactionTerm N κ xs rtop rtop n) atTop atBot := by
    have hprod := htopRatio.pos_mul_atBot one_pos htopLogAtBot
    have hscaled := hrate.pos_mul_atBot (κ.positive rtop) hprod
    apply hscaled.congr'
    filter_upwards [] with n
    change κ.k rtop * ((sourceTop n / sourceTop n) *
      Real.log (tierMonomial (xs n) (N.reaction rtop).target / sourceTop n)) =
      κ.k rtop * (sourceTop n / sourceTop n) *
        Real.log (tierMonomial (xs n) (N.reaction rtop).target / sourceTop n)
    ring
  let hs : Finset N.R := Finset.univ.erase rtop
  have htermBound (r : N.R) (hr : r ∈ hs) :
      ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
        normalizedTierReactionTerm N κ xs rtop r n ≤ c := by
    have hrne : r ≠ rtop := (Finset.mem_erase.mp hr).1
    exact normalizedTierReactionTerm_eventually_bounded_above htd htrans D κ rtop r htop hrne
  let bound : N.R → ℝ := fun r =>
    if hr : r ∈ hs then Classical.choose (htermBound r hr) else 0
  have hbound (r : N.R) (hr : r ∈ hs) :
      0 ≤ bound r ∧ ∀ᶠ n in atTop,
        normalizedTierReactionTerm N κ xs rtop r n ≤ bound r := by
    dsimp [bound]
    rw [dif_pos hr]
    exact Classical.choose_spec (htermBound r hr)
  let C : ℝ := ∑ r ∈ hs, bound r
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun r hr => (hbound r hr).1
  have hCbound : ∀ᶠ n in atTop,
      ∑ r ∈ hs, normalizedTierReactionTerm N κ xs rtop r n ≤ C := by
    have hall : ∀ᶠ n in atTop, ∀ r ∈ hs,
        normalizedTierReactionTerm N κ xs rtop r n ≤ bound r :=
      (Filter.eventually_all_finset hs).2 fun r hr => (hbound r hr).2
    filter_upwards [hall] with n hn
    dsimp [C]
    exact Finset.sum_le_sum fun r hr => hn r hr
  have htopSmall : ∀ᶠ n in atTop,
      normalizedTierReactionTerm N κ xs rtop rtop n ≤ -(C + 1) := by
    have h := htopTermAtBot
    rw [tendsto_atBot] at h
    exact h (-(C + 1))
  have htotal : ∀ᶠ n in atTop,
      normalizedTierReactionTerm N κ xs rtop rtop n +
        ∑ r ∈ Finset.univ.erase rtop,
          normalizedTierReactionTerm N κ xs rtop r n < 0 := by
    filter_upwards [htopSmall, hCbound] with n hnTop hnRest
    have hle := add_le_add hnTop hnRest
    linarith
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 htotal
  refine ⟨n₀, ?_⟩
  intro n hn
  have hsplit : N.tierDissipation κ (xs n) / sourceTop n =
      normalizedTierReactionTerm N κ xs rtop rtop n +
        ∑ r ∈ Finset.univ.erase rtop,
          normalizedTierReactionTerm N κ xs rtop r n := by
    unfold tierDissipation
    rw [Finset.sum_div, ← Finset.add_sum_erase _ _ (Finset.mem_univ rtop)]
    congr 1
    · dsimp [normalizedTierReactionTerm, sourceTop]
      field_simp [ne_of_gt (hsourceTopPos n)]
      <;> ring
    · apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_erase] at hr
      simp [normalizedTierReactionTerm, sourceTop]
      field_simp [ne_of_gt (tierMonomial_pos_of_positiveSequence htrans.1.1 n
        (N.reaction rtop).source)]
      <;> ring
  have hnorm : N.tierDissipation κ (xs n) / sourceTop n < 0 := by
    rw [hsplit]
    exact hn₀ n hn
  have hlt := (div_lt_iff₀ (hsourceTopPos n)).mp hnorm
  simpa using hlt

private theorem IsTransversalTierSequence.comp_strictMono
    {N : Network S} {xs : ℕ → Concentration S}
    (htrans : N.IsTransversalTierSequence xs) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : N.IsTransversalTierSequence (xs ∘ φ) := by
  have hφtop := hφ.tendsto_atTop
  have hstrict {y y' : Complex S} (h : TierStrictBelow xs y y') :
      TierStrictBelow (xs ∘ φ) y y' := by
    change Tendsto (fun n => tierMonomial (xs (φ n)) y /
      tierMonomial (xs (φ n)) y') atTop (𝓝 0)
    exact h.comp hφtop
  have hLE {y y' : Complex S} (h : TierLE xs y y') :
      TierLE (xs ∘ φ) y y' := by
    rcases h with h | h
    · exact Or.inl (hstrict h)
    · obtain ⟨c, hc, hlim⟩ := h
      exact Or.inr ⟨c, hc, hlim.comp hφtop⟩
  have hcmp : N.TierComparable (xs ∘ φ) := by
    intro y hy y' hy'
    rcases htrans.1.2.2 y hy y' hy' with h | h
    · exact Or.inl (hLE h)
    · exact Or.inr (hstrict h)
  have hcross : ∃ r : N.R,
      TierStrictBelow (xs ∘ φ) (N.reaction r).source (N.reaction r).target ∨
      TierStrictBelow (xs ∘ φ) (N.reaction r).target (N.reaction r).source := by
    obtain ⟨r, hcross⟩ := htrans.2
    refine ⟨r, ?_⟩
    rcases hcross with h | h
    · exact Or.inl (hstrict h)
    · exact Or.inr (hstrict h)
  exact ⟨⟨htrans.1.1.comp φ,
    htrans.1.2.1.comp_strictMono hφ, hcmp⟩, hcross⟩

/-- **Tier dissipation is eventually negative on every transversal tier sequence.** Failure would
give a subsequence with nonnegative dissipation. Lemma 4.4 supplies a multiscale decomposition on a
further subsequence, where the top-source estimate above makes dissipation strictly negative. -/
theorem TierDescending.tierDissipationEventuallyNegative
    {N : Network S} (htd : N.TierDescending) : N.TierDissipationEventuallyNegative := by
  intro κ xs htrans
  by_contra hnot
  have hnotEventually :
      ¬∀ᶠ n in atTop, N.tierDissipation κ (xs n) < 0 := by
    intro hev
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
    exact hnot ⟨n₀, hn₀⟩
  have hfrequent : ∃ᶠ n in atTop, 0 ≤ N.tierDissipation κ (xs n) := by
    have hfrequent' : ∃ᶠ n in atTop, ¬ N.tierDissipation κ (xs n) < 0 :=
      (Filter.not_eventually).1 hnotEventually
    exact hfrequent'.mono fun n hn => le_of_not_gt hn
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_of_frequently_atTop hfrequent
  have htransφ : N.IsTransversalTierSequence (xs ∘ φ) := htrans.comp_strictMono hφ
  obtain ⟨ψ, hψ, hD⟩ :=
    N.everyTierSequenceHasScaleDecomposition (xs ∘ φ) htransφ.1
  obtain ⟨D⟩ := hD
  have htransψ : N.IsTransversalTierSequence ((xs ∘ φ) ∘ ψ) :=
    htransφ.comp_strictMono hψ
  obtain ⟨n₀, hneg⟩ :=
    htd.tierDissipation_eventually_negative_of_scaleDecomposition htransψ D κ
  have hnonneg : 0 ≤ N.tierDissipation κ (((xs ∘ φ) ∘ ψ) n₀) := by
    simpa [Function.comp_apply] using hbad (ψ n₀)
  exact (not_lt_of_ge hnonneg) (hneg n₀ le_rfl)

end Network
end CRNT
