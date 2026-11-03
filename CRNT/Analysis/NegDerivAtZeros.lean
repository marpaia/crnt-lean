import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# A function with negative derivative at each of its zeros has at most one zero

`no_two_zeros_of_deriv_neg`: let `G` be differentiable on an order-connected set `I ⊆ ℝ` with
`G' w < 0` at every zero `w ∈ I`.  Then `G` has at most one zero in `I`.

Proof: right of a zero `w₁`, `G < 0`; left of a later zero `w₂`, `G > 0`; the first zero `c` after
a negative point then has `G < 0` on its left, so the left slopes at `c` are positive and
`G' c ≥ 0`.

Nothing here is an axiom or a `sorry`.
-/

open Filter Topology Set

namespace CRNT

theorem no_two_zeros_of_deriv_neg {G G' : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hd : ∀ w ∈ I, HasDerivAt G (G' w) w) (hneg : ∀ w ∈ I, G w = 0 → G' w < 0)
    {w₁ w₂ : ℝ} (h₁ : w₁ ∈ I) (h₂ : w₂ ∈ I) (hz₁ : G w₁ = 0) (hz₂ : G w₂ = 0) (hlt : w₁ < w₂) :
    False := by
  have hsub : Icc w₁ w₂ ⊆ I := hI.out h₁ h₂
  have hcont : ContinuousOn G (Icc w₁ w₂) := fun w hw => (hd w (hsub hw)).continuousAt.continuousWithinAt
  -- slopes at a zero
  have hslope : ∀ c ∈ I, G c = 0 → ∀ᶠ w in 𝓝[≠] c, G w / (w - c) < 0 := by
    intro c hc hz
    have ht := (hasDerivAt_iff_tendsto_slope.mp (hd c hc))
    have := ht.eventually (gt_mem_nhds (hneg c hc hz))
    filter_upwards [this] with w hw
    simpa [slope_def_field, hz] using hw
  -- a negative point just right of `w₁`
  obtain ⟨a, ha1, ha2, hGa⟩ : ∃ a, w₁ < a ∧ a < w₂ ∧ G a < 0 := by
    have hev := (hslope w₁ h₁ hz₁).filter_mono (nhdsWithin_mono _ (fun w (hw : w ∈ Ioi w₁) =>
      (ne_of_gt hw : w ≠ w₁)))
    have hev2 : ∀ᶠ w in 𝓝[>] w₁, w < w₂ := Ioo_mem_nhdsGT hlt |> Filter.mem_of_superset <|
      fun w hw => hw.2
    obtain ⟨a, ⟨ha, hlt2⟩, hpos⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
    refine ⟨a, hpos, hlt2, ?_⟩
    have hden : 0 < a - w₁ := by linarith [show w₁ < a from hpos]
    have := ha
    exact (div_neg_iff.mp this).elim (fun h => absurd h.2 (not_lt.mpr hden.le)) (fun h => h.1)
  -- a positive point just left of `w₂`, right of `a`
  obtain ⟨b, hb1, hb2, hGb⟩ : ∃ b, a < b ∧ b < w₂ ∧ 0 < G b := by
    have hev := (hslope w₂ h₂ hz₂).filter_mono (nhdsWithin_mono _ (fun w (hw : w ∈ Iio w₂) =>
      (ne_of_lt hw : w ≠ w₂)))
    have hev2 : ∀ᶠ w in 𝓝[<] w₂, a < w := Ioo_mem_nhdsLT ha2 |> Filter.mem_of_superset <|
      fun w hw => hw.1
    obtain ⟨b, ⟨hb, hab⟩, hlt2⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
    refine ⟨b, hab, hlt2, ?_⟩
    have hden : b - w₂ < 0 := by linarith [show b < w₂ from hlt2]
    exact (div_neg_iff.mp hb).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.mpr hden.le))
  -- the first zero after `a`
  set Z := {w ∈ Icc a b | G w = 0} with hZ
  have hZne : Z.Nonempty := by
    have hab : Icc a b ⊆ Icc w₁ w₂ := Icc_subset_Icc ha1.le hb2.le
    obtain ⟨c, hc, hGc⟩ := intermediate_value_Icc hb1.le (hcont.mono hab) ⟨hGa.le, hGb.le⟩
    exact ⟨c, hc, hGc⟩
  have hZcl : IsClosed Z := by
    have hab : Icc a b ⊆ Icc w₁ w₂ := Icc_subset_Icc ha1.le hb2.le
    exact (hcont.mono hab).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZbdd : BddBelow Z := ⟨a, fun w hw => hw.1.1⟩
  set c := sInf Z with hc
  have hcZ : c ∈ Z := hZcl.csInf_mem hZne hZbdd
  have hca : a < c := lt_of_le_of_ne hcZ.1.1 (fun h => by rw [← h] at hcZ; linarith [hcZ.2])
  have hcI : c ∈ I := hsub ⟨ha1.le.trans hcZ.1.1, hcZ.1.2.trans hb2.le⟩
  -- `G < 0` on `[a, c)`
  have hneg_left : ∀ w ∈ Ico a c, G w < 0 := by
    intro w hw
    by_contra hge; push Not at hge
    have hsub' : Icc a w ⊆ Icc w₁ w₂ := Icc_subset_Icc ha1.le (hw.2.le.trans (hcZ.1.2.trans hb2.le))
    obtain ⟨e, he, hGe⟩ := intermediate_value_Icc hw.1 (hcont.mono hsub') ⟨hGa.le, hge⟩
    have heZ : e ∈ Z := ⟨⟨he.1, he.2.trans (hw.2.le.trans hcZ.1.2)⟩, hGe⟩
    have := csInf_le hZbdd heZ
    linarith [he.2, hw.2]
  -- left slopes at `c` are positive, contradicting `G' c < 0`
  have hev := (hslope c hcI hcZ.2).filter_mono (nhdsWithin_mono _ (fun w (hw : w ∈ Iio c) =>
    (ne_of_lt hw : w ≠ c)))
  have hev2 : ∀ᶠ w in 𝓝[<] c, a < w := Ioo_mem_nhdsLT hca |> Filter.mem_of_superset <|
    fun w hw => hw.1
  obtain ⟨w, ⟨hw, haw⟩, hwc⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
  have hGw := hneg_left w ⟨haw.le, hwc⟩
  have hden : w - c < 0 := by linarith [show w < c from hwc]
  have : 0 < G w / (w - c) := div_pos_of_neg_of_neg hGw hden
  linarith

end CRNT
