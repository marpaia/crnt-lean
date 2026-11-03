import CRNT.Stochastic.NonExplosion
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic

/-!
# Almost-sure non-explosion of conservative stochastic reaction networks

The jump times of the continuous-time chain are `T_n = ∑_{k<n} E_k / λ(n_k)`, where `n_k` is the
embedded jump path and `E_k` are i.i.d. unit exponential variables. The chain is non-explosive
iff `T_n → ∞` almost surely. For a conservative network started at `n₀`, the exit rates along
every jump path from `n₀` are bounded by a constant `Λ`
(`CRNT.Network.exists_exitRate_bound_of_conservative`), so `T_n ≥ Λ⁻¹ ∑_{k<n} E_k`, and the
second Borel–Cantelli lemma gives `∑ E_k = ∞` almost surely for independent nonnegative
variables with `P(E_k ≥ 1)` bounded below — in particular for unit exponentials, where
`P(E_k ≥ 1) = e⁻¹`.

Main results:
* `CRNT.tendsto_partialSum_atTop_of_iIndepFun`.
* `CRNT.Network.ae_tendsto_jumpTimes_atTop_of_conservative`.

The statement holds simultaneously for every (possibly random) jump path from `n₀`, so no
independence between the holding times and the jump path is needed.
-/

namespace CRNT

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

/-- **Partial sums of independent nonnegative variables diverge** when `P(E_k ≥ 1)` is bounded
below. -/
theorem tendsto_partialSum_atTop_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (E : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (E k))
    (hind : iIndepFun E μ) (hnn : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ E k ω) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hprob : ∀ k, p ≤ μ {ω | 1 ≤ E k ω}) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n, E k ω) atTop atTop := by
  set s : ℕ → Set Ω := fun k => {ω | 1 ≤ E k ω}
  have hsm : ∀ k, MeasurableSet (s k) := fun k => measurableSet_le measurable_const (hmeas k)
  have hindS : iIndepSet s μ := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hind.meas_biInter fun i _ => ⟨Set.Ici 1, measurableSet_Ici, rfl⟩
  have hsum : (∑' n, μ (s n)) = ∞ := by
    refine top_unique ?_
    calc (∞ : ℝ≥0∞) = ∑' _n : ℕ, p := (ENNReal.tsum_const_eq_top_of_ne_zero hp).symm
      _ ≤ ∑' n, μ (s n) := ENNReal.tsum_le_tsum fun n => hprob n
  have hlim := measure_limsup_eq_one hsm hindS hsum
  have hae : ∀ᵐ ω ∂μ, ω ∈ limsup s atTop := by
    rw [ae_iff]
    have : μ (limsup s atTop)ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hsm)]; exact hlim
    simpa [Set.compl_def] using this
  filter_upwards [hae, ae_all_iff.mpr hnn] with ω hω hnnω
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  -- the partial sums are monotone and exceed every natural number
  have hmono : Monotone fun n => ∑ k ∈ Finset.range n, E k ω := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
      fun k _ _ => hnnω k
  have hgrow : ∀ M : ℕ, ∃ n, (M : ℝ) ≤ ∑ k ∈ Finset.range n, E k ω := by
    intro M
    induction M with
    | zero => exact ⟨0, by simp⟩
    | succ M ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hk, hEk⟩ := (frequently_atTop.mp hω) n
      refine ⟨k + 1, ?_⟩
      rw [Finset.sum_range_succ]
      have := hmono hk
      have hEk' : 1 ≤ E k ω := hEk
      push_cast
      linarith
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ := hgrow ⌈b⌉₊
  exact ⟨n, fun m hm => le_trans (Nat.le_ceil b) (hn.trans (hmono hm))⟩

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Uniform exit-rate bound along jump paths of a conservative network.** -/
theorem exists_exitRate_bound_of_conservative (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) (n₀ : S → ℕ) :
    ∃ Λ : ℝ, ∀ n : ℕ → (S → ℕ), N.IsJumpPath κ n → n 0 = n₀ → ∀ k,
      N.exitRate κ (n k) ≤ Λ := by
  classical
  obtain ⟨w, hwinv, hwpos⟩ := hcons
  by_cases hS : (Finset.univ : Finset S).Nonempty
  · obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ w hS
    have hwmin : 0 < w s₀ := hwpos s₀
    obtain ⟨B, hB⟩ := exists_nat_ge (weightedCount w n₀ / w s₀)
    refine ⟨∑ r, κ.k r * ∏ s, ((B : ℝ) ^ (N.reaction r).source s), fun n hpath h0 k => ?_⟩
    refine N.exitRate_le_of_le κ fun s => ?_
    have hW := N.weightedTotal_jumpPath κ hwinv hpath k
    rw [h0] at hW
    have hle : w s * (n k s : ℝ) ≤ weightedCount w (n k) :=
      Finset.single_le_sum (f := fun s => w s * (n k s : ℝ))
        (fun t _ => mul_nonneg (hwpos t).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h1 : w s₀ * (n k s : ℝ) ≤ w s * (n k s : ℝ) :=
      mul_le_mul_of_nonneg_right (hs₀ s (Finset.mem_univ s)) (Nat.cast_nonneg _)
    have h2 : (n k s : ℝ) ≤ weightedCount w n₀ / w s₀ := by
      rw [le_div_iff₀ hwmin]; rw [hW] at hle; linarith
    exact_mod_cast h2.trans hB
  · refine ⟨N.exitRate κ n₀, fun n _ h0 k => ?_⟩
    have : n k = n₀ := funext fun s => absurd ⟨s, Finset.mem_univ s⟩ hS
    rw [this]

/-- **Conservative networks are almost surely non-explosive.** Let `E_k` be independent
nonnegative holding-time variables with `P(E_k ≥ 1)` bounded below (e.g. i.i.d. unit
exponentials), and let `ω ↦ n_ω` be any random jump path from `n₀`. Then the jump times
`∑_{k<n} E_k / λ(n_ω k)` tend to infinity almost surely. -/
theorem ae_tendsto_jumpTimes_atTop_of_conservative (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) (n₀ : S → ℕ) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (E : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (E k))
    (hind : iIndepFun E μ) (hnn : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ E k ω) {p : ℝ≥0∞} (hp : p ≠ 0)
    (hprob : ∀ k, p ≤ μ {ω | 1 ≤ E k ω}) (path : Ω → ℕ → (S → ℕ))
    (hpath : ∀ ω, N.IsJumpPath κ (path ω)) (h0 : ∀ ω, path ω 0 = n₀) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n, E k ω / N.exitRate κ (path ω k))
      atTop atTop := by
  obtain ⟨Λ, hΛ⟩ := N.exists_exitRate_bound_of_conservative κ hcons n₀
  filter_upwards [tendsto_partialSum_atTop_of_iIndepFun E hmeas hind hnn hp hprob,
    ae_all_iff.mpr hnn] with ω hω hnnω
  have hpos : ∀ k, 0 < N.exitRate κ (path ω k) := fun k => by
    obtain ⟨r, hr, -⟩ := hpath ω k
    exact N.exitRate_pos_of_rate_pos κ hr
  have hΛpos : 0 < Λ := lt_of_lt_of_le (hpos 0) (hΛ (path ω) (hpath ω) (h0 ω) 0)
  have hlow : ∀ n, (∑ k ∈ Finset.range n, E k ω) / Λ ≤
      ∑ k ∈ Finset.range n, E k ω / N.exitRate κ (path ω k) := by
    intro n
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun k _ =>
      div_le_div_of_nonneg_left (hnnω k) (hpos k) (hΛ (path ω) (hpath ω) (h0 ω) k)
  exact tendsto_atTop_mono hlow (hω.atTop_div_const hΛpos)

end Network

end CRNT
