import CRNT.Stochastic.MinimalSemigroupDynkin
import CRNT.Stochastic.NetworkForwardEquation

/-!
# Moments and global balance of invariant laws

* If `QV ≤ −f + K` with `V, f ≥ 0`, every invariant probability `π` of the minimal transition
  function has `∑_b π(b) f(b) ≤ K` (`sum_invariant_mul_le`, `tsum_invariant_mul_le`), without any
  a priori moment assumption on `π`: average the Dynkin bound over `[0, T]` from a finite part
  of `π` and let `T → ∞`.
* An invariant law with `∑ π q < ∞` satisfies global balance `∑_a π(a) Q(a, b) = 0`
  (`tsum_invariant_mul_Q`), by dominated convergence of the slopes at `t = 0⁺`; for networks this
  is stationarity for the chemical master equation (`isCMEStationary_of_invariant`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Moment bound for invariant laws.** -/
theorem sum_invariant_mul_le (V f : α → ℝ) (hV : ∀ a, 0 ≤ V a) (hf : ∀ a, 0 ≤ f a) {K : ℝ}
    (hK : 0 ≤ K) (hdrift : ∀ a, J.drift V a ≤ -f a + K) {π : α → ℝ} (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : HasSum π 1) (hinv : ∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b)
    (F : Finset α) : ∑ b ∈ F, π b * f b ≤ K := by
  classical
  set c₀ := ∑ b ∈ F, π b * f b with hc₀
  set C := ∑ b ∈ F, f b with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun b _ => hf b
  -- for every finite `G`, `c₀ ≤ K + (1 − π(G)) C`
  have hG : ∀ G : Finset α, c₀ ≤ K + (1 - ∑ a ∈ G, π a) * C := by
    intro G
    have hπG : ∑ a ∈ G, π a ≤ 1 := hπ1.summable.sum_le_tsum G (fun a _ => hπ0 a) |>.trans_eq hπ1.tsum_eq
    -- pointwise in `t`
    have hpt : ∀ t, 0 ≤ t → c₀ ≤ ∑ a ∈ G, π a * ∑ b ∈ F, J.Pmin t a b * f b +
        (1 - ∑ a ∈ G, π a) * C := by
      intro t ht
      have hb : ∀ b, π b ≤ ∑ a ∈ G, π a * J.Pmin t a b + (1 - ∑ a ∈ G, π a) := by
        intro b
        have hs : Summable fun a => π a * J.Pmin t a b :=
          Summable.of_nonneg_of_le (fun a => mul_nonneg (hπ0 a) (J.Pmin_nonneg t ht a b))
            (fun a => mul_le_of_le_one_right (hπ0 a) (J.Pmin_le_one t ht a b)) hπ1.summable
        have h1 := hs.sum_add_tsum_compl (s := G)
        have h2 := hπ1.summable.sum_add_tsum_compl (s := G)
        have h3 : ∑' a : ↑(↑G : Set α)ᶜ, π a * J.Pmin t a b ≤ ∑' a : ↑(↑G : Set α)ᶜ, π a :=
          (hs.subtype _).tsum_le_tsum (fun a => mul_le_of_le_one_right (hπ0 a)
            (J.Pmin_le_one t ht a b)) (hπ1.summable.subtype _)
        rw [← hinv t ht b, ← h1]
        rw [hπ1.tsum_eq] at h2
        linarith
      calc c₀ ≤ ∑ b ∈ F, (∑ a ∈ G, π a * J.Pmin t a b + (1 - ∑ a ∈ G, π a)) * f b :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hb b) (hf b)
        _ = ∑ a ∈ G, π a * ∑ b ∈ F, J.Pmin t a b * f b + (1 - ∑ a ∈ G, π a) * C := by
            simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, hC]
            congr 1
            · rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    -- average over `[0, T]`
    have hT : ∀ T, 0 < T → c₀ ≤ (∑ a ∈ G, π a * V a) / T + K + (1 - ∑ a ∈ G, π a) * C := by
      intro T hT
      have hcont : ContinuousOn (fun t => ∑ a ∈ G, π a * ∑ b ∈ F, J.Pmin t a b * f b)
          (Icc 0 T) := by
        refine continuousOn_finsetSum _ fun a _ => continuousOn_const.mul ?_
        refine continuousOn_finsetSum _ fun b _ => ?_
        exact ((J.continuousOn_Pmin a b).mono fun t ht => ht.1).mul continuousOn_const
      set r := (1 - ∑ a ∈ G, π a) * C with hr
      have hha : ∀ a ∈ G, IntervalIntegrable (fun t => π a * ∑ b ∈ F, J.Pmin t a b * f b)
          volume 0 T := fun a _ =>
        (continuousOn_const.mul (continuousOn_finsetSum _ fun b _ =>
          ((J.continuousOn_Pmin a b).mono fun t ht => ht.1).mul continuousOn_const)).intervalIntegrable_of_Icc
          hT.le
      have hgi : IntervalIntegrable (fun t => ∑ a ∈ G, π a * ∑ b ∈ F, J.Pmin t a b * f b)
          volume 0 T := hcont.intervalIntegrable_of_Icc hT.le
      have hri : IntervalIntegrable (fun _ : ℝ => r) volume 0 T := intervalIntegrable_const
      have hci : IntervalIntegrable (fun _ : ℝ => c₀) volume 0 T := intervalIntegrable_const
      have hint := intervalIntegral.integral_mono_on hT.le hci (hgi.add hri)
        fun t ht => hpt t ht.1
      have e1 : ∫ t in (0 : ℝ)..T, c₀ = T * c₀ := by simp
      have e2 : ∫ t in (0 : ℝ)..T, ((∑ a ∈ G, π a * ∑ b ∈ F, J.Pmin t a b * f b) + r) =
          (∑ a ∈ G, π a * ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * f b) + T * r := by
        rw [intervalIntegral.integral_add hgi hri, intervalIntegral.integral_finset_sum hha]
        simp [intervalIntegral.integral_const_mul]
      rw [e1, e2] at hint
      have hD : ∀ a ∈ G, π a * ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * f b ≤
          π a * (V a + K * T) := fun a _ =>
        mul_le_mul_of_nonneg_left (J.integral_sum_Pmin_mul_le V f hV hf hK hdrift hT.le a F)
          (hπ0 a)
      have hsum := Finset.sum_le_sum hD
      have hsplit : ∑ a ∈ G, π a * (V a + K * T) = ∑ a ∈ G, π a * V a + K * T * ∑ a ∈ G, π a := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hsplit] at hsum
      have hKT : K * T * ∑ a ∈ G, π a ≤ K * T :=
        mul_le_of_le_one_right (by positivity) hπG
      rw [div_add' _ _ _ hT.ne', div_add' _ _ _ hT.ne', le_div_iff₀ hT]
      nlinarith
    -- `T → ∞`
    have hlim : Tendsto (fun T : ℝ => (∑ a ∈ G, π a * V a) / T + K + (1 - ∑ a ∈ G, π a) * C)
        atTop (𝓝 (0 + K + (1 - ∑ a ∈ G, π a) * C)) :=
      ((tendsto_const_nhds.div_atTop tendsto_id).add_const _).add_const _
    rw [zero_add] at hlim
    exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun T hT' => hT T hT')
  -- `π(G) → 1`
  have hlimG : Tendsto (fun G : Finset α => K + (1 - ∑ a ∈ G, π a) * C) atTop
      (𝓝 (K + (1 - 1) * C)) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.sub hπ1).mul_const C)
  rw [sub_self, zero_mul, add_zero] at hlimG
  exact ge_of_tendsto hlimG (Eventually.of_forall hG)

theorem tsum_invariant_mul_le (V f : α → ℝ) (hV : ∀ a, 0 ≤ V a) (hf : ∀ a, 0 ≤ f a) {K : ℝ}
    (hK : 0 ≤ K) (hdrift : ∀ a, J.drift V a ≤ -f a + K) {π : α → ℝ} (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : HasSum π 1) (hinv : ∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b) :
    Summable (fun b => π b * f b) ∧ ∑' b, π b * f b ≤ K := by
  have h := J.sum_invariant_mul_le V f hV hf hK hdrift hπ0 hπ1 hinv
  have hs : Summable fun b => π b * f b :=
    summable_of_sum_le (fun b => mul_nonneg (hπ0 b) (hf b)) h
  exact ⟨hs, hs.tsum_le_of_sum_le h⟩

/-- **Global balance for invariant laws.** -/
theorem tsum_invariant_mul_Q {π : α → ℝ} (hπ0 : ∀ a, 0 ≤ π a) (hπs : Summable π)
    (hinv : ∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b)
    (hq : Summable fun a => π a * J.q a) (b : α) : ∑' a, π a * J.Q a b = 0 := by
  classical
  have hzero : ∀ h, 0 < h → ∑' a, π a * ((J.Pmin h a b - (if a = b then 1 else 0)) / h) = 0 := by
    intro h hh
    have hs1 : Summable fun a => π a * J.Pmin h a b :=
      Summable.of_nonneg_of_le (fun a => mul_nonneg (hπ0 a) (J.Pmin_nonneg h hh.le a b))
        (fun a => mul_le_of_le_one_right (hπ0 a) (J.Pmin_le_one h hh.le a b)) hπs
    have hs2 : Summable fun a => π a * (if a = b then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := {b}) fun a ha => by
        rw [Finset.mem_singleton] at ha; rw [if_neg ha, mul_zero]
    have e : (fun a => π a * ((J.Pmin h a b - (if a = b then 1 else 0)) / h)) =
        fun a => (π a * J.Pmin h a b - π a * (if a = b then 1 else 0)) / h :=
      funext fun a => by ring
    rw [e, tsum_div_const, hs1.tsum_sub hs2, hinv h hh.le b,
      tsum_eq_single b fun a ha => by rw [if_neg ha, mul_zero]]
    simp
  have hlim : Tendsto (fun h => ∑' a, π a * ((J.Pmin h a b - (if a = b then 1 else 0)) / h))
      (𝓝[>] 0) (𝓝 (∑' a, π a * J.Q a b)) := by
    refine tendsto_tsum_of_dominated_convergence hq (fun a =>
      (J.tendsto_slope_Pmin_zero a b).const_mul (π a)) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 a), abs_div, abs_of_pos (mem_Ioi.mp hh)]
    refine mul_le_mul_of_nonneg_left ?_ (hπ0 a)
    rw [div_le_iff₀ (mem_Ioi.mp hh)]
    exact J.abs_Pmin_sub_le a b (mem_Ioi.mp hh).le
  have hlim0 : Tendsto (fun h => ∑' a, π a * ((J.Pmin h a b - (if a = b then 1 else 0)) / h))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun h hh => (hzero h hh).symm)
  exact tendsto_nhds_unique hlim hlim0

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The right side of the master equation through the generator matrix. -/
theorem cmeRHS_eq_tsum_Q (N : Network S) (κ : RateConstants N) {P : (S → ℕ) → ℝ}
    (hP0 : ∀ c, 0 ≤ P c) (hsum : Summable fun c => P c * N.exitRate κ c) (m : S → ℕ) :
    N.cmeRHS κ P m = ∑' c, P c * (N.jumpSystem κ).Q c m := by
  classical
  have hQ : ∀ c, P c * (N.jumpSystem κ).Q c m = ∑ r, P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then 1 else 0) - P c * N.exitRate κ c * (if c = m then 1 else 0) := by
    intro c
    have hj := N.sum_rate_mul_jumpNextCount κ (fun l => if l = m then (1 : ℝ) else 0) c
    show P c * (∑ r : N.R, N.stochasticMassActionRate κ c r *
      (if N.jumpNextCount c r = m then 1 else 0) - N.exitRate κ c * (if c = m then 1 else 0)) = _
    rw [hj, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun r _ => by ring
    · ring
  have hfire : ∀ r, Summable fun c => P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then (1 : ℝ) else 0) := fun r =>
    Summable.of_nonneg_of_le (fun c => mul_nonneg (mul_nonneg (hP0 c)
      (N.stochasticMassActionRate_nonneg κ c r)) (by split_ifs <;> norm_num))
      (fun c => by
        have h1 : (if N.fireCount c r = m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        have h2 : N.stochasticMassActionRate κ c r ≤ N.exitRate κ c :=
          Finset.single_le_sum (f := fun r => N.stochasticMassActionRate κ c r)
            (fun r _ => N.stochasticMassActionRate_nonneg κ c r) (Finset.mem_univ r)
        have h3 := mul_nonneg (hP0 c) (N.stochasticMassActionRate_nonneg κ c r)
        calc P c * N.stochasticMassActionRate κ c r * (if N.fireCount c r = m then (1 : ℝ) else 0)
            ≤ P c * N.stochasticMassActionRate κ c r * 1 := mul_le_mul_of_nonneg_left h1 h3
          _ ≤ P c * N.exitRate κ c := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 (hP0 c)) hsum
  have hdiag : Summable fun c => P c * N.exitRate κ c * (if c = m then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {m}) fun c hc => by
      rw [Finset.mem_singleton] at hc; rw [if_neg hc, mul_zero]
  have hin : ∀ r, ∑' c, P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then (1 : ℝ) else 0) = N.cmeInflow κ P m r := by
    intro r
    rw [(N.tsum_mul_rate_fire_eq κ P (fun l => if l = m then (1 : ℝ) else 0) r (hfire r)).2]
    rw [tsum_eq_single m fun l hl => by rw [if_neg hl, zero_mul]]
    simp
  rw [tsum_congr hQ, (summable_sum fun r _ => hfire r).tsum_sub hdiag,
    Summable.tsum_finsetSum fun r _ => hfire r]
  rw [tsum_eq_single m fun c hc => by rw [if_neg hc, mul_zero]]
  simp only [hin, if_true, mul_one, cmeRHS]

/-- **Invariant laws are stationary for the master equation**, given a summable exit rate. -/
theorem isCMEStationary_of_invariant (N : Network S) (κ : RateConstants N)
    {π : (S → ℕ) → ℝ} (hπ0 : ∀ a, 0 ≤ π a) (hπs : Summable π)
    (hinv : ∀ s, 0 ≤ s → ∀ b, ∑' c, π c * N.transition κ s c b = π b)
    (hq : Summable fun a => π a * N.exitRate κ a) : N.IsCMEStationary κ π := by
  intro m
  have h := (N.jumpSystem κ).tsum_invariant_mul_Q hπ0 hπs hinv hq m
  rw [← cmeRHS_eq_tsum_Q N κ hπ0 hq m] at h
  unfold cmeRHS exitRate at h
  linarith

end Network
end CRNT
