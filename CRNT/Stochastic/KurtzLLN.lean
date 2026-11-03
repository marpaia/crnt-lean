import CRNT.Stochastic.OpenLLN

/-!
# Kurtz's law of large numbers in probability, for every network (fixed times)

For an arbitrary mass-action network and a solution `x` of the mass-action equation on `[0, T]`
with values in `[0, R_x]^S`, the volume-scaled chain satisfies

`E_n min(|X^V(t)/V − x(t)|², 1) ≤ C₀ · gronwallBound(|n/V − x(0)|², C₁, C₂/V, t)`

(`kurtz_lln`), so `X^V(t)/V → x(t)` in probability whenever `n_V/V → x(0)`
(`kurtz_lln_tendsto`, `kurtz_lln_prob`).  No conservation law, weight or non-explosion hypothesis
is needed: the expectation is taken under the minimal (possibly sub-stochastic) transition
function.

Proof: freeze the chain outside `{∑ c ≤ R V}` with `R = |S| R_x + |S| + 1`.  On a frozen state
the distance `|c/V − x|²` is at least `1` (Cauchy–Schwarz), so the frozen mass is at most the
mean squared distance `D'` of the frozen chain, and the frozen-state term in the derivative of
`D'` is absorbed into `D'` itself: `D'` satisfies a closed Grönwall inequality with source
`O(1/V)`.  The original chain agrees with the frozen one up to the frozen mass inside the level
set, and the bounded observable `min(·, 1)` costs at most the frozen mass outside it.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Far from `[0, R_x]^S` the squared distance is at least one. -/
theorem one_le_dist_sq_of_sum_gt {Rx V : ℝ} (hV : 0 < V) {c : S → ℕ} {z : Concentration S}
    (hz : ∀ s, z s ≤ Rx)
    (hc : ((Fintype.card S : ℝ) * Rx + Fintype.card S + 1) * V < ∑ s, (c s : ℝ)) :
    1 ≤ ∑ s, ((c s : ℝ) / V - z s) ^ 2 := by
  set d := (Fintype.card S : ℝ) with hd
  have hsum : d + 1 < ∑ s, ((c s : ℝ) / V - z s) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    have h1 : d * Rx + d + 1 < (∑ s, (c s : ℝ)) / V := by rw [lt_div_iff₀ hV]; linarith
    have h2 : ∑ s, z s ≤ d * Rx := by
      calc ∑ s, z s ≤ ∑ _s : S, Rx := Finset.sum_le_sum fun s _ => hz s
        _ = d * Rx := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset S))
    (f := fun s => (c s : ℝ) / V - z s)
  rw [Finset.card_univ] at hCS
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hpos : 0 < d + 1 := by linarith
  have hsq : (d + 1) ^ 2 ≤ (∑ s, ((c s : ℝ) / V - z s)) ^ 2 :=
    pow_le_pow_left₀ hpos.le hsum.le 2
  have hdpos : 0 < d := by
    by_contra h
    have hd' : d = 0 := le_antisymm (not_lt.mp h) hd0
    have : Fintype.card S = 0 := by rw [hd] at hd'; exact_mod_cast hd'
    have hS : IsEmpty S := Fintype.card_eq_zero_iff.mp this
    have : ∑ s, ((c s : ℝ) / V - z s) = 0 := Finset.sum_of_isEmpty _
    linarith
  by_contra hlt
  push Not at hlt
  have : d * ∑ s, ((c s : ℝ) / V - z s) ^ 2 < d := by nlinarith
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Kurtz's law of large numbers in probability, fixed times, any network.** -/
theorem kurtz_lln (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₀ C₁ C₂ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      ∀ t ∈ Icc 0 T,
        ∑' m, N.transition (N.volumeScale κ V (by linarith)) t n m *
            min (∑ s, ((m s : ℝ) / V - x t s) ^ 2) 1 ≤
          C₀ * gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := by
  classical
  set w : S → ℝ := fun _ => 1 with hwdef
  have hw : ∀ s, 0 < w s := fun _ => one_pos
  have hwt : ∀ c : S → ℕ, wt w c = ∑ s, (c s : ℝ) := fun c => by simp [wt, hwdef]
  set d := (Fintype.card S : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set R := d * Rx + d + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set R₁ := ∑ s, R / w s with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun s _ => div_nonneg hR0 (hw s).le
  set Rb := max R₁ Rx with hRb
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn
    (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  obtain ⟨F2, hF2⟩ := (isCompact_Icc (a := (0 : Concentration S)) (b := fun _ => Rb)).exists_bound_of_continuousOn
    (f := fun z => ∑ s, N.massActionVectorField κ z s ^ 2)
    (continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp (N.contDiff_massActionVectorField κ).continuous).pow 2).continuousOn
  have hF2' : ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ∑ s, N.massActionVectorField κ z s ^ 2 ≤ max F2 0 := fun z hz =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hF2 z hz).trans (le_max_left _ _))
  set C₁ := 1 + 2 * d * L + max F2 0 with hC₁
  set C₂ := d * N.rateErr κ R₁ ^ 2 + N.noiseConst κ R₁ with hC₂
  set G₀ := d * (R₁ + Rx) ^ 2 with hG₀
  have hC₁1 : 1 + max F2 0 ≤ C₁ := by
    have : (0 : ℝ) ≤ 2 * d * L := by positivity
    linarith
  have hC₁0 : 0 ≤ C₁ := by have := le_max_right F2 0; linarith
  have hC₂0 : 0 ≤ C₂ := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg
      (mul_nonneg (κ.positive r).le (by positivity)) (Finset.sum_nonneg fun s _ => sq_nonneg _))
  have hG₀0 : 0 ≤ G₀ := by positivity
  refine ⟨G₀ + 2, C₁, C₂, by positivity, hC₁0, hC₂0, fun V hV n t ht => ?_⟩
  have hV0 : 0 < V := by linarith
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
  have hg0 : ∀ τ b, 0 ≤ g τ b := fun τ b => Finset.sum_nonneg fun s _ => sq_nonneg _
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  have hP0 : ∀ b, 0 ≤ J.Pmin t n b := fun b => J.Pmin_nonneg t ht.1 n b
  have hPs : Summable fun b => J.Pmin t n b :=
    summable_of_sum_le hP0 fun F => J.sum_Pmin_le_one t ht.1 n F
  have hP1 : ∑' b, J.Pmin t n b ≤ 1 := hPs.tsum_le_of_sum_le fun F => J.sum_Pmin_le_one t ht.1 n F
  have hC₁ne : C₁ ≠ 0 := by have := le_max_right F2 0; linarith
  have hgron0 : g 0 n ≤ gronwallBound (g 0 n) C₁ (C₂ / V) t := by
    rw [gronwallBound_of_K_ne_0 hC₁ne]
    have h1 : 1 ≤ Real.exp (C₁ * t) := Real.one_le_exp (mul_nonneg hC₁0 ht.1)
    have h2 : 0 ≤ C₂ / V / C₁ := div_nonneg (div_nonneg hC₂0 hV0.le) hC₁0
    nlinarith [hg0 0 n]
  have hmin : ∀ b, J.Pmin t n b * min (g t b) 1 ≤ J.Pmin t n b := fun b =>
    mul_le_of_le_one_right (hP0 b) (min_le_right _ _)
  have hfs : Summable fun b => J.Pmin t n b * min (g t b) 1 :=
    Summable.of_nonneg_of_le (fun b => mul_nonneg (hP0 b) (le_min (hg0 t b) zero_le_one)) hmin hPs
  have hC0 : 0 ≤ gronwallBound (g 0 n) C₁ (C₂ / V) t := le_trans (hg0 0 n) hgron0
  -- the case `|n/V − x(0)|² ≥ 1` is trivial
  by_cases hn1 : 1 ≤ g 0 n
  · calc ∑' m, J.Pmin t n m * min (g t m) 1 ≤ ∑' m, J.Pmin t n m :=
          hfs.tsum_le_tsum hmin hPs
      _ ≤ 1 := hP1
      _ ≤ g 0 n := hn1
      _ ≤ gronwallBound (g 0 n) C₁ (C₂ / V) t := hgron0
      _ ≤ (G₀ + 2) * gronwallBound (g 0 n) C₁ (C₂ / V) t := by nlinarith
  push Not at hn1
  have hnK : wt w n ≤ R * V := by
    rw [hwt]
    by_contra h
    push Not at h
    have := one_le_dist_sq_of_sum_gt hV0 (z := x 0) (fun s => ((hxB 0 ⟨le_rfl, ht.1.trans ht.2⟩).2 s)) h
    linarith
  set K := levelSet w (R * V) with hK
  set Rset := levelSet w (R * V + N.dwMax w) with hRset
  set Js := J.stopOutside K with hJs
  obtain ⟨hsupp, hclosed, hnRs⟩ := N.frozen_setup κ hw hV0 hnK
  have hfrozen : ∀ τ ∈ Icc 0 T, ∀ c, c ∉ K → 1 ≤ g τ c := by
    intro τ hτ c hc
    have h : R * V < ∑ s, (c s : ℝ) := by
      rw [← hwt]; by_contra h'; push Not at h'; exact hc ((mem_levelSet hw).mpr h')
    exact one_le_dist_sq_of_sum_gt hV0 (fun s => (hxB τ hτ).2 s) h
  -- Grönwall for the frozen chain
  set g' : ℝ → (S → ℕ) → ℝ := fun τ b =>
    ∑ s, 2 * ((b s : ℝ) / V - x τ s) * -(N.massActionVectorField κ (x τ) s) with hg'
  set D : ℝ → ℝ := fun τ => ∑ b ∈ Rset, Js.Pmin τ n b * g τ b with hD
  have hgder : ∀ τ ∈ Ioo 0 T, ∀ b, HasDerivAt (fun τ => g τ b) (g' τ b) τ := by
    intro τ hτ b
    have hxτ := hasDerivAt_pi.mp (hx τ hτ)
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun τ => (b s : ℝ) / V - x τ s) (-(N.massActionVectorField κ (x τ) s))
        τ := by simpa using (hxτ s).const_sub ((b s : ℝ) / V)
    convert h1.pow 2 using 1
    push_cast; ring
  have hDder : ∀ τ ∈ Ioo 0 T, HasDerivAt D
      (∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (g τ) c + g' τ c)) τ := fun τ hτ =>
    Js.hasDerivAt_sum_finite n Rset hsupp hclosed g g' hτ.1 fun b _ => hgder τ hτ b
  have hpt : ∀ τ ∈ Ioo 0 T, ∀ c ∈ Rset, Js.drift (g τ) c + g' τ c ≤ C₁ * g τ c + C₂ / V := by
    intro τ hτ c _
    have hτI : τ ∈ Icc 0 T := Ioo_subset_Icc_self hτ
    have hxτB : x τ ∈ Icc (0 : Concentration S) fun _ => Rb := by
      obtain ⟨h1, h2⟩ := hxB τ hτI
      exact ⟨h1, fun s => (h2 s).trans (le_max_right _ _)⟩
    have hgc := hg0 τ c
    rw [JumpSystem.drift_stopOutside]
    split_ifs with hcK
    · have h := N.drift_dist_sq_le κ hV hR₁0 (le_max_left _ _) hL c
        (coord_le_of_wt_le hw hR0 hV0 ((mem_levelSet hw).mp hcK)) (x τ) hxτB
      have hle : (1 + 2 * Fintype.card S * L) * g τ c ≤ C₁ * g τ c := by
        apply mul_le_mul_of_nonneg_right _ hgc
        have := le_max_right F2 0
        simp only [hC₁, hd]; linarith
      have e : (N.jumpSystem (N.volumeScale κ V (by linarith))).drift (g τ) c + g' τ c ≤
          (1 + 2 * Fintype.card S * L) * g τ c + C₂ / V := h
      linarith
    · have h1 := hfrozen τ hτI c hcK
      have hgg : g' τ c ≤ g τ c + ∑ s, N.massActionVectorField κ (x τ) s ^ 2 := by
        simp only [hg', hg, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        nlinarith [sq_nonneg ((c s : ℝ) / V - x τ s + N.massActionVectorField κ (x τ) s)]
      have hF := hF2' (x τ) hxτB
      have hFg : max F2 0 ≤ max F2 0 * g τ c := le_mul_of_one_le_right (le_max_right _ _) h1
      have hC1g : (1 + max F2 0) * g τ c ≤ C₁ * g τ c := mul_le_mul_of_nonneg_right hC₁1 hgc
      have : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
      nlinarith
  have hbound : ∀ τ ∈ Ioo 0 T,
      ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (g τ) c + g' τ c) ≤ C₁ * D τ + C₂ / V := by
    intro τ hτ
    calc ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (g τ) c + g' τ c)
        ≤ ∑ c ∈ Rset, Js.Pmin τ n c * (C₁ * g τ c + C₂ / V) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hpt τ hτ c hc)
            (Js.Pmin_nonneg τ hτ.1.le n c)
      _ = C₁ * D τ + C₂ / V * ∑ c ∈ Rset, Js.Pmin τ n c := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ C₁ * D τ + C₂ / V := by
          have h1 := Js.sum_Pmin_le_one τ hτ.1.le n Rset
          have h2 : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
          nlinarith
  have hDc : ContinuousOn D (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ((Js.continuousOn_Pmin n b).mono fun τ hτ => hτ.1).mul ?_
    refine continuousOn_finsetSum _ fun s _ => ?_
    exact (continuousOn_const.sub ((continuous_apply s).comp_continuousOn hxc)).pow 2
  have hD0 : D 0 = g 0 n := by
    simp only [hD, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun h => absurd hnRs h)]
    simp
  have hDt : D t ≤ gronwallBound (g 0 n) C₁ (C₂ / V) t := by
    have := le_gronwallBound_of_hasDerivAt_Ioo hC₁ne hDc hDder hbound ht
    rwa [hD0] at this
  -- frozen mass and comparison
  set P : (S → ℕ) → ℝ := fun b => J.Pmin t n b with hP
  set P' : (S → ℕ) → ℝ := fun b => Js.Pmin t n b with hP'
  have hP'0 : ∀ b, 0 ≤ P' b := fun b => Js.Pmin_nonneg t ht.1 n b
  have hreach : ∀ c, Js.ReachPos n c → c ∈ Rset := fun c h =>
    (mem_levelSet hw).mpr (N.wt_le_of_reachPos_stop κ hw hV0 hnK h)
  have hP'sum : ∑ b ∈ Rset, P' b = 1 := by
    have hΛ : ∀ c, Js.ReachPos n c → Js.q c ≤ ∑ c ∈ Rset, Js.q c := fun c hc =>
      Finset.single_le_sum (f := fun c => Js.q c) (fun c _ => Js.q_nonneg c) (hreach c hc)
    have h1 := Js.hasSum_Pmin_one hΛ ht.1
    calc ∑ b ∈ Rset, P' b = ∑' b, Js.Pmin t n b :=
          (tsum_eq_sum (s := Rset) fun b hb => hsupp t b hb).symm
      _ = 1 := h1.tsum_eq
  have hKsub : K ⊆ Rset := fun b hb => (mem_levelSet hw).mpr
    (le_trans ((mem_levelSet hw).mp hb) (by linarith [N.dwMax_nonneg w]))
  set Q := ∑ b ∈ Rset.filter (fun b => b ∉ K), P' b with hQdef
  have hQD : Q ≤ D t := by
    calc Q ≤ ∑ b ∈ Rset.filter (fun b => b ∉ K), P' b * g t b :=
          Finset.sum_le_sum fun b hb => le_mul_of_one_le_right (hP'0 b)
            (hfrozen t ht b (Finset.mem_filter.mp hb).2)
      _ ≤ D t := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun b _ _ => mul_nonneg (hP'0 b) (hg0 t b)
  have hKP' : ∑ b ∈ K, P' b = 1 - Q := by
    have := Finset.sum_filter_add_sum_filter_not Rset (fun b => b ∈ K) P'
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hKsub, hP'sum] at this
    linarith
  have hPP' : ∀ b ∈ K, P' b ≤ P b := fun b hb => J.Pmin_stopOutside_le K ht.1 n hb
  have hKPle : ∑ b ∈ K, P' b ≤ ∑ b ∈ K, P b := Finset.sum_le_sum hPP'
  have hgK : ∀ b ∈ K, g t b ≤ G₀ := by
    intro b hb
    have hcb := coord_le_of_wt_le hw hR0 hV0 ((mem_levelSet hw).mp hb)
    have hxt := hxB t ht
    calc g t b ≤ ∑ _s : S, (R₁ + Rx) ^ 2 := Finset.sum_le_sum fun s _ => by
          have h1 : (b s : ℝ) / V ≤ R₁ := by rw [div_le_iff₀ hV0]; exact hcb s
          have h2 : 0 ≤ (b s : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
          have h3 := hxt.1 s
          have h4 := hxt.2 s
          have h5 : |(b s : ℝ) / V - x t s| ≤ R₁ + Rx := by
            rw [abs_le]; constructor <;> simp only [Pi.zero_apply] at h3 <;> linarith
          calc ((b s : ℝ) / V - x t s) ^ 2 = |(b s : ℝ) / V - x t s| ^ 2 := (sq_abs _).symm
            _ ≤ (R₁ + Rx) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
      _ = G₀ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit := tsum_split K hfs
  have hin : ∑ b ∈ K, P b * min (g t b) 1 ≤ D t + G₀ * Q := by
    calc ∑ b ∈ K, P b * min (g t b) 1 ≤ ∑ b ∈ K, P b * g t b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hP0 b)
      _ = ∑ b ∈ K, P' b * g t b + ∑ b ∈ K, (P b - P' b) * g t b := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ D t + ∑ b ∈ K, (P b - P' b) * G₀ := by
          refine add_le_add ?_ (Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
            (hgK b hb) (by linarith [hPP' b hb]))
          exact Finset.sum_le_sum_of_subset_of_nonneg hKsub fun b _ _ =>
            mul_nonneg (hP'0 b) (hg0 t b)
      _ ≤ D t + G₀ * Q := by
          rw [← Finset.sum_mul, Finset.sum_sub_distrib]
          have : ∑ b ∈ K, P b ≤ 1 := J.sum_Pmin_le_one t ht.1 n K
          nlinarith
  have hout : ∑' b, (if b ∈ K then 0 else P b * min (g t b) 1) ≤ Q := by
    have hs1 : Summable fun b => if b ∈ K then (0 : ℝ) else P b :=
      (hPs.sub (summable_of_ne_finset_zero (s := K) (f := fun b => if b ∈ K then P b else 0)
        fun b hb => if_neg hb)).congr fun b => by split_ifs <;> simp
    have hsg : Summable fun b => if b ∈ K then (0 : ℝ) else P b * min (g t b) 1 :=
      (hfs.sub (summable_of_ne_finset_zero (s := K)
        (f := fun b => if b ∈ K then P b * min (g t b) 1 else 0)
        fun b hb => if_neg hb)).congr fun b => by by_cases h : b ∈ K <;> simp [h, hP]
    have hle : ∀ b, (if b ∈ K then 0 else P b * min (g t b) 1) ≤ (if b ∈ K then 0 else P b) := by
      intro b; split_ifs
      · exact le_rfl
      · exact hmin b
    have hPsplit := tsum_split K hPs
    calc ∑' b, (if b ∈ K then 0 else P b * min (g t b) 1) ≤ ∑' b, (if b ∈ K then 0 else P b) :=
          hsg.tsum_le_tsum hle hs1
      _ = ∑' b, P b - ∑ b ∈ K, P b := by linarith
      _ ≤ Q := by
          have : ∑' b, P b ≤ 1 := hP1
          linarith
  have hmain : ∑' m, N.transition κV t n m * min (g t m) 1 = ∑' b, P b * min (g t b) 1 := rfl
  rw [hmain, hsplit]
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun b _ => hP'0 b
  calc ∑ b ∈ K, P b * min (g t b) 1 + ∑' b, (if b ∈ K then 0 else P b * min (g t b) 1)
      ≤ D t + G₀ * Q + Q := add_le_add hin hout
    _ ≤ D t + G₀ * D t + D t := by nlinarith
    _ = (G₀ + 2) * D t := by ring
    _ ≤ (G₀ + 2) * gronwallBound (g 0 n) C₁ (C₂ / V) t :=
        mul_le_mul_of_nonneg_left hDt (by positivity)

/-- **Kurtz's law of large numbers in probability as `V → ∞`, any network.** With `V = k + 1`
and initial counts `n_k` with `n_k / V → x(0)`, `E min(|X^V(t)/V − x(t)|², 1) → 0`. -/
theorem kurtz_lln_tendsto (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m * min (∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2) 1)
      atTop (𝓝 0) := by
  obtain ⟨C₀, C₁, C₂, hC₀, -, -, hbd⟩ := N.kurtz_lln κ hRx x hxc hx hxB
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hε : Tendsto (fun k : ℕ => C₂ / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hup := (tendsto_gronwallBound hn0 hε C₁ t).const_mul C₀
  rw [mul_zero] at hup
  refine squeeze_zero (fun k => tsum_nonneg fun m => mul_nonneg
    ((N.jumpSystem _).Pmin_nonneg t ht.1 _ _)
      (le_min (Finset.sum_nonneg fun s _ => sq_nonneg _) zero_le_one))
    (fun k => hbd ((k : ℝ) + 1) (hV k) (n k) t ht) hup

/-- **Convergence in probability.** For every `δ ∈ (0, 1]`, the probability that
`|X^V(t)/V − x(t)|² ≥ δ` tends to `0`. -/
theorem kurtz_lln_prob (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m *
          (if δ ≤ ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2 then 1 else 0)) atTop (𝓝 0) := by
  have hE := (N.kurtz_lln_tendsto κ hRx x hxc hx hxB n hn0 ht).div_const δ
  rw [zero_div] at hE
  refine squeeze_zero (fun k => tsum_nonneg fun m => mul_nonneg
    ((N.jumpSystem _).Pmin_nonneg t ht.1 _ _) (by split_ifs <;> norm_num)) (fun k => ?_) hE
  set J := N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))
  have hP0 : ∀ m, 0 ≤ J.Pmin t (n k) m := fun m => J.Pmin_nonneg t ht.1 (n k) m
  have hPs : Summable fun m => J.Pmin t (n k) m :=
    summable_of_sum_le hP0 fun F => J.sum_Pmin_le_one t ht.1 (n k) F
  set G : (S → ℕ) → ℝ := fun m => ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2 with hG
  have hG0 : ∀ m, 0 ≤ G m := fun m => Finset.sum_nonneg fun s _ => sq_nonneg _
  have hpt : ∀ m, J.Pmin t (n k) m * (if δ ≤ G m then 1 else 0) ≤
      J.Pmin t (n k) m * min (G m) 1 / δ := by
    intro m
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (hP0 m)
    split_ifs with h
    · rw [le_div_iff₀ hδ, one_mul]; exact le_min h hδ1
    · exact div_nonneg (le_min (hG0 m) zero_le_one) hδ.le
  have hs1 : Summable fun m => J.Pmin t (n k) m * (if δ ≤ G m then 1 else 0) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hP0 m) (by split_ifs <;> norm_num))
      (fun m => mul_le_of_le_one_right (hP0 m) (by split_ifs <;> norm_num)) hPs
  have hs2 : Summable fun m => J.Pmin t (n k) m * min (G m) 1 / δ :=
    (Summable.of_nonneg_of_le (fun m => mul_nonneg (hP0 m) (le_min (hG0 m) zero_le_one))
      (fun m => mul_le_of_le_one_right (hP0 m) (min_le_right _ _)) hPs).div_const δ
  calc ∑' m, J.Pmin t (n k) m * (if δ ≤ G m then 1 else 0)
      ≤ ∑' m, J.Pmin t (n k) m * min (G m) 1 / δ := hs1.tsum_le_tsum hpt hs2
    _ = (∑' m, J.Pmin t (n k) m * min (G m) 1) / δ := tsum_div_const

end Network

namespace Examples
namespace Cubic

open Network

/-- `2X → 3X`, `3X → 2X` (rates `1`): the weight is increased only by a bimolecular reaction. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2], ![3]⟩ else ⟨![3], ![2]⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- No positive weight satisfies `MonoWeight`. -/
theorem not_monoWeight : ¬ ∃ w : Fin 1 → ℝ, (∀ s, 0 < w s) ∧ net.MonoWeight w := by
  rintro ⟨w, hw, h⟩
  have hpos : 0 < net.dw w 0 := by
    simp [dw, Network.reactionVector, Reaction.vector]
    linarith [hw 0]
  have := h 0 hpos
  simp [srcMol] at this

def xstar : Concentration (Fin 1) := fun _ => 1

theorem equilibrium : net.massActionVectorField κ xstar = 0 := by
  funext u
  rw [massActionVectorField_apply]
  fin_cases u
  simp [Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]
  norm_num

/-- **Law of large numbers in probability for `2X → 3X`, `3X → 2X`.** Started from `V` molecules
at volume `V = k + 1`, `P(|X^V(t)/V − 1|² ≥ δ) → 0` for every `δ ∈ (0, 1]`, `t ∈ [0, 1]`. -/
theorem lln_prob {t : ℝ} (ht : t ∈ Icc 0 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun k : ℕ => ∑' m, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        t (fun _ => k + 1) m *
          (if δ ≤ ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2 then 1 else 0)) atTop (𝓝 0) := by
  refine kurtz_lln_prob net κ (Rx := 1) (by norm_num) (fun _ => xstar) continuousOn_const
    (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (fun k _ => k + 1) ?_ ht hδ hδ1
  have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 1 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2
      = 0 := by
    intro k
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp [xstar, hk]
  simp only [h]
  exact tendsto_const_nhds

end Cubic
end Examples

end CRNT
