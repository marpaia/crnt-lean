import CRNT.Stochastic.NonlinearCLTTraj
import CRNT.Stochastic.KurtzLLN
import CRNT.Stochastic.OpenLLN

/-!
# The nonlinear CLT for networks without a conservation law

The generator–duality argument of `NonlinearCLTTraj`, run for the chain frozen outside
`{∑ c ≤ R V}` (`R = |S| R_x + |S| + 1`).  Frozen states are at squared distance at least one from
the trajectory, so the frozen mass is bounded by the frozen chain's mean squared distance, which
is `O(1/V)` when the initial fluctuation is `O(1)` (`frozen_unit_dist_le`).  On frozen states the
generator vanishes and the time derivative of the observable is `O(√V)`, so the frozen states
contribute `O(√V · 1/V)` to the derivative of the expectation; the original chain differs from
the frozen one by at most three times the frozen mass on a bounded observable.  No conservation
law, weight or non-explosion hypothesis is needed (`nonlinear_clt_open`).
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

set_option maxHeartbeats 1600000 in
/-- **Grönwall for the chain frozen outside `{∑ c ≤ R V}`, any network**, with
`R = |S| R_x + |S| + 1`. -/
theorem frozen_unit_dist_le (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      wt (fun _ => (1 : ℝ)) n ≤ ((Fintype.card S : ℝ) * Rx + Fintype.card S + 1) * V →
      ∀ t ∈ Icc 0 T,
        ∑ b ∈ levelSet (fun _ => (1 : ℝ)) (((Fintype.card S : ℝ) * Rx + Fintype.card S + 1) * V +
            N.dwMax (fun _ => (1 : ℝ))),
          ((N.jumpSystem (N.volumeScale κ V (by linarith))).stopOutside
            (levelSet (fun _ => (1 : ℝ)) (((Fintype.card S : ℝ) * Rx + Fintype.card S + 1) * V))).Pmin
              t n b * ∑ s, ((b s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := by
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
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun V hV n hnK t ht => ?_⟩
  have hV0 : 0 < V := by linarith
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
  have hg0 : ∀ τ b, 0 ≤ g τ b := fun τ b => Finset.sum_nonneg fun s _ => sq_nonneg _
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  have hC₁ne : C₁ ≠ 0 := by have := le_max_right F2 0; linarith
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
  exact hDt

/-- The generator of the frozen chain vanishes off the freezing set. -/
theorem _root_.CRNT.JumpSystem.cdrift_stopOutside {α : Type*} [DecidableEq α] (J : JumpSystem α)
    (K : Finset α) (f : α → ℂ) (a : α) :
    (J.stopOutside K).cdrift f a = if a ∈ K then J.cdrift f a else 0 := by
  unfold JumpSystem.cdrift JumpSystem.stopOutside
  split_ifs with h
  · simp [h]
  · simp [h]

set_option maxHeartbeats 6400000 in
/-- **The CLT error estimate for an arbitrary network, at fixed volume.** -/
theorem clt_error_open (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (θf θf' : ℝ → S → ℝ) (hθc : ContinuousOn θf (Icc 0 T))
    (hθd : ∀ u ∈ Ioo 0 T, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s) :
    ∃ K V₀ : ℝ, 0 ≤ K ∧ 1 ≤ V₀ ∧ ∀ (V : ℝ) (hV1 : 1 ≤ V), V₀ ≤ V → ∀ n : S → ℕ,
      ‖∑' m, (N.transition (N.volumeScale κ V (by linarith)) T n m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
          (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ))‖ ≤
        K * (1 + ∑ s, zeta V (x 0) n s ^ 2) / Real.sqrt V := by
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
  have hRb0 : 0 ≤ Rb := le_trans hR₁0 (le_max_left _ _)
  have hxB' : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rb := fun t ht =>
    ⟨(hxB t ht).1, fun s => ((hxB t ht).2 s).trans (le_max_right _ _)⟩
  have hx0 : ∀ t ∈ Icc 0 T, ∀ s, 0 ≤ x t s := fun t ht s => (hxB t ht).1 s
  -- the frozen mean squared distance
  obtain ⟨C₁, C₂, hC₁, hC₂, hfr⟩ := N.frozen_unit_dist_le κ hRx x hxc hx hxB
  -- bounds on θ, the Jacobian, the field and the Gaussian density
  obtain ⟨Θ₀, hΘ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun u => ∑ s, |θf u s|)
    (continuousOn_finsetSum _ fun s _ => ((continuous_apply s).comp_continuousOn hθc).abs)
  set Θ := max Θ₀ 0 with hΘ
  have hΘ0 : 0 ≤ Θ := le_max_right _ _
  have hθΘ : ∀ u ∈ Icc 0 T, ∑ s, |θf u s| ≤ Θ := fun u hu =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hΘ₀ u hu).trans (le_max_left _ _))
  have hfC : ContDiff ℝ ⊤ (N.massActionVectorField κ) := N.contDiff_massActionVectorField κ
  obtain ⟨LD₀, hLD₀⟩ := (isCompact_Icc (a := (0 : Concentration S)) (b := fun _ => Rb)).exists_bound_of_continuousOn
    (f := fun z => fderiv ℝ (N.massActionVectorField κ) z)
    ((hfC.continuous_fderiv (by simp)).continuousOn)
  set LD := max LD₀ 0 with hLD
  have hLD0 : 0 ≤ LD := le_max_right _ _
  have hLDb : ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ‖fderiv ℝ (N.massActionVectorField κ) z‖ ≤ LD := fun z hz => (hLD₀ z hz).trans (le_max_left _ _)
  obtain ⟨Fs₀, hFs₀⟩ := (isCompact_Icc (a := (0 : Concentration S)) (b := fun _ => Rb)).exists_bound_of_continuousOn
    (f := fun z => N.massActionVectorField κ z) hfC.continuous.continuousOn
  set Fs := max Fs₀ 0 with hFs
  have hFs0 : 0 ≤ Fs := le_max_right _ _
  have hFsb : ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ‖N.massActionVectorField κ z‖ ≤ Fs := fun z hz => (hFs₀ z hz).trans (le_max_left _ _)
  have hΦcont : ContinuousOn (fun u => N.quadG κ (x u) (θf u)) (Icc 0 T) := by
    have h2 : ContinuousOn (fun u => (x u, θf u)) (Icc 0 T) := hxc.prodMk hθc
    exact ((N.continuous_quadG₂ κ).comp_continuousOn h2).congr fun u _ => rfl
  obtain ⟨Φm₀, hΦm₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hΦcont
  set Φm := max Φm₀ 0 with hΦm
  have hΦm0 : 0 ≤ Φm := le_max_right _ _
  obtain ⟨C, V₀, hC0, hV₀, hgen⟩ := N.generator_error_le_traj κ hRb0 hΘ0
  set D₀ := N.dwMax w with hD₀
  have hD₀0 : 0 ≤ D₀ := N.dwMax_nonneg w
  set C₃ := Θ * LD * (R + D₀ + Rb) + Θ * Fs + Φm / 2 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  set E₁ := Real.exp (C₁ * T) with hE₁
  have hE₁1 : 1 ≤ E₁ := Real.one_le_exp (mul_nonneg hC₁ hT.le)
  set K := max 2 (T * (C + (C + C₃) * (1 + C₂ * T) * E₁) + 3 * (1 + C₂ * T) * E₁) with hKdef
  have hK2 : 2 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K, V₀, hK0, hV₀, fun V hV1 hV n => ?_⟩
  have hV0 : 0 < V := by linarith
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have hsV1 : 1 ≤ Real.sqrt V := Real.one_le_sqrt.mpr hV1
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  set G₀ := ∑ s, zeta V (x 0) n s ^ 2 with hG₀
  have hG₀0 : 0 ≤ G₀ := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hzV : ∀ (y : Concentration S) (c : S → ℕ),
      ∑ s, zeta V y c s ^ 2 = V * ∑ s, ((c s : ℝ) / V - y s) ^ 2 := by
    intro y c
    simp only [zeta, mul_pow, Real.sq_sqrt hV0.le, Finset.mul_sum]
  have hG₀eq : G₀ = V * ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 := hzV (x 0) n
  -- the target value and its norm
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]; simp
  set Itot := ∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u) with hItot
  have hItot0 : 0 ≤ Itot := intervalIntegral.integral_nonneg hT.le fun u hu =>
    N.quadG_nonneg κ (hx0 u hu) _
  have hb1 : ‖Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
      ((Itot / 2 : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    linarith
  have hP0 : ∀ τ, 0 ≤ τ → ∀ b, 0 ≤ J.Pmin τ n b := fun τ hτ b => J.Pmin_nonneg τ hτ n b
  have hPs : ∀ τ, 0 ≤ τ → Summable fun b => J.Pmin τ n b := fun τ hτ =>
    summable_of_sum_le (hP0 τ hτ) fun F => J.sum_Pmin_le_one τ hτ n F
  have hP1 : ∀ τ, 0 ≤ τ → ∑' b, J.Pmin τ n b ≤ 1 := fun τ hτ =>
    (hPs τ hτ).tsum_le_of_sum_le fun F => J.sum_Pmin_le_one τ hτ n F
  set A : ℂ := ∑' m, (N.transition κV T n m : ℂ) *
    Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) with hA
  have hAnorm_s : Summable fun m => ‖(N.transition κV T n m : ℂ) *
      Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ))‖ := by
    refine (hPs T hT.le).congr fun m => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ N.transition κV T n m from hP0 T hT.le m), hexp1, mul_one]
    rfl
  have hA1 : ‖A‖ ≤ 1 := by
    refine (norm_tsum_le_tsum_norm hAnorm_s).trans ?_
    refine le_of_eq_of_le (tsum_congr fun m => ?_) (hP1 T hT.le)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ N.transition κV T n m from hP0 T hT.le m), hexp1, mul_one]
    rfl
  -- the trivial case: the initial count is far from `V x(0)`
  by_cases hnK : ¬ wt w n ≤ R * V
  · push Not at hnK
    have hfar : 1 ≤ ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 := by
      rw [hwt] at hnK
      exact one_le_dist_sq_of_sum_gt hV0 (fun s => (hxB 0 ⟨le_rfl, hT.le⟩).2 s) hnK
    have hGV : V ≤ G₀ := by rw [hG₀eq]; nlinarith
    have hratio : 1 ≤ (1 + G₀) / Real.sqrt V := by
      rw [le_div_iff₀ hsV, one_mul]
      have : Real.sqrt V ≤ V := by nlinarith [Real.sq_sqrt hV0.le, hsV1]
      linarith
    calc ‖A - Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) - ((Itot / 2 : ℝ) : ℂ))‖
        ≤ ‖A‖ + ‖Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
            ((Itot / 2 : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
      _ ≤ K * ((1 + G₀) / Real.sqrt V) := by nlinarith
      _ = K * (1 + G₀) / Real.sqrt V := by ring
  push Not at hnK
  -- the frozen chain
  set Kset := levelSet w (R * V) with hKset
  set Rset := levelSet w (R * V + D₀) with hRset
  set Js := J.stopOutside Kset with hJs
  obtain ⟨hsupp, hclosed, hnRs⟩ := N.frozen_setup κ hw hV0 hnK
  have hcK : ∀ c ∈ Kset, ∀ s, (c s : ℝ) ≤ Rb * V := fun c hc s =>
    (coord_le_of_wt_le hw hR0 hV0 ((mem_levelSet hw).mp hc) s).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hV0.le)
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
  have hg0 : ∀ τ b, 0 ≤ g τ b := fun τ b => Finset.sum_nonneg fun s _ => sq_nonneg _
  have hfrozen : ∀ τ ∈ Icc 0 T, ∀ c, c ∉ Kset → 1 ≤ g τ c := by
    intro τ hτ c hc
    have h : R * V < ∑ s, (c s : ℝ) := by
      rw [← hwt]; by_contra h'; push Not at h'; exact hc ((mem_levelSet hw).mpr h')
    exact one_le_dist_sq_of_sum_gt hV0 (fun s => (hxB τ hτ).2 s) h
  set D : ℝ → ℝ := fun τ => ∑ b ∈ Rset, Js.Pmin τ n b * g τ b with hDdef
  have hDle : ∀ τ ∈ Icc 0 T, V * D τ ≤ (G₀ + C₂ * T) * E₁ := by
    intro τ hτ
    have h1 := hfr V hV1 n hnK τ hτ
    have hg00 : 0 ≤ ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
    have h2 := gronwallBound_le_mul_exp hg00 hC₁ (div_nonneg hC₂ hV0.le) hτ.1 (K := C₁)
      (ε := C₂ / V) (δ := ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2)
    have hexp : Real.exp (C₁ * τ) ≤ E₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hC₁)
    calc V * D τ ≤ V * ((∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 + C₂ / V * τ) * Real.exp (C₁ * τ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hV0.le
      _ = (G₀ + C₂ * τ) * Real.exp (C₁ * τ) := by rw [hG₀eq]; field_simp
      _ ≤ (G₀ + C₂ * T) * E₁ := by
          apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
          nlinarith [hτ.2]
  have hQD : ∀ τ ∈ Icc 0 T, ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin τ n b ≤ D τ := by
    intro τ hτ
    calc ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin τ n b
        ≤ ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin τ n b * g τ b :=
          Finset.sum_le_sum fun b hb => le_mul_of_one_le_right (Js.Pmin_nonneg τ hτ.1 n b)
            (hfrozen τ hτ b (Finset.mem_filter.mp hb).2)
      _ ≤ D τ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun b _ _ => mul_nonneg (Js.Pmin_nonneg τ hτ.1 n b) (hg0 τ b)
  have hD0 : ∀ τ ∈ Icc 0 T, 0 ≤ D τ := fun τ hτ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (Js.Pmin_nonneg τ hτ.1 n b) (hg0 τ b)
  -- the Gaussian factor
  set Φ : ℝ → ℝ := fun u => N.quadG κ (x u) (θf u) with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) := by
    have h2 : ContinuousOn (fun u => (x u, θf u)) (Icc 0 T) := hxc.prodMk hθc
    exact ((N.continuous_quadG₂ κ).comp_continuousOn h2).congr fun u _ => rfl
  have hΦ0 : ∀ u ∈ Icc 0 T, 0 ≤ Φ u := fun u hu => N.quadG_nonneg κ (hx0 u hu) _
  set Ifn : ℝ → ℝ := fun u => ∫ v in u..T, Φ v with hIfn
  have hIder : ∀ u ∈ Ioo 0 T, HasDerivAt Ifn (-Φ u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_left ((hΦc.mono (Icc_subset_Icc hu.1.le le_rfl)).intervalIntegrable_of_Icc hu.2.le)
      ((hΦc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu)
      ((hΦc.mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hu.1 hu.2))
  have hIc : ContinuousOn Ifn (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (a := 0) (b := T)
      (f := Φ) (by rw [uIcc_of_le hT.le]; exact hΦc.integrableOn_Icc)
    rwa [uIcc_of_le hT.le] at this
  have hI0 : ∀ u ∈ Icc 0 T, 0 ≤ Ifn u := fun u hu =>
    intervalIntegral.integral_nonneg hu.2 fun v hv => hΦ0 v ⟨hu.1.trans hv.1, hv.2⟩
  -- the observable
  set th : ℝ → (S → ℕ) → ℝ := fun u b => ∑ s, θf u s * zeta V (x u) b s with hth
  set F : ℝ → (S → ℕ) → ℂ := fun u b =>
    Complex.exp (I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ)) with hF
  set F' : ℝ → (S → ℕ) → ℂ := fun u b =>
    F u b * (I * ((∑ s, θf' u s * zeta V (x u) b s -
      Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
      ((Φ u / 2 : ℝ) : ℂ)) with hF'
  have hFnorm : ∀ u ∈ Icc 0 T, ∀ b, ‖F u b‖ ≤ 1 := by
    intro u hu b
    simp only [hF, Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    have := hI0 u hu
    linarith
  have hFder : ∀ u ∈ Ioo 0 T, ∀ b, HasDerivAt (fun u => F u b) (F' u b) u := by
    intro u hu b
    have hxs := hasDerivAt_pi.mp (hx u hu)
    have hzd : ∀ s, HasDerivAt (fun u => zeta V (x u) b s)
        (-(Real.sqrt V * N.massActionVectorField κ (x u) s)) u := by
      intro s
      have := ((hxs s).const_sub ((b s : ℝ) / V)).const_mul (Real.sqrt V)
      simpa [zeta, mul_neg] using this
    have hth' : HasDerivAt (fun u => th u b) (∑ s, θf' u s * zeta V (x u) b s -
        Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s) u := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun s u => θf u s * zeta V (x u) b s)
        (A' := fun s => θf' u s * zeta V (x u) b s +
          θf u s * -(Real.sqrt V * N.massActionVectorField κ (x u) s)) fun s _ =>
          ((hasDerivAt_pi.mp (hθd u hu)) s).mul (hzd s)
      convert this using 1
      rw [Finset.sum_add_distrib, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring
    have hin : HasDerivAt (fun u => I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ))
        (I * ((∑ s, θf' u s * zeta V (x u) b s -
          Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)) u := by
      have h1 := (hth'.ofReal_comp).const_mul I
      have h2 := ((hIder u hu).div_const 2).ofReal_comp
      convert h1.sub h2 using 1
      push_cast; ring
    have := hin.cexp
    simpa [hF', hF] using this
  -- pointwise error
  have hpt : ∀ u ∈ Icc 0 T, ∀ c ∈ Kset,
      ‖J.cdrift (F u) c + F' u c‖ ≤ C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V := by
    intro u hu c hc
    have hcd := N.cdrift_expObs κ hV0 (x u) (θf u) ((Ifn u / 2 : ℝ) : ℂ) c
    have heqF : J.cdrift (F u) c + F' u c = F u c *
        (∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V (x u) c s -
            Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)) := by
      have : J.cdrift (F u) c = F u c * ∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) := hcd
      rw [this]
      simp only [hF']
      ring
    rw [heqF, norm_mul]
    have hg := hgen (x u) (hxB' u hu) (θf u) (θf' u) (hθΘ u hu) (hadj u hu) V hV1 hV c (hcK c hc)
    have hz2 : ‖zeta V (x u) c‖ ^ 2 ≤ ∑ s, zeta V (x u) c s ^ 2 := norm_sq_le_sum_sq _
    calc ‖F u c‖ * ‖∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V (x u) c s -
            Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)‖
        ≤ 1 * (C * (1 + ‖zeta V (x u) c‖ ^ 2) / Real.sqrt V) :=
          mul_le_mul (hFnorm u hu c) hg (norm_nonneg _) zero_le_one
      _ ≤ C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V := by
          rw [one_mul]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hsV.le
  -- the frozen expectation
  set E : ℝ → ℂ := fun u => ∑ b ∈ Rset, (Js.Pmin u n b : ℂ) * F u b with hE
  have hEder : ∀ u ∈ Ioo 0 T, HasDerivAt E (∑ c ∈ Rset, (Js.Pmin u n c : ℂ) *
      (Js.cdrift (F u) c + F' u c)) u := fun u hu =>
    Js.hasDerivAt_csum_finite n Rset hsupp hclosed F F' hu.1 fun b _ => hFder u hu b
  -- frozen states: the time derivative is `O(√V)`
  have hF'frozen : ∀ u ∈ Icc 0 T, ∀ c ∈ Rset, ‖F' u c‖ ≤ Real.sqrt V * C₃ := by
    intro u hu c hc
    have hxu := hxB' u hu
    have hcR : wt w c ≤ R * V + D₀ := (mem_levelSet hw).mp hc
    have hcs : ∀ s, (c s : ℝ) / V ≤ R + D₀ := by
      intro s
      have h1 : (c s : ℝ) ≤ wt w c := by
        rw [hwt]
        exact Finset.single_le_sum (f := fun s => (c s : ℝ)) (fun s _ => Nat.cast_nonneg _)
          (Finset.mem_univ s)
      rw [div_le_iff₀ hV0]
      nlinarith
    have hzn : ‖zeta V (x u) c‖ ≤ Real.sqrt V * (R + D₀ + Rb) := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
      rw [Real.norm_eq_abs]
      simp only [zeta]
      rw [abs_mul, abs_of_pos hsV]
      apply mul_le_mul_of_nonneg_left _ hsV.le
      have h1 := hcs s
      have h2 : 0 ≤ (c s : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
      have h3 := hxu.1 s
      have h4 := hxu.2 s
      simp only [Pi.zero_apply] at h3
      rw [abs_le]; constructor <;> nlinarith
    have hlin : |∑ s, θf' u s * zeta V (x u) c s| ≤ Θ * LD * (Real.sqrt V * (R + D₀ + Rb)) := by
      rw [hadj u hu, abs_neg]
      refine (abs_dot_le _ _).trans ?_
      have hJz : ‖fderiv ℝ (N.massActionVectorField κ) (x u) (zeta V (x u) c)‖ ≤
          LD * (Real.sqrt V * (R + D₀ + Rb)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hLDb _ hxu) hzn (norm_nonneg _) hLD0)
      have := mul_le_mul (hθΘ u hu) hJz (norm_nonneg _) hΘ0
      linarith
    have hfx : |∑ s, θf u s * N.massActionVectorField κ (x u) s| ≤ Θ * Fs :=
      (abs_dot_le _ _).trans (mul_le_mul (hθΘ u hu) (hFsb _ hxu) (norm_nonneg _) hΘ0)
    have hΦu : Φ u ≤ Φm := by
      have := hΦm₀ u hu
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    simp only [hF']
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hFnorm u hu c)).trans ?_
    calc ‖I * ((∑ s, θf' u s * zeta V (x u) c s -
          Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)‖
        ≤ |∑ s, θf' u s * zeta V (x u) c s -
            Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s| + |Φ u / 2| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (Θ * LD * (Real.sqrt V * (R + D₀ + Rb)) + Real.sqrt V * (Θ * Fs)) + Φm / 2 := by
          have h1 : |∑ s, θf' u s * zeta V (x u) c s -
              Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s| ≤
              |∑ s, θf' u s * zeta V (x u) c s| +
                |Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s| := abs_sub _ _
          have h1' : |Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s| ≤
              Real.sqrt V * (Θ * Fs) := by
            rw [abs_mul, abs_of_pos hsV]; exact mul_le_mul_of_nonneg_left hfx hsV.le
          have h2 : |Φ u / 2| ≤ Φm / 2 := by
            rw [abs_div, abs_two, abs_of_nonneg (hΦ0 u hu)]; linarith
          linarith
      _ ≤ Real.sqrt V * C₃ := by
          simp only [hC₃]
          nlinarith [mul_nonneg hsV.le hΦm0]
  -- the derivative bound
  set B := (C + (C + C₃) * (G₀ + C₂ * T) * E₁) / Real.sqrt V with hBdef
  have hEbound : ∀ u ∈ Ioo 0 T,
      ‖∑ c ∈ Rset, (Js.Pmin u n c : ℂ) * (Js.cdrift (F u) c + F' u c)‖ ≤ B := by
    intro u hu
    have huI := Ioo_subset_Icc_self hu
    have hP'0 : ∀ c, 0 ≤ Js.Pmin u n c := fun c => Js.Pmin_nonneg u hu.1.le n c
    have hpt' : ∀ c ∈ Rset, ‖Js.cdrift (F u) c + F' u c‖ ≤
        C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V +
          (if c ∈ Kset then 0 else Real.sqrt V * C₃) := by
      intro c hc
      rw [JumpSystem.cdrift_stopOutside]
      split_ifs with hcK'
      · rw [add_zero]; exact hpt u huI c hcK'
      · rw [zero_add]
        have : 0 ≤ C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V := by
          have := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => sq_nonneg (zeta V (x u) c s)
          positivity
        linarith [hF'frozen u huI c hc]
    have hsum1 : ∑ c ∈ Rset, Js.Pmin u n c ≤ 1 := Js.sum_Pmin_le_one u hu.1.le n Rset
    have hsumz : ∑ c ∈ Rset, Js.Pmin u n c * ∑ s, zeta V (x u) c s ^ 2 = V * D u := by
      simp only [hDdef, hzV (x u)]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hsumf : ∑ c ∈ Rset, Js.Pmin u n c * (if c ∈ Kset then 0 else Real.sqrt V * C₃) =
        Real.sqrt V * C₃ * ∑ c ∈ Rset.filter (fun c => c ∉ Kset), Js.Pmin u n c := by
      rw [Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
    have hVD := hDle u huI
    have hQ := hQD u huI
    have hDu0 := hD0 u huI
    calc ‖∑ c ∈ Rset, (Js.Pmin u n c : ℂ) * (Js.cdrift (F u) c + F' u c)‖
        ≤ ∑ c ∈ Rset, Js.Pmin u n c * (C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V +
            (if c ∈ Kset then 0 else Real.sqrt V * C₃)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP'0 c)]
          exact mul_le_mul_of_nonneg_left (hpt' c hc) (hP'0 c)
      _ = C / Real.sqrt V * (∑ c ∈ Rset, Js.Pmin u n c +
            ∑ c ∈ Rset, Js.Pmin u n c * ∑ s, zeta V (x u) c s ^ 2) +
          ∑ c ∈ Rset, Js.Pmin u n c * (if c ∈ Kset then 0 else Real.sqrt V * C₃) := by
          have e1 : ∑ c ∈ Rset, Js.Pmin u n c * (C * (1 + ∑ s, zeta V (x u) c s ^ 2) /
              Real.sqrt V) = C / Real.sqrt V * (∑ c ∈ Rset, Js.Pmin u n c +
                ∑ c ∈ Rset, Js.Pmin u n c * ∑ s, zeta V (x u) c s ^ 2) := by
            rw [← Finset.sum_add_distrib, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by ring
          rw [← e1, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ C / Real.sqrt V * (1 + (G₀ + C₂ * T) * E₁) + Real.sqrt V * C₃ * D u := by
          rw [hsumz, hsumf]
          have h1 : 0 ≤ C / Real.sqrt V := by positivity
          have h2 : 0 ≤ Real.sqrt V * C₃ := by positivity
          have e1 := mul_le_mul_of_nonneg_left (add_le_add hsum1 hVD) h1
          have e2 := mul_le_mul_of_nonneg_left hQ h2
          linarith
      _ ≤ B := by
          have hsVD : Real.sqrt V * D u ≤ (G₀ + C₂ * T) * E₁ / Real.sqrt V := by
            rw [le_div_iff₀ hsV]
            have : Real.sqrt V * D u * Real.sqrt V = V * D u := by
              rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt hV0.le]
            rw [this]; exact hVD
          have hC3 : Real.sqrt V * C₃ * D u ≤ C₃ * ((G₀ + C₂ * T) * E₁ / Real.sqrt V) := by
            have := mul_le_mul_of_nonneg_left hsVD hC₃0
            linarith
          have e : (C + (C + C₃) * (G₀ + C₂ * T) * E₁) / Real.sqrt V =
              C / Real.sqrt V * (1 + (G₀ + C₂ * T) * E₁) +
                C₃ * ((G₀ + C₂ * T) * E₁ / Real.sqrt V) := by ring
          rw [hBdef, e]
          linarith
  -- continuity of the frozen expectation
  have hEc : ContinuousOn E (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn
        ((Js.continuousOn_Pmin n b).mono fun u hu => hu.1))
    · simp only [hF, hth, zeta]
      refine Continuous.comp_continuousOn Complex.continuous_exp ?_
      refine ContinuousOn.sub (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_))
        (Complex.continuous_ofReal.comp_continuousOn (hIc.div_const 2))
      refine continuousOn_finsetSum _ fun s _ => ?_
      exact ((continuous_apply s).comp_continuousOn hθc).mul (continuousOn_const.mul
        (continuousOn_const.sub ((continuous_apply s).comp_continuousOn hxc)))
  -- mean value inequality
  have hmv : ∀ ε ∈ Ioo 0 T, ‖E T - E ε‖ ≤ B * (T - ε) := by
    intro ε hε
    exact norm_image_sub_le_of_norm_deriv_right_le_segment (f := E)
      (f' := fun u => ∑ c ∈ Rset, (Js.Pmin u n c : ℂ) * (Js.cdrift (F u) c + F' u c))
      (a := ε) (b := T) (C := B) (hEc.mono (Icc_subset_Icc hε.1.le le_rfl))
      (fun u hu => (hEder u ⟨lt_of_lt_of_le hε.1 hu.1, hu.2⟩).hasDerivWithinAt)
      (fun u hu => hEbound u ⟨lt_of_lt_of_le hε.1 hu.1, hu.2⟩) T ⟨hε.2.le, le_rfl⟩
  have hlimE : Tendsto (fun ε => ‖E T - E ε‖) (𝓝[>] 0) (𝓝 ‖E T - E 0‖) := by
    have h1 : Tendsto E (𝓝[>] 0) (𝓝 (E 0)) :=
      ((hEc 0 ⟨le_rfl, hT.le⟩).tendsto).mono_left (nhdsWithin_le_of_mem
        (mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self))
    exact (tendsto_const_nhds.sub h1).norm
  have hlimB : Tendsto (fun ε => B * (T - ε)) (𝓝[>] 0) (𝓝 (B * (T - 0))) :=
    ((tendsto_const_nhds.sub tendsto_id).const_mul B).mono_left nhdsWithin_le_nhds
  have hET0 : ‖E T - E 0‖ ≤ B * T := by
    have := le_of_tendsto_of_tendsto hlimE hlimB (by
      filter_upwards [Ioo_mem_nhdsGT hT] with ε hε using hmv ε hε)
    simpa using this
  have hE0 : E 0 = Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
      ((Itot / 2 : ℝ) : ℂ)) := by
    simp only [hE, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
      (fun h => absurd hnRs h)]
    simp [hF, hIfn, hth, hΦ, hItot]
  -- comparison of the original chain with the frozen one at time `T`
  set P : (S → ℕ) → ℝ := fun b => J.Pmin T n b with hP
  set P' : (S → ℕ) → ℝ := fun b => Js.Pmin T n b with hP'
  have hP'0 : ∀ b, 0 ≤ P' b := fun b => Js.Pmin_nonneg T hT.le n b
  have hreach : ∀ c, Js.ReachPos n c → c ∈ Rset := fun c h =>
    (mem_levelSet hw).mpr (N.wt_le_of_reachPos_stop κ hw hV0 hnK h)
  have hP'sum : ∑ b ∈ Rset, P' b = 1 := by
    have hΛ : ∀ c, Js.ReachPos n c → Js.q c ≤ ∑ c ∈ Rset, Js.q c := fun c hc =>
      Finset.single_le_sum (f := fun c => Js.q c) (fun c _ => Js.q_nonneg c) (hreach c hc)
    have h1 := Js.hasSum_Pmin_one hΛ hT.le
    calc ∑ b ∈ Rset, P' b = ∑' b, Js.Pmin T n b :=
          (tsum_eq_sum (s := Rset) fun b hb => hsupp T b hb).symm
      _ = 1 := h1.tsum_eq
  have hKsub : Kset ⊆ Rset := fun b hb => (mem_levelSet hw).mpr
    (le_trans ((mem_levelSet hw).mp hb) (by linarith))
  set Q := ∑ b ∈ Rset.filter (fun b => b ∉ Kset), P' b with hQdef
  have hKP' : ∑ b ∈ Kset, P' b = 1 - Q := by
    have := Finset.sum_filter_add_sum_filter_not Rset (fun b => b ∈ Kset) P'
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hKsub, hP'sum] at this
    linarith
  have hPP' : ∀ b ∈ Kset, P' b ≤ P b := fun b hb => J.Pmin_stopOutside_le Kset hT.le n hb
  have hKP : ∑ b ∈ Kset, P b ≤ 1 := J.sum_Pmin_le_one T hT.le n Kset
  have hPsT := hPs T hT.le
  have hout : ∑' b, (if b ∈ Kset then 0 else P b) ≤ Q := by
    have h := tsum_split Kset hPsT
    have : ∑ b ∈ Kset, P' b ≤ ∑ b ∈ Kset, P b := Finset.sum_le_sum hPP'
    have h1 := hP1 T hT.le
    linarith
  have hP's : Summable P' := summable_of_ne_finset_zero (s := Rset) fun b hb => hsupp T b hb
  have hdiff_s : Summable fun b => |P b - P' b| :=
    Summable.of_nonneg_of_le (fun b => abs_nonneg _) (fun b => by
      rw [abs_le]; constructor <;> linarith [hP0 T hT.le b, hP'0 b]) (hPsT.add hP's)
  have hdiff : ∑' b, |P b - P' b| ≤ 3 * Q := by
    have h := tsum_split Kset hdiff_s
    have hin : ∑ b ∈ Kset, |P b - P' b| ≤ Q := by
      have : ∀ b ∈ Kset, |P b - P' b| = P b - P' b := fun b hb =>
        abs_of_nonneg (by linarith [hPP' b hb])
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
      linarith
    have hs1 : Summable fun b => if b ∈ Kset then (0 : ℝ) else P b :=
      (hPsT.sub (summable_of_ne_finset_zero (s := Kset) (f := fun b => if b ∈ Kset then P b else 0)
        fun b hb => if_neg hb)).congr fun b => by by_cases h : b ∈ Kset <;> simp [h, hP]
    have hs2 : Summable fun b => if b ∈ Kset then (0 : ℝ) else P' b :=
      summable_of_ne_finset_zero (s := Rset) fun b hb => by
        by_cases h : b ∈ Kset
        · simp [h]
        · simp only [h, if_false, hP']; exact hsupp T b hb
    have hs3 : Summable fun b => if b ∈ Kset then (0 : ℝ) else |P b - P' b| :=
      (hdiff_s.sub (summable_of_ne_finset_zero (s := Kset)
        (f := fun b => if b ∈ Kset then |P b - P' b| else 0) fun b hb => if_neg hb)).congr
        fun b => by by_cases h : b ∈ Kset <;> simp [h]
    have hQ' : ∑' b, (if b ∈ Kset then (0 : ℝ) else P' b) = Q := by
      rw [tsum_eq_sum (s := Rset) fun b hb => by
          by_cases h : b ∈ Kset
          · simp [h]
          · simp only [h, if_false, hP']; exact hsupp T b hb,
        hQdef, Finset.sum_filter]
      exact Finset.sum_congr rfl fun b _ => by by_cases h : b ∈ Kset <;> simp [h]
    have hout2 : ∑' b, (if b ∈ Kset then 0 else |P b - P' b|) ≤ Q + Q := by
      calc ∑' b, (if b ∈ Kset then 0 else |P b - P' b|)
          ≤ ∑' b, ((if b ∈ Kset then 0 else P b) + (if b ∈ Kset then (0 : ℝ) else P' b)) :=
            hs3.tsum_le_tsum (fun b => by
              by_cases h : b ∈ Kset
              · simp [h]
              · simp only [h, if_false]
                rw [abs_le]; constructor <;> linarith [hP0 T hT.le b, hP'0 b]) (hs1.add hs2)
        _ = ∑' b, (if b ∈ Kset then 0 else P b) + ∑' b, (if b ∈ Kset then (0 : ℝ) else P' b) :=
            hs1.tsum_add hs2
        _ ≤ Q + Q := by rw [hQ']; linarith
    linarith
  have hET : E T = ∑' m, (P' m : ℂ) *
      Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) := by
    simp only [hE, hF, hIfn, intervalIntegral.integral_same, zero_div, Complex.ofReal_zero,
      sub_zero]
    refine (tsum_eq_sum fun m hm => ?_).symm
    show (Js.Pmin T n m : ℂ) * _ = 0
    rw [hsupp T m hm]; simp
  have hcomp : ‖A - E T‖ ≤ 3 * Q := by
    rw [hA, hET]
    have hsA : Summable fun m => (N.transition κV T n m : ℂ) *
        Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) :=
      Summable.of_norm hAnorm_s
    have hsE : Summable fun m => (P' m : ℂ) *
        Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) :=
      summable_of_ne_finset_zero (s := Rset) fun m hm => by
        simp only [hP']; rw [hsupp T m hm]; simp
    rw [← hsA.tsum_sub hsE]
    have hsD : Summable fun m => ‖(N.transition κV T n m : ℂ) *
        Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) -
        (P' m : ℂ) * Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ))‖ := by
      refine hdiff_s.congr fun m => ?_
      rw [← sub_mul, norm_mul, hexp1, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      rfl
    refine (norm_tsum_le_tsum_norm hsD).trans ?_
    refine le_of_eq_of_le (tsum_congr fun m => ?_) hdiff
    rw [← sub_mul, norm_mul, hexp1, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rfl
  have hQT : Q ≤ (G₀ + C₂ * T) * E₁ / V := by
    have h1 := hQD T ⟨hT.le, le_rfl⟩
    have h2 := hDle T ⟨hT.le, le_rfl⟩
    rw [le_div_iff₀ hV0]
    nlinarith
  -- assemble
  rw [← hE0]
  have hfin : 3 * ((G₀ + C₂ * T) * E₁ / V) + B * T ≤ K * (1 + G₀) / Real.sqrt V := by
    have hVsV : (G₀ + C₂ * T) * E₁ / V ≤ (G₀ + C₂ * T) * E₁ / Real.sqrt V :=
      div_le_div_of_nonneg_left (by positivity) hsV (by nlinarith [Real.sq_sqrt hV0.le, hsV1])
    have hKle : T * (C + (C + C₃) * (1 + C₂ * T) * E₁) + 3 * (1 + C₂ * T) * E₁ ≤ K :=
      le_max_right _ _
    have hA1' : G₀ + C₂ * T ≤ (1 + C₂ * T) * (1 + G₀) := by nlinarith [mul_nonneg hC₂ hT.le]
    have hBT : B * T ≤ T * (C + (C + C₃) * (1 + C₂ * T) * E₁) * (1 + G₀) / Real.sqrt V := by
      simp only [hBdef]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hsV.le
      have h1 : C ≤ C * (1 + G₀) := le_mul_of_one_le_right hC0 (by linarith)
      have h2 : (C + C₃) * (G₀ + C₂ * T) * E₁ ≤ (C + C₃) * ((1 + C₂ * T) * (1 + G₀)) * E₁ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hA1' (by positivity)
      nlinarith
    have h3 : 3 * ((G₀ + C₂ * T) * E₁ / Real.sqrt V) ≤
        3 * (1 + C₂ * T) * E₁ * (1 + G₀) / Real.sqrt V := by
      rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hsV.le
      nlinarith [mul_le_mul_of_nonneg_right hA1' (by linarith : (0:ℝ) ≤ E₁)]
    have h4 : (T * (C + (C + C₃) * (1 + C₂ * T) * E₁) + 3 * (1 + C₂ * T) * E₁) * (1 + G₀) /
        Real.sqrt V ≤ K * (1 + G₀) / Real.sqrt V := by
      apply div_le_div_of_nonneg_right _ hsV.le
      exact mul_le_mul_of_nonneg_right hKle (by linarith)
    have e : T * (C + (C + C₃) * (1 + C₂ * T) * E₁) * (1 + G₀) / Real.sqrt V +
        3 * (1 + C₂ * T) * E₁ * (1 + G₀) / Real.sqrt V =
        (T * (C + (C + C₃) * (1 + C₂ * T) * E₁) + 3 * (1 + C₂ * T) * E₁) * (1 + G₀) /
          Real.sqrt V := by ring
    have h5 := mul_le_mul_of_nonneg_left hVsV (by norm_num : (0:ℝ) ≤ 3)
    linarith
  calc ‖A - E 0‖ ≤ ‖A - E T‖ + ‖E T - E 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 * Q + B * T := add_le_add hcomp hET0
    _ ≤ 3 * ((G₀ + C₂ * T) * E₁ / V) + B * T := by linarith
    _ ≤ K * (1 + G₀) / Real.sqrt V := hfin

/-- **Central limit theorem for an arbitrary network along a trajectory.** For any network
(no conservation law, weight or non-explosion hypothesis), a solution `x` of the mass-action
equation on `[0, T]` with values in `[0, R_x]^S`, a `C¹` solution `θ(·)` of the adjoint
linearized equation `θ'(u) · v = −θ(u) · Df(x(u)) v`, and initial counts with
`√V (n_V/V − x(0)) → z₀`, under the minimal transition function:

`E exp(i θ(T) · √V (X^V(T)/V − x(T))) → exp(i θ(0) · z₀ − ½ ∫₀ᵀ ∑_r λ_r(x(u)) (θ(u) · Δ_r)² du)`. -/
theorem nonlinear_clt_open (N : Network S) (κ : RateConstants N) {T Rx : ℝ} (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (θf θf' : ℝ → S → ℝ) (hθc : ContinuousOn θf (Icc 0 T))
    (hθd : ∀ u ∈ Ioo 0 T, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s)
    (n : ℕ → S → ℕ)
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (x 0) (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (n k) m : ℂ) * Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)))
      atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) -
        (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ)))) := by
  obtain ⟨K, V₀, hK0, hV₀, hbd⟩ := N.clt_error_open κ hT hRx x hxc hx hxB θf θf' hθc hθd hadj
  set Ib : ℂ := (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ) with hIb
  set b : ℕ → ℂ := fun k => Complex.exp (I * ((∑ s, θf 0 s * zeta ((k : ℝ) + 1) (x 0) (n k) s : ℝ) : ℂ) - Ib)
    with hb
  have hblim : Tendsto b atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib))) := by
    have hcont : Continuous fun z : S → ℝ =>
        Complex.exp (I * ((∑ s, θf 0 s * z s : ℝ) : ℂ) - Ib) := by fun_prop
    exact (hcont.tendsto z₀).comp hz
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hden
  have hG : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2)) atTop
      (𝓝 (K * (1 + ∑ s, z₀ s ^ 2))) := by
    have hc : Continuous fun z : S → ℝ => K * (1 + ∑ s, z s ^ 2) := by fun_prop
    exact (hc.tendsto z₀).comp hz
  have herr : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2) /
      Real.sqrt ((k : ℝ) + 1)) atTop (𝓝 0) := hG.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb' := (tendsto_iff_norm_sub_tendsto_zero.mp hblim)
  have htot := herr.add hb'
  rw [add_zero] at htot
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ htot
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  filter_upwards [hden.eventually_ge_atTop V₀] with k hk
  have h1 := hbd ((k : ℝ) + 1) (hV k) hk (n k)
  calc ‖∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖
      ≤ ‖∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) - b k‖ +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2) / Real.sqrt ((k : ℝ) + 1) +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := by
        gcongr



end Network

namespace Examples
namespace InflowAnnihilationCLT

open Network InflowAnnihilation

/-- The Jacobian of `x ↦ 2 − 2x²` at `1`. -/
theorem jac_apply (v : Fin 1 → ℝ) :
    fderiv ℝ (net.massActionVectorField κ) xstar v = fun _ => -4 * v 0 := by
  set f := net.massActionVectorField κ with hf
  have hD : HasFDerivAt f (fderiv ℝ f xstar) xstar :=
    ((net.contDiff_massActionVectorField κ).differentiable (by simp) xstar).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => xstar + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add xstar
  have hD' : HasFDerivAt f (fderiv ℝ f xstar) (xstar + (0 : ℝ) • v) := by simpa using hD
  have h1 : HasDerivAt (fun t : ℝ => f (xstar + t • v)) (fderiv ℝ f xstar v) (0 : ℝ) := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => xstar + t • v) (0 : ℝ) hD' hline
    exact this
  have h2 : HasDerivAt (fun t : ℝ => f (xstar + t • v)) (fun _ => -4 * v 0) (0 : ℝ) := by
    rw [hasDerivAt_pi]
    intro s
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hfun : (fun t : ℝ => f (xstar + t • v) 0) = fun t => 2 + -((1 + t * v 0) ^ 2 * 2) := by
      funext t
      simp [hf, massActionVectorField_apply, Fin.sum_univ_two, massActionRate, κ, xstar,
        Complex.massActionMonomial, Network.reactionVector, Reaction.vector]
    rw [hfun]
    have ha : HasDerivAt (fun t : ℝ => 1 + t * v 0) (v 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add 1
    convert ((ha.pow 2).mul_const 2).neg.const_add 2 using 1
    simp; ring
  exact h1.unique h2

/-- The adjoint solution `θ(u) = e^{4(u − T)}`. -/
noncomputable def θf (T u : ℝ) : Fin 1 → ℝ := fun _ => Real.exp (4 * (u - T))

noncomputable def θf' (T u : ℝ) : Fin 1 → ℝ := fun _ => 4 * Real.exp (4 * (u - T))

theorem hasDerivAt_θf (T u : ℝ) : HasDerivAt (θf T) (θf' T u) u := by
  rw [hasDerivAt_pi]
  intro s
  have h : HasDerivAt (fun u : ℝ => Real.exp (4 * (u - T))) (Real.exp (4 * (u - T)) * 4) u := by
    have := ((hasDerivAt_id u).sub_const T).const_mul 4
    simpa using this.exp
  have e : θf' T u s = Real.exp (4 * (u - T)) * 4 := by
    show 4 * Real.exp (4 * (u - T)) = _
    ring
  rw [e]
  exact h

theorem adjoint (T u : ℝ) (v : Fin 1 → ℝ) :
    ∑ s, θf' T u s * v s =
      -∑ s, θf T u s * fderiv ℝ (net.massActionVectorField κ) xstar v s := by
  rw [jac_apply]
  simp [θf, θf']
  ring

theorem quadG_θf (T u : ℝ) : net.quadG κ xstar (θf T u) = 6 * Real.exp (8 * (u - T)) := by
  simp [quadG, θf, Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]
  have : Real.exp (8 * (u - T)) = Real.exp (4 * (u - T)) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [this]; ring

theorem integral_quadG (T : ℝ) :
    ∫ u in (0 : ℝ)..T, net.quadG κ xstar (θf T u) = 3 / 4 * (1 - Real.exp (-8 * T)) := by
  simp_rw [quadG_θf]
  have hder : ∀ u ∈ Set.uIcc 0 T, HasDerivAt (fun u : ℝ => 3 / 4 * Real.exp (8 * (u - T)))
      (6 * Real.exp (8 * (u - T))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => 8 * (u - T)) 8 u := by
      simpa using ((hasDerivAt_id u).sub_const T).const_mul 8
    have := h0.exp.const_mul (3 / 4)
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((by fun_prop : Continuous fun u : ℝ => 6 * Real.exp (8 * (u - T))).intervalIntegrable _ _)]
  simp
  ring_nf

/-- **CLT for the non-conservative network `0 → X`, `2X → 0`** at its equilibrium `x* = 1`.
Started from `V` molecules at volume `V = k + 1`, `E exp(i ζ(T)) → exp(−(3/8)(1 − e^{−8T}))`:
the fluctuation is asymptotically normal with variance `(3/4)(1 − e^{−8T})`. -/
theorem clt {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k : ℕ => ∑' m, (net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (fun _ => k + 1) m : ℂ) *
          Complex.exp (I * ((zeta ((k : ℝ) + 1) xstar m 0 : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp ((-(3 / 8) * (1 - Real.exp (-8 * T)) : ℝ) : ℂ))) := by
  have hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xstar (fun _ => k + 1)) atTop (𝓝 0) := by
    have : ∀ k : ℕ, zeta ((k : ℝ) + 1) xstar (fun _ => k + 1) = 0 := by
      intro k; funext s
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [zeta, xstar, hk]
    simp only [this]; exact tendsto_const_nhds
  have h := nonlinear_clt_open net κ (Rx := 1) hT (by norm_num) (fun _ => xstar) continuousOn_const
    (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (θf T) (θf' T)
    (fun u _ => (hasDerivAt_θf T u).continuousAt.continuousWithinAt) (fun u _ => hasDerivAt_θf T u)
    (fun u _ v => adjoint T u v) (fun k _ => k + 1) hz
  have hθT : ∀ s, θf T T s = 1 := fun s => by simp [θf]
  have hlhs : ∀ (k : ℕ) (m : Fin 1 → ℕ),
      ∑ s, θf T T s * zeta ((k : ℝ) + 1) xstar m s = zeta ((k : ℝ) + 1) xstar m 0 := fun k m => by
    simp [hθT]
  simp_rw [hlhs] at h
  rw [integral_quadG] at h
  convert h using 2
  simp
  ring_nf

end InflowAnnihilationCLT
end Examples

end CRNT
