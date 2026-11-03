import CRNT.Stochastic.SubconservativeLLN
import CRNT.Stochastic.MinimalSemigroupStochastic

/-!
# Kurtz's law of large numbers for networks whose weight grows only through inflows

A strictly positive weight `w` is fixed such that every reaction that increases `⟨w, ·⟩` has the
zero complex as its source (`InflowWeight`): inflows `0 → y` may increase the weight, every other
reaction conserves or decreases it.  Fully open networks whose internal reactions do not increase
the number of molecules are the basic example; the reachable state space is infinite.

Proof by truncation.  With `u(c) = ⟨w, c⟩` and `a(t) = M + K₀ t` (`K₀` the weight input rate of the
inflows per unit volume), freeze the chain outside `{u ≤ R V}`, `R = M + K₀ T + 1`
(`JumpSystem.stopOutside`).

* The frozen chain lives on a finite set, and the one-sided quantity
  `ψ_t(c) = ((u(c)/V − a(t))⁺)²` has `E ψ_t ≤ C t / V`; since `ψ ≥ 1` on frozen states, the frozen
  mass is `O(1/V)` uniformly on `[0, T]`.
* For the frozen chain the mean squared distance to the mass-action solution satisfies the
  Grönwall inequality of the conservative case, with an extra `O(1/V)` from the frozen mass.
* The original chain agrees with the frozen one up to the frozen mass inside `{u ≤ R V}`, and the
  part outside is controlled by the fourth moment of `1 + u/V`, which has linear drift.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT

/-- **Grönwall on an open interval of differentiability.** -/
theorem le_gronwallBound_of_hasDerivAt_Ioo {D D' : ℝ → ℝ} {K e T : ℝ} (hK : K ≠ 0)
    (hDc : ContinuousOn D (Icc 0 T)) (hD : ∀ τ ∈ Ioo 0 T, HasDerivAt D (D' τ) τ)
    (hb : ∀ τ ∈ Ioo 0 T, D' τ ≤ K * D τ + e) {t : ℝ} (ht : t ∈ Icc 0 T) :
    D t ≤ gronwallBound (D 0) K e t := by
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0; rw [gronwallBound_x0]
  · have hT : 0 < T := lt_of_lt_of_le htpos ht.2
    have hgron : ∀ ε ∈ Ioo (0 : ℝ) t, D t ≤ gronwallBound (D ε) K e (t - ε) := by
      intro ε hε
      have hsub : Icc ε t ⊆ Icc 0 T := Icc_subset_Icc hε.1.le ht.2
      have h := le_gronwallBound_of_liminf_deriv_right_le (f := D) (f' := D')
        (δ := D ε) (K := K) (ε := e) (a := ε) (b := t) (hDc.mono hsub)
        (fun τ hτ r hr => ((hD τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩
          ).hasDerivWithinAt).liminf_right_slope_le hr) le_rfl
        (fun τ hτ => hb τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩)
      exact h t ⟨hε.2.le, le_rfl⟩
    have hcont : Tendsto (fun ε => gronwallBound (D ε) K e (t - ε)) (𝓝[>] 0)
        (𝓝 (gronwallBound (D 0) K e (t - 0))) := by
      simp only [gronwallBound_of_K_ne_0 hK]
      have hD0t : Tendsto D (𝓝[>] 0) (𝓝 (D 0)) := by
        have hw := hDc 0 ⟨le_rfl, hT.le⟩
        refine hw.tendsto.mono_left ?_
        refine nhdsWithin_le_of_mem ?_
        exact mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
      have hlin : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝 (t - 0)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      have hexp := (Real.continuous_exp.tendsto _).comp (hlin.const_mul K)
      exact (hD0t.mul hexp).add (tendsto_const_nhds.mul (hexp.sub tendsto_const_nhds))
    have hle := ge_of_tendsto hcont (by
      filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε using hgron ε hε)
    rwa [sub_zero] at hle

/-- `z ↦ (z⁺)²` is differentiable with derivative `2 z⁺`. -/
theorem hasDerivAt_posPart_sq (z : ℝ) :
    HasDerivAt (fun z : ℝ => (max z 0) ^ 2) (2 * max z 0) z := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hev : (fun z : ℝ => (max z 0) ^ 2) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hz] with y hy
      rw [max_eq_right (le_of_lt hy)]; ring
    rw [max_eq_right hz.le, mul_zero]
    exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev
  · subst hz
    rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, smul_eq_mul, mul_zero]
    have h1 : (fun h : ℝ => h ^ 2) =o[𝓝 0] fun h => h := by
      have := Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)
      simpa using this
    refine Asymptotics.IsBigO.trans_isLittleO ?_ h1
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    rcases le_total h 0 with hh | hh
    · rw [max_eq_right hh]; nlinarith [sq_nonneg h]
    · rw [max_eq_left hh]
  · have hev : (fun z : ℝ => (max z 0) ^ 2) =ᶠ[𝓝 z] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds hz] with y hy
      rw [max_eq_left (le_of_lt hy)]
    rw [max_eq_left hz.le]
    have := hasDerivAt_pow 2 z
    simp only [Nat.cast_ofNat] at this
    convert this.congr_of_eventuallyEq hev using 1
    ring

/-- One-sided second-order bound for `(z⁺)²`. -/
theorem posPart_sq_add_le (z d : ℝ) :
    (max (z + d) 0) ^ 2 ≤ (max z 0) ^ 2 + 2 * max z 0 * d + d ^ 2 := by
  have hrhs : (max z 0) ^ 2 + 2 * max z 0 * d + d ^ 2 = (max z 0 + d) ^ 2 := by ring
  rw [hrhs]
  rcases le_total (z + d) 0 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (max z 0 + d)]
  · rw [max_eq_left h]
    have h1 : z + d ≤ max z 0 + d := by linarith [le_max_left z 0]
    exact pow_le_pow_left₀ h h1 2

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The weight of a count. -/
noncomputable def wt (w : S → ℝ) (c : S → ℕ) : ℝ := ∑ s, w s * (c s : ℝ)

omit [DecidableEq S] in
theorem wt_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s) (c : S → ℕ) : 0 ≤ wt w c :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)

/-- The weight increment of reaction `r`. -/
noncomputable def dw (N : Network S) (w : S → ℝ) (r : N.R) : ℝ := ∑ s, w s * N.reactionVector r s

/-- **Only inflows increase the weight.** -/
def InflowWeight (N : Network S) (w : S → ℝ) : Prop :=
  ∀ r, 0 < N.dw w r → ∀ s, (N.reaction r).source s = 0

theorem wt_jumpNextCount (N : Network S) (κ : RateConstants N) (w : S → ℝ) {c : S → ℕ}
    {r : N.R} (hr : 0 < N.stochasticMassActionRate κ c r) :
    wt w (N.jumpNextCount c r) = wt w c + N.dw w r := by
  have hen : N.Enabled c r := by
    by_contra h
    rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ c r h] at hr
    exact lt_irrefl _ hr
  have hcast : ∀ s, (N.jumpNextCount c r s : ℝ) = (c s : ℝ) + N.reactionVector r s := by
    intro s
    simp only [jumpNextCount, reactionVector_apply]
    rw [Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  simp only [wt, dw, hcast, mul_add, Finset.sum_add_distrib]

/-- An inflow fires at the constant rate `κ_r V`. -/
theorem stochasticRate_inflow (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (c : S → ℕ) {r : N.R} (h0 : ∀ s, (N.reaction r).source s = 0) :
    N.stochasticMassActionRate (N.volumeScale κ V hV) c r = κ.k r * V := by
  rw [stochasticRate_volumeScale]
  simp [densRate, h0]
  ring

/-- The weight input rate of the inflows, per unit volume. -/
noncomputable def inRate (N : Network S) (κ : RateConstants N) (w : S → ℝ) : ℝ :=
  ∑ r, κ.k r * max (N.dw w r) 0

theorem inRate_nonneg (N : Network S) (κ : RateConstants N) (w : S → ℝ) : 0 ≤ N.inRate κ w :=
  Finset.sum_nonneg fun r _ => mul_nonneg (κ.positive r).le (le_max_right _ _)

/-- The largest weight increment. -/
noncomputable def dwMax (N : Network S) (w : S → ℝ) : ℝ := ∑ r, |N.dw w r|

theorem dwMax_nonneg (N : Network S) (w : S → ℝ) : 0 ≤ N.dwMax w :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_dw_le (N : Network S) (w : S → ℝ) (r : N.R) : |N.dw w r| ≤ N.dwMax w :=
  Finset.single_le_sum (f := fun r => |N.dw w r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)

/-- **Weight-increasing reactions are at most monomolecular.** -/
def MonoWeight (N : Network S) (w : S → ℝ) : Prop :=
  ∀ r, 0 < N.dw w r → N.srcMol r ≤ 1

theorem InflowWeight.monoWeight {N : Network S} {w : S → ℝ} (h : N.InflowWeight w) :
    N.MonoWeight w := fun r hr => by
  simp [srcMol, h r hr]

/-- `∑_s 1/w_s`. -/
noncomputable def wInv (w : S → ℝ) : ℝ := ∑ s, (w s)⁻¹

omit [DecidableEq S] in
theorem wInv_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s) : 0 ≤ wInv w :=
  Finset.sum_nonneg fun s _ => (inv_pos.mpr (hw s)).le

omit [DecidableEq S] in
theorem sum_coord_le {w : S → ℝ} (hw : ∀ s, 0 < w s) (c : S → ℕ) :
    ∑ s, (c s : ℝ) ≤ wInv w * wt w c := by
  rw [wInv, Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 : w s * (c s : ℝ) ≤ wt w c := Finset.single_le_sum
    (f := fun s => w s * (c s : ℝ)) (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _))
    (Finset.mem_univ s)
  rw [inv_mul_eq_div, le_div_iff₀ (hw s)]
  linarith

/-- A source of molecularity at most one fires at rate at most `κ_r (V + ∑_s c_s)`. -/
theorem rate_le_of_srcMol_le_one (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (c : S → ℕ) {r : N.R} (hr : N.srcMol r ≤ 1) :
    N.stochasticMassActionRate (N.volumeScale κ V hV) c r ≤ κ.k r * (V + ∑ s, (c s : ℝ)) := by
  classical
  rw [stochasticRate_volumeScale]
  unfold densRate
  have hsum0 : 0 ≤ ∑ s, (c s : ℝ) := Finset.sum_nonneg fun s _ => Nat.cast_nonneg _
  by_cases h : ∃ s₀, (N.reaction r).source s₀ ≠ 0
  · obtain ⟨s₀, hs₀⟩ := h
    have hle : (N.reaction r).source s₀ ≤ N.srcMol r := Finset.single_le_sum
      (f := fun s => (N.reaction r).source s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s₀)
    have h1 : (N.reaction r).source s₀ = 1 := by omega
    have hother : ∀ s, s ≠ s₀ → (N.reaction r).source s = 0 := by
      intro s hs
      by_contra hne
      have : (N.reaction r).source s + (N.reaction r).source s₀ ≤ N.srcMol r := by
        unfold srcMol
        rw [← Finset.sum_pair hs]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => Nat.zero_le _
      omega
    rw [Finset.prod_eq_single s₀ (fun s _ hs => by rw [hother s hs]; simp)
      (fun h => absurd (Finset.mem_univ s₀) h), h1]
    simp only [Nat.descFactorial_one, pow_one]
    have hcs : (c s₀ : ℝ) ≤ ∑ s, (c s : ℝ) := Finset.single_le_sum
      (f := fun s => (c s : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ s₀)
    have hk := (κ.positive r).le
    rw [show V * (κ.k r * ((c s₀ : ℝ) / V)) = κ.k r * (c s₀ : ℝ) by field_simp]
    nlinarith
  · push Not at h
    simp only [h, Nat.descFactorial_zero, Nat.cast_one, pow_zero, div_one,
      Finset.prod_const_one, mul_one]
    have hk := (κ.positive r).le
    nlinarith

/-- Per-reaction bound: `λ_r ⟨w, Δ_r⟩ ≤ κ_r ⟨w, Δ_r⟩⁺ (V + ⟨1/w⟩ u)`. -/
theorem rate_mul_dw_le (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hmono : N.MonoWeight w) {V : ℝ} (hV : 0 < V) (c : S → ℕ) (r : N.R) :
    N.stochasticMassActionRate (N.volumeScale κ V hV) c r * N.dw w r ≤
      (κ.k r * max (N.dw w r) 0) * (V + wInv w * wt w c) := by
  have hX := sum_coord_le hw c
  rcases lt_or_ge 0 (N.dw w r) with hpos | hnp
  · rw [max_eq_left hpos.le]
    have h1 := N.rate_le_of_srcMol_le_one κ hV c (hmono r hpos)
    have h2 : κ.k r * (V + ∑ s, (c s : ℝ)) ≤ κ.k r * (V + wInv w * wt w c) :=
      mul_le_mul_of_nonneg_left (by linarith) (κ.positive r).le
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hpos.le
    linarith
  · have h1 : N.stochasticMassActionRate (N.volumeScale κ V hV) c r * N.dw w r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (N.stochasticMassActionRate_nonneg _ c r) hnp
    have h2 : 0 ≤ (κ.k r * max (N.dw w r) 0) * (V + wInv w * wt w c) :=
      mul_nonneg (mul_nonneg (κ.positive r).le (le_max_right _ _))
        (add_nonneg hV.le (mul_nonneg (wInv_nonneg hw) (wt_nonneg hw c)))
    linarith

/-- The weighted drift is at most `K₀ (V + ⟨1/w⟩ u)`. -/
theorem sum_rate_mul_dw_le (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (hmono : N.MonoWeight w) {V : ℝ} (hV : 0 < V) (c : S → ℕ) :
    ∑ r, N.stochasticMassActionRate (N.volumeScale κ V hV) c r * N.dw w r ≤
      N.inRate κ w * (V + wInv w * wt w c) := by
  rw [inRate, Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ => N.rate_mul_dw_le κ hw hmono hV c r

/-- The moment constant. -/
noncomputable def momConst (N : Network S) (κ : RateConstants N) (w : S → ℝ) : ℝ :=
  4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * N.inRate κ w

theorem momConst_nonneg (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) : 0 ≤ N.momConst κ w := by
  unfold momConst
  have := N.dwMax_nonneg w
  have := N.inRate_nonneg κ w
  have := wInv_nonneg hw
  positivity

/-- **Linear drift of the fourth moment of `1 + u/V`.** -/
theorem drift_moment_le (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (hmono : N.MonoWeight w) {V : ℝ} (hV : 1 ≤ V) (c : S → ℕ) :
    (N.jumpSystem (N.volumeScale κ V (by linarith))).drift (fun b => (1 + wt w b / V) ^ 4) c ≤
      N.momConst κ w * (1 + wt w c / V) ^ 4 := by
  have hV0 : 0 < V := by linarith
  set y := 1 + wt w c / V with hy
  have hy1 : 1 ≤ y := by
    have := div_nonneg (wt_nonneg hw c) hV0.le; linarith
  have hWi := wInv_nonneg hw
  have hterm : ∀ r : N.R,
      N.stochasticMassActionRate (N.volumeScale κ V hV0) c r *
          ((1 + wt w (N.jumpNextCount c r) / V) ^ 4 - y ^ 4) ≤
        4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * (κ.k r * max (N.dw w r) 0) * y ^ 4 := by
    intro r
    set lam := N.stochasticMassActionRate (N.volumeScale κ V hV0) c r with hlam
    have hlam0 : 0 ≤ lam := N.stochasticMassActionRate_nonneg _ c r
    have hrhs0 : 0 ≤ 4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * (κ.k r * max (N.dw w r) 0) *
        y ^ 4 := by
      have := N.dwMax_nonneg w
      have := (κ.positive r).le
      positivity
    rcases hlam0.eq_or_lt with hl | hl
    · rw [← hl, zero_mul]; exact hrhs0
    · rw [N.wt_jumpNextCount _ w hl]
      set d := N.dw w r / V with hd
      have hnext : 1 + (wt w c + N.dw w r) / V = y + d := by rw [hy, hd]; ring
      rw [hnext]
      have hyd0 : 0 ≤ y + d := by
        rw [← hnext]
        have := div_nonneg (wt_nonneg hw (N.jumpNextCount c r)) hV0.le
        rw [N.wt_jumpNextCount _ w hl] at this
        linarith
      rcases lt_or_ge 0 (N.dw w r) with hpos | hnp
      · rw [max_eq_left hpos.le]
        have hd0 : 0 < d := div_pos hpos hV0
        have hdle : d ≤ N.dwMax w := by
          rw [hd, div_le_iff₀ hV0]
          have := (abs_le.mp (N.abs_dw_le w r)).2
          nlinarith [N.dwMax_nonneg w]
        have hdiff : (y + d) ^ 4 - y ^ 4 ≤ 4 * d * (y + d) ^ 3 := by
          nlinarith [sq_nonneg y, sq_nonneg (y + d), mul_pos hd0 hd0, hyd0,
            mul_nonneg hd0.le (sq_nonneg y), mul_nonneg hd0.le (sq_nonneg (y + d))]
        have hyd : y + d ≤ (1 + N.dwMax w) * y := by nlinarith [N.dwMax_nonneg w]
        have h3 : (y + d) ^ 3 ≤ (1 + N.dwMax w) ^ 3 * y ^ 3 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ hyd0 hyd 3
        have hy3 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (show 3 ≤ 4 by norm_num)
        -- `λ d ≤ κ ⟨w, Δ⟩ (1 + ⟨1/w⟩) y`
        have hlamd : lam * d ≤ κ.k r * N.dw w r * ((1 + wInv w) * y) := by
          have h1 := N.rate_mul_dw_le κ hw hmono hV0 c r
          rw [max_eq_left hpos.le] at h1
          have h2 : lam * d = lam * N.dw w r / V := by rw [hd]; ring
          rw [h2, div_le_iff₀ hV0]
          have h4 : V + wInv w * wt w c ≤ (1 + wInv w) * y * V := by
            have e : (1 + wInv w) * y * V = (1 + wInv w) * (V + wt w c) := by
              rw [hy]; field_simp
            rw [e]
            have := wt_nonneg hw c
            nlinarith
          have hk := mul_nonneg (κ.positive r).le hpos.le
          calc lam * N.dw w r ≤ κ.k r * N.dw w r * (V + wInv w * wt w c) := h1
            _ ≤ κ.k r * N.dw w r * ((1 + wInv w) * y * V) := mul_le_mul_of_nonneg_left h4 hk
            _ = κ.k r * N.dw w r * ((1 + wInv w) * y) * V := by ring
        have hk := mul_nonneg (κ.positive r).le hpos.le
        have hP3 : 0 ≤ (y + d) ^ 3 := by positivity
        calc lam * ((y + d) ^ 4 - y ^ 4) ≤ lam * (4 * d * (y + d) ^ 3) :=
              mul_le_mul_of_nonneg_left hdiff hlam0
          _ = 4 * (lam * d) * (y + d) ^ 3 := by ring
          _ ≤ 4 * (κ.k r * N.dw w r * ((1 + wInv w) * y)) * (y + d) ^ 3 := by
              apply mul_le_mul_of_nonneg_right _ hP3
              linarith
          _ ≤ 4 * (κ.k r * N.dw w r * ((1 + wInv w) * y)) * ((1 + N.dwMax w) ^ 3 * y ^ 3) := by
              apply mul_le_mul_of_nonneg_left h3
              have := le_trans zero_le_one hy1
              positivity
          _ = 4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * (κ.k r * N.dw w r) * (y * y ^ 3) := by ring
          _ ≤ 4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * (κ.k r * N.dw w r) * y ^ 4 := by
              apply mul_le_mul_of_nonneg_left _ (by have := N.dwMax_nonneg w; positivity)
              rw [← pow_succ']
      · have hd0 : d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnp hV0.le
        have hle : (y + d) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hyd0 (by linarith) 4
        have : lam * ((y + d) ^ 4 - y ^ 4) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam0 (by linarith)
        linarith
  unfold JumpSystem.drift
  calc ∑ i, (N.jumpSystem (N.volumeScale κ V _)).rate i c *
        ((fun b => (1 + wt w b / V) ^ 4) ((N.jumpSystem (N.volumeScale κ V _)).next i c) -
          (fun b => (1 + wt w b / V) ^ 4) c)
      ≤ ∑ r : N.R, 4 * (1 + N.dwMax w) ^ 3 * (1 + wInv w) * (κ.k r * max (N.dw w r) 0) * y ^ 4 :=
        Finset.sum_le_sum fun r _ => hterm r
    _ = N.momConst κ w * y ^ 4 := by
        rw [momConst, inRate, ← Finset.sum_mul, ← Finset.mul_sum]

/-! ## Level sets and the frozen chain -/

/-- The finite set `{c : ⟨w, c⟩ ≤ B}`. -/
noncomputable def levelSet (w : S → ℝ) (B : ℝ) : Finset (S → ℕ) := by
  classical
  exact (Fintype.piFinset fun s => Finset.range (⌈B / w s⌉₊ + 1)).filter (fun c => wt w c ≤ B)

theorem mem_levelSet {w : S → ℝ} (hw : ∀ s, 0 < w s) {B : ℝ} {c : S → ℕ} :
    c ∈ levelSet w B ↔ wt w c ≤ B := by
  classical
  unfold levelSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro s
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have h1 : w s * (c s : ℝ) ≤ B := le_trans (Finset.single_le_sum
    (f := fun s => w s * (c s : ℝ)) (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _))
    (Finset.mem_univ s)) h
  have h2 : (c s : ℝ) ≤ B / w s := by rw [le_div_iff₀ (hw s)]; linarith
  exact_mod_cast h2.trans (Nat.le_ceil _)

/-- Coordinates are bounded on a level set. -/
theorem coord_le_of_wt_le {w : S → ℝ} (hw : ∀ s, 0 < w s) {R V : ℝ} (hR : 0 ≤ R) (hV : 0 < V)
    {c : S → ℕ} (hc : wt w c ≤ R * V) (s : S) : (c s : ℝ) ≤ (∑ s, R / w s) * V := by
  have h1 : w s * (c s : ℝ) ≤ R * V := le_trans (Finset.single_le_sum
    (f := fun s => w s * (c s : ℝ)) (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _))
    (Finset.mem_univ s)) hc
  have h2 : (c s : ℝ) ≤ R / w s * V := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (hw s)]; linarith
  have h3 : R / w s ≤ ∑ s, R / w s := Finset.single_le_sum (f := fun s => R / w s)
    (fun s _ => div_nonneg hR (hw s).le) (Finset.mem_univ s)
  exact h2.trans (mul_le_mul_of_nonneg_right h3 hV.le)

end Network

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

theorem drift_stopOutside (K : Finset α) (g : α → ℝ) (a : α) :
    (J.stopOutside K).drift g a = if a ∈ K then J.drift g a else 0 := by
  unfold drift stopOutside
  split_ifs with h
  · simp [h]
  · simp [h]

theorem q_stopOutside_le (K : Finset α) (a : α) : (J.stopOutside K).q a ≤ J.q a := by
  unfold q
  refine Finset.sum_le_sum fun i _ => ?_
  show (if a ∈ K then J.rate i a else 0) ≤ J.rate i a
  split_ifs
  · exact le_rfl
  · exact J.rate_nonneg i a

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reachable counts of the frozen chain stay below `R V + max |Δw|`. -/
theorem wt_le_of_reachPos_stop (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) {V : ℝ} (hV : 0 < V) {B : ℝ} {n c : S → ℕ} (hn : wt w n ≤ B)
    (h : ((N.jumpSystem (N.volumeScale κ V hV)).stopOutside (levelSet w B)).ReachPos n c) :
    wt w c ≤ B + N.dwMax w := by
  induction h with
  | refl => linarith [N.dwMax_nonneg w]
  | @tail x y _ hxy _ =>
      obtain ⟨r, hr, rfl⟩ := hxy
      have hx : x ∈ levelSet w B := by
        by_contra hx
        simp [JumpSystem.stopOutside, hx] at hr
      have hr' : 0 < N.stochasticMassActionRate (N.volumeScale κ V hV) x r := by
        have : 0 < (N.jumpSystem (N.volumeScale κ V hV)).rate r x := by
          simpa [JumpSystem.stopOutside, hx] using hr
        exact this
      show wt w (N.jumpNextCount x r) ≤ _
      rw [N.wt_jumpNextCount _ w hr']
      have := (abs_le.mp (N.abs_dw_le w r)).2
      have := (mem_levelSet hw).mp hx
      linarith

/-- The bound on `∑_r ρ_r` over counts with `c/V ≤ R₁`. -/
noncomputable def rhoMax (N : Network S) (κ : RateConstants N) (R₁ : ℝ) : ℝ :=
  ∑ r, κ.k r * ((R₁ + N.srcMol r + 1) ^ N.srcMol r) ^ Fintype.card S

/-- The frozen-chain constant. -/
noncomputable def psiConst (N : Network S) (κ : RateConstants N) (w : S → ℝ) (R : ℝ) : ℝ :=
  N.dwMax w ^ 2 * N.rhoMax κ (∑ s, R / w s)

theorem psiConst_nonneg (N : Network S) (κ : RateConstants N) (w : S → ℝ) {R : ℝ}
    (hw : ∀ s, 0 < w s) (hR : 0 ≤ R) : 0 ≤ N.psiConst κ w R := by
  unfold psiConst rhoMax
  have hR₁ : 0 ≤ ∑ s, R / w s := Finset.sum_nonneg fun s _ => div_nonneg hR (hw s).le
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun r _ => mul_nonneg (κ.positive r).le ?_)
  positivity

/-- The observable `((u/V − A)⁺)²`. -/
noncomputable def psiObs (w : S → ℝ) (V A : ℝ) (b : S → ℕ) : ℝ :=
  (max (wt w b / V - A) 0) ^ 2

/-- The moving level `a(τ) = (M + 1) e^{K τ} − 1`. -/
noncomputable def aFun (M K τ : ℝ) : ℝ := (M + 1) * Real.exp (K * τ) - 1

theorem aFun_zero (M K : ℝ) : aFun M K 0 = M := by simp [aFun]

theorem aFun_nonneg {M K τ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hτ : 0 ≤ τ) : 0 ≤ aFun M K τ := by
  unfold aFun
  have : 1 ≤ Real.exp (K * τ) := Real.one_le_exp (mul_nonneg hK hτ)
  nlinarith

theorem aFun_mono {M K τ T : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (h : τ ≤ T) :
    aFun M K τ ≤ aFun M K T := by
  unfold aFun
  have : Real.exp (K * τ) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hK)
  nlinarith

theorem max_mul_self (z : ℝ) : max z 0 * z = (max z 0) ^ 2 := by
  rcases le_total z 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h]; ring

/-- **Drift of the one-sided observable.** On `{u ≤ R V}`, with `z = u/V − A`,
`drift ψ ≤ 2 z⁺ K₀ (1 + ⟨1/w⟩ A) + 2 K₀ ⟨1/w⟩ (z⁺)² + C/V`. -/
theorem drift_psiObs_le (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (hmono : N.MonoWeight w) {V R A : ℝ} (hV : 1 ≤ V) (hR : 0 ≤ R)
    {c : S → ℕ} (hc : wt w c ≤ R * V) :
    (N.jumpSystem (N.volumeScale κ V (by linarith))).drift (psiObs w V A) c ≤
      2 * max (wt w c / V - A) 0 * (N.inRate κ w * (1 + wInv w * A)) +
        2 * (N.inRate κ w * wInv w) * (max (wt w c / V - A) 0) ^ 2 + N.psiConst κ w R / V := by
  have hV0 : 0 < V := by linarith
  set K₀ := N.inRate κ w with hK₀
  set z := wt w c / V - A with hz
  set R₁ := ∑ s, R / w s with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun s _ => div_nonneg hR (hw s).le
  have hcR : ∀ s, (c s : ℝ) ≤ R₁ * V := coord_le_of_wt_le hw hR hV0 hc
  have hzp : 0 ≤ max z 0 := le_max_right _ _
  have hterm : ∀ r : N.R,
      N.stochasticMassActionRate (N.volumeScale κ V hV0) c r *
          (psiObs w V A (N.jumpNextCount c r) - psiObs w V A c) ≤
        2 * max z 0 / V * (N.stochasticMassActionRate (N.volumeScale κ V hV0) c r * N.dw w r) +
          N.densRate κ V r c * N.dwMax w ^ 2 / V := by
    intro r
    set lam := N.stochasticMassActionRate (N.volumeScale κ V hV0) c r with hlam
    have hlam0 : 0 ≤ lam := N.stochasticMassActionRate_nonneg _ c r
    have hlamV : lam = V * N.densRate κ V r c := stochasticRate_volumeScale N κ hV0 c r
    have hdw2 : N.dw w r ^ 2 ≤ N.dwMax w ^ 2 := by
      have := N.abs_dw_le w r
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rcases hlam0.eq_or_lt with hl | hl
    · rw [← hl, zero_mul, zero_mul, mul_zero, zero_add]
      have := N.densRate_nonneg κ hV0 r c
      positivity
    · have hnext : psiObs w V A (N.jumpNextCount c r) = (max (z + N.dw w r / V) 0) ^ 2 := by
        unfold psiObs
        rw [N.wt_jumpNextCount _ w hl, hz]
        congr 2
        ring
      have hcur : psiObs w V A c = (max z 0) ^ 2 := rfl
      rw [hnext, hcur]
      have h1 := posPart_sq_add_le z (N.dw w r / V)
      have h2 : lam * ((max (z + N.dw w r / V) 0) ^ 2 - (max z 0) ^ 2) ≤
          lam * (2 * max z 0 * (N.dw w r / V) + (N.dw w r / V) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0
      have h3 : lam * (N.dw w r / V) ^ 2 ≤ N.densRate κ V r c * N.dwMax w ^ 2 / V := by
        rw [hlamV, div_pow]
        have hρ := N.densRate_nonneg κ hV0 r c
        rw [show V * N.densRate κ V r c * (N.dw w r ^ 2 / V ^ 2) =
            N.densRate κ V r c * N.dw w r ^ 2 / V by field_simp]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdw2 hρ) hV0.le
      have h4 : lam * (2 * max z 0 * (N.dw w r / V)) = 2 * max z 0 / V * (lam * N.dw w r) := by
        field_simp
      nlinarith
  have hsum : (N.jumpSystem (N.volumeScale κ V hV0)).drift (psiObs w V A) c ≤
      2 * max z 0 / V * (K₀ * (V + wInv w * wt w c)) + N.rhoMax κ R₁ * N.dwMax w ^ 2 / V := by
    unfold JumpSystem.drift
    calc ∑ i, (N.jumpSystem (N.volumeScale κ V hV0)).rate i c *
          (psiObs w V A ((N.jumpSystem (N.volumeScale κ V hV0)).next i c) - psiObs w V A c)
        ≤ ∑ r : N.R, (2 * max z 0 / V *
            (N.stochasticMassActionRate (N.volumeScale κ V hV0) c r * N.dw w r) +
              N.densRate κ V r c * N.dwMax w ^ 2 / V) :=
          Finset.sum_le_sum fun r _ => hterm r
      _ = 2 * max z 0 / V *
            ∑ r, N.stochasticMassActionRate (N.volumeScale κ V hV0) c r * N.dw w r +
          (∑ r, N.densRate κ V r c) * N.dwMax w ^ 2 / V := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [mul_div_assoc, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ ≤ 2 * max z 0 / V * (K₀ * (V + wInv w * wt w c)) +
            N.rhoMax κ R₁ * N.dwMax w ^ 2 / V := by
          have hA := N.sum_rate_mul_dw_le κ hw hmono hV0 c
          have hB : ∑ r, N.densRate κ V r c ≤ N.rhoMax κ R₁ :=
            Finset.sum_le_sum fun r _ => N.densRate_le κ r hV hR₁0 c hcR
          have hc1 : 0 ≤ 2 * max z 0 / V := by positivity
          have hc2 : 0 ≤ N.dwMax w ^ 2 / V := by positivity
          have e1 := mul_le_mul_of_nonneg_left hA hc1
          have e2 := mul_le_mul_of_nonneg_right hB hc2
          have e3 : (∑ r, N.densRate κ V r c) * N.dwMax w ^ 2 / V =
              (∑ r, N.densRate κ V r c) * (N.dwMax w ^ 2 / V) := by ring
          have e4 : N.rhoMax κ R₁ * N.dwMax w ^ 2 / V = N.rhoMax κ R₁ * (N.dwMax w ^ 2 / V) := by
            ring
          rw [e3, e4]
          linarith
  have hfin : 2 * max z 0 / V * (K₀ * (V + wInv w * wt w c)) =
      2 * max z 0 * (K₀ * (1 + wInv w * A)) + 2 * (K₀ * wInv w) * (max z 0 * z) := by
    have hu : wt w c = (z + A) * V := by rw [hz]; field_simp; ring
    rw [hu]
    field_simp
    ring
  rw [hfin, max_mul_self] at hsum
  have : N.psiConst κ w R / V = N.rhoMax κ R₁ * N.dwMax w ^ 2 / V := by
    rw [psiConst, mul_comm]
  rw [this]
  exact hsum

theorem hasDerivAt_psiObs (w : S → ℝ) (V M K : ℝ) (b : S → ℕ) (t : ℝ) :
    HasDerivAt (fun τ => psiObs w V (aFun M K τ) b)
      (2 * max (wt w b / V - aFun M K t) 0 * -((M + 1) * K * Real.exp (K * t))) t := by
  have h1 : HasDerivAt (fun τ : ℝ => wt w b / V - aFun M K τ)
      (-((M + 1) * K * Real.exp (K * t))) t := by
    have he : HasDerivAt (fun τ : ℝ => Real.exp (K * τ)) (Real.exp (K * t) * K) t := by
      simpa using ((hasDerivAt_id t).const_mul K).exp
    have h2 := ((he.const_mul (M + 1)).sub_const 1).const_sub (wt w b / V)
    have e : (-((M + 1) * K * Real.exp (K * t))) = -((M + 1) * (Real.exp (K * t) * K)) := by ring
    rw [e]
    exact h2
  exact (hasDerivAt_posPart_sq _).comp t h1

theorem continuous_psiObs (w : S → ℝ) (V M K : ℝ) (b : S → ℕ) :
    Continuous fun τ => psiObs w V (aFun M K τ) b := by
  unfold psiObs aFun
  fun_prop

/-- The data of the frozen chain started at `n`. -/
theorem frozen_setup (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    {V : ℝ} (hV : 0 < V) {B : ℝ} {n : S → ℕ} (hn : wt w n ≤ B) :
    let Js := (N.jumpSystem (N.volumeScale κ V hV)).stopOutside (levelSet w B)
    (∀ τ, ∀ b, b ∉ levelSet w (B + N.dwMax w) → Js.Pmin τ n b = 0) ∧
    (∀ c ∈ levelSet w (B + N.dwMax w), ∀ i, 0 < Js.rate i c →
      Js.next i c ∈ levelSet w (B + N.dwMax w)) ∧
    n ∈ levelSet w (B + N.dwMax w) := by
  intro Js
  refine ⟨fun τ b hb => ?_, fun c _ i hi => ?_, ?_⟩
  · refine JumpSystem.Pmin_eq_zero_of_not_reachPos _ τ fun h => hb ?_
    exact (mem_levelSet hw).mpr (N.wt_le_of_reachPos_stop κ hw hV hn h)
  · have hcK : c ∈ levelSet w B := by
      by_contra hcK
      simp [Js, JumpSystem.stopOutside, hcK] at hi
    have hi' : 0 < N.stochasticMassActionRate (N.volumeScale κ V hV) c i := by
      have : 0 < (N.jumpSystem (N.volumeScale κ V hV)).rate i c := by
        simpa [Js, JumpSystem.stopOutside, hcK] using hi
      exact this
    rw [mem_levelSet hw]
    show wt w (N.jumpNextCount c i) ≤ _
    rw [N.wt_jumpNextCount _ w hi']
    have := (abs_le.mp (N.abs_dw_le w i)).2
    have := (mem_levelSet hw).mp hcK
    linarith
  · rw [mem_levelSet hw]; linarith [N.dwMax_nonneg w]

/-- The growth rate of the moving level. -/
noncomputable def levelRate (N : Network S) (κ : RateConstants N) (w : S → ℝ) : ℝ :=
  N.inRate κ w * (1 + wInv w)

/-- The Grönwall rate of the one-sided observable. -/
noncomputable def psiRate (N : Network S) (κ : RateConstants N) (w : S → ℝ) : ℝ :=
  1 + 2 * (N.inRate κ w * wInv w)

/-- **The frozen mass is `O(1/V)`.** -/
theorem frozen_mass_le (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hmono : N.MonoWeight w) {M T R V : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hR : (M + 1) * Real.exp (N.levelRate κ w * T) ≤ R) (hV : 1 ≤ V) {n : S → ℕ}
    (hn : wt w n ≤ M * V) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∑ b ∈ (levelSet w (R * V + N.dwMax w)).filter (fun b => b ∉ levelSet w (R * V)),
        ((N.jumpSystem (N.volumeScale κ V (by linarith))).stopOutside
          (levelSet w (R * V))).Pmin t n b ≤
      N.psiConst κ w R * Real.exp (N.psiRate κ w * T) / V := by
  classical
  have hV0 : 0 < V := by linarith
  set K₀ := N.inRate κ w with hK₀
  have hK₀0 : 0 ≤ K₀ := N.inRate_nonneg κ w
  have hWi := wInv_nonneg hw
  set K := N.levelRate κ w with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hK₀0 (by linarith)
  set Kψ := N.psiRate κ w with hKψ
  have hKψ1 : 1 ≤ Kψ := by
    have : 0 ≤ 2 * (K₀ * wInv w) := by positivity
    simp only [hKψ, psiRate]; linarith
  have hexp1 : 1 ≤ Real.exp (K * T) := Real.one_le_exp (mul_nonneg hK0 hT)
  have hR1 : M + 1 ≤ R := le_trans (le_mul_of_one_le_right (by linarith) hexp1) hR
  have hR0 : 0 ≤ R := by linarith
  have hnR : wt w n ≤ R * V := le_trans hn (mul_le_mul_of_nonneg_right (by linarith) hV0.le)
  set Kset := levelSet w (R * V) with hKset
  set Rset := levelSet w (R * V + N.dwMax w) with hRset
  set Js := (N.jumpSystem (N.volumeScale κ V hV0)).stopOutside Kset with hJs
  obtain ⟨hsupp, hclosed, hnRs⟩ := N.frozen_setup κ hw hV0 hnR
  set C := N.psiConst κ w R with hC
  have hC0 : 0 ≤ C := N.psiConst_nonneg κ w hw hR0
  set ψ : ℝ → (S → ℕ) → ℝ := fun τ b => psiObs w V (aFun M K τ) b with hψ
  set D : ℝ → ℝ := fun τ => ∑ b ∈ Rset, Js.Pmin τ n b * ψ τ b with hD
  set g' : ℝ → (S → ℕ) → ℝ := fun τ b =>
    2 * max (wt w b / V - aFun M K τ) 0 * -((M + 1) * K * Real.exp (K * τ)) with hg'
  have hDder : ∀ τ ∈ Ioo 0 T, HasDerivAt D
      (∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (ψ τ) c + g' τ c)) τ := by
    intro τ hτ
    exact Js.hasDerivAt_sum_finite n Rset hsupp hclosed ψ g' hτ.1
      fun b _ => hasDerivAt_psiObs w V M K b τ
  have hpt : ∀ τ, 0 ≤ τ → ∀ c ∈ Rset, Js.drift (ψ τ) c + g' τ c ≤ Kψ * ψ τ c + C / V := by
    intro τ hτ c _
    have hψ0 : 0 ≤ ψ τ c := sq_nonneg _
    have ha0 := aFun_nonneg hM hK0 hτ
    have hzp : 0 ≤ max (wt w c / V - aFun M K τ) 0 := le_max_right _ _
    have hcancel : (M + 1) * K * Real.exp (K * τ) = K * (aFun M K τ + 1) := by
      unfold aFun; ring
    rw [JumpSystem.drift_stopOutside]
    split_ifs with hcK
    · have h := N.drift_psiObs_le κ hw hmono (A := aFun M K τ) hV hR0
        ((mem_levelSet hw).mp hcK)
      have hlev : K₀ * (1 + wInv w * aFun M K τ) ≤ K * (aFun M K τ + 1) := by
        set A := aFun M K τ with hA
        have hKe : K = K₀ * (1 + wInv w) := rfl
        rw [hKe]
        nlinarith [mul_nonneg hK₀0 (add_nonneg ha0 hWi)]
      have e1 : 2 * max (wt w c / V - aFun M K τ) 0 * (K₀ * (1 + wInv w * aFun M K τ)) ≤
          2 * max (wt w c / V - aFun M K τ) 0 * (K * (aFun M K τ + 1)) :=
        mul_le_mul_of_nonneg_left hlev (by positivity)
      have e2 : 2 * (K₀ * wInv w) * ψ τ c ≤ Kψ * ψ τ c := by
        apply mul_le_mul_of_nonneg_right _ hψ0
        simp only [hKψ, psiRate]; linarith
      simp only [hg', hcancel]
      have : ψ τ c = (max (wt w c / V - aFun M K τ) 0) ^ 2 := rfl
      rw [this] at e2 ⊢
      linarith
    · have : g' τ c ≤ 0 := by
        simp only [hg']
        have : 0 ≤ (M + 1) * K * Real.exp (K * τ) := by
          have := Real.exp_pos (K * τ); positivity
        nlinarith
      have : 0 ≤ C / V := div_nonneg hC0 hV0.le
      have : 0 ≤ Kψ * ψ τ c := mul_nonneg (by linarith) hψ0
      linarith
  have hD0 : ∀ τ, 0 ≤ τ → 0 ≤ D τ := fun τ hτ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (Js.Pmin_nonneg τ hτ n b) (sq_nonneg _)
  have hbound : ∀ τ ∈ Ioo 0 T,
      ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (ψ τ) c + g' τ c) ≤ Kψ * D τ + C / V := by
    intro τ hτ
    calc ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (ψ τ) c + g' τ c)
        ≤ ∑ c ∈ Rset, Js.Pmin τ n c * (Kψ * ψ τ c + C / V) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hpt τ hτ.1.le c hc)
            (Js.Pmin_nonneg τ hτ.1.le n c)
      _ = Kψ * D τ + (C / V) * ∑ c ∈ Rset, Js.Pmin τ n c := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ Kψ * D τ + C / V := by
          have h1 := Js.sum_Pmin_le_one τ hτ.1.le n Rset
          have h2 : 0 ≤ C / V := div_nonneg hC0 hV0.le
          nlinarith
  have hDc : ContinuousOn D (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    exact ((Js.continuousOn_Pmin n b).mono fun τ hτ => hτ.1).mul
      (continuous_psiObs w V M K b).continuousOn
  have hDat0 : D 0 = 0 := by
    simp only [hD, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun h => absurd hnRs h)]
    simp only [if_true, one_mul, hψ, psiObs, aFun_zero]
    have : wt w n / V - M ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ hV0]; exact hn
    rw [max_eq_right this]; ring
  have hKψne : Kψ ≠ 0 := by linarith
  have hgr := le_gronwallBound_of_hasDerivAt_Ioo hKψne hDc hDder hbound ht
  rw [hDat0, gronwallBound_of_K_ne_0 hKψne] at hgr
  have hDt : D t ≤ C / V * Real.exp (Kψ * T) := by
    have h1 : Real.exp (Kψ * t) ≤ Real.exp (Kψ * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))
    have h2 : 0 ≤ C / V := div_nonneg hC0 hV0.le
    have h3 : 0 ≤ Real.exp (Kψ * t) := (Real.exp_pos _).le
    have h4 : C / V / Kψ ≤ C / V := div_le_self h2 hKψ1
    have h5 : 0 ≤ C / V / Kψ := div_nonneg h2 (by linarith)
    have h6 : 1 ≤ Real.exp (Kψ * t) := Real.one_le_exp (mul_nonneg (by linarith) ht.1)
    nlinarith
  have hQ : ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin t n b ≤ D t := by
    calc ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin t n b
        ≤ ∑ b ∈ Rset.filter (fun b => b ∉ Kset), Js.Pmin t n b * ψ t b := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbK : b ∉ Kset := (Finset.mem_filter.mp hb).2
          have hwb : R * V < wt w b := by
            by_contra h; push Not at h; exact hbK ((mem_levelSet hw).mpr h)
          have haT : aFun M K t ≤ R - 1 := by
            have := aFun_mono hM hK0 ht.2 (T := T)
            unfold aFun at this ⊢
            linarith
          have hz : 1 ≤ wt w b / V - aFun M K t := by
            have h1 : R < wt w b / V := by rw [lt_div_iff₀ hV0]; linarith
            linarith
          have hpsi : 1 ≤ ψ t b := by
            simp only [hψ, psiObs]
            rw [max_eq_left (by linarith)]
            nlinarith
          have hP := Js.Pmin_nonneg t ht.1 n b
          nlinarith
      _ ≤ D t := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun b _ _ => mul_nonneg (Js.Pmin_nonneg t ht.1 n b) (sq_nonneg _)
  calc _ ≤ D t := hQ
    _ ≤ C / V * Real.exp (Kψ * T) := hDt
    _ = C * Real.exp (Kψ * T) / V := by ring

set_option maxHeartbeats 1000000 in
/-- **Grönwall for the frozen chain.** -/
theorem frozen_dist_le (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hmono : N.MonoWeight w) {M T R Rx : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hR : (M + 1) * Real.exp (N.levelRate κ w * T) ≤ R)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ), wt w n ≤ M * V →
      ∀ t ∈ Icc 0 T,
        ∑ b ∈ levelSet w (R * V + N.dwMax w),
          ((N.jumpSystem (N.volumeScale κ V (by linarith))).stopOutside
            (levelSet w (R * V))).Pmin t n b * ∑ s, ((b s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := by
  classical
  have hexp1 : 1 ≤ Real.exp (N.levelRate κ w * T) := Real.one_le_exp (mul_nonneg
    (mul_nonneg (N.inRate_nonneg κ w) (by linarith [wInv_nonneg hw])) hT)
  have hR1 : M + 1 ≤ R := le_trans (le_mul_of_one_le_right (by linarith) hexp1) hR
  have hR0 : 0 ≤ R := by linarith
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
  set C₁ := 1 + 2 * (Fintype.card S : ℝ) * L with hC₁
  set C₂b := (Fintype.card S : ℝ) * N.rateErr κ R₁ ^ 2 + N.noiseConst κ R₁ with hC₂b
  set C₂ := C₂b + max F2 0 * (N.psiConst κ w R * Real.exp (N.psiRate κ w * T)) with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₁1 : 1 ≤ C₁ := by
    have : (0 : ℝ) ≤ 2 * Fintype.card S * L := by positivity
    linarith
  have hC₂b0 : 0 ≤ C₂b := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg
      (mul_nonneg (κ.positive r).le (by positivity)) (Finset.sum_nonneg fun s _ => sq_nonneg _))
  have hψ0 := N.psiConst_nonneg κ w hw hR0
  have hC₂0 : 0 ≤ C₂ := add_nonneg hC₂b0 (mul_nonneg (le_max_right _ _)
    (mul_nonneg hψ0 (Real.exp_pos _).le))
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun V hV n hn t ht => ?_⟩
  have hV0 : 0 < V := by linarith
  have hnR : wt w n ≤ R * V := le_trans hn (mul_le_mul_of_nonneg_right (by linarith) hV0.le)
  set K := levelSet w (R * V) with hK
  set Rset := levelSet w (R * V + N.dwMax w) with hRset
  set Js := (N.jumpSystem (N.volumeScale κ V hV0)).stopOutside K with hJs
  obtain ⟨hsupp, hclosed, hnRs⟩ := N.frozen_setup κ hw hV0 hnR
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
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
  have hpt : ∀ τ ∈ Ioo 0 T, ∀ c ∈ Rset, Js.drift (g τ) c + g' τ c ≤
      C₁ * g τ c + C₂b / V + (if c ∈ K then 0 else max F2 0) := by
    intro τ hτ c _
    have hxτB : x τ ∈ Icc (0 : Concentration S) fun _ => Rb := by
      obtain ⟨h1, h2⟩ := hxB τ (Ioo_subset_Icc_self hτ)
      exact ⟨h1, fun s => (h2 s).trans (le_max_right _ _)⟩
    rw [JumpSystem.drift_stopOutside]
    split_ifs with hcK
    · have := N.drift_dist_sq_le κ hV hR₁0 (le_max_left _ _) hL c
        (coord_le_of_wt_le hw hR0 hV0 ((mem_levelSet hw).mp hcK)) (x τ) hxτB
      rw [add_zero]
      exact this
    · have hg0 : 0 ≤ g τ c := Finset.sum_nonneg fun s _ => sq_nonneg _
      have hgg : g' τ c ≤ g τ c + ∑ s, N.massActionVectorField κ (x τ) s ^ 2 := by
        simp only [hg', hg, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun s _ => ?_
        nlinarith [sq_nonneg ((c s : ℝ) / V - x τ s + N.massActionVectorField κ (x τ) s)]
      have hF := hF2' (x τ) hxτB
      have : 0 ≤ C₂b / V := div_nonneg hC₂b0 hV0.le
      have hCg : g τ c ≤ C₁ * g τ c := by nlinarith
      linarith
  have hbound : ∀ τ ∈ Ioo 0 T,
      ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (g τ) c + g' τ c) ≤ C₁ * D τ + C₂ / V := by
    intro τ hτ
    have hQ := N.frozen_mass_le κ hw hmono hM hT hR hV hn (Ioo_subset_Icc_self hτ)
    calc ∑ c ∈ Rset, Js.Pmin τ n c * (Js.drift (g τ) c + g' τ c)
        ≤ ∑ c ∈ Rset, Js.Pmin τ n c *
            (C₁ * g τ c + C₂b / V + (if c ∈ K then 0 else max F2 0)) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hpt τ hτ c hc)
            (Js.Pmin_nonneg τ hτ.1.le n c)
      _ = C₁ * D τ + C₂b / V * ∑ c ∈ Rset, Js.Pmin τ n c +
            max F2 0 * ∑ c ∈ Rset.filter (fun c => c ∉ K), Js.Pmin τ n c := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
          · rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
      _ ≤ C₁ * D τ + C₂b / V + max F2 0 * (N.psiConst κ w R * Real.exp (N.psiRate κ w * T) / V) := by
          have h1 := Js.sum_Pmin_le_one τ hτ.1.le n Rset
          have h2 : 0 ≤ C₂b / V := div_nonneg hC₂b0 hV0.le
          have h3 := mul_le_mul_of_nonneg_left hQ (le_max_right F2 0)
          nlinarith
      _ = C₁ * D τ + C₂ / V := by rw [hC₂]; ring
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
  have hC₁ne : C₁ ≠ 0 := by linarith
  have := le_gronwallBound_of_hasDerivAt_Ioo hC₁ne hDc hDder hbound ht
  rwa [hD0] at this

/-- Splitting a summable series along a finite set. -/
theorem tsum_split {α : Type*} [DecidableEq α] (K : Finset α) {f : α → ℝ} (hf : Summable f) :
    ∑' b, f b = ∑ b ∈ K, f b + ∑' b, (if b ∈ K then 0 else f b) := by
  have h1 : Summable (fun b => if b ∈ K then f b else 0) :=
    summable_of_ne_finset_zero (s := K) fun b hb => if_neg hb
  have h2 : Summable (fun b => if b ∈ K then 0 else f b) :=
    (hf.sub h1).congr fun b => by split_ifs <;> simp
  have h3 : ∑ b ∈ K, f b = ∑' b, (if b ∈ K then f b else 0) := by
    rw [tsum_eq_sum (s := K) fun b hb => if_neg hb]
    exact Finset.sum_congr rfl fun b hb => (if_pos hb).symm
  rw [h3, ← h1.tsum_add h2]
  exact tsum_congr fun b => by split_ifs <;> simp

/-- `u² ≤ L² + (1 + u)⁴ / L²` for `u ≥ 0`, `L ≥ 1`. -/
theorem sq_le_split {u L : ℝ} (hu : 0 ≤ u) (hL : 1 ≤ L) : u ^ 2 ≤ L ^ 2 + (1 + u) ^ 4 / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have h4 : 0 ≤ (1 + u) ^ 4 / L ^ 2 := by positivity
  rcases le_total u L with h | h
  · have : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu h 2
    linarith
  · have h1 : u ^ 2 * L ^ 2 ≤ u ^ 4 := by nlinarith [pow_le_pow_left₀ hL0.le h 2, sq_nonneg u]
    have h2 : u ^ 4 ≤ (1 + u) ^ 4 := pow_le_pow_left₀ hu (by linarith) 4
    have : u ^ 2 ≤ (1 + u) ^ 4 / L ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [sq_nonneg L]

set_option maxHeartbeats 1600000 in
/-- **Kurtz's law of large numbers when the weight grows at most linearly, at fixed times.**
For a positive weight `w` that only reactions with at most one source molecule increase
(`MonoWeight`: inflows `0 → y` and monomolecular reactions such as `X → 2X`), a solution `x` of the
mass-action equation on `[0, T]` with values in `[0, R_x]^S`, there are constants such that for
every `V ≥ 1`, every initial count `n` with `⟨w, n⟩ ≤ M V`, every `t ∈ [0, T]` and every `L ≥ 1`,

`E_n |X^V(t)/V − x(t)|² ≤ gronwallBound (|n/V − x(0)|²) C₁ (C₂/V) t + C₃ (L²/V + 1/L²)`. -/
theorem mono_lln (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hmono : N.MonoWeight w) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      wt w n ≤ M * V → ∀ t ∈ Icc 0 T, ∀ L : ℝ, 1 ≤ L →
        ∑' m, N.transition (N.volumeScale κ V (by linarith)) t n m *
            ∑ s, ((m s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t +
            C₃ * (L ^ 2 / V + 1 / L ^ 2) := by
  classical
  set K₀ := N.inRate κ w with hK₀
  have hK₀0 : 0 ≤ K₀ := N.inRate_nonneg κ w
  set R := (M + 1) * Real.exp (N.levelRate κ w * T) with hRdef
  have hexp1 : 1 ≤ Real.exp (N.levelRate κ w * T) := Real.one_le_exp (mul_nonneg
    (mul_nonneg hK₀0 (by linarith [wInv_nonneg hw])) hT)
  have hR1 : M + 1 ≤ R := le_mul_of_one_le_right (by linarith) hexp1
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨C₁, C₂, hC₁, hC₂, hfr⟩ := N.frozen_dist_le κ hw hmono hM hT (R := R) le_rfl x hxc hx hxB
  set R₁ := ∑ s, R / w s with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun s _ => div_nonneg hR0 (hw s).le
  set CQ := N.psiConst κ w R * Real.exp (N.psiRate κ w * T) with hCQ
  have hCQ0 : 0 ≤ CQ := mul_nonneg (N.psiConst_nonneg κ w hw hR0) (Real.exp_pos _).le
  set G₀ := (Fintype.card S : ℝ) * (R₁ + Rx) ^ 2 with hG₀
  set Wi := ∑ s, (w s)⁻¹ ^ 2 with hWi
  have hWi0 : 0 ≤ Wi := Finset.sum_nonneg fun s _ => sq_nonneg _
  set X2 := 2 * (Fintype.card S : ℝ) * Rx ^ 2 with hX2
  set CM := Real.exp (N.momConst κ w * T) * (1 + M) ^ 4 with hCM
  have hCM0 : 0 ≤ CM := by positivity
  set C₃ := (G₀ + 2 * Wi + X2) * CQ + 2 * Wi * CM with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃0, fun V hV n hn t ht L hL => ?_⟩
  have hV0 : 0 < V := by linarith
  have hL0 : 0 < L := by linarith
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  set K := levelSet w (R * V) with hK
  set Rset := levelSet w (R * V + N.dwMax w) with hRset
  set Js := J.stopOutside K with hJs
  have hnR : wt w n ≤ R * V := le_trans hn (mul_le_mul_of_nonneg_right (by linarith) hV0.le)
  obtain ⟨hsupp, -, -⟩ := N.frozen_setup κ hw hV0 hnR
  set g : (S → ℕ) → ℝ := fun b => ∑ s, ((b s : ℝ) / V - x t s) ^ 2 with hg
  have hg0 : ∀ b, 0 ≤ g b := fun b => Finset.sum_nonneg fun s _ => sq_nonneg _
  set P : (S → ℕ) → ℝ := fun b => J.Pmin t n b with hP
  set P' : (S → ℕ) → ℝ := fun b => Js.Pmin t n b with hP'
  have hP0 : ∀ b, 0 ≤ P b := fun b => J.Pmin_nonneg t ht.1 n b
  have hP'0 : ∀ b, 0 ≤ P' b := fun b => Js.Pmin_nonneg t ht.1 n b
  -- stochasticity of the original chain
  have hPsum : HasSum P 1 := by
    have := N.hasSum_transition_one_of_weight κV w hw (fun r hr => hmono r hr) ht.1 n
    exact this
  -- stochasticity of the frozen chain on `Rset`
  have hreach : ∀ c, Js.ReachPos n c → c ∈ Rset := fun c h =>
    (mem_levelSet hw).mpr (N.wt_le_of_reachPos_stop κ hw hV0 hnR h)
  have hP'sum : ∑ b ∈ Rset, P' b = 1 := by
    have hΛ : ∀ c, Js.ReachPos n c → Js.q c ≤ ∑ c ∈ Rset, Js.q c := fun c hc =>
      Finset.single_le_sum (f := fun c => Js.q c) (fun c _ => Js.q_nonneg c) (hreach c hc)
    have h1 := Js.hasSum_Pmin_one hΛ ht.1
    calc ∑ b ∈ Rset, P' b = ∑' b, Js.Pmin t n b :=
          (tsum_eq_sum (s := Rset) fun b hb => hsupp t b hb).symm
      _ = 1 := h1.tsum_eq
  have hKsub : K ⊆ Rset := fun b hb => (mem_levelSet hw).mpr
    (le_trans ((mem_levelSet hw).mp hb) (by linarith [N.dwMax_nonneg w]))
  -- the frozen mass
  set Q := ∑ b ∈ Rset.filter (fun b => b ∉ K), P' b with hQdef
  have hQ : Q ≤ CQ / V := N.frozen_mass_le κ hw hmono hM hT (R := R) le_rfl hV hn ht
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun b _ => hP'0 b
  have hKP' : ∑ b ∈ K, P' b = 1 - Q := by
    have := Finset.sum_filter_add_sum_filter_not Rset (fun b => b ∈ K) P'
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hKsub, hP'sum] at this
    linarith
  have hKP : ∑ b ∈ K, P b ≤ 1 := J.sum_Pmin_le_one t ht.1 n K
  have hPP' : ∀ b ∈ K, P' b ≤ P b := fun b hb =>
    J.Pmin_stopOutside_le K ht.1 n hb
  have hdiff : ∑ b ∈ K, (P b - P' b) ≤ Q := by
    rw [Finset.sum_sub_distrib]; linarith
  -- the outer mass
  have hPs : Summable P := hPsum.summable
  have hout : ∑' b, (if b ∈ K then 0 else P b) ≤ Q := by
    have h := tsum_split K hPs
    rw [hPsum.tsum_eq] at h
    have : ∑ b ∈ K, P' b ≤ ∑ b ∈ K, P b := Finset.sum_le_sum hPP'
    linarith
  -- the fourth moment
  set Y : (S → ℕ) → ℝ := fun b => (1 + wt w b / V) ^ 4 with hY
  have hY0 : ∀ b, 0 ≤ Y b := fun b => by
    have := div_nonneg (wt_nonneg hw b) hV0.le; positivity
  have hmomF : ∀ F : Finset (S → ℕ), ∑ b ∈ F, P b * Y b ≤ CM := by
    intro F
    have h := J.sum_Pmin_mul_le Y hY0 (N.momConst_nonneg κ hw)
      (fun c => N.drift_moment_le κ hw hmono hV c) ht.1 n F
    have hYn : Y n ≤ (1 + M) ^ 4 := by
      have h1 : wt w n / V ≤ M := by rw [div_le_iff₀ hV0]; exact hn
      have h0 : 0 ≤ wt w n / V := div_nonneg (wt_nonneg hw n) hV0.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4
    have he : Real.exp (N.momConst κ w * t) ≤ Real.exp (N.momConst κ w * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (N.momConst_nonneg κ hw))
    calc ∑ b ∈ F, P b * Y b ≤ Real.exp (N.momConst κ w * t) * Y n := h
      _ ≤ CM := mul_le_mul he hYn (hY0 n) (Real.exp_pos _).le
  have hPYs : Summable fun b => P b * Y b :=
    summable_of_sum_le (fun b => mul_nonneg (hP0 b) (hY0 b)) hmomF
  have hPY : ∑' b, P b * Y b ≤ CM :=
    hPYs.tsum_le_of_sum_le hmomF
  -- pointwise bounds on `g`
  have hgK : ∀ b ∈ K, g b ≤ G₀ := by
    intro b hb
    have hcb := coord_le_of_wt_le hw hR0 hV0 ((mem_levelSet hw).mp hb)
    have hxt := hxB t ht
    calc g b ≤ ∑ _s : S, (R₁ + Rx) ^ 2 := Finset.sum_le_sum fun s _ => by
          have h1 : (b s : ℝ) / V ≤ R₁ := by rw [div_le_iff₀ hV0]; exact hcb s
          have h2 : 0 ≤ (b s : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
          have h3 := hxt.1 s
          have h4 := hxt.2 s
          have h5 : |(b s : ℝ) / V - x t s| ≤ R₁ + Rx := by
            rw [abs_le]; constructor <;> simp only [Pi.zero_apply] at h3 <;> linarith
          calc ((b s : ℝ) / V - x t s) ^ 2 = |(b s : ℝ) / V - x t s| ^ 2 := (sq_abs _).symm
            _ ≤ (R₁ + Rx) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
      _ = G₀ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hgall : ∀ b, g b ≤ 2 * Wi * (L ^ 2 + Y b / L ^ 2) + X2 := by
    intro b
    set u := wt w b / V with hu
    have hu0 : 0 ≤ u := div_nonneg (wt_nonneg hw b) hV0.le
    have hxt := hxB t ht
    have hcoord : ∀ s, (b s : ℝ) / V ≤ (w s)⁻¹ * u := by
      intro s
      have h1 : w s * (b s : ℝ) ≤ wt w b := Finset.single_le_sum
        (f := fun s => w s * (b s : ℝ)) (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _))
        (Finset.mem_univ s)
      rw [hu, div_le_iff₀ hV0]
      have hws := hw s
      rw [show (w s)⁻¹ * (wt w b / V) * V = wt w b / w s by field_simp]
      rw [le_div_iff₀ hws]; linarith
    calc g b ≤ ∑ s, (2 * ((w s)⁻¹ ^ 2 * u ^ 2) + 2 * Rx ^ 2) := Finset.sum_le_sum fun s _ => by
          have h0 : 0 ≤ (b s : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
          have h1 := hcoord s
          have h3 := hxt.1 s
          have h4 := hxt.2 s
          simp only [Pi.zero_apply] at h3
          have h5 : ((b s : ℝ) / V) ^ 2 ≤ (w s)⁻¹ ^ 2 * u ^ 2 := by
            rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 2
          have h6 : (x t s) ^ 2 ≤ Rx ^ 2 := pow_le_pow_left₀ h3 h4 2
          nlinarith [sq_nonneg ((b s : ℝ) / V + x t s)]
      _ = 2 * Wi * u ^ 2 + X2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hX2, hWi,
            Finset.mul_sum, Finset.sum_mul]
          congr 1
          · exact Finset.sum_congr rfl fun s _ => by ring
          · ring
      _ ≤ 2 * Wi * (L ^ 2 + Y b / L ^ 2) + X2 := by
          have := sq_le_split hu0 hL
          have h2 : 0 ≤ 2 * Wi := by positivity
          nlinarith
  -- summability of the main series
  have hdom : ∀ b, P b * g b ≤ P b * (G₀ + X2 + 2 * Wi * L ^ 2) + (2 * Wi / L ^ 2) * (P b * Y b) := by
    intro b
    by_cases hb : b ∈ K
    · have h1 := hgK b hb
      have h2 : 0 ≤ X2 + 2 * Wi * L ^ 2 := by positivity
      have h3 : 0 ≤ (2 * Wi / L ^ 2) * (P b * Y b) :=
        mul_nonneg (by positivity) (mul_nonneg (hP0 b) (hY0 b))
      nlinarith [hP0 b]
    · have h1 := hgall b
      have hG0 : 0 ≤ G₀ := by positivity
      have h4 : P b * (2 * Wi * (L ^ 2 + Y b / L ^ 2) + X2) =
          P b * (X2 + 2 * Wi * L ^ 2) + (2 * Wi / L ^ 2) * (P b * Y b) := by ring
      nlinarith [hP0 b, mul_le_mul_of_nonneg_left h1 (hP0 b)]
  have hfs : Summable fun b => P b * g b :=
    Summable.of_nonneg_of_le (fun b => mul_nonneg (hP0 b) (hg0 b)) hdom
      ((hPs.mul_right _).add (hPYs.mul_left _))
  -- the split
  have hsplit := tsum_split K hfs
  have hin : ∑ b ∈ K, P b * g b ≤ ∑ b ∈ Rset, P' b * g b + G₀ * Q := by
    calc ∑ b ∈ K, P b * g b = ∑ b ∈ K, P' b * g b + ∑ b ∈ K, (P b - P' b) * g b := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ ∑ b ∈ Rset, P' b * g b + ∑ b ∈ K, (P b - P' b) * G₀ := by
          refine add_le_add ?_ (Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
            (hgK b hb) (by linarith [hPP' b hb]))
          exact Finset.sum_le_sum_of_subset_of_nonneg hKsub fun b _ _ =>
            mul_nonneg (hP'0 b) (hg0 b)
      _ ≤ ∑ b ∈ Rset, P' b * g b + G₀ * Q := by
          rw [← Finset.sum_mul]
          have hG0 : 0 ≤ G₀ := by positivity
          nlinarith
  have houtg : ∑' b, (if b ∈ K then 0 else P b * g b) ≤
      (X2 + 2 * Wi * L ^ 2) * Q + (2 * Wi / L ^ 2) * CM := by
    have hs1 : Summable fun b => if b ∈ K then (0 : ℝ) else P b := by
      refine (hPs.sub (summable_of_ne_finset_zero (s := K) (f := fun b => if b ∈ K then P b else 0)
        fun b hb => if_neg hb)).congr fun b => by split_ifs <;> simp
    have hle : ∀ b, (if b ∈ K then 0 else P b * g b) ≤
        (X2 + 2 * Wi * L ^ 2) * (if b ∈ K then 0 else P b) + (2 * Wi / L ^ 2) * (P b * Y b) := by
      intro b
      split_ifs with hb
      · simp only [mul_zero, zero_add]
        exact mul_nonneg (by positivity) (mul_nonneg (hP0 b) (hY0 b))
      · have h1 := mul_le_mul_of_nonneg_left (hgall b) (hP0 b)
        have h4 : P b * (2 * Wi * (L ^ 2 + Y b / L ^ 2) + X2) =
            (X2 + 2 * Wi * L ^ 2) * P b + (2 * Wi / L ^ 2) * (P b * Y b) := by ring
        linarith
    have hsg : Summable fun b => if b ∈ K then (0 : ℝ) else P b * g b :=
      (hfs.sub (summable_of_ne_finset_zero (s := K) (f := fun b => if b ∈ K then P b * g b else 0)
        fun b hb => if_neg hb)).congr fun b => by split_ifs <;> simp
    calc ∑' b, (if b ∈ K then 0 else P b * g b)
        ≤ ∑' b, ((X2 + 2 * Wi * L ^ 2) * (if b ∈ K then 0 else P b) +
            (2 * Wi / L ^ 2) * (P b * Y b)) :=
          hsg.tsum_le_tsum hle ((hs1.mul_left _).add (hPYs.mul_left _))
      _ = (X2 + 2 * Wi * L ^ 2) * ∑' b, (if b ∈ K then 0 else P b) +
            (2 * Wi / L ^ 2) * ∑' b, P b * Y b := by
          rw [(hs1.mul_left _).tsum_add (hPYs.mul_left _), tsum_mul_left, tsum_mul_left]
      _ ≤ (X2 + 2 * Wi * L ^ 2) * Q + (2 * Wi / L ^ 2) * CM := by
          have h1 : 0 ≤ X2 + 2 * Wi * L ^ 2 := by positivity
          have h2 : 0 ≤ 2 * Wi / L ^ 2 := by positivity
          have e1 := mul_le_mul_of_nonneg_left hout h1
          have e2 := mul_le_mul_of_nonneg_left hPY h2
          linarith
  -- assemble
  have hfro := hfr V hV n hn t ht
  have hmain : ∑' m, N.transition κV t n m * g m = ∑' b, P b * g b := rfl
  rw [hmain, hsplit]
  have hQV : Q ≤ CQ * L ^ 2 / V := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    calc Q ≤ CQ / V := hQ
      _ ≤ CQ * L ^ 2 / V :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right hCQ0 hL2) hV0.le
  have hfinal : G₀ * Q + ((X2 + 2 * Wi * L ^ 2) * Q + (2 * Wi / L ^ 2) * CM) ≤
      C₃ * (L ^ 2 / V + 1 / L ^ 2) := by
    have hG0 : 0 ≤ G₀ := by positivity
    have hX20 : 0 ≤ X2 := by positivity
    -- direct estimate
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hQ1 : (G₀ + X2) * Q ≤ (G₀ + X2) * CQ * (L ^ 2 / V) := by
      have := mul_le_mul_of_nonneg_left hQV (add_nonneg hG0 hX20)
      calc (G₀ + X2) * Q ≤ (G₀ + X2) * (CQ * L ^ 2 / V) := this
        _ = (G₀ + X2) * CQ * (L ^ 2 / V) := by ring
    have hQ2 : 2 * Wi * L ^ 2 * Q ≤ 2 * Wi * CQ * (L ^ 2 / V) := by
      have := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * Wi * L ^ 2 by positivity)
      calc 2 * Wi * L ^ 2 * Q ≤ 2 * Wi * L ^ 2 * (CQ / V) := this
        _ = 2 * Wi * CQ * (L ^ 2 / V) := by ring
    have hT3 : (2 * Wi / L ^ 2) * CM = 2 * Wi * CM * (1 / L ^ 2) := by ring
    have hA : 0 ≤ L ^ 2 / V := by positivity
    have hB : 0 ≤ 1 / L ^ 2 := by positivity
    have hC3 : C₃ * (L ^ 2 / V + 1 / L ^ 2) = ((G₀ + 2 * Wi + X2) * CQ) * (L ^ 2 / V) +
        ((G₀ + 2 * Wi + X2) * CQ) * (1 / L ^ 2) + (2 * Wi * CM) * (L ^ 2 / V) +
        (2 * Wi * CM) * (1 / L ^ 2) := by rw [hC₃]; ring
    rw [hC3, hT3]
    have h1 : 0 ≤ ((G₀ + 2 * Wi + X2) * CQ) * (1 / L ^ 2) := by positivity
    have h2 : 0 ≤ (2 * Wi * CM) * (L ^ 2 / V) := by positivity
    have key : G₀ * Q + ((X2 + 2 * Wi * L ^ 2) * Q + 2 * Wi * CM * (1 / L ^ 2)) =
        (G₀ + X2) * Q + 2 * Wi * L ^ 2 * Q + 2 * Wi * CM * (1 / L ^ 2) := by ring
    have key2 : ((G₀ + 2 * Wi + X2) * CQ) * (L ^ 2 / V) +
        ((G₀ + 2 * Wi + X2) * CQ) * (1 / L ^ 2) + (2 * Wi * CM) * (L ^ 2 / V) +
        (2 * Wi * CM) * (1 / L ^ 2) =
        (G₀ + X2) * CQ * (L ^ 2 / V) + 2 * Wi * CQ * (L ^ 2 / V) +
          2 * Wi * CM * (1 / L ^ 2) + (((G₀ + 2 * Wi + X2) * CQ) * (1 / L ^ 2) +
            (2 * Wi * CM) * (L ^ 2 / V)) := by ring
    rw [key, key2]
    linarith
  calc ∑ b ∈ K, P b * g b + ∑' b, (if b ∈ K then 0 else P b * g b)
      ≤ (∑ b ∈ Rset, P' b * g b + G₀ * Q) +
          ((X2 + 2 * Wi * L ^ 2) * Q + (2 * Wi / L ^ 2) * CM) := add_le_add hin houtg
    _ ≤ gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t +
          C₃ * (L ^ 2 / V + 1 / L ^ 2) := by
        have : ∑ b ∈ Rset, P' b * g b ≤
            gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := hfro
        linarith

/-- **The law of large numbers as `V → ∞`, `MonoWeight` networks.** With `V = k + 1` and initial
counts `n_k` satisfying `⟨w, n_k⟩ ≤ M V` and `n_k / V → x(0)`, the mean squared distance
`E |X^V(t)/V − x(t)|²` tends to `0` for every `t ∈ [0, T]`. -/
theorem mono_lln_tendsto (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (hmono : N.MonoWeight w) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ) (hn : ∀ k, wt w (n k) ≤ M * ((k : ℝ) + 1))
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2) atTop
      (𝓝 0) := by
  obtain ⟨C₁, C₂, C₃, -, -, -, hbd⟩ := N.mono_lln κ hw hmono hM hT hRx x hxc hx hxB
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set Lk : ℕ → ℝ := fun k => Real.sqrt (Real.sqrt ((k : ℝ) + 1)) with hLk
  have hL1 : ∀ k, 1 ≤ Lk k := fun k =>
    Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (hV k))
  have hL2 : ∀ k, Lk k ^ 2 = Real.sqrt ((k : ℝ) + 1) := fun k =>
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hden
  have hε : Tendsto (fun k : ℕ => C₂ / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hup := tendsto_gronwallBound hn0 hε C₁ t
  have hextra : Tendsto (fun k : ℕ => C₃ * (Lk k ^ 2 / ((k : ℝ) + 1) + 1 / Lk k ^ 2)) atTop
      (𝓝 0) := by
    have h1 : (fun k : ℕ => C₃ * (Lk k ^ 2 / ((k : ℝ) + 1) + 1 / Lk k ^ 2)) =
        fun k : ℕ => C₃ * (2 * (1 / Real.sqrt ((k : ℝ) + 1))) := by
      funext k
      rw [hL2 k, Real.sqrt_div_self']
      ring
    have h2 : Tendsto (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsq
    rw [h1]
    simpa using (h2.const_mul 2).const_mul C₃
  have htot := hup.add hextra
  rw [add_zero] at htot
  refine squeeze_zero (fun k => tsum_nonneg fun m => mul_nonneg
    ((N.jumpSystem _).Pmin_nonneg t ht.1 _ _) (Finset.sum_nonneg fun s _ => sq_nonneg _))
    (fun k => hbd ((k : ℝ) + 1) (hV k) (n k) (hn k) t ht (Lk k) (hL1 k)) htot


/-- **Inflow-weight networks** (only zero-source reactions increase `w`), fixed times. -/
theorem inflow_lln (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hinf : N.InflowWeight w) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hRx : 0 ≤ Rx)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      wt w n ≤ M * V → ∀ t ∈ Icc 0 T, ∀ L : ℝ, 1 ≤ L →
        ∑' m, N.transition (N.volumeScale κ V (by linarith)) t n m *
            ∑ s, ((m s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t +
            C₃ * (L ^ 2 / V + 1 / L ^ 2) :=
  N.mono_lln κ hw hinf.monoWeight hM hT hRx x hxc hx hxB

/-- **Inflow-weight networks**, `V → ∞`. -/
theorem inflow_lln_tendsto (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (hinf : N.InflowWeight w) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ) (hn : ∀ k, wt w (n k) ≤ M * ((k : ℝ) + 1))
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2) atTop
      (𝓝 0) :=
  N.mono_lln_tendsto κ hw hinf.monoWeight hM hT hRx x hxc hx hxB n hn hn0 ht

end Network

namespace Examples
namespace InflowAnnihilation

open Network

/-- `0 → X` (rate `2`), `2X → 0` (rate `1`). -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨0, ![1]⟩ else ⟨![2], 0⟩⟩

def κ : RateConstants net := ⟨fun r => if r = 0 then 2 else 1, fun r => by
  split_ifs <;> norm_num⟩

/-- The weight `w = 1`. -/
def w : Fin 1 → ℝ := fun _ => 1

theorem inflowWeight : net.InflowWeight w := by
  intro r hr s
  fin_cases r
  · rfl
  · exfalso
    simp [dw, w, Network.reactionVector, Reaction.vector] at hr
    norm_num at hr

/-- No positive weight is conserved or decreased by every reaction. -/
theorem not_subconservative :
    ¬ ∃ w' : Fin 1 → ℝ, (∀ s, 0 < w' s) ∧ ∀ r, ∑ s, w' s * net.reactionVector r s ≤ 0 := by
  rintro ⟨w', hpos, h⟩
  have := h 0
  simp [Network.reactionVector, Reaction.vector] at this
  linarith [hpos 0]

/-- The equilibrium `x* = 1`. -/
def xstar : Concentration (Fin 1) := fun _ => 1

theorem equilibrium : net.massActionVectorField κ xstar = 0 := by
  funext u
  rw [massActionVectorField_apply]
  fin_cases u
  simp [Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]

/-- **LLN instance for the open network `0 → X`, `2X → 0`.** Started from `V` molecules at
volume `V = k + 1`, `E |X^V(t)/V − 1|² → 0` for every `t ∈ [0, 1]`. -/
theorem lln {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun k : ℕ => ∑' m, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        t (fun _ => k + 1) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2) atTop (𝓝 0) := by
  refine inflow_lln_tendsto net κ (w := w) (fun _ => one_pos) inflowWeight (M := 1) (Rx := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => xstar) continuousOn_const (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (fun k _ => k + 1)
    (fun k => ?_) ?_ ht
  · simp [wt, w]
  · have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 1 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2
        = 0 := by
      intro k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [xstar, hk]
    simp only [h]
    exact tendsto_const_nhds

end InflowAnnihilation

namespace Autocatalytic

open Network

/-- `X → 2X`, `2X → X` (rates `1`). -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1], ![2]⟩ else ⟨![2], ![1]⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

def w : Fin 1 → ℝ := fun _ => 1

theorem monoWeight : net.MonoWeight w := by
  intro r hr
  fin_cases r
  · simp [srcMol]
  · exfalso
    simp [dw, w, Network.reactionVector, Reaction.vector] at hr

/-- The autocatalytic step increases the weight and has a nonzero source. -/
theorem not_inflowWeight : ¬ net.InflowWeight w := by
  intro h
  have := h 0 (by simp [dw, w, Network.reactionVector, Reaction.vector]) 0
  simp at this

theorem not_subconservative :
    ¬ ∃ w' : Fin 1 → ℝ, (∀ s, 0 < w' s) ∧ ∀ r, ∑ s, w' s * net.reactionVector r s ≤ 0 := by
  rintro ⟨w', hpos, h⟩
  have := h 0
  simp [Network.reactionVector, Reaction.vector] at this
  linarith [hpos 0]

def xstar : Concentration (Fin 1) := fun _ => 1

theorem equilibrium : net.massActionVectorField κ xstar = 0 := by
  funext u
  rw [massActionVectorField_apply]
  fin_cases u
  simp [Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
    Network.reactionVector, Reaction.vector]
  norm_num

/-- **LLN instance for the autocatalytic network `X → 2X`, `2X → X`.** Started from `V`
molecules at volume `V = k + 1`, `E |X^V(t)/V − 1|² → 0` for every `t ∈ [0, 1]`. -/
theorem lln {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun k : ℕ => ∑' m, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        t (fun _ => k + 1) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2) atTop (𝓝 0) := by
  refine mono_lln_tendsto net κ (w := w) (fun _ => one_pos) monoWeight (M := 1) (Rx := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => xstar) continuousOn_const (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (fun k _ => k + 1)
    (fun k => ?_) ?_ ht
  · simp [wt, w]
  · have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 1 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2
        = 0 := by
      intro k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [xstar, hk]
    simp only [h]
    exact tendsto_const_nhds

end Autocatalytic
end Examples

end CRNT
