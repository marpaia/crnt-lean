import CRNT.Dynamics.DelayMassActionInvariance
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.Compact

/-! # Local existence and first-step uniqueness for delayed mass-action systems

This file proves a first-step existence theorem for reaction-specific mass-action delays. It uses
only a positive lower bound on nonzero delays, so that all delayed production on the first interval
is a known forcing term. It makes no global-existence or continuation claim.
-/

namespace CRNT
namespace Network

open Set Filter Topology

set_option maxHeartbeats 2400000

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A continuous history for a finite mass-action delay network gives a solution on a sufficiently
short initial interval, provided every nonzero reaction delay is bounded below by `d`. Zero-delay
reactions are included in the instantaneous polynomial field; positive-delay production is the
known history forcing. The theorem asserts only a local solution, not global continuation. -/
theorem massActionDelay_local_exists_of_delayGap
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d : ℝ) (hd : 0 < d)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (φ : ℝ → Concentration S) (hφ : Continuous φ) (x₀ : Concentration S)
    (hφ₀ : φ 0 = x₀) :
    ∃ h : ℝ, 0 < h ∧ h ≤ d ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  classical
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else φ (t - τ r))
  let B := ‖x₀‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K := Real.toNNReal (massActionLipschitzConstant
    (N.instantaneousDelayNetwork τ) (N.instantaneousDelayRates τ κ) B)
  have hK : ∀ t, LipschitzOnWith K (f t) (Metric.closedBall x₀ 1) := by
    intro t u hu u' hu'
    have hu0 : u ∈ Metric.closedBall (0 : Concentration S) B := by
      rw [Metric.mem_closedBall, dist_zero_right] at *
      rw [dist_eq_norm] at hu
      have := norm_add_le (u - x₀) x₀
      have heq : u - x₀ + x₀ = u := sub_add_cancel _ _
      rw [heq] at this
      dsimp [B]
      linarith
    have hu'0 : u' ∈ Metric.closedBall (0 : Concentration S) B := by
      rw [Metric.mem_closedBall, dist_zero_right] at *
      rw [dist_eq_norm] at hu'
      have := norm_add_le (u' - x₀) x₀
      have heq : u' - x₀ + x₀ = u' := sub_add_cancel _ _
      rw [heq] at this
      dsimp [B]
      linarith
    have hL := N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ B
      (fun r => φ (t - τ r))
    change edist (N.massActionDelayField κ u
        (fun r => if τ r = 0 then u else φ (t - τ r)))
      (N.massActionDelayField κ u'
        (fun r => if τ r = 0 then u' else φ (t - τ r))) ≤ _
    exact hL hu0 hu'0
  have hcont : Continuous (Function.uncurry f) := by
    apply continuous_pi
    intro s
    change Continuous (fun p : ℝ × Concentration S =>
      ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial
          (if τ r = 0 then p.2 else φ (p.1 - τ r)) *
            ((N.reaction r).target s : ℝ) -
        (N.reaction r).source.massActionMonomial p.2 *
            ((N.reaction r).source s : ℝ)))
    apply continuous_finsetSum
    intro r hr
    by_cases hzero : τ r = 0
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
  let C : Set (ℝ × Concentration S) := Set.Icc 0 d ×ˢ Metric.closedBall x₀ 1
  have hCcompact : IsCompact C := isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  have hCbdd : BddAbove (Set.image (fun p : ℝ × Concentration S => ‖f p.1 p.2‖) C) := by
    exact hCcompact.bddAbove_image (by
      exact (continuous_norm.comp hcont).continuousOn)
  obtain ⟨M, hM⟩ := hCbdd
  have hM0 : 0 ≤ M := by
    have hmem : (0, x₀) ∈ C := by
      exact ⟨⟨le_rfl, hd.le⟩, Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)⟩
    have hle := hM (Set.mem_image_of_mem _ hmem)
    exact le_trans (norm_nonneg _) hle
  let L := Real.toNNReal M
  let h := min d (1 / (M + 1))
  have hh : 0 < h := lt_min hd (one_div_pos.mpr (by linarith))
  have hhd : h ≤ d := min_le_left _ _
  have hhM : M * h ≤ 1 := by
    have hhr := min_le_right d (1 / (M + 1))
    have hmul := mul_le_mul_of_nonneg_left hhr hM0
    have hpos : 0 < M + 1 := by linarith
    have hfactor : M * (1 / (M + 1)) ≤ 1 := by
      have heq : M * (1 / (M + 1)) = M / (M + 1) := by ring
      rw [heq, div_le_one hpos]
      linarith
    exact le_trans hmul hfactor
  have hpl : IsPicardLindelof f (tmin := 0) (tmax := h)
      ⟨0, ⟨le_rfl, hh.le⟩⟩ x₀ 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hK t
    · intro u hu
      exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht u hu
      have hmem : (t, u) ∈ C := ⟨⟨ht.1, le_trans ht.2 hhd⟩, hu⟩
      have hmemb := hM (Set.mem_image_of_mem _ hmem)
      rw [Real.coe_toNNReal M hM0]
      exact hmemb
    · rw [sub_zero, sub_self, max_eq_left hh.le]
      simpa [L, Real.coe_toNNReal M hM0] using hhM
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let x : ℝ → Concentration S := fun t => if t < 0 then φ t else α t
  have hx0 : x 0 = x₀ := by simp [x, hα0]
  refine ⟨h, hh, hhd, x, ?_, hx0, ?_⟩
  · intro t ht
    by_cases hneg : t < 0
    · simp [x, hneg]
    · have hzero : t = 0 := by linarith
      simp [x, hzero, hα0, hφ₀]
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hxt : x t = α t := by simp [x, not_lt.mpr ht0]
    have hdel : ∀ r, x (t - τ r) = (if τ r = 0 then α t else φ (t - τ r)) := by
      intro r
      by_cases hzero : τ r = 0
      · simp [hzero, hxt]
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ≤ 0 := by
          have := hgap r hpos
          linarith [ht.2, hhd]
        by_cases heq : t - τ r < 0
        · simp [hzero, x, heq]
        · have hz : t - τ r = 0 := le_antisymm harg (le_of_not_gt heq)
          simp [hzero, x, hz, hα0, hφ₀]
    have hfield : N.delayField κ τ x t = f t (α t) := by
      have : (fun r => x (t - τ r)) =
          (fun r => if τ r = 0 then α t else φ (t - τ r)) := funext hdel
      change N.massActionDelayField κ (x t) (fun r => x (t - τ r)) = _
      rw [hxt, this]
    have hcong : ∀ s ∈ Set.Icc 0 h, x s = α s := by
      intro s hs
      simp [x, not_lt.mpr hs.1]
    exact (hα t ht).congr_of_mem hcong ht |>.congr_deriv hfield.symm

/-- **Uniform first-step existence for bounded restart data.** The step length depends only on
the network, rates, delay bounds, and supplied bounds on the initial state and history, rather
than on the particular restart data. -/
theorem massActionDelay_local_exists_uniform
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d D B H : ℝ)
    (hd : 0 < d) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) :
    ∃ h : ℝ, 0 < h ∧ h ≤ d ∧ ∀ (φ : ℝ → Concentration S), Continuous φ →
      (∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → φ 0 = x₀ → ∃ x : ℝ → Concentration S,
        (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  classical
  let F : Concentration S × (N.R → Concentration S) → Concentration S := fun p =>
    N.massActionDelayField κ p.1 (fun r => if τ r = 0 then p.1 else p.2 r)
  have hF : Continuous F := by
    apply continuous_pi
    intro s
    change Continuous (fun p : Concentration S × (N.R → Concentration S) =>
      ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial
          (if τ r = 0 then p.1 else p.2 r) * ((N.reaction r).target s : ℝ) -
        (N.reaction r).source.massActionMonomial p.1 * ((N.reaction r).source s : ℝ)))
    apply continuous_finsetSum
    intro r hr
    by_cases hzero : τ r = 0
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
  let Z : Set (N.R → Concentration S) :=
    Set.pi Set.univ (fun _ => Metric.closedBall 0 H)
  let C := Metric.closedBall (0 : Concentration S) (B + 1) ×ˢ Z
  have hCcompact : IsCompact C :=
    (isCompact_closedBall 0 (B + 1)).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall 0 H)
  have hCbdd : BddAbove (Set.image (fun p => ‖F p‖) C) :=
    hCcompact.bddAbove_image ((continuous_norm.comp hF).continuousOn)
  obtain ⟨M, hM⟩ := hCbdd
  have hM0 : 0 ≤ M := by
    have hmem : (0, fun _ : N.R => (0 : Concentration S)) ∈ C := by
      constructor
      · exact Metric.mem_closedBall_self (by linarith [hB])
      · intro r _
        exact Metric.mem_closedBall_self hH
    exact le_trans (norm_nonneg _) (hM (Set.mem_image_of_mem _ hmem))
  let K := Real.toNNReal (massActionLipschitzConstant
    (N.instantaneousDelayNetwork τ) (N.instantaneousDelayRates τ κ) (B + 1))
  let h := min d (1 / (M + 1))
  have hh : 0 < h := lt_min hd (one_div_pos.mpr (by linarith))
  have hhd : h ≤ d := min_le_left _ _
  have hhM : M * h ≤ 1 := by
    have hm := min_le_right d (1 / (M + 1))
    have hmul := mul_le_mul_of_nonneg_left hm hM0
    have hpos : 0 < M + 1 := by linarith
    have hfactor : M * (1 / (M + 1)) ≤ 1 := by
      have heq : M * (1 / (M + 1)) = M / (M + 1) := by ring
      rw [heq, div_le_one hpos]
      linarith
    exact le_trans hmul hfactor
  refine ⟨h, hh, hhd, ?_⟩
  intro φ hφ hφbound x₀ hx₀ hφ₀
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else φ (t - τ r))
  have hK : ∀ t, LipschitzOnWith K (f t) (Metric.closedBall x₀ 1) := by
    intro t u hu u' hu'
    have hu0 : u ∈ Metric.closedBall (0 : Concentration S) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      have htri := norm_add_le (u - x₀) x₀
      have heq : u - x₀ + x₀ = u := sub_add_cancel _ _
      rw [heq] at htri
      linarith
    have hu'0 : u' ∈ Metric.closedBall (0 : Concentration S) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall, dist_eq_norm] at hu'
      have htri := norm_add_le (u' - x₀) x₀
      have heq : u' - x₀ + x₀ = u' := sub_add_cancel _ _
      rw [heq] at htri
      linarith
    exact N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ (B + 1)
      (fun r => φ (t - τ r)) hu0 hu'0
  have hcont : Continuous (Function.uncurry f) := by
    apply continuous_pi
    intro s
    change Continuous (fun p : ℝ × Concentration S =>
      ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial
          (if τ r = 0 then p.2 else φ (p.1 - τ r)) *
            ((N.reaction r).target s : ℝ) -
        (N.reaction r).source.massActionMonomial p.2 *
            ((N.reaction r).source s : ℝ)))
    apply continuous_finsetSum
    intro r hr
    by_cases hzero : τ r = 0
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
    · simp [hzero]
      unfold Complex.massActionMonomial
      fun_prop
  have hMactual : ∀ t ∈ Set.Icc 0 d, ∀ u ∈ Metric.closedBall x₀ 1, ‖f t u‖ ≤ M := by
    intro t ht u hu
    have huU : u ∈ Metric.closedBall (0 : Concentration S) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      have htri := norm_add_le (u - x₀) x₀
      have heq : u - x₀ + x₀ = u := sub_add_cancel _ _
      rw [heq] at htri
      linarith
    let z : N.R → Concentration S := fun r =>
      if τ r = 0 then 0 else φ (t - τ r)
    have hz : z ∈ Z := by
      intro r hr
      by_cases hzero : τ r = 0
      · simpa [z, hzero, Metric.mem_closedBall, dist_zero_right] using hH
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ∈ Set.Icc (-D) 0 := by
          constructor <;> rcases ht with ⟨ht0, htd⟩
          · linarith [hτD r]
          · linarith [hgap r hpos]
        simpa [z, hzero] using hφbound (t - τ r) harg
    have hmem : (u, z) ∈ C := ⟨huU, hz⟩
    have heq : f t u = F (u, z) := by
      dsimp [f, F, z]
      congr 1
      funext r
      by_cases hzero : τ r = 0 <;> simp [hzero]
    rw [heq]
    exact hM (Set.mem_image_of_mem _ hmem)
  let L := Real.toNNReal M
  have hpl : IsPicardLindelof f (tmin := 0) (tmax := h)
      ⟨0, ⟨le_rfl, hh.le⟩⟩ x₀ 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact hK t
    · intro u hu
      exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro t ht u hu
      have hm := hMactual t ⟨ht.1, le_trans ht.2 hhd⟩ u hu
      rw [Real.coe_toNNReal M hM0]
      exact hm
    · rw [sub_zero, sub_self, max_eq_left hh.le]
      simpa [L, Real.coe_toNNReal M hM0] using hhM
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let x : ℝ → Concentration S := fun t => if t < 0 then φ t else α t
  have hx0 : x 0 = x₀ := by simp [x, hα0]
  refine ⟨x, ?_, hx0, ?_⟩
  · intro t ht
    by_cases hneg : t < 0
    · simp [x, hneg]
    · have hzero : t = 0 := by linarith
      simp [x, hzero, hα0, hφ₀]
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hxt : x t = α t := by simp [x, not_lt.mpr ht0]
    have hdel : ∀ r, x (t - τ r) =
        (if τ r = 0 then α t else φ (t - τ r)) := by
      intro r
      by_cases hzero : τ r = 0
      · simp [hzero, hxt]
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ≤ 0 := by linarith [hgap r hpos, ht.2, hhd]
        by_cases heq : t - τ r < 0
        · simp [hzero, x, heq]
        · have hz0 : t - τ r = 0 := le_antisymm harg (le_of_not_gt heq)
          simp [hzero, x, hz0, hα0, hφ₀]
    have hfield : N.delayField κ τ x t = f t (α t) := by
      have : (fun r => x (t - τ r)) =
          (fun r => if τ r = 0 then α t else φ (t - τ r)) := funext hdel
      change N.massActionDelayField κ (x t) (fun r => x (t - τ r)) = _
      rw [hxt, this]
    have hcong : ∀ s ∈ Set.Icc 0 h, x s = α s := by
      intro s hs
      simp [x, not_lt.mpr hs.1]
    exact (hα t ht).congr_of_mem hcong ht |>.congr_deriv hfield.symm

/-- The uniform restart theorem with a continuous global representative.  Picard--Lindelöf
controls the path only on the restart interval, so we extend it constantly after that interval;
the prescribed history is unchanged. This form is convenient for iterating restarts. -/
theorem massActionDelay_local_exists_uniform_continuous
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d D B H : ℝ)
    (hd : 0 < d) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) :
    ∃ h : ℝ, 0 < h ∧ h ≤ d ∧ ∀ (φ : ℝ → Concentration S), Continuous φ →
      (∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → φ 0 = x₀ → ∃ x : ℝ → Concentration S,
        Continuous x ∧ (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  obtain ⟨h, hh, hhd, hex⟩ := N.massActionDelay_local_exists_uniform κ τ d D B H hd hB hH
    hτ hgap hτD
  refine ⟨h, hh, hhd, ?_⟩
  intro φ hφ hφbound x₀ hx₀ hφ₀
  obtain ⟨x, hxhist, hx₀', hxderiv⟩ := hex φ hφ hφbound x₀ hx₀ hφ₀
  let y : ℝ → Concentration S := Set.piecewise (Set.Iic h) x (fun _ => x h)
  have hxcontIic : ContinuousOn x (Set.Iic h) := by
    have hleft : ContinuousOn x (Set.Iic 0) := by
      apply hφ.continuousOn.congr
      intro t ht
      exact hxhist t ht
    have hmid : ContinuousOn x (Set.Icc 0 h) := by
      intro t ht
      exact (hxderiv t ht).continuousWithinAt
    have hcover : Set.Iic h = Set.Iic 0 ∪ Set.Icc 0 h := by
      ext t
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
      constructor
      · intro ht
        by_cases ht0 : t ≤ 0
        · exact Or.inl ht0
        · exact Or.inr ⟨le_of_not_ge ht0, ht⟩
      · rintro (ht | ⟨_, ht⟩) <;> linarith
    rw [hcover]
    exact hleft.union_of_isClosed hmid isClosed_Iic isClosed_Icc
  have hycont : Continuous y := by
    have hfront : ∀ t ∈ frontier (Set.Iic h), x t = (fun _ : ℝ => x h) t := by
      intro t ht
      have hteq : t = h := by simpa using ht
      subst t
      rfl
    have hpw : Continuous (Set.piecewise (Set.Iic h) x (fun _ : ℝ => x h)) := by
      apply continuous_piecewise hfront
      · simpa [isClosed_Iic.closure_eq] using hxcontIic
      · exact continuousOn_const
    simpa only [y] using hpw
  refine ⟨y, hycont, ?_, ?_, ?_⟩
  · intro t ht
    have hth : t ≤ h := by linarith [ht, hh.le]
    simp [y, Set.mem_Iic, hth]
    exact hxhist t ht
  · simp [y, hh.le, hx₀']
  · intro t ht
    have hyt : y t = x t := by simp [y, Set.mem_Iic, ht.2]
    have hfun : (fun s => y s) =ᶠ[nhdsWithin t (Set.Icc 0 h)] fun s => x s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [y, Set.mem_Iic, hs.2]
    have hderiv := (hxderiv t ht).congr_of_eventuallyEq hfun hyt
    have hfield : N.delayField κ τ y t = N.delayField κ τ x t := by
      funext s
      simp only [Network.delayField]
      have hyarg (r : N.R) : y (t - τ r) = x (t - τ r) := by
        have harg : t - τ r ≤ h := by linarith [ht.2, hτ r]
        simp [y, Set.mem_Iic, harg]
      simp [hyt, hyarg]
    exact hderiv.congr_deriv hfield.symm

/-- Restart a differentiable trajectory at time `a` with the uniform step.  The restarted path
matches the old path through `a`; on the new slab it solves the same autonomous delay field.
This is the finite-stage gluing primitive for conservative global continuation. -/
theorem massActionDelay_uniform_restart
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (D B H h a : ℝ)
    (hh : 0 < h) (hτ : ∀ r, 0 ≤ τ r) (ha : 0 ≤ a)
    (hrestart : ∀ (φ : ℝ → Concentration S), Continuous φ →
      (∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → φ 0 = x₀ → ∃ z : ℝ → Concentration S,
        Continuous z ∧ (∀ t ≤ 0, z t = φ t) ∧ z 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hxStartBound : ‖x a‖ ≤ B)
    (hxBound : ∀ t ∈ Set.Icc (a - D) a, ‖x t‖ ≤ H)
    (hx : ∀ t ∈ Set.Icc 0 a,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 a) t) :
    ∃ y : ℝ → Concentration S,
      Continuous y ∧ (∀ t ≤ a, y t = x t) ∧
      ∀ t ∈ Set.Icc 0 (a + h),
        HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 (a + h)) t := by
  let φ : ℝ → Concentration S := fun s => x (a + s)
  have hφ : Continuous φ := hxc.comp (continuous_const.add continuous_id)
  have hφbound : ∀ s ∈ Set.Icc (-D) 0, ‖φ s‖ ≤ H := by
    intro s hs
    apply hxBound (a + s)
    constructor <;> linarith [hs.1, hs.2]
  have hxa : ‖x a‖ ≤ B := hxStartBound
  have hφ₀ : φ 0 = x a := by simp [φ]
  obtain ⟨z, hzcont, hzhist, hz0, hz⟩ := hrestart φ hφ hφbound (x a) hxa hφ₀
  let y : ℝ → Concentration S := fun t => z (t - a)
  have hycont : Continuous y := hzcont.comp (continuous_id.sub continuous_const)
  have hyold : ∀ t ≤ a, y t = x t := by
    intro t ht
    have harg : t - a ≤ 0 := by linarith
    change z (t - a) = x t
    rw [hzhist (t - a) harg]
    change x (a + (t - a)) = x t
    congr 1
    ring
  have hyStep : ∀ t ∈ Set.Icc a (a + h),
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc a (a + h)) t := by
    intro t ht
    change a ≤ t ∧ t ≤ a + h at ht
    have hu : t - a ∈ Set.Icc 0 h := by
      constructor <;> linarith
    have hmap : HasDerivWithinAt (fun t : ℝ => t - a) 1 (Set.Icc a (a + h)) t := by
      simpa using (hasDerivWithinAt_id (s := Set.Icc a (a + h)) (x := t)).sub_const a
    have hmaps : Set.MapsTo (fun u : ℝ => u - a) (Set.Icc a (a + h)) (Set.Icc 0 h) := by
      intro u hu
      change a ≤ u ∧ u ≤ a + h at hu
      constructor <;> linarith
    have hcomp := (hz (t - a) hu).hasFDerivWithinAt.comp_hasDerivWithinAt
      (x := t) hmap hmaps
    -- The shifted derivative is the original autonomous delay field at the shifted time.
    have hfield : (N.delayField κ τ y t) = N.delayField κ τ z (t - a) := by
      funext s
      simp only [Network.delayField]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [y]
      rw [show t - τ r - a = t - a - τ r by ring]
    simpa [y, Function.comp_def, hfield] using hcomp
  have hyfield_eq (t : ℝ) (ht : t ∈ Set.Icc 0 a) :
      N.delayField κ τ y t = N.delayField κ τ x t := by
    funext s
    simp only [Network.delayField]
    have hyt : y t = x t := hyold t ht.2
    have hyarg (r : N.R) : y (t - τ r) = x (t - τ r) :=
      hyold (t - τ r) (by linarith [ht.2, hτ r])
    simp [hyt, hyarg]
  have hyOldDeriv (t : ℝ) (ht : t ∈ Set.Icc 0 a) :
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 a) t := by
    have heq : ∀ u ∈ Set.Icc 0 a, y u = x u := fun u hu => hyold u hu.2
    have hderiv := (hx t ht).congr heq (hyold t ht.2)
    exact hderiv.congr_deriv (hyfield_eq t ht).symm
  refine ⟨y, hycont, hyold, ?_⟩
  intro t ht
  by_cases hleft : t < a
  · have hmem : Set.Icc 0 a ∈ 𝓝[Set.Icc 0 (a + h)] t := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      let ε := (a - t) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      refine ⟨Set.Icc (t - ε) (t + ε), Icc_mem_nhds ?_ ?_, ?_⟩
      · dsimp [ε]; linarith
      · dsimp [ε]; linarith
      · intro u hu
        constructor
        · exact hu.2.1
        · have : u ≤ t + ε := hu.1.2
          dsimp [ε] at this
          linarith
    have hderiv := hyOldDeriv t ⟨ht.1, le_of_lt hleft⟩
    exact hderiv.mono_of_mem_nhdsWithin hmem
  · by_cases hright : a < t
    · have hmem : Set.Icc a (a + h) ∈ 𝓝[Set.Icc 0 (a + h)] t := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        let ε := (t - a) / 2
        have hε : 0 < ε := by dsimp [ε]; linarith
        refine ⟨Set.Icc (t - ε) (t + ε), Icc_mem_nhds ?_ ?_, ?_⟩
        · dsimp [ε]; linarith
        · dsimp [ε]; linarith
        · intro u hu
          constructor
          · have : t - ε ≤ u := hu.1.1
            dsimp [ε] at this
            linarith
          · exact hu.2.2
      exact (hyStep t ⟨le_of_lt hright, ht.2⟩).mono_of_mem_nhdsWithin hmem
    · have hteq : t = a := le_antisymm (le_of_not_gt hright) (le_of_not_gt hleft)
      subst t
      have hleftDeriv := hyOldDeriv a ⟨ha, le_rfl⟩
      have hrightDeriv := hyStep a ⟨le_rfl, by linarith⟩
      have hcover : Set.Icc 0 a ∪ Set.Icc a (a + h) = Set.Icc 0 (a + h) := by
        ext u
        simp only [Set.mem_union, Set.mem_Icc]
        constructor
        · rintro (⟨hu0, hua⟩ | ⟨hua, huend⟩) <;> constructor <;> linarith
        · rintro ⟨hu0, huend⟩
          by_cases hua : u ≤ a
          · exact Or.inl ⟨hu0, hua⟩
          · exact Or.inr ⟨le_of_not_ge hua, huend⟩
      rw [← hcover]
      exact hleftDeriv.union hrightDeriv

/- Every finite family of reaction delays has a positive lower bound for its positive members.
Take the least positive delay, capped by one; when there are no positive delays, any positive
length is allowed. -/
theorem massActionDelay_exists_positive_step (N : Network S) (τ : N.R → ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ r, 0 < τ r → d ≤ τ r := by
  classical
  by_cases hpos : ∃ r, 0 < τ r
  · let P : Finset N.R := Finset.univ.filter fun r => 0 < τ r
    have hP : P.Nonempty := by
      obtain ⟨r, hr⟩ := hpos
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
    obtain ⟨rmin, hrmin, hmin⟩ := P.exists_min_image τ hP
    refine ⟨min 1 (τ rmin), lt_min (by norm_num) ?_, ?_⟩
    · exact (Finset.mem_filter.mp hrmin).2
    · intro r hr
      have hrP : r ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
      exact le_trans (min_le_right 1 (τ rmin)) (hmin r hrP)
  · refine ⟨1, by norm_num, ?_⟩
    intro r hr
    exact (hpos ⟨r, hr⟩).elim

/-- **Local existence for arbitrary finite nonnegative-delay mass-action networks.** Every
continuous history with an initial value extends to a solution on some nontrivial first interval.
The solution is asserted only through that first interval; no global existence is claimed. -/
theorem massActionDelay_local_exists
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (x₀ : Concentration S) (hφ₀ : φ 0 = x₀) :
    ∃ h : ℝ, 0 < h ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧ x 0 = x₀ ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  obtain ⟨d, hd, hgap⟩ := massActionDelay_exists_positive_step N τ
  obtain ⟨h, hh, hhd, x, hxφ, hx₀, hx⟩ :=
    massActionDelay_local_exists_of_delayGap N κ τ d hd hτ hgap φ hφ x₀ hφ₀
  exact ⟨h, hh, x, hxφ, hx₀, hx⟩

/-- Nonnegative continuous histories produce a locally existing solution that remains in the
nonnegative orthant on its first interval. This combines the first-step Picard–Lindelöf result
with the finite-interval invariance theorem; it does not assert global existence. -/
theorem massActionDelay_local_exists_nonneg_history
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ h : ℝ, 0 < h ∧ ∃ x : ℝ → Concentration S,
      (∀ t ≤ 0, x t = φ t) ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t ∧
        ∀ s, 0 ≤ x t s := by
  obtain ⟨h, hh, x, hxφ, hx₀, hx⟩ :=
    N.massActionDelay_local_exists κ τ hτ φ hφ (φ 0) rfl
  refine ⟨h, hh, x, hxφ, ?_⟩
  intro t ht
  have hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (0 - τ r) 0 → 0 ≤ x q s := by
    intro r s q hq
    rw [hxφ q hq.2]
    exact hφnonneg q hq.2 s
  have hstart : ∀ s, 0 ≤ x 0 s := by
    intro s
    rw [hxφ 0 le_rfl]
    exact hφnonneg 0 le_rfl s
  have hnonneg := N.delayField_nonneg_of_nonnegative_delays κ τ (le_of_lt hh) hτ hx
    hhistory hstart t ht
  exact ⟨hx t ht, hnonneg⟩

/-- Two delayed mass-action solutions with the same history and initial state agree throughout
their common first step. Positive-delay reactions sample only the prescribed history on this
interval, while zero-delay reactions form a locally Lipschitz ordinary vector field. No global
Lipschitz assumption or uniqueness premise is needed. -/
theorem massActionDelay_firstStep_unique
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d T : ℝ)
    (hd : 0 < d) (hT : 0 < T)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (φ : ℝ → Concentration S) (x₀ : Concentration S)
    {x y : ℝ → Concentration S}
    (hxhist : ∀ t ≤ 0, x t = φ t) (hyhist : ∀ t ≤ 0, y t = φ t)
    (hx₀ : x 0 = x₀) (hy₀ : y 0 = x₀)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 (min d T), x t = y t := by
  classical
  let H := min d T
  have hH : 0 < H := lt_min hd hT
  have hHd : H ≤ d := min_le_left _ _
  have hHT : H ≤ T := min_le_right _ _
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else φ (t - τ r))
  have hxcont : ContinuousOn x (Set.Icc 0 T) := fun t ht => (hx t ht).continuousWithinAt
  have hycont : ContinuousOn y (Set.Icc 0 T) := fun t ht => (hy t ht).continuousWithinAt
  obtain ⟨Bx, hBx⟩ := isCompact_Icc.bddAbove_image (f := fun t => ‖x t‖) hxcont.norm
  obtain ⟨By, hBy⟩ := isCompact_Icc.bddAbove_image (f := fun t => ‖y t‖) hycont.norm
  have hBx0 : 0 ≤ Bx := by
    have hmem : ‖x 0‖ ∈ Set.image (fun t => ‖x t‖) (Set.Icc (0 : ℝ) T) :=
      Set.mem_image_of_mem _ ⟨le_rfl, hT.le⟩
    exact le_trans (norm_nonneg _) (hBx hmem)
  have hBy0 : 0 ≤ By := by
    have hmem : ‖y 0‖ ∈ Set.image (fun t => ‖y t‖) (Set.Icc (0 : ℝ) T) :=
      Set.mem_image_of_mem _ ⟨le_rfl, hT.le⟩
    exact le_trans (norm_nonneg _) (hBy hmem)
  let B := max Bx By
  have hB0 : 0 ≤ B := le_max_of_le_left hBx0
  let K := Real.toNNReal
    (massActionLipschitzConstant (N.instantaneousDelayNetwork τ)
      (N.instantaneousDelayRates τ κ) B)
  have hv : ∀ t ∈ Set.Ico 0 H, LipschitzOnWith K (f t)
      (Metric.closedBall (0 : Concentration S) B) := by
    intro t ht u hu u' hu'
    have hL := N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ B
      (fun r => φ (t - τ r))
    change edist (N.massActionDelayField κ u
        (fun r => if τ r = 0 then u else φ (t - τ r)))
      (N.massActionDelayField κ u'
        (fun r => if τ r = 0 then u' else φ (t - τ r))) ≤ _
    exact hL hu hu'
  have hxBall : ∀ t ∈ Set.Icc 0 H, x t ∈ Metric.closedBall (0 : Concentration S) B := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hBx (Set.mem_image_of_mem _ ⟨ht.1, ht.2.trans hHT⟩)) (le_max_left _ _)
  have hyBall : ∀ t ∈ Set.Icc 0 H, y t ∈ Metric.closedBall (0 : Concentration S) B := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hBy (Set.mem_image_of_mem _ ⟨ht.1, ht.2.trans hHT⟩)) (le_max_right _ _)
  have hright : ∀ (g : ℝ → Concentration S)
      (hg : ∀ t ∈ Set.Icc 0 H,
        HasDerivWithinAt g (f t (g t)) (Set.Icc 0 H) t),
      ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt g (f t (g t)) (Set.Ici t) t := by
    intro g hg t ht
    by_cases heq : t = 0
    · subst t
      refine (hg 0 ⟨le_rfl, hH.le⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (-1) H, isOpen_Ioo, ?_, ?_⟩
      · exact ⟨by norm_num, hH⟩
      · intro z hz
        exact ⟨hz.2, hz.1.2.le⟩
    · have ht' : t ∈ Set.Ioo 0 H := ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), ht.2⟩
      have hnhds : Set.Icc 0 H ∈ 𝓝 t := Icc_mem_nhds ht'.1 ht'.2
      exact (hg t ⟨ht.1, ht.2.le⟩).hasDerivAt hnhds |>.hasDerivWithinAt
  have hfield (g : ℝ → Concentration S) (hhist : ∀ t ≤ 0, g t = φ t)
      (t : ℝ) (ht : t ∈ Set.Icc 0 H) :
      N.delayField κ τ g t = f t (g t) := by
    have hdel : ∀ r, g (t - τ r) = (if τ r = 0 then g t else φ (t - τ r)) := by
      intro r
      by_cases hzero : τ r = 0
      · simp [hzero]
      · have hpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hzero)
        have harg : t - τ r ≤ 0 := by
          have := hgap r hpos
          linarith [ht.2, hHd]
        rw [hhist (t - τ r) harg]
        simp [hzero]
    have : (fun r => g (t - τ r)) =
        (fun r => if τ r = 0 then g t else φ (t - τ r)) := funext hdel
    change N.massActionDelayField κ (g t) (fun r => g (t - τ r)) = _
    rw [this]
  have hx' : ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt x (f t (x t)) (Set.Ici t) t := by
    intro t ht
    have hderiv : ∀ s ∈ Set.Icc 0 H,
        HasDerivWithinAt x (f s (x s)) (Set.Icc 0 H) s := by
      intro s hs
      have hsource := hx s ⟨hs.1, hs.2.trans hHT⟩
      have hsource' := hsource.congr_deriv (hfield x hxhist s hs)
      exact hsource'.mono (by
        intro z hz
        exact ⟨hz.1, hz.2.trans hHT⟩)
    exact hright x hderiv t ht
  have hy' : ∀ t ∈ Set.Ico 0 H, HasDerivWithinAt y (f t (y t)) (Set.Ici t) t := by
    intro t ht
    have hderiv : ∀ s ∈ Set.Icc 0 H,
        HasDerivWithinAt y (f s (y s)) (Set.Icc 0 H) s := by
      intro s hs
      have hsource := hy s ⟨hs.1, hs.2.trans hHT⟩
      have hsource' := hsource.congr_deriv (hfield y hyhist s hs)
      exact hsource'.mono (by
        intro z hz
        exact ⟨hz.1, hz.2.trans hHT⟩)
    exact hright y hderiv t ht
  have hxcont' : ContinuousOn x (Set.Icc 0 H) := hxcont.mono (by
    intro t ht
    exact ⟨ht.1, ht.2.trans hHT⟩)
  have hycont' : ContinuousOn y (Set.Icc 0 H) := hycont.mono (by
    intro t ht
    exact ⟨ht.1, ht.2.trans hHT⟩)
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := f) (s := fun _ => Metric.closedBall (0 : Concentration S) B) (K := K)
    hv hxcont' hx' (fun t ht => hxBall t ⟨ht.1, ht.2.le⟩)
    hycont' hy' (fun t ht => hyBall t ⟨ht.1, ht.2.le⟩) (hx₀.trans hy₀.symm)
  exact fun t ht => heq ht

/-- **Finite-interval uniqueness for delayed mass-action solutions.** Two solutions with the same
history and initial state agree on every common finite interval. The proof derives the minimum
positive delay from the finite reaction family, then applies local ODE uniqueness successively;
compactness of the two paths supplies each local Lipschitz ball. -/
theorem massActionDelay_solution_unique
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hτ : ∀ r, 0 ≤ τ r) (φ : ℝ → Concentration S)
    {x y : ℝ → Concentration S}
    (hxhist : ∀ t ≤ 0, x t = φ t) (hyhist : ∀ t ≤ 0, y t = φ t)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, x t = y t := by
  obtain ⟨d, hd, hgap⟩ := massActionDelay_exists_positive_step N τ
  let n : ℕ := Nat.ceil (T / d)
  have hsteps : T ≤ (n : ℝ) * d := by
    have hceil : T / d ≤ (n : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hd).mp hceil
    simpa [n] using hmul
  have hall : ∀ k : ℕ, ∀ q ≤ min T ((k : ℝ) * d), x q = y q := by
    intro k
    induction k with
    | zero =>
        intro q hq
        have hmin : min T ((0 : ℕ) * d) = 0 := by simp [hT]
        rw [hmin] at hq
        rw [hxhist q hq, hyhist q hq]
    | succ k ih =>
        intro q hq
        let c : ℝ := min T ((k : ℝ) * d)
        let e : ℝ := min T (((k + 1 : ℕ) : ℝ) * d)
        have hstep : c ≤ e := by
          dsimp [c, e]
          exact min_le_min_left T (by push_cast; nlinarith [hd])
        by_cases hcT : T ≤ c
        · have heq : e = T := by
            apply min_eq_left
            have hTkd : T ≤ (k : ℝ) * d := le_trans hcT (min_le_right _ _)
            have hsucc : (k : ℝ) * d ≤ ((k + 1 : ℕ) : ℝ) * d := by
              push_cast
              nlinarith [hd]
            exact le_trans hTkd hsucc
          have hc_eq : c = T := le_antisymm (min_le_left _ _) hcT
          have hqprev : q ≤ c := by
            have hqT : q ≤ T := le_trans hq (by simpa [heq] using min_le_left T _)
            simpa [hc_eq] using hqT
          exact ih q (by simpa [c] using hqprev)
        · have hc_lt : c < T := lt_of_not_ge hcT
          have hkd : (k : ℝ) * d < T := by
            by_contra hnot
            have hTle : T ≤ (k : ℝ) * d := le_of_not_gt hnot
            have : c = T := min_eq_left hTle
            exact hc_lt.ne this
          have hc_eq : c = (k : ℝ) * d := min_eq_right hkd.le
          have hc0 : 0 ≤ c := by
            dsimp [c]
            positivity
          have he_upper : e ≤ c + d := by
            calc
              e ≤ ((k + 1 : ℕ) : ℝ) * d := min_le_right _ _
              _ = (k : ℝ) * d + d := by push_cast; ring
              _ = c + d := by rw [hc_eq]
          have hdelta : 0 < e - c := by
            rw [hc_eq] at *
            dsimp [e]
            have hsucc : (k : ℝ) * d < ((k + 1 : ℕ) : ℝ) * d := by
              push_cast
              nlinarith [hd]
            have := lt_min hkd hsucc
            linarith
          have hdelta_le : e - c ≤ d := by linarith
          have hprev : ∀ q ≤ c, x q = y q := by
            intro q hq'
            exact ih q (by simpa [c] using hq')
          let xs : ℝ → Concentration S := fun u => x (u + c)
          let ys : ℝ → Concentration S := fun u => y (u + c)
          let ψ : ℝ → Concentration S := xs
          have hψ : ∀ u ≤ 0, ys u = ψ u := by
            intro u hu
            dsimp [ys, ψ, xs]
            exact (hprev (u + c) (by linarith)).symm
          have hxs₀ : xs 0 = x c := by simp [xs]
          have hys₀ : ys 0 = x c := by
            simpa [ys] using (hprev c le_rfl).symm
          have hxs : ∀ u ∈ Set.Icc 0 (e - c),
              HasDerivWithinAt xs (N.delayField κ τ xs u) (Set.Icc 0 (e - c)) u := by
            intro u hu
            have huT : u + c ∈ Set.Icc 0 T := by
              constructor
              · exact add_nonneg hu.1 hc0
              · have : u + c ≤ e := by calc
                  u + c ≤ (e - c) + c := by nlinarith [hu.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have htrans : HasDerivWithinAt (fun v : ℝ => v + c) 1
                (Set.Icc 0 (e - c)) u := (hasDerivAt_id u).add_const c |>.hasDerivWithinAt
            have hmap : MapsTo (fun v : ℝ => v + c) (Set.Icc 0 (e - c)) (Set.Icc 0 T) := by
              intro v hv
              constructor
              · exact add_nonneg hv.1 hc0
              · have : v + c ≤ e := by calc
                  v + c ≤ (e - c) + c := by nlinarith [hv.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have hcomp := (hx (u + c) huT).scomp u htrans hmap
            have hdelay : N.delayField κ τ xs u = N.delayField κ τ x (u + c) := by
              simp [xs, Network.delayField, massActionDelayField_delayField]
              congr 1
              funext r
              ring
            simpa [xs, Function.comp_def, hdelay] using hcomp
          have hys : ∀ u ∈ Set.Icc 0 (e - c),
              HasDerivWithinAt ys (N.delayField κ τ ys u) (Set.Icc 0 (e - c)) u := by
            intro u hu
            have huT : u + c ∈ Set.Icc 0 T := by
              constructor
              · exact add_nonneg hu.1 hc0
              · have : u + c ≤ e := by calc
                  u + c ≤ (e - c) + c := by nlinarith [hu.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have htrans : HasDerivWithinAt (fun v : ℝ => v + c) 1
                (Set.Icc 0 (e - c)) u := (hasDerivAt_id u).add_const c |>.hasDerivWithinAt
            have hmap : MapsTo (fun v : ℝ => v + c) (Set.Icc 0 (e - c)) (Set.Icc 0 T) := by
              intro v hv
              constructor
              · exact add_nonneg hv.1 hc0
              · have : v + c ≤ e := by calc
                  v + c ≤ (e - c) + c := by nlinarith [hv.2]
                  _ = e := by ring
                exact le_trans this (min_le_left T _)
            have hcomp := (hy (u + c) huT).scomp u htrans hmap
            have hdelay : N.delayField κ τ ys u = N.delayField κ τ y (u + c) := by
              simp [ys, Network.delayField, massActionDelayField_delayField]
              congr 1
              funext r
              ring
            simpa [ys, Function.comp_def, hdelay] using hcomp
          have hsame := N.massActionDelay_firstStep_unique κ τ d (e - c)
            hd hdelta hτ hgap ψ (x c)
            (fun _ _ => rfl) hψ hxs₀ hys₀ hxs hys
          have hmin : min d (e - c) = e - c := min_eq_right hdelta_le
          by_cases hqc : q ≤ c
          · exact hprev q hqc
          · have hqge : c ≤ q := le_of_lt (lt_of_not_ge hqc)
            have hqshift : q - c ∈ Set.Icc (0 : ℝ) (e - c) := by
              constructor <;> linarith
            have hq' := hsame (q - c) (by simpa [hmin] using hqshift)
            have heq_q : (q - c) + c = q := sub_add_cancel _ _
            simpa [xs, ys, ψ, heq_q] using hq'
  intro t ht
  have hlast : min T ((n : ℝ) * d) = T := min_eq_left hsteps
  have ht' : t ≤ min T ((n : ℝ) * d) := by simpa [hlast] using ht.2
  exact hall n t ht'

/-! The following derivative formula separates the network geometry from the conservation
condition: the derivative of the weighted delayed inventory is the weighted stoichiometric
change of each reaction, evaluated at that reaction's delayed source state. -/
theorem delayConservedQuantity_hasDerivWithinAt
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (T : ℝ) (w : S → ℝ)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (N.delayConservedQuantity κ τ w x)
      (∑ r, κ.k r * (N.reaction r).source.massActionMonomial (x (t - τ r)) *
        ∑ s, w s * (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)))
      (Set.Icc 0 T) t := by
  have hmc : ∀ r, Continuous fun u => (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    unfold Complex.massActionMonomial
    exact continuous_finsetProd _ fun s _ => ((continuous_apply s).comp hxc).pow _
  set m : N.R → ℝ → ℝ := fun r u => (N.reaction r).source.massActionMonomial (x u)
  have hint : ∀ r t, HasDerivAt (fun t => ∫ u in (t - τ r)..t, m r u)
      (m r t - m r (t - τ r)) t := by
    intro r t
    have hG := fun t => ((hmc r).integral_hasStrictDerivAt 0 t).hasDerivAt
    have hsplit : (fun t => ∫ u in (t - τ r)..t, m r u) =
        fun t => (∫ u in (0 : ℝ)..t, m r u) - ∫ u in (0 : ℝ)..(t - τ r), m r u := by
      funext t
      rw [intervalIntegral.integral_interval_sub_left
        ((hmc r).intervalIntegrable _ _) ((hmc r).intervalIntegrable _ _)]
    rw [hsplit]
    have h2 : HasDerivAt (fun t => ∫ u in (0 : ℝ)..(t - τ r), m r u)
        (m r (t - τ r)) t := HasDerivAt.comp_sub_const t (τ r) (hG (t - τ r))
    exact (hG t).sub h2
  have hcoord : ∀ s, HasDerivWithinAt (fun t => x t s)
      (N.delayField κ τ x t s) (Set.Icc 0 T) t := fun s =>
        (hasDerivWithinAt_pi.mp (hx t ht)) s
  have h1 : HasDerivWithinAt (fun t => ∑ s, w s * x t s)
      (∑ s, w s * N.delayField κ τ x t s) (Set.Icc 0 T) t :=
    HasDerivWithinAt.fun_sum fun s _ => (hcoord s).const_mul (w s)
  have h2 : HasDerivWithinAt (fun t => ∑ r, κ.k r *
      (∑ s, w s * ((N.reaction r).source s : ℝ)) *
        ∫ u in (t - τ r)..t, m r u)
      (∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
        (m r t - m r (t - τ r))) (Set.Icc 0 T) t :=
    HasDerivWithinAt.fun_sum fun r _ => (hint r t).hasDerivWithinAt.const_mul _
  have hfun : N.delayConservedQuantity κ τ w x = fun t => (∑ s, w s * x t s) +
      ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
        ∫ u in (t - τ r)..t, m r u := rfl
  rw [hfun]
  refine (h1.add h2).congr_deriv ?_
  have e1 : ∑ s, w s * N.delayField κ τ x t s =
      ∑ r, ∑ s, w s * (κ.k r *
        (m r (t - τ r) * ((N.reaction r).target s : ℝ) -
          m r t * ((N.reaction r).source s : ℝ))) := by
    simp only [delayField, Finset.mul_sum]
    exact Finset.sum_comm
  rw [e1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsum : ∑ s, w s * (κ.k r *
      (m r (t - τ r) * ((N.reaction r).target s : ℝ) -
        m r t * ((N.reaction r).source s : ℝ))) =
      κ.k r * m r (t - τ r) * ∑ s, w s *
        (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) +
      κ.k r * (m r (t - τ r) - m r t) *
        ∑ s, w s * ((N.reaction r).source s : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hsum]
  simp only [m]
  ring

/-- The delayed conservation functional remains constant on any finite solution interval.
Unlike `delayConservedQuantity_const`, this statement assumes the delay equation only on
`[0,T]`; it is therefore usable in a continuation argument without presupposing a global
solution. Continuity of the full path supplies the history regularity needed by the integral
terms. -/
theorem delayConservedQuantity_const_on
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (T : ℝ)
    {w : S → ℝ} (hw : w ∈ orthSum N.stoichSubspace)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    N.delayConservedQuantity κ τ w x t = N.delayConservedQuantity κ τ w x 0 := by
  have hmc : ∀ r, Continuous fun u => (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    unfold Complex.massActionMonomial
    exact continuous_finsetProd _ fun s _ => ((continuous_apply s).comp hxc).pow _
  set m : N.R → ℝ → ℝ := fun r u => (N.reaction r).source.massActionMonomial (x u)
  have hprimitive : ∀ r, Continuous fun t => ∫ u in (0 : ℝ)..t, m r u := by
    intro r
    exact continuous_iff_continuousAt.2 fun t =>
      (((hmc r).integral_hasStrictDerivAt 0 t).hasDerivAt).continuousAt
  have hsplit (r : N.R) : (fun t => ∫ u in (t - τ r)..t, m r u) =
      fun t => (∫ u in (0 : ℝ)..t, m r u) - ∫ u in (0 : ℝ)..(t - τ r), m r u := by
    funext t
    rw [intervalIntegral.integral_interval_sub_left
      ((hmc r).intervalIntegrable _ _) ((hmc r).intervalIntegrable _ _)]
  have hcontQ : ContinuousOn (N.delayConservedQuantity κ τ w x) (Set.Icc 0 T) := by
    have hcont : Continuous (N.delayConservedQuantity κ τ w x) := by
      change Continuous (fun t => (∑ s, w s * x t s) +
        ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
          ∫ u in (t - τ r)..t, m r u)
      apply Continuous.add
      · exact continuous_finsetSum Finset.univ fun s _ =>
          ((continuous_apply s).comp hxc).const_mul _
      · apply continuous_finsetSum
        intro r hr
        have hInt : Continuous fun t => ∫ u in (t - τ r)..t, m r u := by
          rw [hsplit r]
          exact (hprimitive r).sub ((hprimitive r).comp (continuous_id.sub continuous_const))
        exact hInt.const_mul _
    exact hcont.continuousOn
  have hderiv : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (N.delayConservedQuantity κ τ w x) 0 (Set.Icc 0 T) t := by
    intro t ht
    have hformula := N.delayConservedQuantity_hasDerivWithinAt κ τ T w hxc hx t
      (Ico_subset_Icc_self ht)
    have hperp : ∀ r, ∑ s, w s * N.reactionVector r s = 0 := fun r =>
      (mem_orthSum.mp hw) _ (N.reactionVector_mem_stoichSubspace r)
    refine hformula.congr_deriv ?_
    apply Finset.sum_eq_zero
    intro r hr
    have hp := hperp r
    simp only [reactionVector_apply] at hp
    simp [hp]
  have hright : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (N.delayConservedQuantity κ τ w x) 0 (Set.Ici t) t := by
    intro t ht
    exact (hderiv t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hconst := constant_of_has_deriv_right_zero hcontQ hright
  exact hconst t ht

/-- If every reaction weakly decreases a positive weighted total, its delayed inventory is
nonincreasing. The delayed inventory includes the reactant mass still in transit, so its derivative
is the weighted reaction loss evaluated at the delayed source state. -/
theorem delayConservedQuantity_antitone_on
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (T D : ℝ)
    (hT : 0 ≤ T) (hτ : ∀ r, 0 ≤ τ r) (hτD : ∀ r, τ r ≤ D)
    (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hxnonneg : ∀ t ∈ Set.Icc (-D) T, ∀ s, 0 ≤ x t s) :
    ∀ t ∈ Set.Icc 0 T,
      N.delayConservedQuantity κ τ w x t ≤ N.delayConservedQuantity κ τ w x 0 := by
  have hmc : ∀ r, Continuous fun u => (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    unfold Complex.massActionMonomial
    exact continuous_finsetProd _ fun s _ => ((continuous_apply s).comp hxc).pow _
  set m : N.R → ℝ → ℝ := fun r u => (N.reaction r).source.massActionMonomial (x u)
  have hprimitive : ∀ r, Continuous fun t => ∫ u in (0 : ℝ)..t, m r u := by
    intro r
    exact continuous_iff_continuousAt.2 fun t =>
      (((hmc r).integral_hasStrictDerivAt 0 t).hasDerivAt).continuousAt
  have hsplit (r : N.R) : (fun t => ∫ u in (t - τ r)..t, m r u) =
      fun t => (∫ u in (0 : ℝ)..t, m r u) - ∫ u in (0 : ℝ)..(t - τ r), m r u := by
    funext t
    rw [intervalIntegral.integral_interval_sub_left
      ((hmc r).intervalIntegrable _ _) ((hmc r).intervalIntegrable _ _)]
  have hcontQ : ContinuousOn (N.delayConservedQuantity κ τ w x) (Set.Icc 0 T) := by
    have hcont : Continuous (N.delayConservedQuantity κ τ w x) := by
      change Continuous (fun t => (∑ s, w s * x t s) +
        ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
          ∫ u in (t - τ r)..t, m r u)
      apply Continuous.add
      · exact continuous_finsetSum Finset.univ fun s _ =>
          ((continuous_apply s).comp hxc).const_mul _
      · apply continuous_finsetSum
        intro r hr
        have hInt : Continuous fun t => ∫ u in (t - τ r)..t, m r u := by
          rw [hsplit r]
          exact (hprimitive r).sub ((hprimitive r).comp (continuous_id.sub continuous_const))
        exact hInt.const_mul _
    exact hcont.continuousOn
  have hformula : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (N.delayConservedQuantity κ τ w x)
        (∑ r, κ.k r * (N.reaction r).source.massActionMonomial (x (t - τ r)) *
          ∑ s, w s * (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)))
        (Set.Icc 0 T) t := by
    intro t ht
    exact N.delayConservedQuantity_hasDerivWithinAt κ τ T w hxc hx t ht
  have hanti : AntitoneOn (N.delayConservedQuantity κ τ w x) (Set.Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (fun t ht => (hformula t ht).continuousWithinAt)
      (fun t ht => (hformula t (interior_subset ht)).mono interior_subset) ?_
    intro t ht
    apply Finset.sum_nonpos
    intro r hr
    have htIcc : t ∈ Set.Icc 0 T := interior_subset ht
    have htDelay : t - τ r ∈ Set.Icc (-D) T := by
      constructor <;> linarith [htIcc.1, htIcc.2, hτ r, hτD r]
    have hmon : 0 ≤ (N.reaction r).source.massActionMonomial (x (t - τ r)) :=
      Complex.massActionMonomial_nonneg (hxnonneg (t - τ r) htDelay) (N.reaction r).source
    have hrate : 0 ≤ κ.k r *
        (N.reaction r).source.massActionMonomial (x (t - τ r)) :=
      mul_nonneg (κ.positive r).le hmon
    have hdelta : ∑ s, w s *
        (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) ≤ 0 := by
      calc
        _ = ∑ s, (w s * ((N.reaction r).target s : ℝ) -
            w s * ((N.reaction r).source s : ℝ)) := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = (∑ s, w s * ((N.reaction r).target s : ℝ)) -
            ∑ s, w s * ((N.reaction r).source s : ℝ) := by
          rw [← Finset.sum_sub_distrib]
        _ ≤ 0 := sub_nonpos.mpr (hsub r)
    exact mul_nonpos_of_nonneg_of_nonpos hrate hdelta
  intro t ht
  exact hanti ⟨le_rfl, hT⟩ ht ht.1

/-- **Finite-interval a priori bound from a nonincreasing delayed inventory.** The equation is
needed only on `[0,T]`; nonnegativity is assumed on the history window that feeds this interval.
This estimate can be used before continuation has been established. -/
theorem delayConservedQuantity_coord_bound_on_of_antitone
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ) (T D : ℝ)
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r) (hτD : ∀ r, τ r ≤ D)
    (hwpos : ∀ s, 0 < w s)
    {x : ℝ → Concentration S}
    (hxnonneg : ∀ t ∈ Set.Icc (-D) T, ∀ s, 0 ≤ x t s)
    (hQanti : ∀ t ∈ Set.Icc 0 T,
      N.delayConservedQuantity κ τ w x t ≤ N.delayConservedQuantity κ τ w x 0) :
    0 ≤ N.delayConservedQuantity κ τ w x 0 ∧
      ∀ t ∈ Set.Icc 0 T, ∀ s, x t s ≤ N.delayConservedQuantity κ τ w x 0 / w s := by
  have hmon_nonneg : ∀ r t, t ∈ Set.Icc 0 T → 0 ≤
      ∫ u in (t - τ r)..t, (N.reaction r).source.massActionMonomial (x u) := by
    intro r t ht
    apply intervalIntegral.integral_nonneg (by linarith [hτ r])
    intro u hu
    have huD : u ∈ Set.Icc (-D) T := by
      constructor <;> rcases ht with ⟨ht0, htT⟩ <;> rcases hu with ⟨huL, huU⟩
      · linarith [hτD r]
      · linarith
    exact Complex.massActionMonomial_nonneg (hxnonneg u huD) (N.reaction r).source
  have hsource_nonneg (r : N.R) :
      0 ≤ ∑ s, w s * ((N.reaction r).source s : ℝ) := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
  have hQnonneg : 0 ≤ N.delayConservedQuantity κ τ w x 0 := by
    unfold delayConservedQuantity
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro s hs
      have h0 : (0 : ℝ) ∈ Set.Icc (-D) T := ⟨by linarith, hT⟩
      exact mul_nonneg (hwpos s).le (hxnonneg 0 h0 s)
    · apply Finset.sum_nonneg
      intro r hr
      exact mul_nonneg (mul_nonneg (κ.positive r).le (hsource_nonneg r))
        (hmon_nonneg r 0 ⟨le_rfl, hT⟩)
  have hsum_nonneg (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      0 ≤ ∑ s, w s * x t s := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hwpos s).le (hxnonneg t (Set.Icc_subset_Icc_left (by linarith) ht) s)
  have hcurrent_le (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      (∑ s, w s * x t s) ≤ N.delayConservedQuantity κ τ w x t := by
    unfold delayConservedQuantity
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (κ.positive r).le (hsource_nonneg r))
        (hmon_nonneg r t ht))
  refine ⟨hQnonneg, ?_⟩
  intro t ht s
  have hcoord_le : w s * x t s ≤ ∑ j, w j * x t j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hwpos j).le
      (hxnonneg t (Set.Icc_subset_Icc_left (by linarith) ht) j)) (Finset.mem_univ s)
  have hcoord : w s * x t s ≤ N.delayConservedQuantity κ τ w x 0 := by
    calc w s * x t s ≤ ∑ j, w j * x t j := hcoord_le
      _ ≤ N.delayConservedQuantity κ τ w x t := hcurrent_le t ht
      _ ≤ N.delayConservedQuantity κ τ w x 0 := hQanti t ht
  exact (le_div_iff₀ (hwpos s)).2 (by simpa [mul_comm] using hcoord)


/-- The conserved-inventory estimate is the equality case of the monotone-inventory bound. -/
theorem delayConservedQuantity_coord_bound_on
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ) (T D : ℝ)
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r) (hτD : ∀ r, τ r ≤ D)
    (hw : w ∈ orthSum N.stoichSubspace) (hwpos : ∀ s, 0 < w s)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hxnonneg : ∀ t ∈ Set.Icc (-D) T, ∀ s, 0 ≤ x t s) :
    0 ≤ N.delayConservedQuantity κ τ w x 0 ∧
      ∀ t ∈ Set.Icc 0 T, ∀ s, x t s ≤ N.delayConservedQuantity κ τ w x 0 / w s := by
  apply delayConservedQuantity_coord_bound_on_of_antitone N κ τ w T D hT hD hτ hτD
    hwpos hxnonneg ?_
  intro t ht
  rw [N.delayConservedQuantity_const_on κ τ T hw hxc hx t ht]

/-- The finite-interval coordinate estimate gives a uniform norm bound on the same interval. -/
theorem delayConservedQuantity_norm_bound_on
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ) (T D : ℝ)
    [Nonempty S] (hT : 0 ≤ T) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (hw : w ∈ orthSum N.stoichSubspace)
    (hwpos : ∀ s, 0 < w s) {x : ℝ → Concentration S} (hxc : Continuous x)
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t)
    (hxnonneg : ∀ t ∈ Set.Icc (-D) T, ∀ s, 0 ≤ x t s) :
    ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ N.delayConservedQuantity κ τ w x 0 /
      ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)) := by
  obtain ⟨hQ, hcoord⟩ := delayConservedQuantity_coord_bound_on N κ τ w T D hT hD hτ
    hτD hw hwpos hxc hx hxnonneg
  let wmin := (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hwmin : wmin ∈ Finset.univ.image w := Finset.min'_mem _ _
  obtain ⟨s₀, hs₀, hws₀⟩ := Finset.mem_image.mp hwmin
  have hmin : 0 < wmin := by rw [← hws₀]; exact hwpos s₀
  have hmin_le (s : S) : wmin ≤ w s :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ s))
  have hB : 0 ≤ N.delayConservedQuantity κ τ w x 0 / wmin := div_nonneg hQ hmin.le
  intro t ht
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro s
  have hup := hcoord t ht s
  have hden : N.delayConservedQuantity κ τ w x 0 / w s ≤
      N.delayConservedQuantity κ τ w x 0 / wmin := by
    apply (div_le_div_iff₀ (hwpos s) hmin).2
    nlinarith [hQ, hmin_le s]
  have htop := le_trans hup hden
  exact abs_le.mpr ⟨by linarith [hB, hxnonneg t (Set.Icc_subset_Icc_left (by linarith) ht) s], htop⟩

/-- Norm boundedness when the weighted delayed inventory is nonincreasing. -/
theorem delayConservedQuantity_norm_bound_on_of_antitone
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ) (T D : ℝ)
    [Nonempty S] (hT : 0 ≤ T) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (hwpos : ∀ s, 0 < w s) {x : ℝ → Concentration S}
    (hxnonneg : ∀ t ∈ Set.Icc (-D) T, ∀ s, 0 ≤ x t s)
    (hQanti : ∀ t ∈ Set.Icc 0 T,
      N.delayConservedQuantity κ τ w x t ≤ N.delayConservedQuantity κ τ w x 0) :
    ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ N.delayConservedQuantity κ τ w x 0 /
      ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)) := by
  obtain ⟨hQ, hcoord⟩ := delayConservedQuantity_coord_bound_on_of_antitone N κ τ w T D
    hT hD hτ hτD hwpos hxnonneg hQanti
  let wmin := (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hwmin : wmin ∈ Finset.univ.image w := Finset.min'_mem _ _
  obtain ⟨s₀, hs₀, hws₀⟩ := Finset.mem_image.mp hwmin
  have hmin : 0 < wmin := by rw [← hws₀]; exact hwpos s₀
  have hmin_le (s : S) : wmin ≤ w s :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ s))
  have hB : 0 ≤ N.delayConservedQuantity κ τ w x 0 / wmin := div_nonneg hQ hmin.le
  intro t ht
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro s
  have hup := hcoord t ht s
  have hden : N.delayConservedQuantity κ τ w x 0 / w s ≤
      N.delayConservedQuantity κ τ w x 0 / wmin := by
    apply (div_le_div_iff₀ (hwpos s) hmin).2
    nlinarith [hQ, hmin_le s]
  have htop := le_trans hup hden
  have hnonneg_t := hxnonneg t (Set.Icc_subset_Icc_left (by linarith) ht) s
  exact abs_le.mpr ⟨by linarith [hB, hnonneg_t], htop⟩

/-- The delayed conservation functional at time zero depends only on the nonpositive history. -/
theorem delayConservedQuantity_zero_congr
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) {x y : ℝ → Concentration S}
    (hxy : ∀ t ≤ 0, x t = y t) :
    N.delayConservedQuantity κ τ w x 0 = N.delayConservedQuantity κ τ w y 0 := by
  unfold delayConservedQuantity
  rw [hxy 0 le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℝ => κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) * z)
  apply intervalIntegral.integral_congr
  intro u hu
  change (N.reaction r).source.massActionMonomial (x u) =
    (N.reaction r).source.massActionMonomial (y u)
  rw [hxy u (by
    have hu' : u ∈ Set.uIcc (0 - τ r) 0 := hu
    rw [Set.uIcc_of_le (by linarith [hτ r])] at hu'
    exact hu'.2)]

/-- A positive conservation weight bounds the initial state directly from its nonnegative
continuous history, before any solution is constructed. -/
theorem delayConservedQuantity_initial_norm_bound
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ)
    [Nonempty S] (hτ : ∀ r, 0 ≤ τ r) (hwpos : ∀ s, 0 < w s)
    (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    0 ≤ N.delayConservedQuantity κ τ w φ 0 ∧
      ‖φ 0‖ ≤ N.delayConservedQuantity κ τ w φ 0 /
        ((Finset.univ.image w).min'
          (Finset.image_nonempty.mpr Finset.univ_nonempty)) := by
  let wmin := (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hwmin : wmin ∈ Finset.univ.image w := Finset.min'_mem _ _
  obtain ⟨s₀, hs₀, hws₀⟩ := Finset.mem_image.mp hwmin
  have hwminpos : 0 < wmin := by rw [← hws₀]; exact hwpos s₀
  have hwmin_le (s : S) : wmin ≤ w s :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ s))
  have hsource (r : N.R) : 0 ≤ ∑ s, w s * ((N.reaction r).source s : ℝ) := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
  have hmon (r : N.R) : 0 ≤
      ∫ u in (0 - τ r)..(0 : ℝ), (N.reaction r).source.massActionMonomial (φ u) := by
    apply intervalIntegral.integral_nonneg (by linarith [hτ r])
    intro u hu
    exact Complex.massActionMonomial_nonneg (hφnonneg u (by linarith [hu.2]))
      (N.reaction r).source
  have hQ : 0 ≤ N.delayConservedQuantity κ τ w φ 0 := by
    unfold delayConservedQuantity
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg (hwpos s).le (hφnonneg 0 le_rfl s)
    · apply Finset.sum_nonneg
      intro r hr
      exact mul_nonneg (mul_nonneg (κ.positive r).le (hsource r)) (hmon r)
  have hcurrent : (∑ s, w s * φ 0 s) ≤ N.delayConservedQuantity κ τ w φ 0 := by
    unfold delayConservedQuantity
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (κ.positive r).le (hsource r)) (hmon r))
  have hcoord (s : S) : φ 0 s ≤ N.delayConservedQuantity κ τ w φ 0 / w s := by
    have hsingle : w s * φ 0 s ≤ ∑ j, w j * φ 0 j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hwpos j).le
        (hφnonneg 0 le_rfl j)) (Finset.mem_univ s)
    have hpair : w s * φ 0 s ≤ N.delayConservedQuantity κ τ w φ 0 :=
      le_trans hsingle (le_trans hcurrent (by rfl))
    exact (le_div_iff₀ (hwpos s)).2 (by simpa [mul_comm] using hpair)
  have hbound_nonneg : 0 ≤ N.delayConservedQuantity κ τ w φ 0 / wmin :=
    div_nonneg hQ hwminpos.le
  have hden (s : S) : N.delayConservedQuantity κ τ w φ 0 / w s ≤
      N.delayConservedQuantity κ τ w φ 0 / wmin := by
    apply (div_le_div_iff₀ (hwpos s) hwminpos).2
    nlinarith [hQ, hwmin_le s]
  have hnorm : ‖φ 0‖ ≤ N.delayConservedQuantity κ τ w φ 0 / wmin := by
    apply (pi_norm_le_iff_of_nonneg hbound_nonneg).2
    intro s
    exact abs_le.mpr ⟨by linarith [hφnonneg 0 le_rfl s], le_trans (hcoord s) (hden s)⟩
  exact ⟨hQ, by simpa [wmin] using hnorm⟩

/-- Start with a nonnegative history and obtain a first step with a weight-loss bound. The step
length is chosen uniformly from the initial-history and nonincreasing-inventory bounds. -/
theorem massActionDelay_weighted_loss_first_step
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (d D H₀ : ℝ)
    [Nonempty S] (hd : 0 < d) (hD : 0 ≤ D)
    (hτ : ∀ r, 0 ≤ τ r) (hgap : ∀ r, 0 < τ r → d ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s)
    (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s)
    (hφbound : ∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H₀) :
    ∃ h : ℝ, 0 < h ∧ h ≤ d ∧
      (∀ (ψ : ℝ → Concentration S), Continuous ψ →
        (∀ t ∈ Set.Icc (-D) 0,
          ‖ψ t‖ ≤ max H₀ (N.delayConservedQuantity κ τ w φ 0 /
            ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)))) →
        ∀ x₀ : Concentration S,
        ‖x₀‖ ≤ N.delayConservedQuantity κ τ w φ 0 /
          ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)) →
        ψ 0 = x₀ → ∃ z : ℝ → Concentration S,
          Continuous z ∧ (∀ t ≤ 0, z t = ψ t) ∧ z 0 = x₀ ∧
          ∀ t ∈ Set.Icc 0 h,
            HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t) ∧
      ∃ x : ℝ → Concentration S,
      Continuous x ∧ (∀ t ≤ 0, x t = φ t) ∧
      (∀ t ∈ Set.Icc (-D) h, ∀ s, 0 ≤ x t s) ∧
      (∀ t ∈ Set.Icc 0 h, ‖x t‖ ≤
        N.delayConservedQuantity κ τ w φ 0 /
          ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty))) ∧
      ∀ t ∈ Set.Icc 0 h,
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 h) t := by
  let wmin : ℝ := (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hwmin_mem : wmin ∈ Finset.univ.image w := Finset.min'_mem _ _
  have hwmin : 0 < wmin := by
    obtain ⟨s, hs, hws⟩ := Finset.mem_image.mp hwmin_mem
    rw [← hws]
    exact hwpos s
  obtain ⟨hQ, hφ₀⟩ := N.delayConservedQuantity_initial_norm_bound κ τ w hτ hwpos φ hφ
    hφnonneg
  let B := N.delayConservedQuantity κ τ w φ 0 / wmin
  have hB : 0 ≤ B := div_nonneg hQ hwmin.le
  have hφ₀B : ‖φ 0‖ ≤ B := by simpa [B, wmin] using hφ₀
  let H := max H₀ B
  have hH : 0 ≤ H := by
    have hH₀ : 0 ≤ H₀ := by
      have := hφbound 0 ⟨by linarith [hD], le_rfl⟩
      exact le_trans (norm_nonneg _) this
    exact le_max_of_le_right hB
  have hH₀H : H₀ ≤ H := le_max_left _ _
  obtain ⟨h, hh, hhd, hrestart⟩ := N.massActionDelay_local_exists_uniform_continuous κ τ d D B H
    hd hB hH hτ hgap hτD
  obtain ⟨x, hxc, hxhist, hx₀, hx⟩ := hrestart φ hφ
    (fun t ht => le_trans (hφbound t ht) hH₀H) (φ 0) hφ₀B rfl
  have hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (0 - τ r) 0 → 0 ≤ x q s := by
    intro r s q hq
    rw [hxhist q hq.2]
    exact hφnonneg q hq.2 s
  have hstart : ∀ s, 0 ≤ x 0 s := by
    intro s
    rw [hxhist 0 le_rfl]
    exact hφnonneg 0 le_rfl s
  have hpos := N.delayField_nonneg_of_nonnegative_delays κ τ hh.le hτ hx hhistory hstart
  have hxnonneg : ∀ t ∈ Set.Icc (-D) h, ∀ s, 0 ≤ x t s := by
    intro t ht s
    by_cases ht0 : t ≤ 0
    · rw [hxhist t ht0]
      exact hφnonneg t ht0 s
    · exact hpos t ⟨le_of_not_ge ht0, ht.2⟩ s
  have hQanti := N.delayConservedQuantity_antitone_on κ τ h D hh.le hτ hτD
    w hsub hxc hx hxnonneg
  have hbound := N.delayConservedQuantity_norm_bound_on_of_antitone κ τ w h D
    hh.le hD hτ hτD hwpos hxnonneg hQanti
  have hQeq := N.delayConservedQuantity_zero_congr κ τ w hτ hxhist
  refine ⟨h, hh, hhd, ?_, x, hxc, hxhist, hxnonneg, ?_, hx⟩
  · intro ψ hψ hψbound x₀ hx₀ hψ₀
    exact hrestart ψ hψ (fun t ht => hψbound t ht) x₀ hx₀ hψ₀
  · intro t ht
    rw [hQeq] at hbound
    simpa [B, wmin] using hbound t ht

/-- A uniform restart preserves positivity and the conservation-law norm bound.  The delayed
invariance theorem supplies nonnegativity on the new slab; the finite-interval conservation
estimate then recovers the same bound from the unchanged history functional. -/
theorem massActionDelay_uniform_restart_nonneg
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (D B H h a : ℝ)
    [Nonempty S] (hh : 0 < h) (hD : 0 ≤ D)
    (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (ha : 0 ≤ a)
    (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s)
    (hrestart : ∀ (φ : ℝ → Concentration S), Continuous φ →
      (∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → φ 0 = x₀ → ∃ z : ℝ → Concentration S,
        Continuous z ∧ (∀ t ≤ 0, z t = φ t) ∧ z 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hxhistory : ∀ t ∈ Set.Icc (-D) 0, ∀ s, 0 ≤ x t s)
    (hxnonneg : ∀ t ∈ Set.Icc 0 a, ∀ s, 0 ≤ x t s)
    (hxStartBound : ‖x a‖ ≤ B)
    (hxBound : ∀ t ∈ Set.Icc (-D) a, ‖x t‖ ≤ H)
    (hx : ∀ t ∈ Set.Icc 0 a,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 a) t) :
    ∃ y : ℝ → Concentration S,
      Continuous y ∧ (∀ t ≤ a, y t = x t) ∧
      (∀ t ∈ Set.Icc (-D) (a + h), ∀ s, 0 ≤ y t s) ∧
      (∀ t ∈ Set.Icc 0 (a + h),
        ‖y t‖ ≤ N.delayConservedQuantity κ τ w y 0 /
          ((Finset.univ.image w).min'
            (Finset.image_nonempty.mpr Finset.univ_nonempty))) ∧
      ∀ t ∈ Set.Icc 0 (a + h),
        HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 (a + h)) t := by
  obtain ⟨y, hyc, hyold, hy⟩ := N.massActionDelay_uniform_restart κ τ D B H h a
    hh hτ ha hrestart hxc hxStartBound
    (fun t ht => hxBound t ⟨by linarith [ht.1, ha], ht.2⟩) hx
  have hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (0 - τ r) 0 → 0 ≤ y q s := by
    intro r s q hq
    rw [hyold q (by linarith [hq.2, ha])]
    exact hxhistory q ⟨by have := hq.1; linarith [hτD r, hD], hq.2⟩ s
  have hstart : ∀ s, 0 ≤ y 0 s := by
    intro s
    rw [hyold 0 ha]
    exact hxnonneg 0 ⟨le_rfl, ha⟩ s
  have hpos := N.delayField_nonneg_of_nonnegative_delays κ τ (show 0 ≤ a + h by linarith [ha, hh])
    hτ hy hhistory hstart
  have hyNonneg : ∀ t ∈ Set.Icc (-D) (a + h), ∀ s, 0 ≤ y t s := by
    intro t ht s
    by_cases ht0 : t ≤ 0
    · rw [hyold t (by linarith [ht0, ha])]
      exact hxhistory t ⟨ht.1, ht0⟩ s
    · exact hpos t ⟨le_of_not_ge ht0, ht.2⟩ s
  have hQanti := N.delayConservedQuantity_antitone_on κ τ (a + h) D
    (by linarith [ha, hh]) hτ hτD w hsub hyc hy hyNonneg
  have hbound := N.delayConservedQuantity_norm_bound_on_of_antitone κ τ w (a + h) D
    (by linarith [ha, hh]) hD hτ hτD hwpos hyNonneg hQanti
  refine ⟨y, hyc, hyold, hyNonneg, ?_, hy⟩
  intro t ht
  exact hbound t ht


/-- Restart a bounded trajectory with nonincreasing delayed inventory while retaining the bound computed from its
initial history. This is the exact induction step for finite-stage global continuation. -/
theorem massActionDelay_weighted_loss_restart_step
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (D B H₀ h a : ℝ)
    [Nonempty S] (hh : 0 < h) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (ha : 0 ≤ a)
    (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s)
    (φ : ℝ → Concentration S) (hφbound : ∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H₀)
    (hrestart : ∀ (ψ : ℝ → Concentration S), Continuous ψ →
      (∀ t ∈ Set.Icc (-D) 0, ‖ψ t‖ ≤ max H₀ B) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → ψ 0 = x₀ → ∃ z : ℝ → Concentration S,
        Continuous z ∧ (∀ t ≤ 0, z t = ψ t) ∧ z 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t)
    {x : ℝ → Concentration S} (hxc : Continuous x)
    (hxhist : ∀ t ≤ 0, x t = φ t)
    (hxnonneg : ∀ t ∈ Set.Icc (-D) a, ∀ s, 0 ≤ x t s)
    (hxBound : ∀ t ∈ Set.Icc 0 a, ‖x t‖ ≤ B)
    (hQ : N.delayConservedQuantity κ τ w x 0 = N.delayConservedQuantity κ τ w φ 0)
    (hx : ∀ t ∈ Set.Icc 0 a,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 a) t) :
    ∃ y : ℝ → Concentration S,
      Continuous y ∧ (∀ t ≤ a, y t = x t) ∧
      (∀ t ∈ Set.Icc (-D) (a + h), ∀ s, 0 ≤ y t s) ∧
      (∀ t ∈ Set.Icc 0 (a + h), ‖y t‖ ≤
        N.delayConservedQuantity κ τ w φ 0 /
          ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty))) ∧
      ∀ t ∈ Set.Icc 0 (a + h),
        HasDerivWithinAt y (N.delayField κ τ y t) (Set.Icc 0 (a + h)) t := by
  have hH₀ : 0 ≤ H₀ := by
    have hzero := hφbound 0 ⟨by linarith [hD], le_rfl⟩
    exact le_trans (norm_nonneg _) hzero
  have hB : 0 ≤ B := by
    have hzero := hxBound 0 ⟨le_rfl, ha⟩
    exact le_trans (norm_nonneg _) hzero
  have hH : 0 ≤ max H₀ B := le_max_of_le_right hB
  have hwindow : ∀ t ∈ Set.Icc (-D) a, ‖x t‖ ≤ max H₀ B := by
    intro t ht
    by_cases ht0 : t ≤ 0
    · rw [hxhist t ht0]
      exact le_trans (hφbound t ⟨ht.1, ht0⟩) (le_max_left _ _)
    · exact le_trans (hxBound t ⟨le_of_not_ge ht0, ht.2⟩) (le_max_right _ _)
  have hstart : ‖x a‖ ≤ B := hxBound a ⟨ha, le_rfl⟩
  have hxhistory : ∀ t ∈ Set.Icc (-D) 0, ∀ s, 0 ≤ x t s := by
    intro t ht s
    exact hxnonneg t ⟨ht.1, le_trans ht.2 ha⟩ s
  have hxnonneg' : ∀ t ∈ Set.Icc 0 a, ∀ s, 0 ≤ x t s := by
    intro t ht s
    exact hxnonneg t ⟨by linarith [ht.1, hD], ht.2⟩ s
  obtain ⟨y, hyc, hyold, hyNonneg, hyBound, hy⟩ :=
    N.massActionDelay_uniform_restart_nonneg κ τ D B (max H₀ B) h a
      hh hD hτ hτD ha w hsub hwpos hrestart hxc hxhistory hxnonneg' hstart
      (fun t ht => hwindow t ⟨by linarith [ht.1, hD], ht.2⟩) hx
  have hQy : N.delayConservedQuantity κ τ w y 0 =
      N.delayConservedQuantity κ τ w x 0 :=
    N.delayConservedQuantity_zero_congr κ τ w hτ (fun t ht => hyold t (le_trans ht ha))
  refine ⟨y, hyc, hyold, hyNonneg, ?_, hy⟩
  intro t ht
  rw [hQy, hQ] at hyBound
  exact hyBound t ht

/-- Iterating the weighted-loss restart step yields solutions on every finite number of uniform
steps, with one history-determined norm bound independent of the number of steps. -/
theorem massActionDelay_weighted_loss_finite_steps
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (D B H₀ h : ℝ)
    [Nonempty S] (hh : 0 < h) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s) (φ : ℝ → Concentration S)
    (hφbound : ∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H₀)
    (hB : B = N.delayConservedQuantity κ τ w φ 0 /
      ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)))
    (hrestart : ∀ (ψ : ℝ → Concentration S), Continuous ψ →
      (∀ t ∈ Set.Icc (-D) 0, ‖ψ t‖ ≤ max H₀ B) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → ψ 0 = x₀ → ∃ z : ℝ → Concentration S,
        Continuous z ∧ (∀ t ≤ 0, z t = ψ t) ∧ z 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t)
    {x₀ : ℝ → Concentration S} (hxc₀ : Continuous x₀)
    (hxhist₀ : ∀ t ≤ 0, x₀ t = φ t)
    (hxnonneg₀ : ∀ t ∈ Set.Icc (-D) h, ∀ s, 0 ≤ x₀ t s)
    (hxBound₀ : ∀ t ∈ Set.Icc 0 h, ‖x₀ t‖ ≤ B)
    (hQ₀ : N.delayConservedQuantity κ τ w x₀ 0 = N.delayConservedQuantity κ τ w φ 0)
    (hx₀ : ∀ t ∈ Set.Icc 0 h,
      HasDerivWithinAt x₀ (N.delayField κ τ x₀ t) (Set.Icc 0 h) t) :
    ∀ n : ℕ, ∃ x : ℝ → Concentration S,
      Continuous x ∧ (∀ t ≤ 0, x t = φ t) ∧
      (∀ t ∈ Set.Icc (-D) (((n : ℝ) + 1) * h), ∀ s, 0 ≤ x t s) ∧
      (∀ t ∈ Set.Icc 0 (((n : ℝ) + 1) * h), ‖x t‖ ≤ B) ∧
      N.delayConservedQuantity κ τ w x 0 = N.delayConservedQuantity κ τ w φ 0 ∧
      ∀ t ∈ Set.Icc 0 (((n : ℝ) + 1) * h),
        HasDerivWithinAt x (N.delayField κ τ x t)
          (Set.Icc 0 (((n : ℝ) + 1) * h)) t := by
  classical
  let T : ℕ → ℝ := fun n => ((n : ℝ) + 1) * h
  have hT_nonneg (n : ℕ) : 0 ≤ T n := by
    dsimp [T]
    positivity
  have hT_succ (n : ℕ) : T (n + 1) = T n + h := by
    dsimp [T]
    push_cast
    ring
  let P : ℕ → Prop := fun n => ∃ x : ℝ → Concentration S,
      Continuous x ∧ (∀ t ≤ 0, x t = φ t) ∧
      (∀ t ∈ Set.Icc (-D) (T n), ∀ s, 0 ≤ x t s) ∧
      (∀ t ∈ Set.Icc 0 (T n), ‖x t‖ ≤ B) ∧
      N.delayConservedQuantity κ τ w x 0 = N.delayConservedQuantity κ τ w φ 0 ∧
      ∀ t ∈ Set.Icc 0 (T n),
        HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 (T n)) t
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        change ∃ x, _
        refine ⟨x₀, hxc₀, hxhist₀, ?_, ?_, hQ₀, ?_⟩
        · intro t ht s
          exact hxnonneg₀ t (by simpa [T] using ht) s
        · intro t ht
          exact hxBound₀ t (by simpa [T] using ht)
        · intro t ht
          have ht' : t ∈ Set.Icc 0 h := by simpa [T] using ht
          simpa [T] using hx₀ t ht'
    | succ n ih =>
        change P n at ih
        obtain ⟨x, hxc, hhist, hnonneg, hbound, hQ, hx⟩ := ih
        have ha : 0 ≤ T n := hT_nonneg n
        obtain ⟨y, hyc, hyold, hyNonneg, hyBound, hy⟩ :=
          N.massActionDelay_weighted_loss_restart_step κ τ D B H₀ h (T n)
            hh hD hτ hτD ha w hsub hwpos φ hφbound hrestart hxc hhist hnonneg
            hbound hQ hx
        unfold P
        rw [hT_succ n]
        have hyBound' : ∀ t ∈ Set.Icc 0 (T n + h), ‖y t‖ ≤ B := by
          intro t ht
          rw [hB]
          exact hyBound t ht
        refine ⟨y, hyc, fun t ht => by
          calc y t = x t := hyold t (by linarith [ha])
            _ = φ t := hhist t ht,
          hyNonneg, hyBound', ?_, ?_⟩
        · exact N.delayConservedQuantity_zero_congr κ τ w hτ
            (fun t ht => hyold t (by linarith [ht, ha])) |>.trans hQ
        · intro t ht
          exact hy t (by simpa [hT_succ n] using ht)
  intro n
  simpa [P, T] using hP n

/-- Coherent finite-stage solutions assemble into one trajectory on every finite time interval.
The hypothesis `hB` identifies the invariant norm bound with the initial history functional. -/
theorem massActionDelay_weighted_loss_global_from_first_step
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (D B H₀ h : ℝ)
    [Nonempty S] (hh : 0 < h) (hD : 0 ≤ D) (hτ : ∀ r, 0 ≤ τ r)
    (hτD : ∀ r, τ r ≤ D) (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s) (φ : ℝ → Concentration S)
    (hφbound : ∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H₀)
    (hB : B = N.delayConservedQuantity κ τ w φ 0 /
      ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)))
    (hrestart : ∀ (ψ : ℝ → Concentration S), Continuous ψ →
      (∀ t ∈ Set.Icc (-D) 0, ‖ψ t‖ ≤ max H₀ B) → ∀ x₀ : Concentration S,
      ‖x₀‖ ≤ B → ψ 0 = x₀ → ∃ z : ℝ → Concentration S,
        Continuous z ∧ (∀ t ≤ 0, z t = ψ t) ∧ z 0 = x₀ ∧
        ∀ t ∈ Set.Icc 0 h,
          HasDerivWithinAt z (N.delayField κ τ z t) (Set.Icc 0 h) t)
    {x₀ : ℝ → Concentration S} (hxc₀ : Continuous x₀)
    (hxhist₀ : ∀ t ≤ 0, x₀ t = φ t)
    (hxnonneg₀ : ∀ t ∈ Set.Icc (-D) h, ∀ s, 0 ≤ x₀ t s)
    (hxBound₀ : ∀ t ∈ Set.Icc 0 h, ‖x₀ t‖ ≤ B)
    (hQ₀ : N.delayConservedQuantity κ τ w x₀ 0 = N.delayConservedQuantity κ τ w φ 0)
    (hx₀ : ∀ t ∈ Set.Icc 0 h,
      HasDerivWithinAt x₀ (N.delayField κ τ x₀ t) (Set.Icc 0 h) t) :
    ∃ X : ℝ → Concentration S, (∀ t ≤ 0, X t = φ t) ∧
      ∀ T : ℝ, 0 ≤ T → ContinuousOn X (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T,
          HasDerivWithinAt X (N.delayField κ τ X t) (Set.Icc 0 T) t := by
  classical
  have hsteps := N.massActionDelay_weighted_loss_finite_steps κ τ D B H₀ h
    hh hD hτ hτD w hsub hwpos φ hφbound hB hrestart hxc₀ hxhist₀ hxnonneg₀
    hxBound₀ hQ₀ hx₀
  let Tn : ℕ → ℝ := fun n => ((n : ℝ) + 1) * h
  let xs : ℕ → (ℝ → Concentration S) := fun n => Classical.choose (hsteps n)
  have hxspec (n : ℕ) := Classical.choose_spec (hsteps n)
  have hcompat : ∀ k m : ℕ, k ≤ m → ∀ y ∈ Set.Icc 0 (Tn k), xs k y = xs m y := by
    intro k m hkm y hy
    have hcast : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkm 1
    have hTkm : Tn k ≤ Tn m := by
      dsimp [Tn]
      exact mul_le_mul_of_nonneg_right hcast hh.le
    obtain ⟨_, hhistK, _, _, _, hderK⟩ := hxspec k
    obtain ⟨_, hhistM, _, _, _, hderM⟩ := hxspec m
    have hderM' : ∀ t ∈ Set.Icc 0 (Tn k),
        HasDerivWithinAt (xs m) (N.delayField κ τ (xs m) t) (Set.Icc 0 (Tn k)) t := by
      intro t ht
      exact (hderM t ⟨ht.1, ht.2.trans hTkm⟩).mono
        (by intro u hu; exact ⟨hu.1, hu.2.trans hTkm⟩)
    have hTk : 0 ≤ Tn k := by
      dsimp [Tn]
      positivity
    exact N.massActionDelay_solution_unique κ τ hTk hτ φ
      (x := xs k) (y := xs m) hhistK hhistM hderK hderM' y hy
  let X : ℝ → Concentration S := fun t =>
    if t ≤ 0 then φ t else xs (Nat.ceil (t / h)) t
  refine ⟨X, ?_, ?_⟩
  · intro t ht
    simp [X, ht]
  · intro T hT
    let m : ℕ := Nat.ceil (T / h)
    have hmh : (m : ℝ) * h ≤ Tn m := by
      dsimp [Tn]
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      calc (m : ℝ) * h ≤ (m : ℝ) * h + h := by linarith
        _ = ((m : ℝ) + 1) * h := by ring
    have hTmh : T ≤ (m : ℝ) * h := by
      have hceil : T / h ≤ (m : ℝ) := by
        have hc := Nat.le_ceil (T / h)
        simpa [m] using hc
      have heq : T = T / h * h := by field_simp
      calc T = T / h * h := heq
        _ ≤ (m : ℝ) * h := mul_le_mul_of_nonneg_right hceil hh.le
    have hagree : ∀ y ∈ Set.Icc 0 T, X y = xs m y := by
      intro y hy
      by_cases hy0 : y ≤ 0
      · simp [X, hy0]
        obtain ⟨_, hhistM, _, _, _, _⟩ := hxspec m
        exact (hhistM y hy0).symm
      · have hceil : Nat.ceil (y / h) ≤ m := by
          have hdiv : y / h ≤ T / h := div_le_div_of_nonneg_right hy.2 hh.le
          have hceils := Nat.ceil_le_ceil hdiv
          simpa [m] using hceils
        have hyT : y ∈ Set.Icc 0 (Tn (Nat.ceil (y / h))) := by
          constructor
          · exact le_of_lt (lt_of_not_ge hy0)
          · have hle := Nat.le_ceil (y / h)
            have heq : y = y / h * h := by field_simp
            have hmul : y / h * h ≤ (Nat.ceil (y / h) : ℝ) * h :=
              mul_le_mul_of_nonneg_right hle hh.le
            have hstep : (Nat.ceil (y / h) : ℝ) * h ≤
                ((Nat.ceil (y / h) : ℝ) + 1) * h := by
              have hn : 0 ≤ (Nat.ceil (y / h) : ℝ) := Nat.cast_nonneg _
              nlinarith [hh.le]
            dsimp [Tn]
            calc y = y / h * h := heq
              _ ≤ (Nat.ceil (y / h) : ℝ) * h := hmul
              _ ≤ ((Nat.ceil (y / h) : ℝ) + 1) * h := hstep
        have hsame := hcompat (Nat.ceil (y / h)) m (by simpa using hceil) y hyT
        simp [X, hy0]
        exact hsame
    have ⟨hcontM, _, _, _, _, hderM⟩ := hxspec m
    have hcont : ContinuousOn (xs m) (Set.Icc 0 T) :=
      hcontM.continuousOn.mono (fun y _ => Set.mem_univ y)
    refine ⟨hcont.congr hagree, ?_⟩
    intro t ht
    have htM : t ∈ Set.Icc 0 (Tn m) := ⟨ht.1, by linarith [ht.2, hTmh, hmh]⟩
    have hder := (hderM t htM).mono
      (by
        intro u (hu : u ∈ Set.Icc 0 T)
        exact ⟨hu.1, le_trans hu.2 (le_trans hTmh hmh)⟩)
    have hcur : X t = xs m t := hagree t ht
    have hdel : ∀ r, X (t - τ r) = xs m (t - τ r) := by
      intro r
      by_cases hq : t - τ r ≤ 0
      · simp [X, hq]
        obtain ⟨_, hhistM, _, _, _, _⟩ := hxspec m
        exact (hhistM (t - τ r) hq).symm
      · have hqmem : t - τ r ∈ Set.Icc 0 T := by
          constructor
          · exact le_of_not_ge hq
          · linarith [ht.2, hτ r]
        exact hagree (t - τ r) hqmem
    have hfield : N.delayField κ τ X t = N.delayField κ τ (xs m) t := by
      funext s
      simp only [Network.delayField]
      simp [hcur, hdel]
    have hder' := hder.congr_of_mem (fun u hu => hagree u hu) ht
    exact hder'.congr_deriv hfield.symm

/-- **Global existence under a positive weighted loss law.** If every reaction weakly decreases a
strictly positive weighted total, then every continuous nonnegative history extends to one
continuous trajectory solving the finite-delay mass-action system on every finite forward
interval. The nonincreasing delayed inventory gives a uniform restart length. -/
theorem massActionDelay_global_exists_of_weighted_subconservation
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) [Nonempty S]
    (hτ : ∀ r, 0 ≤ τ r) (w : S → ℝ)
    (hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ))
    (hwpos : ∀ s, 0 < w s)
    (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ x : ℝ → Concentration S, (∀ t ≤ 0, x t = φ t) ∧
      ∀ T : ℝ, 0 ≤ T → ContinuousOn x (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T,
          HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t := by
  classical
  let D := ∑ r, τ r
  have hD : 0 ≤ D := Finset.sum_nonneg fun r _ => hτ r
  have hτD : ∀ r, τ r ≤ D := by
    intro r
    change τ r ≤ ∑ q, τ q
    exact Finset.single_le_sum (fun q _ => hτ q) (Finset.mem_univ r)
  obtain ⟨d, hd, hgap⟩ := N.massActionDelay_exists_positive_step τ
  obtain ⟨H₀, hH₀⟩ := isCompact_Icc.bddAbove_image
    (f := fun t : ℝ => ‖φ t‖) hφ.continuousOn.norm
  have hφbound : ∀ t ∈ Set.Icc (-D) 0, ‖φ t‖ ≤ H₀ := by
    intro t ht
    exact hH₀ (Set.mem_image_of_mem _ ht)
  obtain ⟨h, hh, hhd, hrestart, x₀, hxc₀, hxhist₀, hxnonneg₀,
      hxBound₀, hx₀⟩ :=
    N.massActionDelay_weighted_loss_first_step κ τ d D H₀ hd hD hτ hgap hτD w hsub hwpos
      φ hφ hφnonneg hφbound
  have hxQ₀ := N.delayConservedQuantity_zero_congr κ τ w hτ hxhist₀
  let B := N.delayConservedQuantity κ τ w φ 0 /
    ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty))
  have hB : B = N.delayConservedQuantity κ τ w φ 0 /
      ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)) := rfl
  exact N.massActionDelay_weighted_loss_global_from_first_step κ τ D B H₀ h hh hD hτ hτD
    w hsub hwpos φ hφbound hB hrestart hxc₀ hxhist₀ hxnonneg₀ hxBound₀ hxQ₀ hx₀

/-- **Global existence under a strictly positive conservation law.** This classical conservative
case follows from the more general positive weighted-loss theorem. -/
theorem massActionDelay_global_exists_of_positive_conservation
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) [Nonempty S]
    (hτ : ∀ r, 0 ≤ τ r) (w : S → ℝ)
    (hw : w ∈ orthSum N.stoichSubspace) (hwpos : ∀ s, 0 < w s)
    (φ : ℝ → Concentration S) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ x : ℝ → Concentration S, (∀ t ≤ 0, x t = φ t) ∧
      ∀ T : ℝ, 0 ≤ T → ContinuousOn x (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T,
          HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc 0 T) t := by
  have hsub : ∀ r, ∑ s, w s * ((N.reaction r).target s : ℝ) ≤
      ∑ s, w s * ((N.reaction r).source s : ℝ) := by
    intro r
    have hp := (mem_orthSum.mp hw) _ (N.reactionVector_mem_stoichSubspace r)
    simp only [reactionVector_apply] at hp
    have heq : (∑ s, w s * ((N.reaction r).target s : ℝ)) =
        ∑ s, w s * ((N.reaction r).source s : ℝ) := by
      apply sub_eq_zero.mp
      calc
        _ = ∑ s, w s * (((N.reaction r).target s : ℝ) -
            ((N.reaction r).source s : ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = 0 := hp
    exact heq.le
  exact N.massActionDelay_global_exists_of_weighted_subconservation κ τ hτ w hsub
    hwpos φ hφ hφnonneg

/-- **A positive conserved weight bounds every nonnegative delayed trajectory.**

Let `w` be a strictly positive conservation law and assume all reaction delays are
nonnegative. The delayed conservation functional is constant; its integral terms are
nonnegative along a nonnegative trajectory. Consequently its initial value bounds each
concentration coordinate at every nonnegative time:
`x_s(t) ≤ Q(0) / w_s`.

This is a priori boundedness for an already-existing global solution. It does not by itself
construct a global solution; it is the invariant estimate needed for a continuation argument. -/
theorem delayConservedQuantity_coord_bound
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ)
    (hτ : ∀ r, 0 ≤ τ r) (hw : w ∈ orthSum N.stoichSubspace)
    (hwpos : ∀ s, 0 < w s) {x : ℝ → Concentration S}
    (hx : N.IsDelaySolution κ τ x)
    (hxnonneg : ∀ t s, 0 ≤ x t s) :
    0 ≤ N.delayConservedQuantity κ τ w x 0 ∧
      ∀ t, 0 ≤ t → ∀ s, x t s ≤ N.delayConservedQuantity κ τ w x 0 / w s := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hmc : ∀ r, Continuous fun u => (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    unfold Complex.massActionMonomial
    exact continuous_finsetProd _ fun s _ => ((continuous_apply s).comp hxc).pow _
  have hint_nonneg : ∀ r t, 0 ≤
      ∫ u in (t - τ r)..t, (N.reaction r).source.massActionMonomial (x u) := by
    intro r t
    apply intervalIntegral.integral_nonneg (by linarith [hτ r])
    intro u hu
    exact Complex.massActionMonomial_nonneg (hxnonneg u) (N.reaction r).source
  have hsource_nonneg : ∀ r, 0 ≤ ∑ s, w s * ((N.reaction r).source s : ℝ) := by
    intro r
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
  have hterm_nonneg : ∀ r, 0 ≤ κ.k r *
      (∑ s, w s * ((N.reaction r).source s : ℝ)) *
        ∫ u in (0 - τ r)..0, (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    exact mul_nonneg (mul_nonneg (κ.positive r).le (hsource_nonneg r))
      (hint_nonneg r 0)
  have hquantity_nonneg : 0 ≤ N.delayConservedQuantity κ τ w x 0 := by
    unfold delayConservedQuantity
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg (hwpos s).le (hxnonneg 0 s)
    · apply Finset.sum_nonneg
      intro r hr
      exact hterm_nonneg r
  have hquantity_eq (t : ℝ) :
      N.delayConservedQuantity κ τ w x t = N.delayConservedQuantity κ τ w x 0 :=
    N.delayConservedQuantity_const κ τ (w := w) hw hx t 0
  have hsum_nonneg (t : ℝ) :
      0 ≤ ∑ s, w s * x t s := by
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hwpos s).le (hxnonneg t s)
  have hcurrent_le (t : ℝ) :
      (∑ s, w s * x t s) ≤ N.delayConservedQuantity κ τ w x t := by
    unfold delayConservedQuantity
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => by
      exact mul_nonneg (mul_nonneg (κ.positive r).le (hsource_nonneg r))
        (hint_nonneg r t))
  refine ⟨hquantity_nonneg, ?_⟩
  intro t ht s
  have hcoord_le : w s * x t s ≤ ∑ j, w j * x t j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hwpos j).le (hxnonneg t j))
      (Finset.mem_univ s)
  have hcoord : w s * x t s ≤ N.delayConservedQuantity κ τ w x 0 := by
    calc w s * x t s ≤ ∑ j, w j * x t j := hcoord_le
      _ ≤ N.delayConservedQuantity κ τ w x t := hcurrent_le t
      _ = N.delayConservedQuantity κ τ w x 0 := hquantity_eq t
  exact (le_div_iff₀ (hwpos s)).2 (by simpa [mul_comm] using hcoord)

/-- **Uniform norm boundedness from a positive conservation law.** For a finite nonempty species
set, the coordinate estimates from `delayConservedQuantity_coord_bound` have a common denominator:
the minimum conservation weight. Thus every nonnegative global solution is bounded on the whole
future half-line by its initial delayed conserved quantity divided by that minimum. -/
theorem delayConservedQuantity_norm_bound
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) (w : S → ℝ)
    [Nonempty S] (hτ : ∀ r, 0 ≤ τ r) (hw : w ∈ orthSum N.stoichSubspace)
    (hwpos : ∀ s, 0 < w s) {x : ℝ → Concentration S}
    (hx : N.IsDelaySolution κ τ x)
    (hxnonneg : ∀ t s, 0 ≤ x t s) :
    ∀ t, 0 ≤ t → ‖x t‖ ≤
      N.delayConservedQuantity κ τ w x 0 /
        ((Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)) := by
  obtain ⟨hQ, hcoord⟩ := delayConservedQuantity_coord_bound N κ τ w hτ hw hwpos hx hxnonneg
  let wmin := (Finset.univ.image w).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hwmin : wmin ∈ Finset.univ.image w := Finset.min'_mem _ _
  obtain ⟨s₀, hs₀, hws₀⟩ := Finset.mem_image.mp hwmin
  have hmin : 0 < wmin := by rw [← hws₀]; exact hwpos s₀
  have hmin_le (s : S) : wmin ≤ w s :=
    Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ s))
  have hB : 0 ≤ N.delayConservedQuantity κ τ w x 0 / wmin :=
    div_nonneg hQ hmin.le
  intro t ht
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro s
  have hup := hcoord t ht s
  have hden : N.delayConservedQuantity κ τ w x 0 / w s ≤
      N.delayConservedQuantity κ τ w x 0 / wmin := by
    apply (div_le_div_iff₀ (hwpos s) hmin).2
    nlinarith [hQ, hmin_le s]
  have htop := le_trans hup hden
  exact abs_le.mpr ⟨by linarith [hB, hxnonneg t s], htop⟩

#print axioms CRNT.Network.massActionDelay_local_exists_of_delayGap
#print axioms CRNT.Network.massActionDelay_exists_positive_step
#print axioms CRNT.Network.massActionDelay_local_exists
#print axioms CRNT.Network.massActionDelay_local_exists_nonneg_history
#print axioms CRNT.Network.massActionDelay_firstStep_unique
#print axioms CRNT.Network.massActionDelay_solution_unique
#print axioms CRNT.Network.massActionDelay_local_exists_uniform
#print axioms CRNT.Network.massActionDelay_local_exists_uniform_continuous
#print axioms CRNT.Network.massActionDelay_uniform_restart
#print axioms CRNT.Network.massActionDelay_uniform_restart_nonneg
#print axioms CRNT.Network.delayConservedQuantity_zero_congr
#print axioms CRNT.Network.delayConservedQuantity_initial_norm_bound
#print axioms CRNT.Network.delayConservedQuantity_hasDerivWithinAt
#print axioms CRNT.Network.delayConservedQuantity_antitone_on
#print axioms CRNT.Network.delayConservedQuantity_coord_bound_on_of_antitone
#print axioms CRNT.Network.delayConservedQuantity_norm_bound_on_of_antitone
#print axioms CRNT.Network.massActionDelay_weighted_loss_first_step
#print axioms CRNT.Network.massActionDelay_weighted_loss_restart_step
#print axioms CRNT.Network.massActionDelay_weighted_loss_finite_steps
#print axioms CRNT.Network.massActionDelay_weighted_loss_global_from_first_step
#print axioms CRNT.Network.massActionDelay_global_exists_of_weighted_subconservation
#print axioms CRNT.Network.massActionDelay_global_exists_of_positive_conservation
#print axioms CRNT.Network.delayConservedQuantity_const_on
#print axioms CRNT.Network.delayConservedQuantity_coord_bound_on
#print axioms CRNT.Network.delayConservedQuantity_norm_bound_on
#print axioms CRNT.Network.delayConservedQuantity_coord_bound
#print axioms CRNT.Network.delayConservedQuantity_norm_bound

end Network
end CRNT
