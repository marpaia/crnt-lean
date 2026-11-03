import CRNT.Dynamics.MassActionLocalDelayComparison

/-! # Positivity for delayed mass-action solutions

This module connects delayed mass-action boundary inwardness to a finite-interval orthant
invariance lemma. It proves positivity for existing differentiable solutions with arbitrary
nonnegative reaction-specific delays, including mixed zero and positive delays, by a finite
method-of-steps argument. Compactness supplies finite-interval bounds; solution existence remains
separate.
-/

namespace CRNT
namespace Network

open Set

variable {S : Type} [DecidableEq S] [Fintype S]

/-- If all reaction histories used on `[a,b]` are nonnegative and the current trajectory is
bounded there, a differentiable delayed mass-action solution starting nonnegative at `a` stays
nonnegative through the interval. The delayed states may differ by reaction. -/
theorem delayField_nonneg_on_interval_of_nonneg_delayed
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b B : ℝ} (hB : 0 ≤ B)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B)
    (hdelayed : ∀ t ∈ Set.Icc a b, ∀ r s, 0 ≤ x (t - τ r) s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  let K : Set (Concentration S) := Metric.closedBall (0 : Concentration S) B
  let L := Real.toNNReal (massActionLipschitzConstant
    N.currentConsumptionNetwork (N.currentConsumptionRates κ) B)
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => x (t - τ r))
  have hxK : ∀ t ∈ Set.Icc a b, x t ∈ K := by
    intro t ht
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hxBound t ht)
  have hclamp : ∀ u ∈ K, (fun i => max (u i) 0) ∈ K := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    have hucoord := (pi_norm_le_iff_of_nonneg hB).mp hu
    intro i
    have hcoord := hucoord i
    rw [Real.norm_eq_abs] at hcoord
    have hupper : u i ≤ B := le_trans (le_abs_self _) hcoord
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le hupper hB
  have hlip : ∀ t ∈ Set.Icc a b, LipschitzOnWith L (f t) K := by
    intro t ht u hu u' hu'
    change edist (N.massActionDelayField κ u (fun r => x (t - τ r)))
      (N.massActionDelayField κ u' (fun r => x (t - τ r))) ≤ _
    exact N.massActionDelayField_lipschitzOnWith_closedBall_byReaction κ B
      (fun r => x (t - τ r)) hu hu'
  have hboundary : ∀ t ∈ Set.Icc a b, ∀ u ∈ K, (∀ j, 0 ≤ u j) →
      ∀ i, u i = 0 → 0 ≤ f t u i := by
    intro t ht u hu hune i hi
    exact N.massActionDelayField_coord_nonneg_of_current_zero κ u
      (fun r => x (t - τ r)) i hi (fun r s => hdelayed t ht r s)
  have hx' : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (f t (x t)) (Set.Icc a b) t := by
    intro t ht
    simpa [f, massActionDelayField_delayField] using hx t ht
  intro t ht s
  exact Dynamics.forwardInvariant_nonnegOrthant_step_on hlip hclamp hboundary
    hx' hxK ha t ht s

/-- A practical method-of-steps form of the positivity result. If the step is no longer than
any reaction delay, all delayed arguments used during the step lie in the supplied prior history
interval `[a-τ_r,a]`. -/
theorem delayField_nonneg_on_methodStep
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ r, b - a ≤ τ r)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B)
    (hhistory : ∀ r s q, q ∈ Set.Icc (a - τ r) a → 0 ≤ x q s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  apply delayField_nonneg_on_interval_of_nonneg_delayed N κ τ hB hx hxBound
  · intro t ht r s
    exact hhistory r s (t - τ r) ⟨by linarith [ht.1], by linarith [ht.2, hstep r]⟩
  · exact ha

/-- A method interval may contain zero delays: their production is evaluated at the current
positive-part clamp, while only strictly positive-delay samples need a prior nonnegative history.
This proves positivity on the interval from a nonnegative initial point and bounded trajectory. -/
theorem delayField_nonneg_on_interval_of_nonneg_positive_delayed
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b B : ℝ} (hB : 0 ≤ B)
    (hτ : ∀ r, 0 ≤ τ r)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B)
    (hdelayed : ∀ t ∈ Set.Icc a b, ∀ r, 0 < τ r → ∀ s, 0 ≤ x (t - τ r) s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  let K : Set (Concentration S) := Metric.closedBall (0 : Concentration S) B
  let L := Real.toNNReal (massActionLipschitzConstant
    (N.instantaneousDelayNetwork τ) (N.instantaneousDelayRates τ κ) B)
  let f : ℝ → Concentration S → Concentration S := fun t u =>
    N.massActionDelayField κ u (fun r => if τ r = 0 then u else x (t - τ r))
  have hxK : ∀ t ∈ Set.Icc a b, x t ∈ K := by
    intro t ht
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hxBound t ht)
  have hclamp : ∀ u ∈ K, (fun i => max (u i) 0) ∈ K := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    have hucoord := (pi_norm_le_iff_of_nonneg hB).mp hu
    intro i
    have hcoord := hucoord i
    rw [Real.norm_eq_abs] at hcoord
    have hupper : u i ≤ B := le_trans (le_abs_self _) hcoord
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le hupper hB
  have hlip : ∀ t ∈ Set.Icc a b, LipschitzOnWith L (f t) K := by
    intro t ht u hu u' hu'
    exact N.massActionDelayField_lipschitzOnWith_zeroDelaySplit κ τ B
      (fun r => x (t - τ r)) hu hu'
  have hboundary : ∀ t ∈ Set.Icc a b, ∀ u ∈ K, (∀ j, 0 ≤ u j) →
      ∀ i, u i = 0 → 0 ≤ f t u i := by
    intro t ht u hu hune i hi
    apply N.massActionDelayField_coord_nonneg_of_current_zero κ u
      (fun r => if τ r = 0 then u else x (t - τ r)) i hi
    intro r s
    by_cases hr : τ r = 0
    · simp [hr]
      exact hune s
    · have hrpos : 0 < τ r := lt_of_le_of_ne (hτ r) (Ne.symm hr)
      simpa [hr] using hdelayed t ht r hrpos s
  have hx' : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (f t (x t)) (Set.Icc a b) t := by
    intro t ht
    have hargs : (fun r => if τ r = 0 then x t else x (t - τ r)) =
        (fun r => x (t - τ r)) := by
      funext r
      by_cases hr : τ r = 0 <;> simp [hr]
    simpa [f, massActionDelayField_delayField, hargs] using hx t ht
  intro t ht s
  exact Dynamics.forwardInvariant_nonnegOrthant_step_on hlip hclamp hboundary
    hx' hxK ha t ht s

/-- Mixed-delay method step: strictly positive reaction delays sample only the supplied prior
history window; zero-delay reactions are handled as part of the instantaneous field. -/
theorem delayField_nonneg_on_mixed_methodStep
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b B : ℝ} (hB : 0 ≤ B) (hτ : ∀ r, 0 ≤ τ r)
    (hstep : ∀ r, 0 < τ r → b - a ≤ τ r)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B)
    (hhistory : ∀ r s q, q ∈ Set.Icc (a - τ r) a → 0 ≤ x q s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  apply delayField_nonneg_on_interval_of_nonneg_positive_delayed N κ τ hB hτ hx hxBound
  · intro t ht r hr s
    exact hhistory r s (t - τ r)
      ⟨by linarith [ht.1], by linarith [ht.2, hstep r hr]⟩
  · exact ha

/-- Positivity propagates across a finite interval for arbitrary reaction-specific strictly
positive delays. A common lower bound `δ` controls the step size, and `M` bounds the initial
history window. The theorem assumes an existing differentiable solution and a bound on its
finite-interval range; it proves positivity from a nonnegative initial point and nonnegative
history on `[a-M,a]`. -/
theorem delayField_nonneg_of_positive_delays_on_bounded_solution
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b B δ M : ℝ} (hab : a ≤ b) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hdelayLower : ∀ r, δ ≤ τ r) (hdelayUpper : ∀ r, τ r ≤ M)
    (n : ℕ) (hsteps : b - a ≤ (n : ℝ) * δ)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B)
    (hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (a - M) a → 0 ≤ x q s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  have hnext : ∀ k : ℕ, (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := by
    intro k
    push_cast
    nlinarith [hδ]
  have hall : ∀ k : ℕ, ∀ t ∈ Set.Icc a (min b (a + (k : ℝ) * δ)),
      ∀ s, 0 ≤ x t s := by
    intro k
    induction k with
    | zero =>
        intro t ht s
        have hmin : min b (a + (0 : ℕ) * δ) = a := by simp [hab]
        rw [hmin] at ht
        have hteq : t = a := le_antisymm ht.2 ht.1
        simpa [hteq] using ha s
    | succ k ih =>
        intro t ht s
        let c : ℝ := a + (k : ℝ) * δ
        let e : ℝ := a + ((k + 1 : ℕ) : ℝ) * δ
        let d : ℝ := min b e
        have hce : c ≤ e := by
          dsimp [c, e]
          push_cast
          nlinarith [hδ]
        by_cases hb : b ≤ c
        · have hmin : min b c = b := min_eq_left hb
          have htb : t ≤ b := le_trans ht.2 (min_le_left _ _)
          have hprev : t ∈ Set.Icc a (min b c) := by
            rw [hmin]
            exact ⟨ht.1, htb⟩
          exact ih t hprev s
        · have hcb : c < b := lt_of_not_ge hb
          have hminprev : min b c = c := min_eq_right hcb.le
          have hcd : c ≤ d := by
            dsimp [d]
            exact le_min hcb.le hce
          have hde : d ≤ e := by dsimp [d]; exact min_le_right _ _
          have hdb : d ≤ b := by dsimp [d]; exact min_le_left _ _
          have hca : a ≤ c := by
            dsimp [c]
            have hn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ.le
            linarith
          by_cases htc : t ≤ c
          · have htprev : t ∈ Set.Icc a (min b c) := by
              rw [hminprev]
              exact ⟨ht.1, htc⟩
            exact ih t htprev s
          · have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
            have htstep : t ∈ Set.Icc c d := ⟨hct, ht.2⟩
            have hbase : ∀ j, 0 ≤ x c j := by
              have hcprev : c ∈ Set.Icc a (min b c) := by rw [hminprev]; exact ⟨hca, le_rfl⟩
              exact ih c hcprev
            have hxs : ∀ u ∈ Set.Icc c d,
                HasDerivWithinAt x (N.delayField κ τ x u) (Set.Icc c d) u := by
              intro u hu
              have huab : u ∈ Set.Icc a b := ⟨hca.trans hu.1, le_trans hu.2 hdb⟩
              exact (hx u huab).mono (fun v hv =>
                ⟨hca.trans hv.1,
                  le_trans hv.2 hdb⟩)
            have hxb : ∀ u ∈ Set.Icc c d, ‖x u‖ ≤ B := by
              intro u hu
              exact hxBound u ⟨hca.trans hu.1, le_trans hu.2 hdb⟩
            have hprior : ∀ r j q, q ∈ Set.Icc (c - τ r) c → 0 ≤ x q j := by
              intro r j q hq
              have hqlo : a - M ≤ q := by
                have hqlo' := hq.1
                dsimp [c] at hqlo'
                linarith [hdelayUpper r]
              by_cases hqa : q ≤ a
              · exact hhistory r j q ⟨hqlo, hqa⟩
              · have haq : a ≤ q := le_of_lt (lt_of_not_ge hqa)
                have hqprev : q ∈ Set.Icc a (min b c) := by
                  rw [hminprev]
                  exact ⟨haq, hq.2⟩
                exact ih q hqprev j
            have hstepLen : d - c ≤ δ := by
              have heq : e = c + δ := by
                dsimp [e, c]
                push_cast
                ring
              calc d - c ≤ e - c := sub_le_sub_right hde c
                _ = δ := by rw [heq]; ring
            have hmethod := delayField_nonneg_on_methodStep N κ τ hB
              (fun r => (hstepLen.trans (hdelayLower r)))
              hxs hxb hprior hbase
            exact hmethod t htstep s
  have hfinal : min b (a + (n : ℝ) * δ) = b := by
    apply min_eq_left
    have : b ≤ a + (n : ℝ) * δ := by linarith
    exact this
  intro t ht s
  have ht' : t ∈ Set.Icc a (min b (a + (n : ℝ) * δ)) := by simpa [hfinal] using ht
  exact hall n t ht' s

/-- Every existing differentiable solution of a finite network with strictly positive,
reaction-specific delays preserves nonnegativity on finite intervals. Continuity on the compact
time interval supplies the local boundedness needed by the clamp argument; finiteness and
nonemptiness of the reaction set supply positive minimum and finite maximum delays. The only
initial-data hypothesis is nonnegativity at the initial time and on each reaction's history
window. This theorem proves invariance for an existing solution, not solution existence. -/
theorem delayField_nonneg_of_positive_delays
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hτ : ∀ r, 0 < τ r) (hR : Nonempty N.R)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (a - τ r) a → 0 ≤ x q s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  have hcont : ContinuousOn x (Set.Icc a b) := by
    intro t ht
    exact (hx t ht).continuousWithinAt
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image (f := fun t => ‖x t‖) hcont.norm
  have hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B := by
    intro t ht
    exact hB (Set.mem_image_of_mem _ ht)
  have hB0 : 0 ≤ B := by
    have hBa := hxBound a ⟨le_rfl, hab⟩
    linarith [norm_nonneg (x a)]
  have hne : (Finset.univ : Finset N.R).Nonempty := by
    obtain ⟨r⟩ := hR
    exact ⟨r, Finset.mem_univ _⟩
  obtain ⟨rmin, hrmin, hmin⟩ := Finset.univ.exists_min_image τ hne
  obtain ⟨rmax, hrmax, hmax⟩ := Finset.univ.exists_max_image τ hne
  let δ := τ rmin
  let M := τ rmax
  have hδ : 0 < δ := by simpa [δ] using hτ rmin
  have hdelayLower : ∀ r, δ ≤ τ r := by
    intro r
    exact hmin r (Finset.mem_univ r)
  have hdelayUpper : ∀ r, τ r ≤ M := by
    intro r
    exact hmax r (Finset.mem_univ r)
  have hhistory' : ∀ (r : N.R) s q, q ∈ Set.Icc (a - M) a → 0 ≤ x q s := by
    intro r s q hq
    have hq' : q ∈ Set.Icc (a - τ rmax) a := by simpa [M] using hq
    exact hhistory rmax s q hq'
  let n := Nat.ceil ((b - a) / δ)
  have hsteps : b - a ≤ (n : ℝ) * δ := by
    have hceil : (b - a) / δ ≤ (n : ℝ) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hδ).mp hceil
    simpa [n] using hmul
  exact delayField_nonneg_of_positive_delays_on_bounded_solution N κ τ
    hab hB0 hδ hdelayLower hdelayUpper n hsteps hx hxBound hhistory' ha

/-- Every existing differentiable solution with nonnegative reaction-specific delays preserves
nonnegativity on a finite interval. Zero-delay reactions are instantaneous; the finite-step size
is the minimum among positive delays. Compactness supplies a bound on the solution range. -/
theorem delayField_nonneg_of_nonnegative_delays
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hτ : ∀ r, 0 ≤ τ r)
    {x : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x (N.delayField κ τ x t) (Set.Icc a b) t)
    (hhistory : ∀ (r : N.R) s q, q ∈ Set.Icc (a - τ r) a → 0 ≤ x q s)
    (ha : ∀ s, 0 ≤ x a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ x t s := by
  have hcont : ContinuousOn x (Set.Icc a b) := by
    intro t ht
    exact (hx t ht).continuousWithinAt
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image (f := fun t => ‖x t‖) hcont.norm
  have hxBound : ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ B := by
    intro t ht
    exact hB (Set.mem_image_of_mem _ ht)
  have hB0 : 0 ≤ B := by
    have hBa := hxBound a ⟨le_rfl, hab⟩
    linarith [norm_nonneg (x a)]
  by_cases hpos : ∃ r, 0 < τ r
  · let P : Finset N.R := Finset.univ.filter fun r => 0 < τ r
    have hP : P.Nonempty := by
      obtain ⟨r, hr⟩ := hpos
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
    obtain ⟨rmin, hrmin, hmin⟩ := P.exists_min_image τ hP
    have hminpos : 0 < τ rmin := (Finset.mem_filter.mp hrmin).2
    let δ := τ rmin
    obtain ⟨rmax, hrmax, hmax⟩ := Finset.univ.exists_max_image τ (by
      obtain ⟨r, _⟩ := hpos
      exact ⟨r, Finset.mem_univ _⟩)
    let M := τ rmax
    have hδ : 0 < δ := by simpa [δ] using hminpos
    have hdelayLower : ∀ r, 0 < τ r → δ ≤ τ r := by
      intro r hr
      have hrP : r ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact hmin r hrP
    have hdelayUpper : ∀ r, τ r ≤ M := by
      intro r
      exact hmax r (Finset.mem_univ r)
    have hhistory' : ∀ (r : N.R) s q, q ∈ Set.Icc (a - M) a → 0 ≤ x q s := by
      intro r s q hq
      have hq' : q ∈ Set.Icc (a - τ rmax) a := by simpa [M] using hq
      exact hhistory rmax s q hq'
    let n := Nat.ceil ((b - a) / δ)
    have hsteps : b - a ≤ (n : ℝ) * δ := by
      have hceil : (b - a) / δ ≤ (n : ℝ) := Nat.le_ceil _
      have hmul := (div_le_iff₀ hδ).mp hceil
      simpa [n] using hmul
    have hnext : ∀ k : ℕ, (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := by
      intro k
      push_cast
      nlinarith [hδ]
    have hall : ∀ k : ℕ, ∀ t ∈ Set.Icc a (min b (a + (k : ℝ) * δ)),
        ∀ s, 0 ≤ x t s := by
      intro k
      induction k with
      | zero =>
          intro t ht s
          have hmin0 : min b (a + (0 : ℕ) * δ) = a := by simp [hab]
          rw [hmin0] at ht
          have hteq : t = a := le_antisymm ht.2 ht.1
          simpa [hteq] using ha s
      | succ k ih =>
          intro t ht s
          let c : ℝ := a + (k : ℝ) * δ
          let e : ℝ := a + ((k + 1 : ℕ) : ℝ) * δ
          let d : ℝ := min b e
          have hce : c ≤ e := by
            dsimp [c, e]
            push_cast
            nlinarith [hδ]
          by_cases hb : b ≤ c
          · have hmin : min b c = b := min_eq_left hb
            have htb : t ≤ b := le_trans ht.2 (min_le_left _ _)
            have hprev : t ∈ Set.Icc a (min b c) := by
              rw [hmin]
              exact ⟨ht.1, htb⟩
            exact ih t hprev s
          · have hcb : c < b := lt_of_not_ge hb
            have hminprev : min b c = c := min_eq_right hcb.le
            have hcd : c ≤ d := by dsimp [d]; exact le_min hcb.le hce
            have hde : d ≤ e := by dsimp [d]; exact min_le_right _ _
            have hdb : d ≤ b := by dsimp [d]; exact min_le_left _ _
            have hca : a ≤ c := by
              dsimp [c]
              have hn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ.le
              linarith
            by_cases htc : t ≤ c
            · have htprev : t ∈ Set.Icc a (min b c) := by
                rw [hminprev]
                exact ⟨ht.1, htc⟩
              exact ih t htprev s
            · have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
              have htstep : t ∈ Set.Icc c d := ⟨hct, ht.2⟩
              have hbase : ∀ j, 0 ≤ x c j := by
                have hcprev : c ∈ Set.Icc a (min b c) := by
                  rw [hminprev]
                  exact ⟨hca, le_rfl⟩
                exact ih c hcprev
              have hxs : ∀ u ∈ Set.Icc c d,
                  HasDerivWithinAt x (N.delayField κ τ x u) (Set.Icc c d) u := by
                intro u hu
                have huab : u ∈ Set.Icc a b := ⟨hca.trans hu.1, le_trans hu.2 hdb⟩
                exact (hx u huab).mono (fun v hv =>
                  ⟨hca.trans hv.1, le_trans hv.2 hdb⟩)
              have hxb : ∀ u ∈ Set.Icc c d, ‖x u‖ ≤ B := by
                intro u hu
                exact hxBound u ⟨hca.trans hu.1, le_trans hu.2 hdb⟩
              have hprior : ∀ r j q, q ∈ Set.Icc (c - τ r) c → 0 ≤ x q j := by
                intro r j q hq
                have hqlo : a - M ≤ q := by
                  have hqlo' := hq.1
                  dsimp [c] at hqlo'
                  linarith [hdelayUpper r]
                by_cases hqa : q ≤ a
                · exact hhistory' r j q ⟨hqlo, hqa⟩
                · have haq : a ≤ q := le_of_lt (lt_of_not_ge hqa)
                  have hqprev : q ∈ Set.Icc a (min b c) := by
                    rw [hminprev]
                    exact ⟨haq, hq.2⟩
                  exact ih q hqprev j
              have hstepLen : d - c ≤ δ := by
                have heq : e = c + δ := by dsimp [e, c, δ]; push_cast; ring
                calc d - c ≤ e - c := sub_le_sub_right hde c
                  _ = δ := by rw [heq]; ring
              have hmethod := delayField_nonneg_on_mixed_methodStep N κ τ hB0 hτ
                (fun r hr => (hstepLen.trans (hdelayLower r hr))) hxs hxb hprior hbase
              exact hmethod t htstep s
    have hfinal : min b (a + (n : ℝ) * δ) = b := by
      apply min_eq_left
      have : b ≤ a + (n : ℝ) * δ := by linarith
      exact this
    intro t ht s
    have ht' : t ∈ Set.Icc a (min b (a + (n : ℝ) * δ)) := by simpa [hfinal] using ht
    exact hall n t ht' s
  · have hzero : ∀ r, τ r = 0 := by
      intro r
      have hnot : ¬ 0 < τ r := fun hr => hpos ⟨r, hr⟩
      exact le_antisymm (not_lt.mp hnot) (hτ r)
    have hdelayed : ∀ t ∈ Set.Icc a b, ∀ r, 0 < τ r → ∀ s, 0 ≤ x (t - τ r) s := by
      intro t ht r hr
      have hfalse : False := by
        rw [hzero r] at hr
        exact (lt_irrefl 0 hr)
      exact hfalse.elim
    exact delayField_nonneg_on_interval_of_nonneg_positive_delayed N κ τ hB0 hτ
      hx hxBound hdelayed ha

/-- Common-delay single-species-source comparison with nonnegative histories as the only
order-domain hypotheses. Positivity of each exact solution and its compact-interval bound are
derived from the preceding invariance theorem; they need not be assumed on the trajectories. -/
theorem delay_comparison_massAction_commonDelay_singleSpeciesSources_of_nonnegative_history
    (N : Network S) (κ : N.RateConstants) (hsrc : N.HasSingleSpeciesSources)
    {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.massActionDelayField κ (x t) (fun _ => x (t - τ)))
        (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.massActionDelayField κ (y t) (fun _ => y (t - τ)))
        (Set.Icc 0 T) t)
    (horder : ∀ r ∈ Set.Icc (-τ) 0, x r ≤ y r)
    (hxHistory : ∀ r ∈ Set.Icc (-τ) 0, ∀ s, 0 ≤ x r s)
    (hyHistory : ∀ r ∈ Set.Icc (-τ) 0, ∀ s, 0 ≤ y r s) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  have hxPos := delayField_nonneg_of_nonnegative_delays N κ (fun _ => τ) hT
    (fun _ => hτ.le)
    (by
      intro t ht
      simpa [massActionDelayField_delayField] using hx t ht)
    (by
      intro r s q hq
      apply hxHistory q
      simpa using hq)
    (fun s => hxHistory 0 ⟨by linarith, le_rfl⟩ s)
  have hyPos := delayField_nonneg_of_nonnegative_delays N κ (fun _ => τ) hT
    (fun _ => hτ.le)
    (by
      intro t ht
      simpa [massActionDelayField_delayField] using hy t ht)
    (by
      intro r s q hq
      apply hyHistory q
      simpa using hq)
    (fun s => hyHistory 0 ⟨by linarith, le_rfl⟩ s)
  have hxNonneg : ∀ t ∈ Set.Icc (-τ) T, ∀ s, 0 ≤ x t s := by
    intro t ht s
    by_cases ht0 : t ≤ 0
    · exact hxHistory t ⟨ht.1, ht0⟩ s
    · have htpos : 0 ≤ t := le_of_lt (lt_of_not_ge ht0)
      exact hxPos t ⟨htpos, ht.2⟩ s
  have hyNonneg : ∀ t ∈ Set.Icc (-τ) T, ∀ s, 0 ≤ y t s := by
    intro t ht s
    by_cases ht0 : t ≤ 0
    · exact hyHistory t ⟨ht.1, ht0⟩ s
    · have htpos : 0 ≤ t := le_of_lt (lt_of_not_ge ht0)
      exact hyPos t ⟨htpos, ht.2⟩ s
  have hxCont : ContinuousOn x (Set.Icc 0 T) := by
    intro t ht
    exact (hx t ht).continuousWithinAt
  have hyCont : ContinuousOn y (Set.Icc 0 T) := by
    intro t ht
    exact (hy t ht).continuousWithinAt
  obtain ⟨Bx, hxImageBound⟩ := isCompact_Icc.bddAbove_image
    (f := fun t => ‖x t‖) hxCont.norm
  obtain ⟨By, hyImageBound⟩ := isCompact_Icc.bddAbove_image
    (f := fun t => ‖y t‖) hyCont.norm
  have hBx : 0 ≤ Bx := by
    have := hxImageBound (Set.mem_image_of_mem _ (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩))
    linarith [norm_nonneg (x 0)]
  have hBy : 0 ≤ By := by
    have := hyImageBound (Set.mem_image_of_mem _ (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩))
    linarith [norm_nonneg (y 0)]
  let B := max Bx By
  have hB : 0 ≤ B := le_max_of_le_left hBx
  have hxBound : ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ B := by
    intro t ht
    exact (hxImageBound (Set.mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hyBound : ∀ t ∈ Set.Icc 0 T, ‖y t‖ ≤ B := by
    intro t ht
    exact (hyImageBound (Set.mem_image_of_mem _ ht)).trans (le_max_right _ _)
  exact delay_comparison_massAction_commonDelay_singleSpeciesSources N κ hsrc hτ hT hB
    (by
      intro t ht
      exact hx t ht)
    (by
      intro t ht
      exact le_rfl)
    hy horder hxBound hyBound hxNonneg hyNonneg

end Network
end CRNT

#print axioms CRNT.Network.delayField_nonneg_on_interval_of_nonneg_delayed
#print axioms CRNT.Network.delayField_nonneg_on_methodStep
#print axioms CRNT.Network.delayField_nonneg_on_interval_of_nonneg_positive_delayed
#print axioms CRNT.Network.delayField_nonneg_on_mixed_methodStep
#print axioms CRNT.Network.delayField_nonneg_of_positive_delays_on_bounded_solution
#print axioms CRNT.Network.delayField_nonneg_of_positive_delays
#print axioms CRNT.Network.delayField_nonneg_of_nonnegative_delays
#print axioms CRNT.Network.delay_comparison_massAction_commonDelay_singleSpeciesSources_of_nonnegative_history
