import CRNT.Stochastic.MinimalSemigroupNonExplosion

/-!
# Foster's criterion for the continuous-time chain: expected hitting times

Let `C` be a finite set of states, `V ≥ 0` with finite sublevel sets and `QV ≤ −ε` off `C`
(`ε > 0`). For the chain stopped on entering `C` (`stopOn C`: all rates vanish on `C`), the
probability `u(t, a) = 1 − ∑_{b ∈ C} P^C(t)(a, b)` of not having entered `C` by time `t`
satisfies

`∫₀ᵀ u(t, a) dt ≤ V(a) / ε`  (`integral_notAbsorbed_le`),

so the expected hitting time of `C` is at most `V(a)/ε`; since `u(·, a)` is nonincreasing
(Chapman–Kolmogorov), `u(T, a) ≤ V(a)/(εT)` and `C` is entered with probability tending to one
(`tendsto_absorbed_one`).

Proof without path measures: with `m_k(t, a) = ∑_{b ∉ C} P^C_k(t)(a, b)` and
`M_k(t, a) = ∑_b P^C_k(t)(a, b) V(b)`, induction through the backward recursion gives
`ε ∫₀ᵀ m_k(t, a) dt + M_k(T, a) ≤ V(a)` for every number of jumps `k` (`foster_le`), using the
Fubini identity `∫₀ᵀ ∫₀ᵗ φ(s) ψ(t − s) ds dt = ∫₀ᵀ φ(s) ∫₀^{T−s} ψ` (`integral_integral_conv`).
Non-explosion of the stopped chain (`hasSum_Pmin_one_of_drift`) identifies `lim_k m_k` with `u`.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

/-- **Fubini for a convolution** over the triangle `0 ≤ s ≤ t ≤ T`. -/
theorem integral_integral_conv {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (∫ s in (0 : ℝ)..t, φ s * ψ (t - s)) =
      ∫ s in (0 : ℝ)..T, φ s * ∫ u in (0 : ℝ)..(T - s), ψ u := by
  let g : ℝ → ℝ := fun u => if 0 ≤ u then ψ u else 0
  have hgm : Measurable g := Measurable.ite measurableSet_Ici hψ.measurable measurable_const
  obtain ⟨Mφ, hMφ⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hφ.continuousOn
  obtain ⟨Mψ, hMψ⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hψ.continuousOn
  have hgb : ∀ u ≤ T, ‖g u‖ ≤ Mψ := by
    intro u hu
    by_cases h0 : 0 ≤ u
    · simp only [g, h0, ite_true]; exact hMψ u ⟨h0, hu⟩
    · simp only [g, h0, ite_false, norm_zero]; exact (norm_nonneg _).trans (hMψ 0 ⟨le_rfl, hT⟩)
  have hFint : ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s => φ s * g (t - s)) volume 0 T := by
    intro t ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Measure.integrableOn_of_bounded (M := Mφ * Mψ) measure_Ioc_lt_top.ne
      (hφ.measurable.mul (hgm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    rw [norm_mul]
    exact mul_le_mul (hMφ s ⟨hs.1.le, hs.2⟩) (hgb _ (by linarith [ht.2, hs.1]))
      (norm_nonneg _) ((norm_nonneg _).trans (hMφ s ⟨hs.1.le, hs.2⟩))
  have hgi : ∀ a b : ℝ, a ≤ b → b ≤ T → IntervalIntegrable g volume a b := by
    intro a b hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact Measure.integrableOn_of_bounded (M := Mψ) measure_Ioc_lt_top.ne
      hgm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hgb u (hu.2.trans hb))
  -- extend the inner integral to `[0, T]`
  have h1 : ∀ t ∈ uIcc (0 : ℝ) T,
      ∫ s in (0 : ℝ)..t, φ s * ψ (t - s) = ∫ s in (0 : ℝ)..T, φ s * g (t - s) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have hI := hFint t ht
    have hmem : t ∈ uIcc (0 : ℝ) T := by rw [uIcc_of_le hT]; exact ht
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (hI.mono_set (uIcc_subset_uIcc left_mem_uIcc hmem))
      (hI.mono_set (uIcc_subset_uIcc hmem right_mem_uIcc))]
    have hzero : ∫ s in t..T, φ s * g (t - s) = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
        intervalIntegral.integral_zero]
      refine Filter.Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le ht.2] at hs
      have : ¬ (0 ≤ t - s) := by linarith [hs.1]
      simp [g, this]
    rw [hzero, add_zero]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have : 0 ≤ t - s := by linarith [hs.2]
    simp [g, this]
  -- integrability on the square
  have hsq : IntegrableOn (Function.uncurry fun t s => φ s * g (t - s))
      (uIoc (0 : ℝ) T ×ˢ uIoc (0 : ℝ) T) := by
    rw [uIoc_of_le hT]
    refine Measure.integrableOn_of_bounded (M := Mφ * Mψ) ?_ ?_
      (ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_)
    · exact ((measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).trans_lt
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
    · exact ((hφ.measurable.comp measurable_snd).mul
        (hgm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    · obtain ⟨h1', h2'⟩ := hp
      simp only [Function.uncurry, norm_mul]
      exact mul_le_mul (hMφ _ ⟨h2'.1.le, h2'.2⟩) (hgb _ (by linarith [h1'.2, h2'.1]))
        (norm_nonneg _) ((norm_nonneg _).trans (hMφ _ ⟨h2'.1.le, h2'.2⟩))
  -- the inner integral after swapping
  have h3 : ∀ s ∈ uIcc (0 : ℝ) T,
      ∫ t in (0 : ℝ)..T, φ s * g (t - s) = φ s * ∫ u in (0 : ℝ)..(T - s), ψ u := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun u => g u) s]
    congr 1
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hgi _ _ (by linarith [hs.1]) (by linarith [hs.1]))
      (hgi _ _ (by linarith [hs.2]) (by linarith [hs.1]))]
    have hz : ∫ u in (0 - s)..0, g u = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
        intervalIntegral.integral_zero]
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with u hu0 hu
      rw [uIoc_of_le (by linarith [hs.1])] at hu
      have : ¬ (0 ≤ u) := fun h => hu0 (le_antisymm hu.2 h)
      simp [g, this]
    rw [hz, zero_add]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith [hs.2])] at hu
    simp [g, hu.1]
  calc ∫ t in (0 : ℝ)..T, (∫ s in (0 : ℝ)..t, φ s * ψ (t - s))
      = ∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..T, φ s * g (t - s) := intervalIntegral.integral_congr h1
    _ = ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, φ s * g (t - s) :=
        intervalIntegral_intervalIntegral_swap hsq
    _ = _ := intervalIntegral.integral_congr h3

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The jump system stopped on a finite set `C`: all rates vanish on `C`. -/
def stopOn (C : Finset α) : JumpSystem α where
  ι := J.ι
  rate i a := if a ∈ C then 0 else J.rate i a
  rate_nonneg i a := by
    split_ifs
    · exact le_rfl
    · exact J.rate_nonneg i a
  next := J.next

/-- The indicator of the complement of `C`. -/
def outside (C : Finset α) (b : α) : ℝ := if b ∈ C then 0 else 1

variable {J}

theorem sum_stopOn_rate_mul_of_mem {C : Finset α} {a : α} (ha : a ∈ C)
    (f : (J.stopOn C).ι → ℝ) : ∑ i, (J.stopOn C).rate i a * f i = 0 := by
  show ∑ i : J.ι, (if a ∈ C then 0 else J.rate i a) * f i = _
  simp [ha]

theorem sum_stopOn_rate_mul_of_not_mem {C : Finset α} {a : α} (ha : a ∉ C)
    (f : (J.stopOn C).ι → ℝ) : ∑ i, (J.stopOn C).rate i a * f i = ∑ i : J.ι, J.rate i a * f i := by
  show ∑ i : J.ι, (if a ∈ C then 0 else J.rate i a) * f i = _
  simp [ha]

theorem stopOn_q_of_mem {C : Finset α} {a : α} (ha : a ∈ C) : (J.stopOn C).q a = 0 := by
  have := sum_stopOn_rate_mul_of_mem (J := J) ha (fun _ => (1 : ℝ))
  simpa [q] using this

theorem stopOn_q_of_not_mem {C : Finset α} {a : α} (ha : a ∉ C) :
    (J.stopOn C).q a = J.q a := by
  have := sum_stopOn_rate_mul_of_not_mem (J := J) ha (fun _ => (1 : ℝ))
  simpa [q] using this

theorem stopOn_drift_of_mem {C : Finset α} {a : α} (ha : a ∈ C) (V : α → ℝ) :
    (J.stopOn C).drift V a = 0 :=
  sum_stopOn_rate_mul_of_mem ha (fun i => V (J.next i a) - V a)

theorem stopOn_drift_of_not_mem {C : Finset α} {a : α} (ha : a ∉ C) (V : α → ℝ) :
    (J.stopOn C).drift V a = J.drift V a :=
  sum_stopOn_rate_mul_of_not_mem ha (fun i => V (J.next i a) - V a)

/-- On `C` the stopped system does not move. -/
theorem stopOn_P_of_mem {C : Finset α} {a : α} (ha : a ∈ C) (k : ℕ) (t : ℝ) (b : α) :
    (J.stopOn C).P k t a b = if a = b then 1 else 0 := by
  cases k with
  | zero => simp [P_zero, stopOn_q_of_mem ha]
  | succ k =>
      rw [P_succ]
      have h0 : ∀ s, Real.exp (-((J.stopOn C).q a * s)) * ∑ i, (J.stopOn C).rate i a *
          (J.stopOn C).P k (t - s) ((J.stopOn C).next i a) b = 0 := fun s => by
        rw [sum_stopOn_rate_mul_of_mem ha, mul_zero]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s _ => h0 s,
        intervalIntegral.integral_zero, add_zero, stopOn_q_of_mem ha]
      simp

theorem stopOn_wmass_of_mem {C : Finset α} {a : α} (ha : a ∈ C) (W : α → ℝ) (k : ℕ) (t : ℝ) :
    (J.stopOn C).wmass W k t a = W a := by
  unfold wmass
  simp [stopOn_P_of_mem ha, (J.stopOn C).mem_reachK_self k a]

theorem stopOn_Pmin_of_mem {C : Finset α} {a : α} (ha : a ∈ C) (t : ℝ) (b : α) :
    (J.stopOn C).Pmin t a b = if a = b then 1 else 0 := by
  simp [Pmin, stopOn_P_of_mem ha]

/-- **Foster estimate with `k` jumps.** If `V ≥ 0` and `QV ≤ −ε` off `C`, then for the system
stopped on `C`, `ε ∫₀ᵀ P_k(t)(a, Cᶜ) dt + ∑_b P_k(T)(a, b) V(b) ≤ V(a)`. -/
theorem foster_le (C : Finset α) (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) {ε : ℝ}
    (hdrift : ∀ a, a ∉ C → J.drift V a ≤ -ε) (k : ℕ) :
    ∀ T, 0 ≤ T → ∀ a, ε * (∫ t in (0 : ℝ)..T, (J.stopOn C).wmass (outside C) k t a) +
      (J.stopOn C).wmass V k T a ≤ V a := by
  have hqV : ∀ a, a ∉ C → ε ≤ J.q a * V a := by
    intro a ha
    have h1 := J.sum_rate_mul_next V a
    have h2 : 0 ≤ ∑ i, J.rate i a * V (J.next i a) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i a) (hV _)
    linarith [hdrift a ha]
  have hqI : ∀ a T, J.q a * ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) =
      1 - Real.exp (-(J.q a * T)) := by
    intro a T
    rw [← intervalIntegral.integral_const_mul]; exact integral_exp_decay _ _
  induction k with
  | zero =>
      intro T hT a
      by_cases ha : a ∈ C
      · have h0 : ∀ t, (J.stopOn C).wmass (outside C) 0 t a = 0 := fun t => by
          rw [stopOn_wmass_of_mem ha]; simp [outside, ha]
        rw [stopOn_wmass_of_mem ha V]
        simp only [h0, intervalIntegral.integral_zero, mul_zero, zero_add, le_refl]
      · simp only [wmass_zero, stopOn_q_of_not_mem ha, outside, ha, ite_false, mul_one]
        have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) :=
          intervalIntegral.integral_nonneg hT fun t _ => (Real.exp_pos _).le
        have h1 := mul_le_mul_of_nonneg_right (hqV a ha) hI0
        have h2 : J.q a * V a * ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) =
            V a * (1 - Real.exp (-(J.q a * T))) := by rw [← hqI a T]; ring
        linarith
  | succ k ih =>
      intro T hT a
      by_cases ha : a ∈ C
      · have h0 : ∀ t, (J.stopOn C).wmass (outside C) (k + 1) t a = 0 := fun t => by
          rw [stopOn_wmass_of_mem ha]; simp [outside, ha]
        rw [stopOn_wmass_of_mem ha V]
        simp only [h0, intervalIntegral.integral_zero, mul_zero, zero_add, le_refl]
      · have hq := stopOn_q_of_not_mem (J := J) ha
        let φ : ℝ → ℝ := fun s => Real.exp (-(J.q a * s))
        let ψ : ℝ → ℝ := fun u => ∑ i, J.rate i a * (J.stopOn C).wmass (outside C) k u (J.next i a)
        let χ : ℝ → ℝ := fun u => ∑ i, J.rate i a * (J.stopOn C).wmass V k u (J.next i a)
        have hφc : Continuous φ := by fun_prop
        have hψc : Continuous ψ := continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((J.stopOn C).continuous_wmass _ k _)
        have hχc : Continuous χ := continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((J.stopOn C).continuous_wmass _ k _)
        have hm : ∀ t, (J.stopOn C).wmass (outside C) (k + 1) t a =
            φ t + ∫ s in (0 : ℝ)..t, φ s * ψ (t - s) := by
          intro t
          rw [wmass_succ, hq]
          congr 1
          · simp [φ, outside, ha]
          · refine intervalIntegral.integral_congr fun s _ => ?_
            rw [sum_stopOn_rate_mul_of_not_mem ha]; rfl
        have hM : (J.stopOn C).wmass V (k + 1) T a =
            φ T * V a + ∫ s in (0 : ℝ)..T, φ s * χ (T - s) := by
          rw [wmass_succ, hq]
          congr 1
          refine intervalIntegral.integral_congr fun s _ => ?_
          rw [sum_stopOn_rate_mul_of_not_mem ha]; rfl
        have hB : Continuous fun t => ∫ s in (0 : ℝ)..t, φ s * ψ (t - s) := by
          have hF : Continuous (Function.uncurry fun (t s : ℝ) => φ s * ψ (t - s)) :=
            (hφc.comp continuous_snd).mul (hψc.comp (continuous_fst.sub continuous_snd))
          exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hF continuous_id
        have hint_m : ∫ t in (0 : ℝ)..T, (J.stopOn C).wmass (outside C) (k + 1) t a =
            (∫ t in (0 : ℝ)..T, φ t) + ∫ s in (0 : ℝ)..T, φ s * ∫ u in (0 : ℝ)..(T - s), ψ u := by
          simp only [hm]
          rw [intervalIntegral.integral_add (hφc.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
            integral_integral_conv hφc hψc hT]
        have hΨ : ∀ v, ∫ u in (0 : ℝ)..v, ψ u = ∑ i, J.rate i a *
            ∫ u in (0 : ℝ)..v, (J.stopOn C).wmass (outside C) k u (J.next i a) := by
          intro v
          show ∫ u in (0 : ℝ)..v, ∑ i, J.rate i a * (J.stopOn C).wmass (outside C) k u (J.next i a)
            = _
          rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
          · exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
          · exact (continuous_const.mul ((J.stopOn C).continuous_wmass _ k _)).intervalIntegrable _ _
        have hPc : Continuous fun v => ∫ u in (0 : ℝ)..v, ψ u :=
          intervalIntegral.continuous_primitive (fun _ _ => hψc.intervalIntegrable _ _) 0
        have hbound : ∀ s ∈ Icc (0 : ℝ) T,
            ε * (φ s * ∫ u in (0 : ℝ)..(T - s), ψ u) + φ s * χ (T - s) ≤
              φ s * ∑ i, J.rate i a * V (J.next i a) := by
          intro s hs
          have hTs : 0 ≤ T - s := by linarith [hs.2]
          have hin : ε * ∑ i, J.rate i a *
              (∫ u in (0 : ℝ)..(T - s), (J.stopOn C).wmass (outside C) k u (J.next i a)) +
              χ (T - s) ≤ ∑ i, J.rate i a * V (J.next i a) := by
            simp only [χ]
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun i _ => ?_
            calc ε * (J.rate i a *
                  ∫ u in (0 : ℝ)..(T - s), (J.stopOn C).wmass (outside C) k u (J.next i a)) +
                  J.rate i a * (J.stopOn C).wmass V k (T - s) (J.next i a)
                = J.rate i a * (ε *
                    (∫ u in (0 : ℝ)..(T - s), (J.stopOn C).wmass (outside C) k u (J.next i a)) +
                    (J.stopOn C).wmass V k (T - s) (J.next i a)) := by ring
              _ ≤ J.rate i a * V (J.next i a) :=
                  mul_le_mul_of_nonneg_left (ih (T - s) hTs (J.next i a)) (J.rate_nonneg i a)
          rw [hΨ]
          have hφs : 0 ≤ φ s := (Real.exp_pos _).le
          have := mul_le_mul_of_nonneg_left hin hφs
          linarith
        have hf1c : Continuous fun s => ε * (φ s * ∫ u in (0 : ℝ)..(T - s), ψ u) :=
          continuous_const.mul (hφc.mul (hPc.comp (continuous_const.sub continuous_id)))
        have hf2c : Continuous fun s => φ s * χ (T - s) :=
          hφc.mul (hχc.comp (continuous_const.sub continuous_id))
        have hgc : Continuous fun s => φ s * ∑ i, J.rate i a * V (J.next i a) :=
          hφc.mul continuous_const
        have hmono := intervalIntegral.integral_mono_on hT
          ((hf1c.add hf2c).intervalIntegrable (μ := volume) 0 T)
          (hgc.intervalIntegrable (μ := volume) 0 T) hbound
        simp only [Pi.add_apply] at hmono
        rw [intervalIntegral.integral_add (hf1c.intervalIntegrable (μ := volume) 0 T)
            (hf2c.intervalIntegrable (μ := volume) 0 T), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_mul_const] at hmono
        have hsumV : ∑ i, J.rate i a * V (J.next i a) ≤ J.q a * V a - ε := by
          rw [J.sum_rate_mul_next]; linarith [hdrift a ha]
        have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, φ t :=
          intervalIntegral.integral_nonneg hT fun t _ => (Real.exp_pos _).le
        have h3 := mul_le_mul_of_nonneg_left hsumV hI0
        have hqI' : J.q a * ∫ t in (0 : ℝ)..T, φ t = 1 - φ T := hqI a T
        have h4 : (∫ t in (0 : ℝ)..T, φ t) * (J.q a * V a - ε) =
            (1 - φ T) * V a - ε * ∫ t in (0 : ℝ)..T, φ t := by
          rw [← hqI']; ring
        rw [hint_m, hM]
        linarith

variable (J)

theorem mass_le_one (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (a : α) : J.mass k t a ≤ 1 :=
  J.sum_P_le_one k t ht a _

theorem mass_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (a : α) : 0 ≤ J.mass k t a :=
  Finset.sum_nonneg fun b _ => J.P_nonneg k t ht a b

/-- If the minimal transition function is stochastic at `a`, the mass of `P_k(t)(a, ·)` tends to
`1` as the number of jumps grows. -/
theorem tendsto_mass_one {t : ℝ} (ht : 0 ≤ t) {a : α} (h : HasSum (fun b => J.Pmin t a b) 1) :
    Tendsto (fun k => J.mass k t a) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx =>
    Eventually.of_forall fun k => lt_of_le_of_lt (J.mass_le_one k ht a) hx⟩
  obtain ⟨F, hF⟩ : ∃ F : Finset α, x < ∑ b ∈ F, J.Pmin t a b :=
    (Filter.Tendsto.eventually h (lt_mem_nhds hx)).exists
  have hlim : Tendsto (fun k => ∑ b ∈ F, J.P k t a b) atTop (𝓝 (∑ b ∈ F, J.Pmin t a b)) :=
    tendsto_finsetSum _ fun b _ => J.tendsto_P t ht a b
  filter_upwards [hlim.eventually (lt_mem_nhds hF)] with k hk
  calc x < ∑ b ∈ F, J.P k t a b := hk
    _ ≤ ∑ b ∈ F ∪ J.reachK k a, J.P k t a b :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
          J.P_nonneg k t ht a b
    _ = J.mass k t a := J.sum_P_eq_mass_of_subset k t a Finset.subset_union_right

/-- The mass outside `C`: `∑_{b ∉ C} P_k(t)(a, b) = mass − ∑_{b ∈ C} P_k(t)(a, b)`. -/
theorem wmass_outside_eq (C : Finset α) (k : ℕ) (t : ℝ) (a : α) :
    J.wmass (outside C) k t a = J.mass k t a - ∑ b ∈ C, J.P k t a b := by
  unfold wmass mass
  have h : ∀ b, J.P k t a b * outside C b = J.P k t a b - (if b ∈ C then J.P k t a b else 0) := by
    intro b; unfold outside; split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_mem]
  congr 1
  refine Finset.sum_subset Finset.inter_subset_right fun b hbC hb => ?_
  exact J.P_eq_zero_of_not_mem k t a b fun hR => hb (Finset.mem_inter.mpr ⟨hR, hbC⟩)

/-- **Foster's criterion: expected hitting time.** If `V ≥ 0` has finite sublevel sets and
`QV ≤ −ε` off the finite set `C`, then for the chain stopped on `C` the probability of not
having entered `C` by time `t` has integral over `[0, T]` at most `V(a)/ε`. -/
theorem integral_notAbsorbed_le (C : Finset α) (V : α → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite) {ε : ℝ} (hε : 0 < ε)
    (hdrift : ∀ a, a ∉ C → J.drift V a ≤ -ε) {T : ℝ} (hT : 0 ≤ T) (a : α) :
    ∫ t in (0 : ℝ)..T, (1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b) ≤ V a / ε := by
  have hdrift' : ∀ b, (J.stopOn C).drift V b ≤ 0 * V b := by
    intro b
    rw [zero_mul]
    by_cases hb : b ∈ C
    · rw [stopOn_drift_of_mem hb]
    · rw [stopOn_drift_of_not_mem hb]; linarith [hdrift b hb]
  have hstoch : ∀ t, 0 ≤ t → HasSum (fun b => (J.stopOn C).Pmin t a b) 1 := fun t ht =>
    (J.stopOn C).hasSum_Pmin_one_of_drift V hV hfin le_rfl hdrift' ht a
  have hlim : ∀ t, 0 ≤ t → Tendsto (fun k => (J.stopOn C).wmass (outside C) k t a) atTop
      (𝓝 (1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b)) := by
    intro t ht
    simp only [wmass_outside_eq]
    exact ((J.stopOn C).tendsto_mass_one ht (hstoch t ht)).sub
      (tendsto_finsetSum _ fun b _ => (J.stopOn C).tendsto_P t ht a b)
  have hint : Tendsto (fun k => ∫ t in (0 : ℝ)..T, (J.stopOn C).wmass (outside C) k t a) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, (1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun k =>
        ((J.stopOn C).continuous_wmass _ k a).aestronglyMeasurable) ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall fun k => Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le hT] at ht
      have ht0 : 0 ≤ t := ht.1.le
      rw [wmass_outside_eq, Real.norm_eq_abs, abs_le]
      have h1 := (J.stopOn C).mass_le_one k ht0 a
      have h2 : 0 ≤ ∑ b ∈ C, (J.stopOn C).P k t a b :=
        Finset.sum_nonneg fun b _ => (J.stopOn C).P_nonneg k t ht0 a b
      have h3 : ∑ b ∈ C, (J.stopOn C).P k t a b ≤ (J.stopOn C).mass k t a := by
        rw [← (J.stopOn C).sum_P_eq_mass_of_subset k t a
          (Finset.subset_union_right (s₁ := C))]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
          (J.stopOn C).P_nonneg k t ht0 a b
      constructor <;> linarith
    · exact Eventually.of_forall fun t ht =>
        hlim t (by rw [uIoc_of_le hT] at ht; exact ht.1.le)
  have hk : ∀ k, ∫ t in (0 : ℝ)..T, (J.stopOn C).wmass (outside C) k t a ≤ V a / ε := by
    intro k
    have h := foster_le C V hV hdrift k T hT a
    have hM0 : 0 ≤ (J.stopOn C).wmass V k T a :=
      Finset.sum_nonneg fun b _ => mul_nonneg ((J.stopOn C).P_nonneg k T hT a b) (hV b)
    rw [le_div_iff₀ hε]; linarith
  exact le_of_tendsto' hint hk

/-- Entering `C` is final: the absorbed probability `∑_{b ∈ C} P^C(t)(a, b)` is nondecreasing
in `t` (Chapman–Kolmogorov). -/
theorem sum_stopOn_Pmin_mono (C : Finset α) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (a : α) :
    ∑ b ∈ C, (J.stopOn C).Pmin t a b ≤ ∑ b ∈ C, (J.stopOn C).Pmin (t + s) a b := by
  refine Finset.sum_le_sum fun b hb => ?_
  have h := le_hasSum ((J.stopOn C).hasSum_Pmin_add ht hs a b) b fun c _ =>
    mul_nonneg ((J.stopOn C).Pmin_nonneg t ht a c) ((J.stopOn C).Pmin_nonneg s hs c b)
  simpa [stopOn_Pmin_of_mem hb] using h

/-- **Foster's criterion: hitting with probability one.** Under the hypotheses of
`integral_notAbsorbed_le`, the probability of not having entered `C` by time `T > 0` is at most
`V(a)/(εT)`. -/
theorem notAbsorbed_le (C : Finset α) (V : α → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite) {ε : ℝ} (hε : 0 < ε)
    (hdrift : ∀ a, a ∉ C → J.drift V a ≤ -ε) {T : ℝ} (hT : 0 < T) (a : α) :
    1 - ∑ b ∈ C, (J.stopOn C).Pmin T a b ≤ V a / (ε * T) := by
  have hcont : ContinuousOn (fun t => 1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b) (uIcc 0 T) := by
    rw [uIcc_of_le hT.le]
    exact continuousOn_const.sub (continuousOn_finsetSum _ fun b _ =>
      ((J.stopOn C).continuousOn_Pmin a b).mono Icc_subset_Ici_self)
  have hmono : ∀ t ∈ Icc (0 : ℝ) T, (1 - ∑ b ∈ C, (J.stopOn C).Pmin T a b) ≤
      1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b := by
    intro t ht
    have := sum_stopOn_Pmin_mono J C ht.1 (sub_nonneg.mpr ht.2) a
    rw [add_sub_cancel] at this
    linarith
  have h1 := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const
    (hcont.intervalIntegrable (μ := volume)) hmono
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  have h2 := J.integral_notAbsorbed_le C V hV hfin hε hdrift hT.le a
  rw [div_mul_eq_div_div, le_div_iff₀ hT, mul_comm]
  linarith

/-- Under Foster's drift condition the chain enters `C` with probability tending to one. -/
theorem tendsto_absorbed_one (C : Finset α) (V : α → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite) {ε : ℝ} (hε : 0 < ε)
    (hdrift : ∀ a, a ∉ C → J.drift V a ≤ -ε) (a : α) :
    Tendsto (fun T => ∑ b ∈ C, (J.stopOn C).Pmin T a b) atTop (𝓝 1) := by
  have hlow : Tendsto (fun T : ℝ => 1 - V a / ε / T) atTop (𝓝 1) := by
    have h0 : Tendsto (fun T : ℝ => V a / ε / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have := J.notAbsorbed_le C V hV hfin hε hdrift hT a
    rw [div_div]; linarith
  · filter_upwards [eventually_ge_atTop 0] with T hT
    exact (J.stopOn C).sum_Pmin_le_one T hT a C

end JumpSystem

end CRNT
