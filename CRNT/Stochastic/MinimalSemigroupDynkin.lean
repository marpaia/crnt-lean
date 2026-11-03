import CRNT.Stochastic.MinimalSemigroupFoster

/-!
# The f-norm (Dynkin) bound for the minimal transition function

If `V ≥ 0`, `f ≥ 0`, `K ≥ 0` and `QV ≤ −f + K`, then

`∫₀ᵀ ∑_b P(t)(a, b) f(b) dt + ∑_b P(T)(a, b) V(b) ≤ V(a) + K T`

for every number of jumps (`dynkin_le`), and hence for the minimal transition function on every
finite set of states (`integral_sum_Pmin_mul_le`; Meyn–Tweedie 1993, the `f`-norm bound). In
particular the time averages charge `{f ≥ R}` by at most `(V(a)/T + K)/R`
(`integral_sum_Pmin_le_of_ge`).
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

theorem integral_exp_add_mul_sub (q T : ℝ) :
    ∫ s in (0 : ℝ)..T, (Real.exp (-(q * s)) + q * Real.exp (-(q * s)) * (T - s)) = T := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) T, HasDerivAt (fun s => -(Real.exp (-(q * s)) * (T - s)))
      (Real.exp (-(q * s)) + q * Real.exp (-(q * s)) * (T - s)) s := by
    intro s _
    have hin : HasDerivAt (fun s : ℝ => -(q * s)) (-q) s := by
      have h0 := ((hasDerivAt_id s).const_mul q).neg
      have hf : (fun s : ℝ => -(q * s)) = -(fun y => q * id y) := by funext y; simp
      rw [hf]; convert h0 using 1; ring
    have h2 : HasDerivAt (fun x => -(Real.exp (-(q * x)) * (T - x))) _ s :=
      (hin.exp.mul ((hasDerivAt_id s).const_sub T)).neg
    convert h2 using 1
    simp only [id]; ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Dynkin bound with `k` jumps.** -/
theorem dynkin_le (V f : α → ℝ) (hV : ∀ a, 0 ≤ V a) {K : ℝ} (hK : 0 ≤ K)
    (hdrift : ∀ a, J.drift V a ≤ -f a + K) (k : ℕ) :
    ∀ T, 0 ≤ T → ∀ a, (∫ t in (0 : ℝ)..T, J.wmass f k t a) + J.wmass V k T a ≤ V a + K * T := by
  have hqI : ∀ a T, J.q a * ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) =
      1 - Real.exp (-(J.q a * T)) := by
    intro a T
    rw [← intervalIntegral.integral_const_mul]; exact integral_exp_decay _ _
  have hfa : ∀ a, f a ≤ K + J.q a * V a := by
    intro a
    have h1 := J.sum_rate_mul_next V a
    have h2 : 0 ≤ ∑ i, J.rate i a * V (J.next i a) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i a) (hV _)
    linarith [hdrift a]
  induction k with
  | zero =>
      intro T hT a
      simp only [wmass_zero]
      have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) :=
        intervalIntegral.integral_nonneg hT fun t _ => (Real.exp_pos _).le
      have hIT : ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t)) ≤ T := by
        have := intervalIntegral.integral_mono_on (f := fun t => Real.exp (-(J.q a * t)))
          (g := fun _ => (1 : ℝ)) hT (by apply Continuous.intervalIntegrable; fun_prop)
          (continuous_const.intervalIntegrable (μ := volume) 0 T)
          fun t ht => Real.exp_le_one_iff.mpr (by nlinarith [J.q_nonneg a, ht.1])
        simpa using this
      rw [intervalIntegral.integral_mul_const]
      set I := ∫ t in (0 : ℝ)..T, Real.exp (-(J.q a * t))
      have h1 := mul_le_mul_of_nonneg_left (hfa a) hI0
      have h2 : J.q a * I * V a = (1 - Real.exp (-(J.q a * T))) * V a := by rw [hqI a T]
      have h3 := mul_le_mul_of_nonneg_left hIT hK
      nlinarith
  | succ k ih =>
      intro T hT a
      let φ : ℝ → ℝ := fun s => Real.exp (-(J.q a * s))
      let ψ : ℝ → ℝ := fun u => ∑ i, J.rate i a * J.wmass f k u (J.next i a)
      let χ : ℝ → ℝ := fun u => ∑ i, J.rate i a * J.wmass V k u (J.next i a)
      have hφc : Continuous φ := by fun_prop
      have hψc : Continuous ψ := continuous_finsetSum _ fun i _ =>
        continuous_const.mul (J.continuous_wmass _ k _)
      have hχc : Continuous χ := continuous_finsetSum _ fun i _ =>
        continuous_const.mul (J.continuous_wmass _ k _)
      have hm : ∀ t, J.wmass f (k + 1) t a = φ t * f a + ∫ s in (0 : ℝ)..t, φ s * ψ (t - s) :=
        fun t => J.wmass_succ f k t a
      have hM : J.wmass V (k + 1) T a = φ T * V a + ∫ s in (0 : ℝ)..T, φ s * χ (T - s) :=
        J.wmass_succ V k T a
      have hB : Continuous fun t => ∫ s in (0 : ℝ)..t, φ s * ψ (t - s) := by
        have hF : Continuous (Function.uncurry fun (t s : ℝ) => φ s * ψ (t - s)) :=
          (hφc.comp continuous_snd).mul (hψc.comp (continuous_fst.sub continuous_snd))
        exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hF continuous_id
      have hA1 : IntervalIntegrable (fun t => φ t * f a) volume 0 T :=
        (hφc.mul continuous_const).intervalIntegrable 0 T
      have hint_m : ∫ t in (0 : ℝ)..T, J.wmass f (k + 1) t a =
          (∫ t in (0 : ℝ)..T, φ t) * f a + ∫ s in (0 : ℝ)..T, φ s * ∫ u in (0 : ℝ)..(T - s), ψ u := by
        simp only [hm]
        rw [intervalIntegral.integral_add hA1 (hB.intervalIntegrable 0 T),
          integral_integral_conv hφc hψc hT, intervalIntegral.integral_mul_const]
      have hΨ : ∀ v, ∫ u in (0 : ℝ)..v, ψ u = ∑ i, J.rate i a *
          ∫ u in (0 : ℝ)..v, J.wmass f k u (J.next i a) := by
        intro v
        show ∫ u in (0 : ℝ)..v, ∑ i, J.rate i a * J.wmass f k u (J.next i a) = _
        rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
        · exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
        · exact (continuous_const.mul (J.continuous_wmass _ k _)).intervalIntegrable _ _
      have hPc : Continuous fun v => ∫ u in (0 : ℝ)..v, ψ u :=
        intervalIntegral.continuous_primitive (fun _ _ => hψc.intervalIntegrable _ _) 0
      have hbound : ∀ s ∈ Icc (0 : ℝ) T,
          φ s * (∫ u in (0 : ℝ)..(T - s), ψ u) + φ s * χ (T - s) ≤
            φ s * (∑ i, J.rate i a * V (J.next i a)) + J.q a * K * (φ s * (T - s)) := by
        intro s hs
        have hTs : 0 ≤ T - s := by linarith [hs.2]
        have hin : (∑ i, J.rate i a *
            (∫ u in (0 : ℝ)..(T - s), J.wmass f k u (J.next i a))) + χ (T - s) ≤
            ∑ i, J.rate i a * V (J.next i a) + J.q a * (K * (T - s)) := by
          simp only [χ, q]
          rw [← Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          have := mul_le_mul_of_nonneg_left (ih (T - s) hTs (J.next i a)) (J.rate_nonneg i a)
          nlinarith
        rw [hΨ]
        have hφs : 0 ≤ φ s := (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left hin hφs
        nlinarith
      have hf1c : Continuous fun s => φ s * ∫ u in (0 : ℝ)..(T - s), ψ u :=
        hφc.mul (hPc.comp (continuous_const.sub continuous_id))
      have hf2c : Continuous fun s => φ s * χ (T - s) :=
        hφc.mul (hχc.comp (continuous_const.sub continuous_id))
      have hgc : Continuous fun s => φ s * (∑ i, J.rate i a * V (J.next i a)) +
          J.q a * K * (φ s * (T - s)) := by
        refine (hφc.mul continuous_const).add (continuous_const.mul (hφc.mul ?_))
        exact continuous_const.sub continuous_id
      have hG1 : IntervalIntegrable (fun s => φ s * (∑ i, J.rate i a * V (J.next i a))) volume 0 T :=
        (hφc.mul continuous_const).intervalIntegrable 0 T
      have hG2 : IntervalIntegrable (fun s => J.q a * K * (φ s * (T - s))) volume 0 T :=
        (continuous_const.mul (hφc.mul (continuous_const.sub continuous_id))).intervalIntegrable 0 T
      have hmono := intervalIntegral.integral_mono_on hT
        ((hf1c.add hf2c).intervalIntegrable (μ := volume) 0 T)
        (hgc.intervalIntegrable (μ := volume) 0 T) hbound
      simp only [Pi.add_apply] at hmono
      rw [intervalIntegral.integral_add (hf1c.intervalIntegrable (μ := volume) 0 T)
          (hf2c.intervalIntegrable (μ := volume) 0 T), intervalIntegral.integral_add hG1 hG2,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul] at hmono
      have hsumV : ∑ i, J.rate i a * V (J.next i a) ≤ -f a + K + J.q a * V a := by
        rw [J.sum_rate_mul_next]; linarith [hdrift a]
      have hI0 : 0 ≤ ∫ t in (0 : ℝ)..T, φ t :=
        intervalIntegral.integral_nonneg hT fun t _ => (Real.exp_pos _).le
      have h3 := mul_le_mul_of_nonneg_left hsumV hI0
      have hqI' : J.q a * ∫ t in (0 : ℝ)..T, φ t = 1 - φ T := hqI a T
      have hP1 : IntervalIntegrable (fun s => φ s * (T - s)) volume 0 T :=
        (hφc.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 T
      have hT' : (∫ t in (0 : ℝ)..T, φ t) + J.q a * ∫ s in (0 : ℝ)..T, φ s * (T - s) = T := by
        have hq2 : IntervalIntegrable (fun x => J.q a * (φ x * (T - x))) volume 0 T := by
          apply Continuous.intervalIntegrable
          exact continuous_const.mul (hφc.mul (continuous_const.sub continuous_id))
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add (hφc.intervalIntegrable 0 T) hq2]
        refine Eq.trans ?_ (integral_exp_add_mul_sub (J.q a) T)
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [φ]; ring
      have h4 : (∫ t in (0 : ℝ)..T, φ t) * (J.q a * V a) = (1 - φ T) * V a := by
        rw [← mul_assoc, mul_comm _ (J.q a), hqI']
      rw [hint_m, hM]
      have h5 : J.q a * K * ∫ s in (0 : ℝ)..T, φ s * (T - s) =
          K * (T - ∫ t in (0 : ℝ)..T, φ t) := by linear_combination K * hT'
      nlinarith [hqI', hT', h3, hmono, h4, h5]

/-- **The `f`-norm bound** for the minimal transition function, on every finite set of states. -/
theorem integral_sum_Pmin_mul_le (V f : α → ℝ) (hV : ∀ a, 0 ≤ V a) (hf : ∀ a, 0 ≤ f a)
    {K : ℝ} (hK : 0 ≤ K) (hdrift : ∀ a, J.drift V a ≤ -f a + K) {T : ℝ} (hT : 0 ≤ T) (a : α)
    (F : Finset α) : ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * f b ≤ V a + K * T := by
  have hk : ∀ k, ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.P k t a b * f b ≤ V a + K * T := by
    intro k
    have h := J.dynkin_le V f hV hK hdrift k T hT a
    have hM0 : 0 ≤ J.wmass V k T a :=
      Finset.sum_nonneg fun b _ => mul_nonneg (J.P_nonneg k T hT a b) (hV b)
    refine le_trans (intervalIntegral.integral_mono_on hT ?_ ?_ fun t ht => ?_) (by linarith)
    · exact (continuous_finsetSum _ fun b _ => (J.continuous_P k a b).mul
        continuous_const).intervalIntegrable 0 T
    · exact (J.continuous_wmass f k a).intervalIntegrable 0 T
    · calc ∑ b ∈ F, J.P k t a b * f b ≤ ∑ b ∈ F ∪ J.reachK k a, J.P k t a b * f b :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
              mul_nonneg (J.P_nonneg k t ht.1 a b) (hf b)
        _ = J.wmass f k t a := J.sum_P_mul_eq_wmass_of_subset f k t a Finset.subset_union_right
  have hlim : Tendsto (fun k => ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.P k t a b * f b) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * f b)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ∑ b ∈ F, f b) (Eventually.of_forall fun k =>
        (continuous_finsetSum _ fun b _ => (J.continuous_P k a b).mul
          continuous_const).aestronglyMeasurable) ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall fun k => Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le hT] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun b _ =>
        mul_nonneg (J.P_nonneg k t ht.1.le a b) (hf b))]
      exact Finset.sum_le_sum fun b _ =>
        mul_le_of_le_one_left (hf b) (J.P_le_one k t ht.1.le a b)
    · refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le hT] at ht
      exact tendsto_finsetSum _ fun b _ => (J.tendsto_P t ht.1.le a b).mul_const _
  exact le_of_tendsto' hlim hk

/-- **Tightness of time averages.** On a finite set where `f ≥ R > 0`, the time average of the
transition probabilities over `[0, T]` is at most `(V(a) + K T)/R`. -/
theorem integral_sum_Pmin_le_of_ge (V f : α → ℝ) (hV : ∀ a, 0 ≤ V a) (hf : ∀ a, 0 ≤ f a)
    {K : ℝ} (hK : 0 ≤ K) (hdrift : ∀ a, J.drift V a ≤ -f a + K) {T : ℝ} (hT : 0 ≤ T) (a : α)
    {R : ℝ} (hR : 0 < R) (G : Finset α) (hG : ∀ b ∈ G, R ≤ f b) :
    ∫ t in (0 : ℝ)..T, ∑ b ∈ G, J.Pmin t a b ≤ (V a + K * T) / R := by
  rw [le_div_iff₀ hR, ← intervalIntegral.integral_mul_const]
  refine le_trans (intervalIntegral.integral_mono_on hT ?_ ?_ fun t ht => ?_)
    (J.integral_sum_Pmin_mul_le V f hV hf hK hdrift hT a G)
  · exact ((continuousOn_finsetSum _ fun b _ => J.continuousOn_Pmin a b).mono
      (by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)).mul continuousOn_const
      |>.intervalIntegrable
  · exact ((continuousOn_finsetSum _ fun b _ => (J.continuousOn_Pmin a b).mul
      continuousOn_const).mono (by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)).intervalIntegrable
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun b hb =>
      mul_le_mul_of_nonneg_left (hG b hb) (J.Pmin_nonneg t ht.1 a b)

end JumpSystem

end CRNT
