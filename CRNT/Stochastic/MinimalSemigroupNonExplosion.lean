import CRNT.Stochastic.MinimalSemigroupChapmanKolmogorov

/-!
# Non-explosion of the minimal transition function under a Lyapunov drift condition

For a jump system with finitely many channels, write `QV(a) = ∑ᵢ rateᵢ(a) (V(nextᵢ a) − V(a))`
(`drift`). If `V ≥ 0` has finite sublevel sets and `QV ≤ c V` for some `c ≥ 0`, the minimal
transition function is stochastic: `∑_b P(t)(a, b) = 1` for every `t ≥ 0`
(`hasSum_Pmin_one_of_drift`; affine form `QV ≤ c V + d` in `hasSum_Pmin_one_of_drift_affine`).

Proof, without path measures:
* moment bound: `∑_b P_k(t)(a, b) V(b) ≤ e^{ct} V(a)` for every `k`, by induction through the
  backward recursion, using `∑ᵢ rateᵢ(a) V(nextᵢ a) ≤ (c + q(a)) V(a)` and
  `∫₀ᵗ e^{−q u} e^{c(t−u)} (c + q) du = e^{ct} − e^{−qt}` (`wmass_le`, `sum_Pmin_mul_le`);
* stopping: the system stopped outside the finite set `K = {V ≤ R}` (`stopOutside`) has bounded
  exit rates, hence is stochastic (`hasSum_Pmin_one`); its mass outside `K` is at most
  `e^{ct} V(a) / R` by the moment bound; on `K` it is dominated by the original minimal
  transition function (`Pmin_stopOutside_le`). Letting `R → ∞` gives total mass `1`.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The generator applied to an observable `V`. -/
def drift (V : α → ℝ) (a : α) : ℝ := ∑ i, J.rate i a * (V (J.next i a) - V a)

omit [DecidableEq α] in
theorem sum_rate_mul_next (V : α → ℝ) (a : α) :
    ∑ i, J.rate i a * V (J.next i a) = J.drift V a + J.q a * V a := by
  simp only [drift, q, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

/-- The jump system stopped outside a finite set `K`: all rates vanish outside `K`. -/
def stopOutside (K : Finset α) : JumpSystem α where
  ι := J.ι
  rate i a := if a ∈ K then J.rate i a else 0
  rate_nonneg i a := by
    split_ifs
    · exact J.rate_nonneg i a
    · exact le_rfl
  next := J.next

variable {J}

theorem stopOutside_rate (K : Finset α) (i : J.ι) (a : α) :
    (J.stopOutside K).rate i a = if a ∈ K then J.rate i a else 0 := rfl

theorem stopOutside_next (K : Finset α) (i : J.ι) (a : α) :
    (J.stopOutside K).next i a = J.next i a := rfl

theorem sum_stopOutside_rate_mul_of_mem {K : Finset α} {a : α} (ha : a ∈ K)
    (f : (J.stopOutside K).ι → ℝ) :
    ∑ i, (J.stopOutside K).rate i a * f i = ∑ i : J.ι, J.rate i a * f i := by
  show ∑ i : J.ι, (if a ∈ K then J.rate i a else 0) * f i = _
  simp [ha]

theorem sum_stopOutside_rate_mul_of_not_mem {K : Finset α} {a : α} (ha : a ∉ K)
    (f : (J.stopOutside K).ι → ℝ) : ∑ i, (J.stopOutside K).rate i a * f i = 0 := by
  show ∑ i : J.ι, (if a ∈ K then J.rate i a else 0) * f i = _
  simp [ha]

theorem stopOutside_q_of_mem {K : Finset α} {a : α} (ha : a ∈ K) :
    (J.stopOutside K).q a = J.q a := by
  have := sum_stopOutside_rate_mul_of_mem (J := J) ha (fun _ => (1 : ℝ))
  simpa [q] using this

theorem stopOutside_q_of_not_mem {K : Finset α} {a : α} (ha : a ∉ K) :
    (J.stopOutside K).q a = 0 := by
  have := sum_stopOutside_rate_mul_of_not_mem (J := J) ha (fun _ => (1 : ℝ))
  simpa [q] using this

theorem stopOutside_q_le (K : Finset α) (a : α) :
    (J.stopOutside K).q a ≤ ∑ c ∈ K, J.q c := by
  by_cases ha : a ∈ K
  · rw [stopOutside_q_of_mem ha]
    exact Finset.single_le_sum (f := J.q) (fun c _ => J.q_nonneg c) ha
  · rw [stopOutside_q_of_not_mem ha]
    exact Finset.sum_nonneg fun c _ => J.q_nonneg c

theorem stopOutside_drift_of_mem {K : Finset α} {a : α} (ha : a ∈ K) (V : α → ℝ) :
    (J.stopOutside K).drift V a = J.drift V a :=
  sum_stopOutside_rate_mul_of_mem ha (fun i => V (J.next i a) - V a)

theorem stopOutside_drift_of_not_mem {K : Finset α} {a : α} (ha : a ∉ K) (V : α → ℝ) :
    (J.stopOutside K).drift V a = 0 :=
  sum_stopOutside_rate_mul_of_not_mem ha (fun i => V (J.next i a) - V a)

/-- Outside `K` the stopped system does not move. -/
theorem stopOutside_P_of_not_mem {K : Finset α} {a b : α} (ha : a ∉ K) (hab : a ≠ b) (k : ℕ)
    (t : ℝ) : (J.stopOutside K).P k t a b = 0 := by
  cases k with
  | zero => simp [P_zero, hab]
  | succ k =>
      rw [P_succ]
      have h0 : ∀ s, Real.exp (-((J.stopOutside K).q a * s)) * ∑ i, (J.stopOutside K).rate i a *
          (J.stopOutside K).P k (t - s) ((J.stopOutside K).next i a) b = 0 := fun s => by
        rw [sum_stopOutside_rate_mul_of_not_mem ha, mul_zero]
      simp [h0, hab]

/-- **Comparison.** On `K`, the stopped system's transition probabilities are dominated by the
original ones. -/
theorem P_stopOutside_le (K : Finset α) (k : ℕ) :
    ∀ t, 0 ≤ t → ∀ a b, b ∈ K → (J.stopOutside K).P k t a b ≤ J.P k t a b := by
  induction k with
  | zero =>
      intro t ht a b hb
      by_cases ha : a ∈ K
      · simp only [P_zero, stopOutside_q_of_mem ha, le_refl]
      · have hab : a ≠ b := fun h => ha (h ▸ hb)
        rw [stopOutside_P_of_not_mem ha hab]
        exact J.P_nonneg 0 t ht a b
  | succ k ih =>
      intro t ht a b hb
      by_cases ha : a ∈ K
      · rw [P_succ, P_succ, stopOutside_q_of_mem ha]
        refine add_le_add le_rfl (intervalIntegral.integral_mono_on ht ?_ ?_ fun s hs => ?_)
        · have := (J.stopOutside K).integrable_term k t a b
          simpa only [stopOutside_q_of_mem ha] using this
        · exact J.integrable_term k t a b
        · refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [sum_stopOutside_rate_mul_of_mem ha]
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _ b hb)
            (J.rate_nonneg i a)
      · have hab : a ≠ b := fun h => ha (h ▸ hb)
        rw [stopOutside_P_of_not_mem ha hab]
        exact J.P_nonneg _ t ht a b

theorem Pmin_stopOutside_le (K : Finset α) {t : ℝ} (ht : 0 ≤ t) (a : α) {b : α} (hb : b ∈ K) :
    (J.stopOutside K).Pmin t a b ≤ J.Pmin t a b :=
  le_of_tendsto_of_tendsto' ((J.stopOutside K).tendsto_P t ht a b) (J.tendsto_P t ht a b)
    fun k => P_stopOutside_le K k t ht a b hb

variable (J)

/-- The weighted row mass `∑_b P_k(t)(a, b) V(b)`. -/
noncomputable def wmass (V : α → ℝ) (k : ℕ) (t : ℝ) (a : α) : ℝ :=
  ∑ b ∈ J.reachK k a, J.P k t a b * V b

theorem sum_P_mul_eq_wmass_of_subset (V : α → ℝ) (k : ℕ) (t : ℝ) (a : α) {F : Finset α}
    (hF : J.reachK k a ⊆ F) : ∑ b ∈ F, J.P k t a b * V b = J.wmass V k t a := by
  unfold wmass
  exact (Finset.sum_subset hF fun b _ hb => by rw [J.P_eq_zero_of_not_mem k t a b hb, zero_mul]).symm

theorem continuous_wmass (V : α → ℝ) (k : ℕ) (a : α) : Continuous fun t => J.wmass V k t a := by
  unfold wmass
  exact continuous_finsetSum _ fun b _ => (J.continuous_P k a b).mul continuous_const

theorem wmass_zero (V : α → ℝ) (t : ℝ) (a : α) :
    J.wmass V 0 t a = Real.exp (-(J.q a * t)) * V a := by
  simp [wmass, reachK, P_zero]

theorem wmass_succ (V : α → ℝ) (k : ℕ) (t : ℝ) (a : α) :
    J.wmass V (k + 1) t a = Real.exp (-(J.q a * t)) * V a +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
        ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a) := by
  unfold wmass
  simp only [P_succ, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single_of_mem a (J.mem_reachK_self _ a) fun b _ hb => by
      simp [Ne.symm hb]]
    simp
  · simp only [← intervalIntegral.integral_mul_const]
    rw [← intervalIntegral.integral_finsetSum fun b _ =>
      (J.integrable_term k t a b).mul_const _]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (Finset.sum_subset (J.reachK_next_subset k a i) fun b _ hb => ?_).symm.trans ?_
    · rw [J.P_eq_zero_of_not_mem k (t - s) (J.next i a) b hb]; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      ring

/-- **Moment bound.** If `QV ≤ c V` with `V ≥ 0` and `c ≥ 0`, then
`∑_b P_k(t)(a, b) V(b) ≤ e^{ct} V(a)` for every number of jumps `k`. -/
theorem wmass_le (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ a, J.drift V a ≤ c * V a) (k : ℕ) :
    ∀ t, 0 ≤ t → ∀ a, J.wmass V k t a ≤ Real.exp (c * t) * V a := by
  induction k with
  | zero =>
      intro t ht a
      rw [wmass_zero]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hV a)
      nlinarith [J.q_nonneg a]
  | succ k ih =>
      intro t ht a
      rw [wmass_succ]
      have hqa := J.q_nonneg a
      have hsumV : ∑ i, J.rate i a * V (J.next i a) ≤ (c + J.q a) * V a := by
        rw [J.sum_rate_mul_next]; nlinarith [hdrift a]
      have hbound : ∀ s ∈ Icc (0 : ℝ) t, Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a) ≤
          (Real.exp (c * t) * V a) * ((c + J.q a) * Real.exp (-((c + J.q a) * s))) := by
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        have h1 : ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a) ≤
            Real.exp (c * (t - s)) * ((c + J.q a) * V a) := by
          calc ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a)
              ≤ ∑ i, J.rate i a * (Real.exp (c * (t - s)) * V (J.next i a)) :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (ih _ hts _) (J.rate_nonneg i a)
            _ = Real.exp (c * (t - s)) * ∑ i, J.rate i a * V (J.next i a) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            _ ≤ Real.exp (c * (t - s)) * ((c + J.q a) * V a) :=
                mul_le_mul_of_nonneg_left hsumV (Real.exp_pos _).le
        have he : Real.exp (-(J.q a * s)) * Real.exp (c * (t - s)) =
            Real.exp (c * t) * Real.exp (-((c + J.q a) * s)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        calc Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a)
            ≤ Real.exp (-(J.q a * s)) * (Real.exp (c * (t - s)) * ((c + J.q a) * V a)) :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = (Real.exp (c * t) * V a) * ((c + J.q a) * Real.exp (-((c + J.q a) * s))) := by
              linear_combination ((c + J.q a) * V a) * he
      have hf : IntervalIntegrable (fun s => Real.exp (-(J.q a * s)) *
          ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a)) volume 0 t := by
        apply Continuous.intervalIntegrable
        refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
        exact continuous_const.mul
          ((J.continuous_wmass V k _).comp (continuous_const.sub continuous_id))
      have hg : IntervalIntegrable (fun s => (Real.exp (c * t) * V a) *
          ((c + J.q a) * Real.exp (-((c + J.q a) * s)))) volume 0 t := by
        apply Continuous.intervalIntegrable; fun_prop
      have hmono := intervalIntegral.integral_mono_on ht hf hg hbound
      rw [intervalIntegral.integral_const_mul, integral_exp_decay] at hmono
      have hexp : Real.exp (c * t) * Real.exp (-((c + J.q a) * t)) = Real.exp (-(J.q a * t)) := by
        rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp (c * t) * V a * (1 - Real.exp (-((c + J.q a) * t))) =
          Real.exp (c * t) * V a - Real.exp (-(J.q a * t)) * V a := by
        rw [← hexp]; ring
      linarith

/-- The moment bound for the minimal transition function, on every finite set of states. -/
theorem sum_Pmin_mul_le (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ a, J.drift V a ≤ c * V a) {t : ℝ} (ht : 0 ≤ t) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin t a b * V b ≤ Real.exp (c * t) * V a := by
  have hlim : Tendsto (fun k => ∑ b ∈ F, J.P k t a b * V b) atTop
      (𝓝 (∑ b ∈ F, J.Pmin t a b * V b)) :=
    tendsto_finsetSum _ fun b _ => (J.tendsto_P t ht a b).mul_const _
  refine le_of_tendsto' hlim fun k => ?_
  calc ∑ b ∈ F, J.P k t a b * V b ≤ ∑ b ∈ F ∪ J.reachK k a, J.P k t a b * V b :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
          mul_nonneg (J.P_nonneg k t ht a b) (hV b)
    _ = J.wmass V k t a := J.sum_P_mul_eq_wmass_of_subset V k t a Finset.subset_union_right
    _ ≤ _ := J.wmass_le V hV hc hdrift k t ht a

/-- **Non-explosion under a Lyapunov drift condition.** If `V ≥ 0` has finite sublevel sets and
`QV ≤ c V` with `c ≥ 0`, the minimal transition function is stochastic. -/
theorem hasSum_Pmin_one_of_drift (V : α → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite) {c : ℝ} (hc : 0 ≤ c)
    (hdrift : ∀ a, J.drift V a ≤ c * V a) {t : ℝ} (ht : 0 ≤ t) (a : α) :
    HasSum (fun b => J.Pmin t a b) 1 := by
  have hnn : ∀ b, 0 ≤ J.Pmin t a b := fun b => J.Pmin_nonneg t ht a b
  have hsum : Summable fun b => J.Pmin t a b :=
    summable_of_sum_le hnn fun F => J.sum_Pmin_le_one t ht a F
  have hle : ∑' b, J.Pmin t a b ≤ 1 :=
    hsum.tsum_le_of_sum_le fun F => J.sum_Pmin_le_one t ht a F
  have hR : ∀ R : ℝ, 0 < R → 1 ≤ ∑' b, J.Pmin t a b + Real.exp (c * t) * V a / R := by
    intro R hR
    let K := (hfin R).toFinset
    have hmemK : ∀ b, b ∈ K ↔ V b ≤ R := fun b => by simp [K]
    have hdrift' : ∀ b, (J.stopOutside K).drift V b ≤ c * V b := by
      intro b
      by_cases hb : b ∈ K
      · rw [stopOutside_drift_of_mem hb]; exact hdrift b
      · rw [stopOutside_drift_of_not_mem hb]; exact mul_nonneg hc (hV b)
    have hstoch : HasSum (fun b => (J.stopOutside K).Pmin t a b) 1 :=
      (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ c ∈ K, J.q c)
        (fun b _ => stopOutside_q_le K b) ht
    have hnn' : ∀ b, 0 ≤ (J.stopOutside K).Pmin t a b :=
      fun b => (J.stopOutside K).Pmin_nonneg t ht a b
    have hfinite : ∀ F : Finset α, ∑ b ∈ F, (J.stopOutside K).Pmin t a b ≤
        ∑ b ∈ K, (J.stopOutside K).Pmin t a b + Real.exp (c * t) * V a / R := by
      intro F
      rw [← Finset.sum_filter_add_sum_filter_not F (· ∈ K)]
      refine add_le_add ?_ ?_
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun b hb => (Finset.mem_filter.mp hb).2) fun b _ _ => hnn' b
      · rw [le_div_iff₀ hR]
        calc (∑ b ∈ F with b ∉ K, (J.stopOutside K).Pmin t a b) * R
            ≤ ∑ b ∈ F with b ∉ K, (J.stopOutside K).Pmin t a b * V b := by
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hnn' b)
              have h := (Finset.mem_filter.mp hb).2
              rw [hmemK] at h
              exact (not_le.mp h).le
          _ ≤ Real.exp (c * t) * V a :=
              (J.stopOutside K).sum_Pmin_mul_le V hV hc hdrift' ht a _
    have h1 : (1 : ℝ) ≤ ∑ b ∈ K, (J.stopOutside K).Pmin t a b + Real.exp (c * t) * V a / R := by
      rw [← hstoch.tsum_eq]
      exact hstoch.summable.tsum_le_of_sum_le hfinite
    have h2 : ∑ b ∈ K, (J.stopOutside K).Pmin t a b ≤ ∑ b ∈ K, J.Pmin t a b :=
      Finset.sum_le_sum fun b hb => Pmin_stopOutside_le K ht a hb
    have h3 : ∑ b ∈ K, J.Pmin t a b ≤ ∑' b, J.Pmin t a b := hsum.sum_le_tsum K fun b _ => hnn b
    linarith
  have hge : 1 ≤ ∑' b, J.Pmin t a b := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hB : 0 ≤ Real.exp (c * t) * V a := mul_nonneg (Real.exp_pos _).le (hV a)
    have hRpos : 0 < Real.exp (c * t) * V a / ε + 1 := by positivity
    have h := hR _ hRpos
    have hlt : Real.exp (c * t) * V a / (Real.exp (c * t) * V a / ε + 1) < ε := by
      rw [div_lt_iff₀ hRpos]
      have : ε * (Real.exp (c * t) * V a / ε) = Real.exp (c * t) * V a := by field_simp
      nlinarith
    linarith
  exact hsum.hasSum_iff.mpr (le_antisymm hle hge)

/-- **Non-explosion, affine drift.** `V ≥ 0` with finite sublevel sets and
`QV ≤ c V + d` (`c, d ≥ 0`) give a stochastic minimal transition function. -/
theorem hasSum_Pmin_one_of_drift_affine (V : α → ℝ) (hV : ∀ a, 0 ≤ V a)
    (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdrift : ∀ a, J.drift V a ≤ c * V a + d) {t : ℝ} (ht : 0 ≤ t) (a : α) :
    HasSum (fun b => J.Pmin t a b) 1 := by
  refine J.hasSum_Pmin_one_of_drift (fun b => V b + 1) (fun b => by linarith [hV b])
    (fun R => (hfin (R - 1)).subset fun b hb => by
      simp only [Set.mem_ofPred_eq] at hb ⊢; linarith)
    (add_nonneg hc hd) (fun b => ?_) ht a
  have h : J.drift (fun b => V b + 1) b = J.drift V b := by
    simp only [drift]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  have := mul_nonneg hd (hV b)
  nlinarith [hdrift b]

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The drift of a linear count observable under stochastic mass action. -/
theorem jumpSystem_drift_linear (N : Network S) (κ : RateConstants N) (w : S → ℝ)
    (n : S → ℕ) :
    (N.jumpSystem κ).drift (linearObservable w) n =
      ∑ r, N.stochasticMassActionRate κ n r * ∑ s, w s * N.reactionVector r s := by
  show ∑ r : N.R, N.stochasticMassActionRate κ n r *
      (linearObservable w (N.jumpNextCount n r) - linearObservable w n) = _
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · congr 1
    unfold linearObservable jumpNextCount
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [reactionVector_apply, Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen, zero_mul, zero_mul]

/-- A reaction with at most one reactant molecule has propensity at most `κ_r (1 + ∑_s n_s)`. -/
theorem stochasticMassActionRate_le_of_molecularity (N : Network S) (κ : RateConstants N)
    (r : N.R) (hr : ∑ s, (N.reaction r).source s ≤ 1) (n : S → ℕ) :
    N.stochasticMassActionRate κ n r ≤ κ.k r * (1 + ∑ s, (n s : ℝ)) := by
  unfold stochasticMassActionRate
  refine mul_le_mul_of_nonneg_left ?_ (κ.positive r).le
  have hsum_nn : 0 ≤ ∑ s, (n s : ℝ) := Finset.sum_nonneg fun s _ => Nat.cast_nonneg _
  by_cases hz : ∀ s, (N.reaction r).source s = 0
  · simp only [hz, Nat.descFactorial_zero, Nat.cast_one, Finset.prod_const_one]
    linarith
  · obtain ⟨s₀, hs₀⟩ := not_forall.mp hz
    have hle : ∀ s, s ≠ s₀ → (N.reaction r).source s = 0 := by
      intro s hs
      by_contra h
      have h2 : (N.reaction r).source s₀ + (N.reaction r).source s ≤
          ∑ s, (N.reaction r).source s := by
        rw [← Finset.sum_pair (Ne.symm hs)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          Nat.zero_le _
      omega
    have h1 : (N.reaction r).source s₀ = 1 := by
      have : (N.reaction r).source s₀ ≤ ∑ s, (N.reaction r).source s :=
        Finset.single_le_sum (f := fun s => (N.reaction r).source s) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ s₀)
      omega
    rw [Finset.prod_eq_single s₀ (fun s _ hs => by rw [hle s hs]; simp) (by simp), h1,
      Nat.descFactorial_one]
    have : (n s₀ : ℝ) ≤ ∑ s, (n s : ℝ) :=
      Finset.single_le_sum (f := fun s => (n s : ℝ)) (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ s₀)
    linarith

/-- Sublevel sets of a positive linear observable are finite. -/
theorem finite_linearObservable_le (w : S → ℝ) (hw : ∀ s, 0 < w s) (R : ℝ) :
    {n : S → ℕ | linearObservable w n ≤ R}.Finite := by
  refine (Fintype.piFinset fun s => Finset.range (⌊R / w s⌋₊ + 1)).finite_toSet.subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro s
  rw [Finset.mem_range]
  have hterm : w s * (n s : ℝ) ≤ linearObservable w n :=
    Finset.single_le_sum (f := fun s => w s * (n s : ℝ))
      (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
  have : (n s : ℝ) ≤ R / w s := by
    rw [le_div_iff₀ (hw s)]; linarith
  exact Nat.lt_succ_of_le (Nat.le_floor this)

/-- **Non-explosion of stochastic mass-action kinetics.** If some positive linear weight `w` is
increased only by reactions with at most one reactant molecule, the minimal transition function
is stochastic from every initial count. (Conservative networks are the case where no reaction
changes `w`.) -/
theorem hasSum_transition_one_of_weight (N : Network S) (κ : RateConstants N) (w : S → ℝ)
    (hw : ∀ s, 0 < w s)
    (hmol : ∀ r, 0 < ∑ s, w s * N.reactionVector r s → ∑ s, (N.reaction r).source s ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) : HasSum (fun m => N.transition κ t n m) 1 := by
  set A : ℝ := ∑ r, κ.k r * max (∑ s, w s * N.reactionVector r s) 0 with hA
  set W : ℝ := ∑ s, (w s)⁻¹ with hW
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun r _ =>
    mul_nonneg (κ.positive r).le (le_max_right _ _)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => (inv_pos.mpr (hw s)).le
  have hV : ∀ m, 0 ≤ linearObservable w m := fun m =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)
  -- `∑_s m_s ≤ W · V(m)`
  have hcount : ∀ m : S → ℕ, ∑ s, (m s : ℝ) ≤ W * linearObservable w m := by
    intro m
    rw [hW, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    have hterm : w s * (m s : ℝ) ≤ linearObservable w m :=
      Finset.single_le_sum (f := fun s => w s * (m s : ℝ))
        (fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    rw [← div_eq_inv_mul, le_div_iff₀ (hw s)]
    linarith
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable w) hV
    (finite_linearObservable_le w hw) (mul_nonneg hA0 hW0) hA0 (fun m => ?_) ht n
  rw [jumpSystem_drift_linear]
  have hterm : ∀ r, N.stochasticMassActionRate κ m r * ∑ s, w s * N.reactionVector r s ≤
      κ.k r * max (∑ s, w s * N.reactionVector r s) 0 * (1 + ∑ s, (m s : ℝ)) := by
    intro r
    have hlam := N.stochasticMassActionRate_nonneg κ m r
    by_cases hpos : 0 < ∑ s, w s * N.reactionVector r s
    · rw [max_eq_left hpos.le]
      have := N.stochasticMassActionRate_le_of_molecularity κ r (hmol r hpos) m
      nlinarith
    · replace hpos := not_lt.mp hpos
      rw [max_eq_right hpos]
      have : 0 ≤ 1 + ∑ s, (m s : ℝ) :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun s _ => Nat.cast_nonneg _)
      nlinarith
  calc ∑ r, N.stochasticMassActionRate κ m r * ∑ s, w s * N.reactionVector r s
      ≤ ∑ r, κ.k r * max (∑ s, w s * N.reactionVector r s) 0 * (1 + ∑ s, (m s : ℝ)) :=
        Finset.sum_le_sum fun r _ => hterm r
    _ = A * (1 + ∑ s, (m s : ℝ)) := by rw [hA, Finset.sum_mul]
    _ ≤ A * (1 + W * linearObservable w m) :=
        mul_le_mul_of_nonneg_left (by linarith [hcount m]) hA0
    _ = A * W * linearObservable w m + A := by ring

end Network

end CRNT
