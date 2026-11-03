import CRNT.Stochastic.MinimalSemigroupDynkin
import CRNT.Stochastic.MinimalSemigroupErgodicInfinite

/-!
# Existence of an invariant law from a Lyapunov drift (Krylov–Bogoliubov) and the
# Foster–Lyapunov ergodic theorem

On a countable state space, let `V ≥ 0`, `f ≥ 0` with finite sublevel sets, `K ≥ 0`, and
`QV ≤ −f + K`, and assume the chain does not explode. Then:

* the time averages `μ_T(b) = T⁻¹ ∫₀ᵀ P(t)(a, b) dt` charge `{f ≤ R}` by at least
  `1 − (V(a)/T + K)/R` (`sum_timeAvg_ge`);
* a pointwise limit `π` of a subsequence of `μ_{n+1}` (compactness of `[0, 1]^α`) is an invariant
  probability, supported on the states reachable from `a` (`exists_invariant_of_drift`);
* with irreducibility, `P(t)(a, ·)` converges in total variation to the unique invariant
  probability for every initial state (`foster_lyapunov_ergodic`).

The invariance proof needs no exchange of sums and integrals: for a finite set `G`,
`∑_{c ∈ G} μ_T(c) P(s)(c, b) ≤ T⁻¹ ∫₀ᵀ P(t + s)(a, b) dt ≤ μ_T(b) + s/T` (Chapman–Kolmogorov),
so the limit is subinvariant, and equal total masses force invariance.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The time average of the transition probabilities over `[0, T]`. -/
noncomputable def timeAvg (a : α) (T : ℝ) (b : α) : ℝ := (∫ t in (0 : ℝ)..T, J.Pmin t a b) / T

theorem intervalIntegrable_Pmin (a b : α) {T₁ T₂ : ℝ} (h₁ : 0 ≤ T₁) (h₂ : 0 ≤ T₂) :
    IntervalIntegrable (fun t => J.Pmin t a b) volume T₁ T₂ :=
  ((J.continuousOn_Pmin a b).mono fun t ht => by
    rcases le_total T₁ T₂ with h | h
    · rw [uIcc_of_le h] at ht; exact h₁.trans ht.1
    · rw [uIcc_of_ge h] at ht; exact h₂.trans ht.1).intervalIntegrable

theorem integral_Pmin_nonneg (a b : α) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ∫ t in (0 : ℝ)..T, J.Pmin t a b :=
  intervalIntegral.integral_nonneg hT fun t ht => J.Pmin_nonneg t ht.1 a b

theorem integral_Pmin_le (a b : α) {T₁ T₂ : ℝ} (h₁ : 0 ≤ T₁) (h : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, J.Pmin t a b ≤ T₂ - T₁ := by
  have := intervalIntegral.integral_mono_on (f := fun t => J.Pmin t a b) (g := fun _ => (1 : ℝ))
    h (J.intervalIntegrable_Pmin a b h₁ (h₁.trans h)) intervalIntegrable_const
    fun t ht => J.Pmin_le_one t (h₁.trans ht.1) a b
  simpa using this

theorem timeAvg_nonneg (a b : α) {T : ℝ} (hT : 0 < T) : 0 ≤ J.timeAvg a T b :=
  div_nonneg (J.integral_Pmin_nonneg a b hT.le) hT.le

theorem timeAvg_le_one (a b : α) {T : ℝ} (hT : 0 < T) : J.timeAvg a T b ≤ 1 := by
  rw [timeAvg, div_le_one hT]
  simpa using J.integral_Pmin_le a b le_rfl hT.le

theorem sum_integral_Pmin (a : α) {T : ℝ} (hT : 0 ≤ T) (F : Finset α) :
    ∑ b ∈ F, ∫ t in (0 : ℝ)..T, J.Pmin t a b = ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b :=
  (intervalIntegral.integral_finsetSum fun b _ => J.intervalIntegrable_Pmin a b le_rfl hT).symm

theorem sum_timeAvg_le_one (a : α) {T : ℝ} (hT : 0 < T) (F : Finset α) :
    ∑ b ∈ F, J.timeAvg a T b ≤ 1 := by
  simp only [timeAvg, ← Finset.sum_div]
  rw [div_le_one hT, J.sum_integral_Pmin a hT.le]
  have := intervalIntegral.integral_mono_on (f := fun t => ∑ b ∈ F, J.Pmin t a b)
    (g := fun _ => (1 : ℝ)) hT.le
    (by rw [← (show (∑ b ∈ F, fun t => J.Pmin t a b) = fun t => ∑ b ∈ F, J.Pmin t a b from by
          funext t; simp)]
        exact IntervalIntegrable.sum F fun b _ => J.intervalIntegrable_Pmin a b le_rfl hT.le)
    intervalIntegrable_const fun t ht => J.sum_Pmin_le_one t ht.1 a F
  simpa using this

/-- **Shift bound** for time averages. -/
theorem integral_Pmin_add_le (a b : α) {T s : ℝ} (hT : 0 ≤ T) (hs : 0 ≤ s) :
    ∫ t in (0 : ℝ)..T, J.Pmin (t + s) a b ≤ (∫ t in (0 : ℝ)..T, J.Pmin t a b) + s := by
  rw [intervalIntegral.integral_comp_add_right (fun t => J.Pmin t a b) s, zero_add]
  show ∫ x in s..T + s, J.Pmin x a b ≤ _
  have hTs : 0 ≤ T + s := by linarith
  have h1 := intervalIntegral.integral_interval_sub_left
    (J.intervalIntegrable_Pmin a b (T₂ := T + s) le_rfl hTs)
    (J.intervalIntegrable_Pmin a b (T₂ := s) le_rfl hs)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (J.intervalIntegrable_Pmin a b (T₂ := T) le_rfl hT)
    (J.intervalIntegrable_Pmin a b (T₁ := T) (T₂ := T + s) hT hTs)
  have h3 := J.integral_Pmin_le a b hT (show T ≤ T + s by linarith)
  have h4 := J.integral_Pmin_nonneg a b hs
  linarith

/-- **Tightness of time averages** under `QV ≤ −f + K`, without explosion. -/
theorem sum_timeAvg_ge [Countable α] (V f : α → ℝ) (hV : ∀ x, 0 ≤ V x) (hf : ∀ x, 0 ≤ f x)
    {K : ℝ} (hK : 0 ≤ K) (hdrift : ∀ x, J.drift V x ≤ -f x + K) (a : α)
    (hstoch : ∀ t, 0 ≤ t → HasSum (fun b => J.Pmin t a b) 1) {T : ℝ} (hT : 0 < T) {R : ℝ}
    (hR : 0 < R) (F : Finset α) (hF : ∀ b, b ∉ F → R ≤ f b) :
    1 - (V a / T + K) / R ≤ ∑ b ∈ F, J.timeAvg a T b := by
  have : Nonempty α := ⟨a⟩
  obtain ⟨e, he⟩ := exists_surjective_nat α
  let G : ℕ → Finset α := fun m => (Finset.range m).image e ∪ F
  have hGmono : Monotone G := fun m m' h => Finset.union_subset_union
    (Finset.image_subset_image (Finset.range_subset_range.mpr h)) le_rfl
  have hGtop : Tendsto G atTop atTop := tendsto_atTop_finset_of_monotone hGmono fun x => by
    obtain ⟨m, rfl⟩ := he x
    exact ⟨m + 1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp))⟩
  have hbound : ∀ m, ∫ t in (0 : ℝ)..T, ∑ b ∈ G m, J.Pmin t a b ≤
      (∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b) + (V a + K * T) / R := by
    intro m
    have hsub : F ⊆ G m := Finset.subset_union_right
    have hsplit : ∀ t, ∑ b ∈ G m, J.Pmin t a b =
        ∑ b ∈ G m \ F, J.Pmin t a b + ∑ b ∈ F, J.Pmin t a b := fun t =>
      (Finset.sum_sdiff hsub).symm
    simp only [hsplit]
    have hi1 : IntervalIntegrable (fun t => ∑ b ∈ G m \ F, J.Pmin t a b) volume 0 T := by
      rw [← (show (∑ b ∈ G m \ F, fun t => J.Pmin t a b) = fun t => ∑ b ∈ G m \ F, J.Pmin t a b
        from by funext t; simp)]
      exact IntervalIntegrable.sum _ fun b _ => J.intervalIntegrable_Pmin a b le_rfl hT.le
    have hi2 : IntervalIntegrable (fun t => ∑ b ∈ F, J.Pmin t a b) volume 0 T := by
      rw [← (show (∑ b ∈ F, fun t => J.Pmin t a b) = fun t => ∑ b ∈ F, J.Pmin t a b
        from by funext t; simp)]
      exact IntervalIntegrable.sum _ fun b _ => J.intervalIntegrable_Pmin a b le_rfl hT.le
    rw [intervalIntegral.integral_add hi1 hi2]
    have := J.integral_sum_Pmin_le_of_ge V f hV hf hK hdrift hT.le a hR (G m \ F)
      fun b hb => hF b (Finset.mem_sdiff.mp hb).2
    linarith
  have hlim : Tendsto (fun m => ∫ t in (0 : ℝ)..T, ∑ b ∈ G m, J.Pmin t a b) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, (1 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun m => ?_) ?_ intervalIntegrable_const ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine (continuousOn_finsetSum _ fun b _ => J.continuousOn_Pmin a b).mono ?_
      rw [uIoc_of_le hT.le]
      exact fun t ht => le_of_lt ht.1
    · refine Eventually.of_forall fun m => Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le hT.le] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun b _ =>
        J.Pmin_nonneg t ht.1.le a b)]
      exact J.sum_Pmin_le_one t ht.1.le a _
    · refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le hT.le] at ht
      exact (hstoch t ht.1.le).comp hGtop
  have hle := le_of_tendsto' hlim hbound
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hle
  simp only [timeAvg, ← Finset.sum_div]
  rw [J.sum_integral_Pmin a hT.le]
  rw [le_div_iff₀ hT]
  have : (V a / T + K) / R * T = (V a + K * T) / R := by field_simp
  nlinarith

/-- **Krylov–Bogoliubov.** Under `QV ≤ −f + K` with `f` having finite sublevel sets and no
explosion, a subsequential limit of the time averages from `a` is an invariant probability,
supported on the states reachable from `a`. -/
theorem exists_invariant_of_drift [Countable α] (V f : α → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hf : ∀ x, 0 ≤ f x) (hfin : ∀ R : ℝ, {x | f x ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    (hdrift : ∀ x, J.drift V x ≤ -f x + K)
    (hstoch : ∀ t, 0 ≤ t → ∀ c, HasSum (fun b => J.Pmin t c b) 1) (a : α) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b) ∧
      ∀ b, ¬ J.ReachPos a b → π b = 0 := by
  classical
  let x : ℕ → α → ℝ := fun n b => J.timeAvg a ((n : ℝ) + 1) b
  have hTpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hxs : ∀ n, x n ∈ Set.pi Set.univ (fun _ : α => Set.Icc (0 : ℝ) 1) := fun n b _ =>
    ⟨J.timeAvg_nonneg a b (hTpos n), J.timeAvg_le_one a b (hTpos n)⟩
  obtain ⟨π, hπmem, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hxs
  have hpt : ∀ b, Tendsto (fun k => x (φ k) b) atTop (𝓝 (π b)) := fun b =>
    (tendsto_pi_nhds.mp hlim) b
  have hπ0 : ∀ b, 0 ≤ π b := fun b => (hπmem b (Set.mem_univ b)).1
  have hφT : Tendsto (fun k => ((φ k : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hsum1 : ∀ F : Finset α, ∑ b ∈ F, π b ≤ 1 := fun F =>
    le_of_tendsto' (tendsto_finsetSum _ fun b _ => hpt b) fun k =>
      J.sum_timeAvg_le_one a (hTpos _) F
  have hπs : Summable π := summable_of_sum_le (c := 1) hπ0 hsum1
  have hmass : ∀ R : ℝ, 0 < R → 1 - K / R ≤ ∑ b ∈ (hfin R).toFinset, π b := by
    intro R hR
    have hF : ∀ b, b ∉ (hfin R).toFinset → R ≤ f b := fun b hb => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hb
      exact (not_le.mp hb).le
    have hlow : Tendsto (fun k => 1 - (V a / (((φ k : ℕ) : ℝ) + 1) + K) / R) atTop
        (𝓝 (1 - (0 + K) / R)) :=
      tendsto_const_nhds.sub (((tendsto_const_nhds.div_atTop hφT).add
        tendsto_const_nhds).div_const R)
    rw [zero_add] at hlow
    exact le_of_tendsto_of_tendsto' hlow (tendsto_finsetSum _ fun b _ => hpt b)
      fun k => J.sum_timeAvg_ge V f hV hf hK hdrift a (fun t ht => hstoch t ht a) (hTpos _) hR _ hF
  have hone : HasSum π 1 := by
    refine hπs.hasSum_iff.mpr (le_antisymm (hπs.tsum_le_of_sum_le hsum1) ?_)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hR : 0 < K / ε + 1 := by positivity
    have h := hmass (K / ε + 1) hR
    have h2 := hπs.sum_le_tsum ((hfin (K / ε + 1)).toFinset) fun b _ => hπ0 b
    have h3 : K / (K / ε + 1) < ε := by
      rw [div_lt_iff₀ hR]
      have : ε * (K / ε) = K := by field_simp
      nlinarith
    linarith
  -- subinvariance
  have hsubinv : ∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b ≤ π b := by
    intro s hs b
    have hcs : Summable fun c => π c * J.Pmin s c b :=
      Summable.of_nonneg_of_le (fun c => mul_nonneg (hπ0 c) (J.Pmin_nonneg s hs c b))
        (fun c => mul_le_of_le_one_right (hπ0 c) (J.Pmin_le_one s hs c b)) hπs
    refine hcs.tsum_le_of_sum_le fun G => ?_
    have hk : ∀ k, ∑ c ∈ G, x (φ k) c * J.Pmin s c b ≤
        x (φ k) b + s / (((φ k : ℕ) : ℝ) + 1) := by
      intro k
      have hT := hTpos (φ k)
      set T := ((φ k : ℕ) : ℝ) + 1 with hTdef
      show ∑ c ∈ G, (∫ t in (0 : ℝ)..T, J.Pmin t a c) / T * J.Pmin s c b ≤
        (∫ t in (0 : ℝ)..T, J.Pmin t a b) / T + s / T
      have e1 : ∑ c ∈ G, (∫ t in (0 : ℝ)..T, J.Pmin t a c) / T * J.Pmin s c b =
          (∫ t in (0 : ℝ)..T, ∑ c ∈ G, J.Pmin t a c * J.Pmin s c b) / T := by
        rw [intervalIntegral.integral_finsetSum fun c _ =>
          (J.intervalIntegrable_Pmin a c le_rfl hT.le).mul_const _, Finset.sum_div]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [intervalIntegral.integral_mul_const]; ring
      rw [e1, ← add_div, div_le_div_iff_of_pos_right hT]
      have hi1 : IntervalIntegrable (fun t => ∑ c ∈ G, J.Pmin t a c * J.Pmin s c b) volume 0 T := by
        refine ContinuousOn.intervalIntegrable ?_
        refine (continuousOn_finsetSum _ fun c _ => (J.continuousOn_Pmin a c).mul
          continuousOn_const).mono ?_
        rw [uIcc_of_le hT.le]; exact Icc_subset_Ici_self
      have hi2 : IntervalIntegrable (fun t => J.Pmin (t + s) a b) volume 0 T := by
        refine ContinuousOn.intervalIntegrable ?_
        refine (J.continuousOn_Pmin a b).comp (continuous_id.add continuous_const).continuousOn
          fun t ht => ?_
        rw [uIcc_of_le hT.le] at ht
        show (0 : ℝ) ≤ t + s
        linarith [ht.1]
      calc ∫ t in (0 : ℝ)..T, ∑ c ∈ G, J.Pmin t a c * J.Pmin s c b
          ≤ ∫ t in (0 : ℝ)..T, J.Pmin (t + s) a b :=
            intervalIntegral.integral_mono_on hT.le hi1 hi2 fun t ht =>
              sum_le_hasSum G (fun c _ => mul_nonneg (J.Pmin_nonneg t ht.1 a c)
                (J.Pmin_nonneg s hs c b)) (J.hasSum_Pmin_add ht.1 hs a b)
        _ ≤ (∫ t in (0 : ℝ)..T, J.Pmin t a b) + s := J.integral_Pmin_add_le a b hT.le hs
    have hlimL : Tendsto (fun k => ∑ c ∈ G, x (φ k) c * J.Pmin s c b) atTop
        (𝓝 (∑ c ∈ G, π c * J.Pmin s c b)) :=
      tendsto_finsetSum _ fun c _ => (hpt c).mul_const _
    have hlimR : Tendsto (fun k => x (φ k) b + s / (((φ k : ℕ) : ℝ) + 1)) atTop (𝓝 (π b + 0)) :=
      (hpt b).add (tendsto_const_nhds.div_atTop hφT)
    rw [add_zero] at hlimR
    exact le_of_tendsto_of_tendsto' hlimL hlimR hk
  refine ⟨π, hπ0, hone, fun s hs => ?_, fun b hb => ?_⟩
  · -- equal total masses force invariance
    let H : α → α → ℝ := fun c b => π c * J.Pmin s c b
    have hH0 : ∀ c b, 0 ≤ H c b := fun c b => mul_nonneg (hπ0 c) (J.Pmin_nonneg s hs c b)
    have hHrow : ∀ c, HasSum (H c) (π c) := fun c => by
      simpa [H] using (hstoch s hs c).mul_left (π c)
    have hHsum : Summable (Function.uncurry H) := by
      refine (summable_prod_of_nonneg fun p => hH0 p.1 p.2).mpr ⟨fun c => (hHrow c).summable, ?_⟩
      simp only [Function.uncurry]
      exact hπs.congr fun c => ((hHrow c).tsum_eq).symm
    have hgsum : Summable fun b => ∑' c, H c b := hHsum.prod_symm.prod
    have htot : ∑' b, ∑' c, H c b = 1 := by
      rw [hHsum.tsum_comm]
      rw [show (fun c => ∑' b, H c b) = π from funext fun c => (hHrow c).tsum_eq]
      exact hone.tsum_eq
    intro b
    by_contra hne
    have hlt : ∑' c, H c b < π b := lt_of_le_of_ne (hsubinv s hs b) hne
    have := Summable.tsum_lt_tsum (fun b' => hsubinv s hs b') hlt hgsum hπs
    rw [htot, hone.tsum_eq] at this
    exact lt_irrefl _ this
  · have h0 : ∀ k, x (φ k) b = 0 := fun k => by
      show (∫ t in (0 : ℝ)..((φ k : ℕ) : ℝ) + 1, J.Pmin t a b) / (((φ k : ℕ) : ℝ) + 1) = 0
      simp [J.Pmin_eq_zero_of_not_reachPos _ hb]
    exact tendsto_nhds_unique (hpt b) (by simp only [h0]; exact tendsto_const_nhds)

/-- **Foster–Lyapunov ergodic theorem** on a closed irreducible class: under `QV ≤ −f + K` with
`f` having finite sublevel sets and no explosion, there is a unique invariant probability on the
class, it charges every state of the class, and from every state of the class the law of the chain
converges to it in total variation. -/
theorem foster_lyapunov_ergodic [Countable α] (V f : α → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hf : ∀ x, 0 ≤ f x) (hfin : ∀ R : ℝ, {x | f x ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    (hdrift : ∀ x, J.drift V x ≤ -f x + K)
    (hstoch : ∀ t, 0 ≤ t → ∀ c, HasSum (fun b => J.Pmin t c b) 1) {E : Set α}
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b) {a₀ : α} (ha₀ : a₀ ∈ E) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b) ∧ (∀ b, b ∉ E → π b = 0) ∧
      (∀ b ∈ E, 0 < π b) ∧
      (∀ a ∈ E, Tendsto (fun t => ∑' b, |J.Pmin t a b - π b|) atTop (𝓝 0)) ∧
      ∀ μ : α → ℝ, (∀ b, 0 ≤ μ b) → (∀ b, b ∉ E → μ b = 0) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' c, μ c * J.Pmin s c b = μ b) → μ = π := by
  obtain ⟨π, hπ0, hπ1, hinv, hsupp⟩ :=
    J.exists_invariant_of_drift V f hV hf hfin hK hdrift hstoch a₀
  have hmemE : ∀ {x c}, x ∈ E → J.ReachPos x c → c ∈ E := by
    intro x c hx h
    induction h with
    | refl => exact hx
    | tail _ hcd ih => obtain ⟨i, hr, rfl⟩ := hcd; exact hE _ ih i hr
  have hπE : ∀ b, b ∉ E → π b = 0 := fun b hb => hsupp b fun h => hb (hmemE ha₀ h)
  have hst : ∀ t, 0 ≤ t → ∀ a ∈ E, HasSum (fun b => J.Pmin t a b) 1 := fun t ht a _ =>
    hstoch t ht a
  have hpos : ∀ b ∈ E, 0 < π b := fun b hb => J.invariant_pos hirr hπ0 hπE hπ1 hinv hb
  refine ⟨π, hπ0, hπ1, hinv, hπE, hpos, fun a ha => ?_, fun μ hμ0 hμE hμ1 hμinv => ?_⟩
  · exact J.tendsto_l1_of_invariant hE hirr hst hπ0 hπE hπ1 hinv ha (hpos a ha)
  · funext b
    exact J.invariant_unique hE hirr hst hπ0 hπE hπ1 hinv hμ0 hμE hμ1 hμinv b

end JumpSystem

end CRNT
