import CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov

/-!
# Uniform moment bounds and convergence in `f`-norm

Under the exponential drift `QV ≤ −cV + K` (`c > 0`, `K ≥ 0`, `V ≥ 0`),

`∑_b P(t)(a, b) V(b) ≤ e^{−ct} V(a) + (K/c)(1 − e^{−ct})`

on every finite set of states (`wmass_le_contract`, `sum_Pmin_mul_le_contract`); the computation is
exact by `(q − c) ∫₀ᵗ e^{−qs} e^{−c(t−s)} ds = e^{−ct} − e^{−qt}` (`mul_integral_exp_exp`).
With the Foster–Lyapunov ergodic theorem this gives convergence in `f`-norm for every
`f ≥ 0` with `f = o(V)` (`tendsto_fnorm_of_drift`, Meyn–Tweedie).
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

theorem mul_integral_exp_exp (q c t : ℝ) :
    (q - c) * ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * Real.exp (-(c * (t - s))) =
      Real.exp (-(c * t)) - Real.exp (-(q * t)) := by
  have h1 : ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * Real.exp (-(c * (t - s))) =
      Real.exp (-(c * t)) * ∫ s in (0 : ℝ)..t, Real.exp (-((q - c) * s)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h2 := JumpSystem.integral_exp_decay (q - c) t
  rw [intervalIntegral.integral_const_mul] at h2
  rw [h1, ← mul_assoc, mul_comm (q - c), mul_assoc, h2, mul_sub, mul_one, ← Real.exp_add]
  ring_nf

theorem integral_exp_exp_le {q c t : ℝ} (hq : 0 ≤ q) (hc : 0 < c) (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * Real.exp (-(c * (t - s))) ≤
      (1 - Real.exp (-(c * t))) / c := by
  have h0 := mul_integral_exp_exp 0 c t
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, zero_sub] at h0
  have hmono : ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) * Real.exp (-(c * (t - s))) ≤
      ∫ s in (0 : ℝ)..t, Real.exp (-(c * (t - s))) :=
    intervalIntegral.integral_mono_on ht (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) fun s hs =>
        mul_le_of_le_one_left (Real.exp_pos _).le
          (Real.exp_le_one_iff.mpr (by nlinarith [hs.1]))
  rw [le_div_iff₀ hc]
  nlinarith

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Contractive moment bound with `k` jumps.** -/
theorem wmass_le_contract (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hdrift : ∀ a, J.drift V a ≤ -c * V a + K) (k : ℕ) :
    ∀ t, 0 ≤ t → ∀ a, J.wmass V k t a ≤
      Real.exp (-(c * t)) * V a + K / c * (1 - Real.exp (-(c * t))) := by
  have hW : ∀ a, 0 ≤ (J.q a - c) * V a + K := by
    intro a
    have h1 := J.sum_rate_mul_next V a
    have h2 : 0 ≤ ∑ i, J.rate i a * V (J.next i a) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i a) (hV _)
    linarith [hdrift a]
  have hsumV : ∀ a, ∑ i, J.rate i a * V (J.next i a) ≤ (J.q a - c) * V a + K := by
    intro a; rw [J.sum_rate_mul_next]; linarith [hdrift a]
  induction k with
  | zero =>
      intro t ht a
      rw [wmass_zero]
      have hA := mul_integral_exp_exp (J.q a) c t
      have hAle := integral_exp_exp_le (J.q_nonneg a) hc ht
      have hA0 : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * Real.exp (-(c * (t - s))) :=
        intervalIntegral.integral_nonneg ht fun s _ => by positivity
      set A := ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * Real.exp (-(c * (t - s)))
      have h1 : (J.q a - c) * A * V a = (Real.exp (-(c * t)) - Real.exp (-(J.q a * t))) * V a := by
        rw [hA]
      have h2 := mul_le_mul_of_nonneg_right (hW a) hA0
      have h3 : K * A ≤ K * ((1 - Real.exp (-(c * t))) / c) := mul_le_mul_of_nonneg_left hAle hK
      have h4 : K * ((1 - Real.exp (-(c * t))) / c) = K / c * (1 - Real.exp (-(c * t))) := by ring
      nlinarith
  | succ k ih =>
      intro t ht a
      rw [wmass_succ]
      set q := J.q a
      set e := fun s => Real.exp (-(q * s)) * Real.exp (-(c * (t - s))) with he
      have hbound : ∀ s ∈ Icc (0 : ℝ) t, Real.exp (-(q * s)) *
          ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a) ≤
          e s * ((q - c) * V a + K) + K / c * q * Real.exp (-(q * s)) - K / c * q * e s := by
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        have hφ : 0 ≤ Real.exp (-(q * s)) := (Real.exp_pos _).le
        have hin : ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a) ≤
            Real.exp (-(c * (t - s))) * ((q - c) * V a + K) +
              K / c * (1 - Real.exp (-(c * (t - s)))) * q := by
          calc ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a)
              ≤ ∑ i, J.rate i a * (Real.exp (-(c * (t - s))) * V (J.next i a) +
                  K / c * (1 - Real.exp (-(c * (t - s))))) :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (ih (t - s) hts _) (J.rate_nonneg i a)
            _ = Real.exp (-(c * (t - s))) * ∑ i, J.rate i a * V (J.next i a) +
                  K / c * (1 - Real.exp (-(c * (t - s)))) * q := by
                simp only [mul_add, Finset.sum_add_distrib, q, JumpSystem.q, Finset.mul_sum,
                  Finset.sum_mul]
                congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
            _ ≤ _ := by
                have := mul_le_mul_of_nonneg_left (hsumV a)
                  (Real.exp_pos (-(c * (t - s)))).le
                linarith
        have := mul_le_mul_of_nonneg_left hin hφ
        simp only [he]
        nlinarith
      have hec : Continuous e := by simp only [he]; fun_prop
      have hf : IntervalIntegrable (fun s => Real.exp (-(q * s)) *
          ∑ i, J.rate i a * J.wmass V k (t - s) (J.next i a)) volume 0 t := by
        apply Continuous.intervalIntegrable
        refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
        exact continuous_const.mul
          ((J.continuous_wmass V k _).comp (continuous_const.sub continuous_id))
      have hg1 : IntervalIntegrable (fun s => e s * ((q - c) * V a + K)) volume 0 t :=
        (hec.mul continuous_const).intervalIntegrable 0 t
      have hg2 : IntervalIntegrable (fun s => K / c * q * Real.exp (-(q * s))) volume 0 t := by
        apply Continuous.intervalIntegrable; fun_prop
      have hg3 : IntervalIntegrable (fun s => K / c * q * e s) volume 0 t :=
        (continuous_const.mul hec).intervalIntegrable 0 t
      have hmono := intervalIntegral.integral_mono_on ht hf ((hg1.add hg2).sub hg3) hbound
      rw [intervalIntegral.integral_sub (hg1.add hg2) hg3, intervalIntegral.integral_add hg1 hg2,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hmono
      have hA := mul_integral_exp_exp q c t
      have hqI : q * ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) = 1 - Real.exp (-(q * t)) := by
        rw [← intervalIntegral.integral_const_mul]; exact integral_exp_decay q t
      set A := ∫ s in (0 : ℝ)..t, e s with hAdef
      have h1 : (q - c) * A * V a = (Real.exp (-(c * t)) - Real.exp (-(q * t))) * V a := by rw [hA]
      have h2 : K / c * q * A - K * A = K / c * (Real.exp (-(c * t)) - Real.exp (-(q * t))) := by
        rw [← hA]; field_simp
      have h3 : K / c * q * ∫ s in (0 : ℝ)..t, Real.exp (-(q * s)) =
          K / c * (1 - Real.exp (-(q * t))) := by rw [mul_assoc, hqI]
      nlinarith [hmono, h1, h2, h3]

/-- The contractive moment bound for the minimal transition function. -/
theorem sum_Pmin_mul_le_contract (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) {c K : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) (hdrift : ∀ a, J.drift V a ≤ -c * V a + K) {t : ℝ} (ht : 0 ≤ t) (a : α)
    (F : Finset α) :
    ∑ b ∈ F, J.Pmin t a b * V b ≤ Real.exp (-(c * t)) * V a + K / c * (1 - Real.exp (-(c * t))) := by
  have hlim : Tendsto (fun k => ∑ b ∈ F, J.P k t a b * V b) atTop
      (𝓝 (∑ b ∈ F, J.Pmin t a b * V b)) :=
    tendsto_finsetSum _ fun b _ => (J.tendsto_P t ht a b).mul_const _
  refine le_of_tendsto' hlim fun k => ?_
  calc ∑ b ∈ F, J.P k t a b * V b ≤ ∑ b ∈ F ∪ J.reachK k a, J.P k t a b * V b :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
          mul_nonneg (J.P_nonneg k t ht a b) (hV b)
    _ = J.wmass V k t a := J.sum_P_mul_eq_wmass_of_subset V k t a Finset.subset_union_right
    _ ≤ _ := J.wmass_le_contract V hV hc hK hdrift k t ht a

/-- **Convergence in `f`-norm** (Meyn–Tweedie) under the exponential drift `QV ≤ −cV + K`, for
every `f ≥ 0` with `f = o(V)`, on a closed irreducible class. -/
theorem tendsto_fnorm_of_drift [Countable α] (V : α → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hfinV : ∀ R : ℝ, {x | V x ≤ R}.Finite) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hdrift : ∀ x, J.drift V x ≤ -c * V x + K)
    (hstoch : ∀ t, 0 ≤ t → ∀ x, HasSum (fun b => J.Pmin t x b) 1) {E : Set α}
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b) {a₀ : α} (ha₀ : a₀ ∈ E) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * J.Pmin s x b = π b) ∧ (∀ b, b ∉ E → π b = 0) ∧
      ∀ f : α → ℝ, (∀ b, 0 ≤ f b) → (∀ ε, 0 < ε → ∃ R, ∀ b, R < V b → f b ≤ ε * V b) →
        ∀ a ∈ E, Tendsto (fun t => ∑' b, |J.Pmin t a b - π b| * f b) atTop (𝓝 0) := by
  classical
  have hdr : ∀ x, J.drift V x ≤ -(c * V x) + K := fun x => by linarith [hdrift x]
  have hfin' : ∀ R : ℝ, {x | c * V x ≤ R}.Finite := fun R =>
    (hfinV (R / c)).subset fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [le_div_iff₀ hc]; linarith
  obtain ⟨π, hπ0, hπ1, hinv, hπE, -, hconv, -⟩ := J.foster_lyapunov_ergodic V (fun x => c * V x)
    hV (fun x => mul_nonneg hc.le (hV x)) hfin' hK hdr hstoch hE hirr ha₀
  have hst : ∀ t, 0 ≤ t → ∀ a ∈ E, HasSum (fun b => J.Pmin t a b) 1 := fun t ht a _ =>
    hstoch t ht a
  refine ⟨π, hπ0, hπ1, hinv, hπE, fun f hf0 hfo a ha => ?_⟩
  set B : ℝ := V a + K / c with hB
  have hB0 : 0 ≤ B := add_nonneg (hV a) (div_nonneg hK hc.le)
  have hmomP : ∀ t, 0 ≤ t → ∀ F : Finset α, ∑ b ∈ F, J.Pmin t a b * V b ≤ B := by
    intro t ht F
    have h := J.sum_Pmin_mul_le_contract V hV hc hK hdrift ht a F
    have he0 : 0 ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(c * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h1 : Real.exp (-(c * t)) * V a ≤ V a := mul_le_of_le_one_left (hV a) he1
    have h2 : K / c * (1 - Real.exp (-(c * t))) ≤ K / c :=
      mul_le_of_le_one_right (div_nonneg hK hc.le) (by linarith)
    linarith
  have hpt : ∀ b, Tendsto (fun t => J.Pmin t a b) atTop (𝓝 (π b)) := fun b =>
    J.tendsto_Pmin_of_invariant hE hirr hst hπ0 hπE hπ1 hinv ha b
  have hmomπ : ∀ F : Finset α, ∑ b ∈ F, π b * V b ≤ B := fun F =>
    le_of_tendsto (tendsto_finsetSum _ fun b _ => (hpt b).mul_const _)
      ((eventually_ge_atTop 0).mono fun t ht => hmomP t ht F)
  have hsPV : ∀ t, 0 ≤ t → Summable fun b => J.Pmin t a b * V b := fun t ht =>
    summable_of_sum_le (fun b => mul_nonneg (J.Pmin_nonneg t ht a b) (hV b)) (hmomP t ht)
  have hsπV : Summable fun b => π b * V b :=
    summable_of_sum_le (fun b => mul_nonneg (hπ0 b) (hV b)) hmomπ
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (4 * (B + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨R, hR⟩ := hfo ε' hε'0
  set F := (hfinV R).toFinset with hF
  have hmemF : ∀ b, b ∈ F ↔ V b ≤ R := fun b => by simp [hF]
  set M : ℝ := ∑ b ∈ F, f b + 1 with hM
  have hM0 : 0 < M := by have := Finset.sum_nonneg fun b (_ : b ∈ F) => hf0 b; linarith
  have hfM : ∀ b ∈ F, f b ≤ M := fun b hb => by
    have := Finset.single_le_sum (f := f) (fun b _ => hf0 b) hb; linarith
  have hfle : ∀ b, f b ≤ M + ε' * V b := fun b => by
    by_cases hb : b ∈ F
    · have := hfM b hb; have := mul_nonneg hε'0.le (hV b); linarith
    · have := hR b (not_le.mp fun h => hb ((hmemF b).mpr h)); linarith
  have hTV := Metric.tendsto_atTop.mp (hconv a ha) (ε / (2 * M)) (by positivity)
  obtain ⟨T₀, hT₀⟩ := hTV
  refine ⟨max T₀ 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  have htT : T₀ ≤ t := (le_max_left _ _).trans ht
  have hTVt := hT₀ t htT
  rw [Real.dist_eq, sub_zero] at hTVt
  set D := ∑' b, |J.Pmin t a b - π b| with hD
  have hsabs : Summable fun b => |J.Pmin t a b - π b| :=
    Summable.of_nonneg_of_le (fun b => abs_nonneg _) (fun b => (abs_sub _ _).trans (by
      rw [abs_of_nonneg (J.Pmin_nonneg t ht0 a b), abs_of_nonneg (hπ0 b)]))
      ((hstoch t ht0 a).summable.add hπ1.summable)
  have hD0 : 0 ≤ D := tsum_nonneg fun b => abs_nonneg _
  rw [abs_of_nonneg hD0] at hTVt
  -- the weighted sum
  have hbound : ∀ b, |J.Pmin t a b - π b| * f b ≤
      M * |J.Pmin t a b - π b| * (if b ∈ F then 1 else 0) +
        ε' * (J.Pmin t a b * V b + π b * V b) := by
    intro b
    have habs : |J.Pmin t a b - π b| ≤ J.Pmin t a b + π b := (abs_sub _ _).trans (by
      rw [abs_of_nonneg (J.Pmin_nonneg t ht0 a b), abs_of_nonneg (hπ0 b)])
    by_cases hb : b ∈ F
    · rw [if_pos hb, mul_one]
      have := mul_le_mul_of_nonneg_left (hfM b hb) (abs_nonneg (J.Pmin t a b - π b))
      have h2 : 0 ≤ ε' * (J.Pmin t a b * V b + π b * V b) :=
        mul_nonneg hε'0.le (add_nonneg (mul_nonneg (J.Pmin_nonneg t ht0 a b) (hV b))
          (mul_nonneg (hπ0 b) (hV b)))
      nlinarith
    · rw [if_neg hb, mul_zero, zero_add]
      have hfb := hR b (not_le.mp fun h => hb ((hmemF b).mpr h))
      calc |J.Pmin t a b - π b| * f b ≤ (J.Pmin t a b + π b) * (ε' * V b) :=
            mul_le_mul habs hfb (hf0 b) (add_nonneg (J.Pmin_nonneg t ht0 a b) (hπ0 b))
        _ = ε' * (J.Pmin t a b * V b + π b * V b) := by ring
  have hsF : Summable fun b => M * |J.Pmin t a b - π b| * (if b ∈ F then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := F) fun b hb => by rw [if_neg hb, mul_zero]
  have hsV : Summable fun b => ε' * (J.Pmin t a b * V b + π b * V b) :=
    ((hsPV t ht0).add hsπV).mul_left ε'
  have hsum : Summable fun b => |J.Pmin t a b - π b| * f b :=
    Summable.of_nonneg_of_le (fun b => mul_nonneg (abs_nonneg _) (hf0 b)) hbound (hsF.add hsV)
  have h1 : ∑' b, M * |J.Pmin t a b - π b| * (if b ∈ F then (1 : ℝ) else 0) ≤ M * D := by
    rw [tsum_eq_sum (s := F) fun b hb => by rw [if_neg hb, mul_zero]]
    calc ∑ b ∈ F, M * |J.Pmin t a b - π b| * (if b ∈ F then (1 : ℝ) else 0)
        = M * ∑ b ∈ F, |J.Pmin t a b - π b| := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b hb => by rw [if_pos hb, mul_one]
      _ ≤ M * D := mul_le_mul_of_nonneg_left
          (hsabs.sum_le_tsum F fun b _ => abs_nonneg _) hM0.le
  have h2 : ∑' b, ε' * (J.Pmin t a b * V b + π b * V b) ≤ ε' * (B + B) := by
    rw [tsum_mul_left, (hsPV t ht0).tsum_add hsπV]
    exact mul_le_mul_of_nonneg_left (add_le_add
      ((hsPV t ht0).tsum_le_of_sum_le (hmomP t ht0)) (hsπV.tsum_le_of_sum_le hmomπ)) hε'0.le
  have htot := Summable.tsum_le_tsum hbound hsum (hsF.add hsV)
  rw [(hsF.tsum_add hsV)] at htot
  have h3 : M * D < ε / 2 := by
    have := mul_lt_mul_of_pos_left hTVt hM0
    rw [show M * (ε / (2 * M)) = ε / 2 by field_simp] at this
    exact this
  have h4 : ε' * (B + B) < ε / 2 := by
    rw [hε']
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun b => mul_nonneg (abs_nonneg _) (hf0 b))]
  linarith

end JumpSystem

end CRNT
