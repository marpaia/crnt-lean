import CRNT.Stochastic.MinimalSemigroupErgodicInfinite
import CRNT.Stochastic.InvariantMoments
import CRNT.Stochastic.MinimalSemigroupFoster
import CRNT.Stochastic.MinimalSemigroupExpect
import CRNT.Stochastic.ProductFormConvergence
import CRNT.Stochastic.MonomolecularLLN

/-!
# Kac's formula for the minimal continuous-time chain

Let `J` be a jump system, `a` a state with `q(a) > 0`, and `J_a = J.stopOn {a}` the chain
absorbed at `a`.  `A(t, c) = P_a(t)(c, a)` is the probability of having hit `a` by time `t`
starting from `c`.  The return time `T_a⁺` to `a` from `a` is the holding time at `a` (mean
`1/q(a)`) plus the hitting time of `a` from the state reached by the first jump, so

`E_a T_a⁺ = 1/q(a) + (1/q(a)) ∫₀^∞ ∑_i rate_i(a) (1 − A(t, next_i a)) dt`.

**Theorem (`kac_formula`).**  On a closed irreducible class `E` on which `J` is stochastic, with
an invariant probability `π` supported on `E` such that `∑ π q < ∞`,

`1/q(a) + (1/q(a)) ∫₀^T ∑_i rate_i(a) (1 − A(t, next_i a)) dt → 1 / (π(a) q(a))`  as `T → ∞`.

In particular the expected return time is finite (positive recurrence in the return-time sense).
The integrand is the survival function of the hitting time: `1 − A(t, c) = ∑_{b ≠ a} P_a(t)(c, b)`
because the absorbed chain is stochastic whenever `J` is (`hasSum_stopOn_Pmin_one`).

Proof, without path measures.
* Comparisons with the absorbed chain, by induction over the number of jumps:
  `P(t)(c, a) ≤ A(t, c)` (`Pmin_le_stopOn`) and the absorbed chain has at least the row mass of `J`
  (`mass_le_stopOn_mass`).
* `ψ(t) = ∑_c π(c) A(t, c)` has derivative `π(a) ∑_i rate_i(a)(1 − A(t, next_i a))`: the backward
  equation of the absorbed chain, differentiation under the sum (dominated by `2 π q`), and global
  balance `∑_c π(c) Q(c, ·) = 0` (`tsum_invariant_mul_Q`).
* `A(t, c) → 1` on `E`: `A(·, c)` is nondecreasing with limit `h(c) ≥ lim P(t)(c, a) = π(a) > 0`;
  `h` is harmonic for the absorbed chain, so `1 − h(c) ≤ (1 − π(a))(1 − h(c))`, i.e. `h = 1`.
  Hence `ψ(T) → 1`, and `ψ(T) − ψ(0) = π(a) ∫₀^T …` gives the formula.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Being at `a` implies having hit `a`** (`k` jumps). -/
theorem P_le_stopOn_P (a : α) (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ c : α,
    J.P k t c a ≤ (J.stopOn {a}).P k t c a := by
  induction k with
  | zero =>
      intro t _ c
      by_cases hc : c = a
      · subst hc
        rw [stopOn_P_of_mem (Finset.mem_singleton_self c), if_pos rfl]
        exact J.P_le_one 0 t (by assumption) c c
      · simp [P_zero, hc]
  | succ k ih =>
      intro t ht c
      by_cases hc : c = a
      · subst hc
        rw [stopOn_P_of_mem (Finset.mem_singleton_self c), if_pos rfl]
        exact J.P_le_one _ t ht c c
      · have hcC : c ∉ ({a} : Finset α) := by simpa using hc
        rw [P_succ, P_succ, stopOn_q_of_not_mem hcC]
        refine add_le_add (le_of_eq rfl) ?_
        have hint2 := (J.stopOn {a}).integrable_term k t c a
        rw [stopOn_q_of_not_mem hcC] at hint2
        refine intervalIntegral.integral_mono_on ht (J.integrable_term k t c a) hint2
          fun s hs => ?_
        rw [sum_stopOn_rate_mul_of_not_mem hcC]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _) (J.rate_nonneg i c)

theorem Pmin_le_stopOn (a : α) {t : ℝ} (ht : 0 ≤ t) (c : α) :
    J.Pmin t c a ≤ (J.stopOn {a}).Pmin t c a :=
  le_of_tendsto_of_tendsto' (J.tendsto_P t ht c a) ((J.stopOn {a}).tendsto_P t ht c a)
    fun k => J.P_le_stopOn_P a k t ht c

/-- **The absorbed chain has at least the row mass of `J`** (`k` jumps). -/
theorem mass_le_stopOn_mass (a : α) (k : ℕ) : ∀ (t : ℝ), 0 ≤ t → ∀ c : α,
    J.mass k t c ≤ (J.stopOn {a}).mass k t c := by
  have hone : ∀ k t, (J.stopOn {a}).mass k t a = 1 := by
    intro k t
    unfold mass
    simp [stopOn_P_of_mem (Finset.mem_singleton_self a), (J.stopOn {a}).mem_reachK_self k a]
  induction k with
  | zero =>
      intro t ht c
      by_cases hc : c = a
      · subst hc; rw [hone]; exact J.mass_le_one 0 ht c
      · have hcC : c ∉ ({a} : Finset α) := by simpa using hc
        rw [mass_zero, mass_zero, stopOn_q_of_not_mem hcC]
  | succ k ih =>
      intro t ht c
      by_cases hc : c = a
      · subst hc; rw [hone]; exact J.mass_le_one _ ht c
      · have hcC : c ∉ ({a} : Finset α) := by simpa using hc
        rw [mass_succ, mass_succ, stopOn_q_of_not_mem hcC]
        refine add_le_add le_rfl ?_
        have hint : ∀ (K : JumpSystem α), IntervalIntegrable (fun s => Real.exp (-(J.q c * s)) *
            ∑ i, K.rate i c * K.mass k (t - s) (K.next i c)) volume 0 t := fun K =>
          Continuous.intervalIntegrable (by
            refine (by fun_prop : Continuous fun s => Real.exp (-(J.q c * s))).mul ?_
            exact continuous_finsetSum _ fun i _ => continuous_const.mul
              ((K.continuous_mass k _).comp (continuous_const.sub continuous_id))) _ _
        refine intervalIntegral.integral_mono_on ht (hint J) (hint (J.stopOn {a})) fun s hs => ?_
        rw [sum_stopOn_rate_mul_of_not_mem hcC]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (ih (t - s) (by linarith [hs.2]) _) (J.rate_nonneg i c)

/-- **The absorbed chain is stochastic where `J` is.** -/
theorem hasSum_stopOn_Pmin_one (a : α) {t : ℝ} (ht : 0 ≤ t) {c : α}
    (h : HasSum (fun b => J.Pmin t c b) 1) : HasSum (fun b => (J.stopOn {a}).Pmin t c b) 1 := by
  set Js := J.stopOn {a}
  have hs : Summable fun b => Js.Pmin t c b :=
    summable_of_sum_le (fun b => Js.Pmin_nonneg t ht c b) (Js.sum_Pmin_le_one t ht c)
  have hle : ∑' b, Js.Pmin t c b ≤ 1 := hs.tsum_le_of_sum_le (Js.sum_Pmin_le_one t ht c)
  have hmass : ∀ k, J.mass k t c ≤ ∑' b, Js.Pmin t c b := by
    intro k
    calc J.mass k t c ≤ Js.mass k t c := J.mass_le_stopOn_mass a k t ht c
      _ = ∑ b ∈ Js.reachK k c, Js.P k t c b := rfl
      _ ≤ ∑ b ∈ Js.reachK k c, Js.Pmin t c b :=
          Finset.sum_le_sum fun b _ => Js.P_le_Pmin k ht c b
      _ ≤ ∑' b, Js.Pmin t c b := hs.sum_le_tsum _ fun b _ => Js.Pmin_nonneg t ht c b
  have hge : 1 ≤ ∑' b, Js.Pmin t c b :=
    le_of_tendsto' (J.tendsto_mass_one ht h) hmass
  have : ∑' b, Js.Pmin t c b = 1 := le_antisymm hle hge
  rw [← this]
  exact hs.hasSum

/-- Reachability for the absorbed chain implies reachability for `J`. -/
theorem reachPos_of_stopOn {C : Finset α} {c b : α} (h : (J.stopOn C).ReachPos c b) :
    J.ReachPos c b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
      obtain ⟨i, hi, rfl⟩ := hxy
      have hi' : 0 < J.rate i x := by
        by_cases hx : x ∈ C
        · simp [stopOn, hx] at hi
        · simpa [stopOn, hx] using hi
      exact ih.tail ⟨i, hi', rfl⟩

theorem stopOn_absorbed_mono (a : α) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (c : α) :
    (J.stopOn {a}).Pmin t c a ≤ (J.stopOn {a}).Pmin s c a := by
  have := J.sum_stopOn_Pmin_mono {a} ht (sub_nonneg.mpr hts) c
  simpa using this

/-- **Hitting with probability one.** On a closed irreducible class carrying an invariant
probability, the chain started anywhere in the class hits `a` with probability tending to one. -/
theorem tendsto_stopOn_absorbed_one {E : Set α}
    (hE : ∀ x ∈ E, ∀ i, 0 < J.rate i x → J.next i x ∈ E)
    (hirr : ∀ x ∈ E, ∀ y ∈ E, J.ReachPos x y)
    (hstoch : ∀ t, 0 ≤ t → ∀ x ∈ E, HasSum (fun b => J.Pmin t x b) 1)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    {a : α} (ha : a ∈ E) {c : α} (hc : c ∈ E) :
    Tendsto (fun T => (J.stopOn {a}).Pmin T c a) atTop (𝓝 1) := by
  classical
  set Js := J.stopOn {a} with hJs
  set A : ℝ → α → ℝ := fun T x => Js.Pmin T x a with hA
  have hA1 : ∀ T, 0 ≤ T → ∀ x, A T x ≤ 1 := fun T hT x => Js.Pmin_le_one T hT x a
  have hA0 : ∀ T, 0 ≤ T → ∀ x, 0 ≤ A T x := fun T hT x => Js.Pmin_nonneg T hT x a
  have hAa : ∀ T, A T a = 1 := fun T => by
    simp [hA, hJs, stopOn_Pmin_of_mem (Finset.mem_singleton_self a)]
  have hmono : ∀ x, Monotone fun n : ℕ => A n x := fun x =>
    monotone_nat_of_le_succ fun n => J.stopOn_absorbed_mono a (Nat.cast_nonneg n)
      (by push_cast; linarith) x
  set h : α → ℝ := fun x => ⨆ n : ℕ, A n x with hh
  have hbdd : ∀ x, BddAbove (Set.range fun n : ℕ => A n x) := fun x =>
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hA1 n (Nat.cast_nonneg n) x⟩
  have hlimN : ∀ x, Tendsto (fun n : ℕ => A n x) atTop (𝓝 (h x)) := fun x =>
    tendsto_atTop_ciSup (hmono x) (hbdd x)
  have hle_h : ∀ x, ∀ T, 0 ≤ T → A T x ≤ h x := by
    intro x T hT
    obtain ⟨n, hn⟩ := exists_nat_ge T
    exact (J.stopOn_absorbed_mono a hT hn x).trans (le_ciSup (hbdd x) n)
  have hh1 : ∀ x, h x ≤ 1 := fun x => ciSup_le fun n => hA1 n (Nat.cast_nonneg n) x
  -- real-time limit
  have hlimR : ∀ x, Tendsto (fun T => A T x) atTop (𝓝 (h x)) := by
    intro x
    have hfloor : Tendsto (fun T : ℝ => A (⌊T⌋₊ : ℕ) x) atTop (𝓝 (h x)) :=
      (hlimN x).comp tendsto_nat_floor_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hfloor tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with T hT
      exact J.stopOn_absorbed_mono a (Nat.cast_nonneg _) (Nat.floor_le hT) x
    · filter_upwards [eventually_ge_atTop 0] with T hT
      exact hle_h x T hT
  -- `h ≥ π(a)` on `E`
  have hπa : 0 < π a := J.invariant_pos hirr hπ0 hπE hπ1 hinv ha
  have hhπ : ∀ x ∈ E, π a ≤ h x := by
    intro x hx
    have hconv := (J.tendsto_Pmin_of_invariant hE hirr hstoch hπ0 hπE hπ1 hinv hx a)
    refine le_of_tendsto' (hconv.comp tendsto_natCast_atTop_atTop) fun n => ?_
    exact (J.Pmin_le_stopOn a (Nat.cast_nonneg n) x).trans (le_ciSup (hbdd x) n)
  -- support of the absorbed chain stays in `E`
  have hreachE : ∀ y, J.ReachPos c y → y ∈ E := by
    intro y hr
    induction hr with
    | refl => exact hc
    | @tail x y _ hxy ih =>
        obtain ⟨i, hi, rfl⟩ := hxy
        exact hE x ih i hi
  have hsuppE : ∀ t, ∀ b, b ∉ E → Js.Pmin t c b = 0 := fun t b hb =>
    Js.Pmin_eq_zero_of_not_reachPos t fun hr => hb (hreachE b (J.reachPos_of_stopOn hr))
  -- harmonicity of `h` along integer times
  have hharm : ∀ n : ℕ, h c = ∑' b, Js.Pmin n c b * h b := by
    intro n
    have hlhs : Tendsto (fun m : ℕ => A ((n : ℝ) + m) c) atTop (𝓝 (h c)) := by
      have := (hlimN c).comp (tendsto_add_atTop_nat n)
      refine this.congr fun m => ?_
      simp [Function.comp, add_comm]
    have hrhs : Tendsto (fun m : ℕ => ∑' b, Js.Pmin n c b * A m b) atTop
        (𝓝 (∑' b, Js.Pmin n c b * h b)) := by
      refine tendsto_tsum_of_dominated_convergence (bound := fun b => Js.Pmin n c b)
        (summable_of_sum_le (fun b => Js.Pmin_nonneg n (Nat.cast_nonneg n) c b)
          (Js.sum_Pmin_le_one n (Nat.cast_nonneg n) c)) (fun b => (hlimN b).const_mul _) ?_
      refine Eventually.of_forall fun m b => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Js.Pmin_nonneg n (Nat.cast_nonneg n) c b)
        (hA0 m (Nat.cast_nonneg m) b))]
      exact mul_le_of_le_one_right (Js.Pmin_nonneg n (Nat.cast_nonneg n) c b)
        (hA1 m (Nat.cast_nonneg m) b)
    have heq : ∀ m : ℕ, A ((n : ℝ) + m) c = ∑' b, Js.Pmin n c b * A m b := fun m =>
      Js.Pmin_add (Nat.cast_nonneg n) (Nat.cast_nonneg m) c a
    exact tendsto_nhds_unique (hlhs.congr heq) hrhs
  -- the key inequality
  have hkey : ∀ n : ℕ, 1 - h c ≤ (1 - π a) * (1 - A n c) := by
    intro n
    have hst := J.hasSum_stopOn_Pmin_one a (Nat.cast_nonneg n) (hstoch n (Nat.cast_nonneg n) c hc)
    have hs := hst.summable
    have h1 : 1 - h c = ∑' b, Js.Pmin n c b * (1 - h b) := by
      have e1 : ∑' b, Js.Pmin n c b * (1 - h b) =
          ∑' b, Js.Pmin n c b - ∑' b, Js.Pmin n c b * h b := by
        rw [← hs.tsum_sub (Summable.of_nonneg_of_le
          (fun b => mul_nonneg (Js.Pmin_nonneg n (Nat.cast_nonneg n) c b)
            (le_trans (hA0 0 le_rfl b) (hle_h b 0 le_rfl)))
          (fun b => mul_le_of_le_one_right (Js.Pmin_nonneg n (Nat.cast_nonneg n) c b) (hh1 b)) hs)]
        exact tsum_congr fun b => by ring
      rw [e1, hst.tsum_eq, ← hharm n]
    have hpt : ∀ b, Js.Pmin n c b * (1 - h b) ≤
        (1 - π a) * (Js.Pmin n c b - (if b = a then Js.Pmin n c b else 0)) := by
      intro b
      have hP0 := Js.Pmin_nonneg n (Nat.cast_nonneg n) c b
      by_cases hba : b = a
      · subst hba
        have : h b = 1 := le_antisymm (hh1 b) (by
          have := hle_h b 0 le_rfl; rw [hAa] at this; exact this)
        rw [this, if_pos rfl]; simp
      · rw [if_neg hba, sub_zero]
        by_cases hbE : b ∈ E
        · have := hhπ b hbE
          rw [mul_comm (1 - π a)]
          exact mul_le_mul_of_nonneg_left (by linarith) hP0
        · rw [hsuppE n b hbE]; simp
    have hsa : Summable fun b => (if b = a then Js.Pmin n c b else 0) :=
      summable_of_ne_finset_zero (s := {a}) fun b hb => by
        simp only [Finset.mem_singleton] at hb; simp [hb]
    have h2 : ∑' b, (Js.Pmin n c b - (if b = a then Js.Pmin n c b else 0)) = 1 - A n c := by
      rw [hs.tsum_sub hsa, hst.tsum_eq, tsum_ite_eq]
    rw [h1]
    calc ∑' b, Js.Pmin n c b * (1 - h b)
        ≤ ∑' b, (1 - π a) * (Js.Pmin n c b - (if b = a then Js.Pmin n c b else 0)) :=
          Summable.tsum_le_tsum hpt
            (Summable.of_nonneg_of_le (fun b => by
              have := Js.Pmin_nonneg n (Nat.cast_nonneg n) c b
              have := hh1 b
              positivity) (fun b => mul_le_of_le_one_right
                (Js.Pmin_nonneg n (Nat.cast_nonneg n) c b) (by
                  have := le_trans (hA0 0 le_rfl b) (hle_h b 0 le_rfl); linarith)) hs)
            ((hs.sub hsa).mul_left _)
      _ = (1 - π a) * (1 - A n c) := by rw [tsum_mul_left, h2]
  -- conclude `h c = 1`
  have hlim := ((hlimN c).const_sub 1).const_mul (1 - π a)
  have hfin : 1 - h c ≤ (1 - π a) * (1 - h c) := ge_of_tendsto' hlim hkey
  have hhc : h c = 1 := by
    have : π a * (1 - h c) ≤ 0 := by nlinarith
    have : 1 - h c ≤ 0 := by
      by_contra hpos; push Not at hpos; nlinarith
    linarith [hh1 c]
  rw [← hhc]
  exact hlimR c

/-- **Stationarity against bounded observables.** For an invariant probability with
`∑ π q < ∞` and `|f| ≤ 1`, `∑_b π(b) (Q f)(b) = 0`. -/
theorem tsum_invariant_mul_drift {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπs : Summable π)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    (hq : Summable fun b => π b * J.q b) (f : α → ℝ) (hf : ∀ c, |f c| ≤ 1) :
    ∑' b, π b * J.drift f b = 0 := by
  classical
  set F : α → α → ℝ := fun b c => π b * J.Q b c * f c with hF
  set G : α × α → ℝ := fun p => π p.1 * |J.Q p.1 p.2| with hG
  have hG0 : 0 ≤ G := fun p => mul_nonneg (hπ0 _) (abs_nonneg _)
  have hrow : ∀ b, ∑' c, |J.Q b c| ≤ 2 * J.q b := by
    intro b
    have := J.sum_abs_Q_mul_le (fun _ => (1 : ℝ)) b
    simp only [abs_one, mul_one] at this
    have hq' : ∑ i, J.rate i b = J.q b := rfl
    linarith
  have hGs : Summable G := by
    rw [summable_prod_of_nonneg hG0]
    refine ⟨fun b => summable_of_ne_finset_zero (s := J.nbhd b) fun c hc => by
      simp [hG, J.Q_eq_zero_of_not_mem hc], ?_⟩
    refine Summable.of_nonneg_of_le (fun b => tsum_nonneg fun c => hG0 (b, c)) (fun b => ?_)
      (hq.mul_left 2)
    show ∑' c, π b * |J.Q b c| ≤ 2 * (π b * J.q b)
    rw [tsum_mul_left]
    nlinarith [hrow b, hπ0 b]
  have hFs : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hGs fun p => ?_
    simp only [Function.uncurry, hF, hG, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hπ0 p.1)]
    have := hf p.2
    have h0 : 0 ≤ π p.1 * |J.Q p.1 p.2| := mul_nonneg (hπ0 _) (abs_nonneg _)
    nlinarith
  have h1 : ∀ b, π b * J.drift f b = ∑' c, F b c := by
    intro b
    rw [← J.tsum_Q_mul f b, ← tsum_mul_left]
    exact tsum_congr fun c => by simp only [hF]; ring
  simp_rw [h1]
  rw [← hFs.tsum_comm]
  have h2 : ∀ c, ∑' b, F b c = f c * ∑' b, π b * J.Q b c := by
    intro c
    rw [← tsum_mul_left]
    exact tsum_congr fun b => by simp only [hF]; ring
  simp_rw [h2, J.tsum_invariant_mul_Q hπ0 hπs hinv hq, mul_zero, tsum_zero]

theorem drift_eq (K : JumpSystem α) (f : α → ℝ) (b : α) :
    K.drift f b = ∑ i, K.rate i b * f (K.next i b) - K.q b * f b := by
  unfold drift q
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem stopOn_q_le (C : Finset α) (b : α) : (J.stopOn C).q b ≤ J.q b := by
  by_cases hb : b ∈ C
  · rw [stopOn_q_of_mem hb]; exact J.q_nonneg b
  · rw [stopOn_q_of_not_mem hb]

/-- The return-tail rate `R(t) = ∑_i rate_i(a) (1 − A(t, next_i a))`. -/
noncomputable def returnTail (a : α) (t : ℝ) : ℝ :=
  ∑ i, J.rate i a * (1 - (J.stopOn {a}).Pmin t (J.next i a) a)

/-- **Derivative of the absorbed stationary mass.** -/
theorem hasDerivAt_absorbed_mass {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπs : Summable π)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    (hq : Summable fun b => π b * J.q b) (a : α) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ∑' b, π b * (J.stopOn {a}).Pmin τ b a) (π a * J.returnTail a t) t := by
  classical
  set Js := J.stopOn {a} with hJs
  set g' : α → ℝ → ℝ := fun b τ => π b * (-Js.q b * Js.Pmin τ b a +
    ∑ i, Js.rate i b * Js.Pmin τ (Js.next i b) a) with hg'
  have hder := hasDerivAt_tsum_of_isPreconnected (u := fun b => π b * (2 * J.q b))
    (g := fun b τ => π b * Js.Pmin τ b a) (g' := g') (t := Ioi 0) (y₀ := t)
    (hq.mul_left 2 |>.congr fun b => by ring) isOpen_Ioi isPreconnected_Ioi
    (fun b y hy => (Js.hasDerivAt_Pmin y hy b a).const_mul (π b))
    (fun b y hy => by
      have hy0 : 0 ≤ y := le_of_lt hy
      simp only [hg', Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 b)]
      refine mul_le_mul_of_nonneg_left ?_ (hπ0 b)
      have hqs := J.stopOn_q_le {a} b
      have h1 : |-Js.q b * Js.Pmin y b a| ≤ Js.q b := by
        rw [abs_mul, abs_neg, abs_of_nonneg (Js.q_nonneg b),
          abs_of_nonneg (Js.Pmin_nonneg y hy0 b a)]
        exact mul_le_of_le_one_right (Js.q_nonneg b) (Js.Pmin_le_one y hy0 b a)
      have h2 : |∑ i, Js.rate i b * Js.Pmin y (Js.next i b) a| ≤ Js.q b := by
        rw [abs_of_nonneg (Finset.sum_nonneg fun i _ =>
          mul_nonneg (Js.rate_nonneg i b) (Js.Pmin_nonneg y hy0 _ a))]
        exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (Js.rate_nonneg i b)
          (Js.Pmin_le_one y hy0 _ a)
      calc |-Js.q b * Js.Pmin y b a + ∑ i, Js.rate i b * Js.Pmin y (Js.next i b) a|
          ≤ |-Js.q b * Js.Pmin y b a| + |∑ i, Js.rate i b * Js.Pmin y (Js.next i b) a| :=
            abs_add_le _ _
        _ ≤ 2 * J.q b := by linarith)
    (show t ∈ Ioi 0 from ht)
    (Summable.of_nonneg_of_le (fun b => mul_nonneg (hπ0 b) (Js.Pmin_nonneg t ht.le b a))
      (fun b => mul_le_of_le_one_right (hπ0 b) (Js.Pmin_le_one t ht.le b a)) hπs)
    (show t ∈ Ioi 0 from ht)
  convert hder using 1
  -- evaluate the derivative
  set A : α → ℝ := fun c => Js.Pmin t c a with hA
  have hAa : A a = 1 := by simp [hA, hJs, stopOn_Pmin_of_mem (Finset.mem_singleton_self a)]
  have hAb : ∀ c, |A c| ≤ 1 := fun c => by
    rw [abs_of_nonneg (Js.Pmin_nonneg t ht.le c a)]; exact Js.Pmin_le_one t ht.le c a
  have hg'eq : ∀ b, g' b t = π b * (if b = a then 0 else J.drift A b) := by
    intro b
    simp only [hg']
    congr 1
    have hd : -Js.q b * Js.Pmin t b a + ∑ i, Js.rate i b * Js.Pmin t (Js.next i b) a =
        Js.drift A b := by rw [drift_eq]; simp only [hA]; ring
    rw [hd]
    split_ifs with hba
    · subst hba; exact stopOn_drift_of_mem (Finset.mem_singleton_self b) A
    · exact stopOn_drift_of_not_mem (by simpa using hba) A
  simp_rw [hg'eq]
  have hsplit : ∀ b, π b * (if b = a then 0 else J.drift A b) =
      π b * J.drift A b - (if b = a then π a * J.drift A a else 0) := by
    intro b; split_ifs with hba
    · subst hba; ring
    · ring
  simp_rw [hsplit]
  have hs1 : Summable fun b => π b * J.drift A b := by
    refine Summable.of_norm_bounded (hq.mul_left 2) fun b => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 b)]
    have : |J.drift A b| ≤ 2 * J.q b := by
      rw [drift_eq]
      have h1 : |∑ i, J.rate i b * A (J.next i b)| ≤ J.q b := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (J.rate_nonneg i b)]
        exact mul_le_of_le_one_right (J.rate_nonneg i b) (hAb _)
      have h2 : |J.q b * A b| ≤ J.q b := by
        rw [abs_mul, abs_of_nonneg (J.q_nonneg b)]
        exact mul_le_of_le_one_right (J.q_nonneg b) (hAb b)
      calc |∑ i, J.rate i b * A (J.next i b) - J.q b * A b|
          ≤ |∑ i, J.rate i b * A (J.next i b)| + |J.q b * A b| := abs_sub _ _
        _ ≤ 2 * J.q b := by linarith
    nlinarith [hπ0 b]
  have hs2 : Summable fun b => (if b = a then π a * J.drift A a else 0) :=
    summable_of_ne_finset_zero (s := {a}) fun b hb => by
      simp only [Finset.mem_singleton] at hb; simp [hb]
  rw [hs1.tsum_sub hs2, J.tsum_invariant_mul_drift hπ0 hπs hinv hq A hAb, tsum_ite_eq, zero_sub]
  rw [drift_eq, hAa]
  unfold returnTail
  simp only [hA, mul_one]
  have e : ∑ i, J.rate i a * (1 - Js.Pmin t (J.next i a) a) =
      J.q a - ∑ i, J.rate i a * Js.Pmin t (J.next i a) a := by
    rw [show J.q a = ∑ i, J.rate i a from rfl, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-- **Kac's formula.** On a closed irreducible class `E` on which the chain is stochastic, with an
invariant probability `π` supported on `E` and `∑ π q < ∞`, for `a ∈ E` with `q(a) > 0`:
`1/q(a) + (1/q(a)) ∫₀^T ∑_i rate_i(a) (1 − P_a(t)(next_i a, a)) dt → 1/(π(a) q(a))`. -/
theorem kac_formula {E : Set α}
    (hE : ∀ x ∈ E, ∀ i, 0 < J.rate i x → J.next i x ∈ E)
    (hirr : ∀ x ∈ E, ∀ y ∈ E, J.ReachPos x y)
    (hstoch : ∀ t, 0 ≤ t → ∀ x ∈ E, HasSum (fun b => J.Pmin t x b) 1)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    (hq : Summable fun b => π b * J.q b) {a : α} (ha : a ∈ E) (hqa : 0 < J.q a) :
    Tendsto (fun T => 1 / J.q a + (∫ t in (0 : ℝ)..T, J.returnTail a t) / J.q a) atTop
      (𝓝 (1 / (π a * J.q a))) := by
  classical
  set Js := J.stopOn {a} with hJs
  have hπs := hπ1.summable
  have hπa : 0 < π a := J.invariant_pos hirr hπ0 hπE hπ1 hinv ha
  set ψ : ℝ → ℝ := fun τ => ∑' b, π b * Js.Pmin τ b a with hψ
  have hψ0 : ψ 0 = π a := by
    simp only [hψ, hJs]
    rw [tsum_eq_single a fun b hb => by
      have : (J.stopOn {a}).Pmin 0 b a = 0 := by
        rw [(J.stopOn {a}).Pmin_zero]; simp [hb]
      rw [this, mul_zero]]
    rw [stopOn_Pmin_of_mem (Finset.mem_singleton_self a), if_pos rfl, mul_one]
  have hRcont : ContinuousOn (fun t => J.returnTail a t) (Ici 0) := by
    unfold returnTail
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (continuousOn_const.sub (Js.continuousOn_Pmin _ a))
  have hψc : ContinuousOn ψ (Ici 0) :=
    continuousOn_tsum (fun b => continuousOn_const.mul (Js.continuousOn_Pmin b a)) hπs
      fun b τ hτ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hπ0 b) (Js.Pmin_nonneg τ hτ b a))]
        exact mul_le_of_le_one_right (hπ0 b) (Js.Pmin_le_one τ hτ b a)
  have hFTC : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, J.returnTail a t = (ψ T - π a) / π a := by
    intro T hT
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (hψc.mono fun x hx => hx.1)
      (fun x hx => J.hasDerivAt_absorbed_mass hπ0 hπs hinv hq a hx.1)
      ((continuousOn_const.mul (hRcont.mono fun x hx => hx.1)).intervalIntegrable_of_Icc hT)
    rw [intervalIntegral.integral_const_mul, hψ0] at h
    field_simp
    linarith
  have hψlim : Tendsto ψ atTop (𝓝 1) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ)) (bound := π)
      (f := fun T b => π b * Js.Pmin T b a) (g := fun b => π b) hπs (fun b => ?_) ?_
    · rwa [hπ1.tsum_eq] at h
    · by_cases hb : b ∈ E
      · have := (J.tendsto_stopOn_absorbed_one hE hirr hstoch hπ0 hπE hπ1 hinv ha hb).const_mul (π b)
        rwa [mul_one] at this
      · simp only [hπE b hb, zero_mul]; exact tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 0] with T hT
      intro b
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hπ0 b) (Js.Pmin_nonneg T hT b a))]
      exact mul_le_of_le_one_right (hπ0 b) (Js.Pmin_le_one T hT b a)
  have hlim : Tendsto (fun T => 1 / J.q a + ((ψ T - π a) / π a) / J.q a) atTop
      (𝓝 (1 / J.q a + ((1 - π a) / π a) / J.q a)) :=
    tendsto_const_nhds.add (((hψlim.sub_const (π a)).div_const (π a)).div_const (J.q a))
  have hval : 1 / J.q a + ((1 - π a) / π a) / J.q a = 1 / (π a * J.q a) := by
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [hFTC T hT]

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Kac's formula for complex-balanced networks.** For a weakly reversible network with a
positive complex-balanced equilibrium `c` and a count `n` with `q(n) > 0`, the expected return
time to `n` is `Z / (π_c(n) q(n))`, where `π_c` is the product form and `Z` its mass on the class of
`n` (no conservation law is assumed; the class may be infinite). -/
theorem kac_productPoisson (N : Network S) (κ : RateConstants N) (hWR : N.WeaklyReversible)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) (n : S → ℕ)
    (hqn : 0 < (N.jumpSystem κ).q n) :
    Tendsto (fun T => 1 / (N.jumpSystem κ).q n +
        (∫ t in (0 : ℝ)..T, (N.jumpSystem κ).returnTail n t) / (N.jumpSystem κ).q n) atTop
      (𝓝 ((∑' x, N.classProductForm κ c n x) /
        (productPoissonPMF c n * (N.jumpSystem κ).q n))) := by
  obtain ⟨hZ, h0, hsupp, h1, hinv⟩ := N.classProductForm_facts κ hWR hc hcb n
  set Z := ∑' x, N.classProductForm κ c n x with hZdef
  set π : (S → ℕ) → ℝ := fun m => N.classProductForm κ c n m / Z with hπ
  have hc0 : c.Nonnegative := fun s => (hc s).le
  have hwn : N.classProductForm κ c n n = productPoissonPMF c n :=
    Set.indicator_of_mem (s := {m | (N.jumpSystem κ).ReachPos n m}) Relation.ReflTransGen.refl _
  have hle : ∀ m, π m ≤ productPoissonPMF c m / Z := by
    intro m
    apply div_le_div_of_nonneg_right _ hZ.le
    unfold classProductForm
    by_cases h : (N.jumpSystem κ).ReachPos n m
    · rw [Set.indicator_of_mem (s := {m | (N.jumpSystem κ).ReachPos n m}) h]
    · rw [Set.indicator_of_notMem (s := {m | (N.jumpSystem κ).ReachPos n m}) h]
      exact productPoissonPMF_nonneg hc0 m
  have hq : Summable fun m => π m * (N.jumpSystem κ).q m := by
    have hs : Summable fun m => productPoissonPMF c m / Z * (N.jumpSystem κ).q m := by
      have : Summable fun m => ∑ r, productPoissonPMF c m * N.stochasticMassActionRate κ m r :=
        summable_sum fun r _ => N.summable_productPoisson_mul_rate κ hc0 r
      refine (this.div_const Z).congr fun m => ?_
      show (∑ r, productPoissonPMF c m * N.stochasticMassActionRate κ m r) / Z =
        productPoissonPMF c m / Z * ∑ r, N.stochasticMassActionRate κ m r
      rw [← Finset.mul_sum]; ring
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (h0 m) ((N.jumpSystem κ).q_nonneg m))
      (fun m => mul_le_mul_of_nonneg_right (hle m) ((N.jumpSystem κ).q_nonneg m)) hs
  have hk := (N.jumpSystem κ).kac_formula (E := {m | (N.jumpSystem κ).ReachPos n m})
    (fun a ha i hr => (ha : (N.jumpSystem κ).ReachPos n a).tail ⟨i, hr, rfl⟩)
    (fun a ha b hb => (N.reachPos_symm κ hWR ha).trans hb)
    (fun t ht a _ => N.hasSum_transition_one_of_complexBalanced κ hc hcb ht a)
    h0 hsupp h1 hinv hq Relation.ReflTransGen.refl hqn
  have hval : 1 / (π n * (N.jumpSystem κ).q n) = Z / (productPoissonPMF c n * (N.jumpSystem κ).q n) := by
    simp only [hπ, hwn]
    have := productPoissonPMF_pos hc n
    field_simp
  rw [hval] at hk
  exact hk

end Network

namespace Examples
namespace BirthDeathKac

open Network

/-- `0 ⇌ X` with unit rates. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨0, ![1]⟩ else ⟨![1], 0⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

def c : Concentration (Fin 1) := fun _ => 1

theorem weaklyReversible : net.WeaklyReversible := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, by simp, by simp⟩
  · exact Relation.ReflTransGen.single ⟨0, by simp, by simp⟩

theorem complexBalanced : net.IsComplexBalanced κ c := by
  intro z _
  simp only [inflow, outflow, Fin.sum_univ_two, massActionRate, Complex.massActionMonomial, κ, c]
  simp only [Fin.isValue, ↓reduceIte, one_pow, Finset.prod_const_one, mul_one, one_ne_zero]
  split_ifs <;> simp_all

theorem c_pos : c.Positive := fun _ => one_pos

/-- From the empty state only the birth `0 → X` can fire, at rate `1`. -/
theorem q_zero : (net.jumpSystem κ).q 0 = 1 := by
  show ∑ r, net.stochasticMassActionRate κ 0 r = 1
  rw [Fin.sum_univ_two]
  simp [stochasticMassActionRate, κ]

/-- **Kac's formula for the birth–death chain `0 ⇌ X` at the empty state**: the expected return
time is `Z / (π_c(0) q(0)) = Z e`, with `Z` the product-form mass of the class. -/
theorem kac :
    Tendsto (fun T => 1 / (net.jumpSystem κ).q 0 +
        (∫ t in (0 : ℝ)..T, (net.jumpSystem κ).returnTail 0 t) / (net.jumpSystem κ).q 0) atTop
      (𝓝 ((∑' x, net.classProductForm κ c 0 x) * Real.exp 1)) := by
  have h := net.kac_productPoisson κ weaklyReversible c_pos complexBalanced 0
    (by rw [q_zero]; exact one_pos)
  have hp : productPoissonPMF c 0 = Real.exp (-1) := by simp [productPoissonPMF, c]
  rw [hp, q_zero, mul_one] at h
  have hv : (∑' x, net.classProductForm κ c 0 x) * Real.exp 1 =
      (∑' x, net.classProductForm κ c 0 x) / Real.exp (-1) := by
    rw [Real.exp_neg, div_inv_eq_mul]
  rw [q_zero, hv]
  exact h

/-- Every count is reachable from the empty state. -/
theorem reach_all (m : Fin 1 → ℕ) : (net.jumpSystem κ).ReachPos 0 m := by
  have h : ∀ k : ℕ, (net.jumpSystem κ).ReachPos 0 (fun _ => k) := by
    intro k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
        refine ih.tail ⟨(0 : Fin 2), ?_, ?_⟩
        · show 0 < net.stochasticMassActionRate κ (fun _ => k) 0
          simp [stochasticMassActionRate, κ]
        · funext s
          show k + 1 = net.jumpNextCount (fun _ => k) (0 : Fin 2) s
          simp [jumpNextCount]
  have hm : m = fun _ => m 0 := funext fun s => by rw [Subsingleton.elim s 0]
  rw [hm]; exact h (m 0)

/-- The product form has total mass one on the class. -/
theorem classMass : ∑' x, net.classProductForm κ c 0 x = 1 := by
  have h : net.classProductForm κ c 0 = productPoissonPMF c := by
    funext x
    exact Set.indicator_of_mem (s := {m | (net.jumpSystem κ).ReachPos 0 m}) (reach_all x) _
  rw [h]
  exact (hasSum_productPoissonPMF fun _ => zero_le_one).tsum_eq

/-- **The expected return time of `0 ⇌ X` (unit rates) to the empty state is `e`.** -/
theorem kac_e :
    Tendsto (fun T => 1 / (net.jumpSystem κ).q 0 +
        (∫ t in (0 : ℝ)..T, (net.jumpSystem κ).returnTail 0 t) / (net.jumpSystem κ).q 0) atTop
      (𝓝 (Real.exp 1)) := by
  have := kac
  rwa [classMass, one_mul] at this

end BirthDeathKac
end Examples

end CRNT
