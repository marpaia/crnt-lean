import CRNT.Stochastic.MinimalSemigroup
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Stochasticity of the minimal transition function under bounded exit rates

If the exit rate is bounded by `Λ` on every state reachable from `a` through positive-rate jumps,
the minimal transition function is stochastic at `a`: `∑_b P(t)(a, b) = 1` (`hasSum_Pmin_one`).

The row of `P_k(t)(a, ·)` is supported on the finite set `R_k(a)` of states reachable in at most
`k` jumps (`P_eq_zero_of_not_mem`). The defect `E_k(t, a) = 1 − ∑_{b ∈ R_k(a)} P_k(t)(a, b)`
(the probability of more than `k` jumps by time `t`) satisfies
`E_{k+1}(t, a) = ∫₀ᵗ e^{−q(a)s} ∑ᵢ rateᵢ(a) E_k(t − s, nextᵢ a) ds` (`defect_succ`), hence
`E_k(t, a) ≤ (Λt)^{k+1}/(k+1)!` on the reachable set (`defect_le`), which tends to `0`.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- States reachable in at most `k` jumps (through any channel). -/
def reachK : ℕ → α → Finset α
  | 0, a => {a}
  | k + 1, a => insert a (Finset.univ.biUnion fun i => reachK k (J.next i a))

theorem mem_reachK_self (k : ℕ) (a : α) : a ∈ J.reachK k a := by
  cases k <;> simp [reachK]

theorem reachK_next_subset (k : ℕ) (a : α) (i : J.ι) :
    J.reachK k (J.next i a) ⊆ J.reachK (k + 1) a := by
  intro b hb
  simp only [reachK, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, hb⟩

theorem P_eq_zero_of_not_mem (k : ℕ) : ∀ (t : ℝ) (a b : α), b ∉ J.reachK k a → J.P k t a b = 0 := by
  induction k with
  | zero =>
      intro t a b hb
      have : a ≠ b := fun h => hb (by simp [reachK, h])
      simp [P_zero, this]
  | succ k ih =>
      intro t a b hb
      have hab : a ≠ b := fun h => hb (h ▸ J.mem_reachK_self (k + 1) a)
      rw [P_succ]
      have hzero : ∀ s, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b = 0 := by
        intro s
        rw [Finset.sum_eq_zero fun i _ => by
          rw [ih _ _ _ fun h => hb (J.reachK_next_subset k a i h), mul_zero], mul_zero]
      simp [hab, hzero]

/-- The row mass of `P_k(t)(a, ·)`. -/
noncomputable def mass (k : ℕ) (t : ℝ) (a : α) : ℝ := ∑ b ∈ J.reachK k a, J.P k t a b

theorem sum_P_eq_mass_of_subset (k : ℕ) (t : ℝ) (a : α) {F : Finset α}
    (hF : J.reachK k a ⊆ F) : ∑ b ∈ F, J.P k t a b = J.mass k t a := by
  unfold mass
  exact (Finset.sum_subset hF fun b _ hb => J.P_eq_zero_of_not_mem k t a b hb).symm

theorem continuous_mass (k : ℕ) (a : α) : Continuous fun t => J.mass k t a := by
  unfold mass
  exact continuous_finsetSum _ fun b _ => J.continuous_P k a b

theorem mass_zero (t : ℝ) (a : α) : J.mass 0 t a = Real.exp (-(J.q a * t)) := by
  simp [mass, reachK, P_zero]

theorem mass_succ (k : ℕ) (t : ℝ) (a : α) :
    J.mass (k + 1) t a = Real.exp (-(J.q a * t)) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.mass k (t - s) (J.next i a) := by
  unfold mass
  simp only [P_succ]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, if_pos (J.mem_reachK_self _ a),
    mul_one, ← intervalIntegral.integral_finsetSum fun b _ => J.integrable_term k t a b]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact J.sum_P_eq_mass_of_subset k (t - s) (J.next i a) (J.reachK_next_subset k a i)

/-- The defect: probability of more than `k` jumps by time `t`. -/
noncomputable def defect (k : ℕ) (t : ℝ) (a : α) : ℝ := 1 - J.mass k t a

theorem defect_nonneg (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (a : α) : 0 ≤ J.defect k t a := by
  unfold defect mass; linarith [J.sum_P_le_one k t ht a (J.reachK k a)]

theorem defect_succ (k : ℕ) (t : ℝ) (a : α) :
    J.defect (k + 1) t a = ∫ s in (0 : ℝ)..t, Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.defect k (t - s) (J.next i a) := by
  have hint : IntervalIntegrable (fun s => Real.exp (-(J.q a * s)) *
      ∑ i, J.rate i a * J.mass k (t - s) (J.next i a)) volume 0 t := by
    apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul ((J.continuous_mass k _).comp (continuous_const.sub continuous_id))
  have hsplit : ∀ s, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.defect k (t - s) (J.next i a) =
      J.q a * Real.exp (-(J.q a * s)) -
        Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.mass k (t - s) (J.next i a) := by
    intro s
    simp only [defect, mul_sub, mul_one, Finset.sum_sub_distrib, q]
    ring
  simp only [hsplit]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) hint,
    integral_exp_decay, defect, mass_succ]
  ring

/-- Reachability through positive-rate jumps. -/
def ReachPos (a c : α) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ i, 0 < J.rate i x ∧ y = J.next i x) a c

/-- **Defect bound** under a bound `Λ` on the exit rates of the reachable states. -/
theorem defect_le {a : α} {Λ : ℝ} (hΛ : ∀ c, J.ReachPos a c → J.q c ≤ Λ) (k : ℕ) :
    ∀ c, J.ReachPos a c → ∀ t, 0 ≤ t →
      J.defect k t c ≤ (Λ * t) ^ (k + 1) / (k + 1).factorial := by
  induction k with
  | zero =>
      intro c hc t ht
      simp only [defect, mass_zero, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
      have h1 : 1 - Real.exp (-(J.q c * t)) ≤ J.q c * t := by
        have := Real.add_one_le_exp (-(J.q c * t)); linarith
      have h2 : J.q c * t ≤ Λ * t := mul_le_mul_of_nonneg_right (hΛ c hc) ht
      linarith
  | succ k ih =>
      intro c hc t ht
      rw [defect_succ]
      have hΛc := hΛ c hc
      have hΛ0 : 0 ≤ Λ := (J.q_nonneg c).trans hΛc
      have hbound : ∀ s ∈ Icc (0 : ℝ) t, Real.exp (-(J.q c * s)) *
          ∑ i, J.rate i c * J.defect k (t - s) (J.next i c) ≤
          Λ * ((Λ * (t - s)) ^ (k + 1) / (k + 1).factorial) := by
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        have hsum : ∑ i, J.rate i c * J.defect k (t - s) (J.next i c) ≤
            J.q c * ((Λ * (t - s)) ^ (k + 1) / (k + 1).factorial) := by
          unfold q; rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hr : 0 < J.rate i c
          · exact mul_le_mul_of_nonneg_left (ih _ (hc.tail ⟨i, hr, rfl⟩) _ hts) hr.le
          · have : J.rate i c = 0 := le_antisymm (not_lt.mp hr) (J.rate_nonneg i c)
            simp [this]
        have hsum_nn : 0 ≤ ∑ i, J.rate i c * J.defect k (t - s) (J.next i c) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (J.rate_nonneg i c) (J.defect_nonneg k _ hts _)
        have he : Real.exp (-(J.q c * s)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [J.q_nonneg c, hs.1])
        have hpow_nn : 0 ≤ (Λ * (t - s)) ^ (k + 1) / (k + 1).factorial := by positivity
        calc Real.exp (-(J.q c * s)) * ∑ i, J.rate i c * J.defect k (t - s) (J.next i c)
            ≤ 1 * ∑ i, J.rate i c * J.defect k (t - s) (J.next i c) :=
              mul_le_mul_of_nonneg_right he hsum_nn
          _ ≤ J.q c * ((Λ * (t - s)) ^ (k + 1) / (k + 1).factorial) := by rw [one_mul]; exact hsum
          _ ≤ Λ * ((Λ * (t - s)) ^ (k + 1) / (k + 1).factorial) :=
              mul_le_mul_of_nonneg_right hΛc hpow_nn
      have hf : IntervalIntegrable (fun s => Real.exp (-(J.q c * s)) *
          ∑ i, J.rate i c * J.defect k (t - s) (J.next i c)) volume 0 t := by
        apply Continuous.intervalIntegrable
        refine Continuous.mul (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
        refine continuous_const.mul ?_
        exact (continuous_const.sub (J.continuous_mass k _)).comp (continuous_const.sub continuous_id)
      have hg : IntervalIntegrable (fun s => Λ * ((Λ * (t - s)) ^ (k + 1) / (k + 1).factorial))
          volume 0 t := by
        apply Continuous.intervalIntegrable; fun_prop
      have hmono := intervalIntegral.integral_mono_on ht hf hg hbound
      refine hmono.trans (le_of_eq ?_)
      -- `∫₀ᵗ Λ (Λ (t − s))^{k+1}/(k+1)! ds = (Λ t)^{k+2}/(k+2)!`
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun u => Λ * ((Λ * u) ^ (k + 1) / (k + 1).factorial)) (a := 0) (b := t) t
      simp only [sub_self, sub_zero] at hsub
      rw [hsub]
      have : ∀ u : ℝ, Λ * ((Λ * u) ^ (k + 1) / (k + 1).factorial) =
          (Λ ^ (k + 2) / (k + 1).factorial) * u ^ (k + 1) := by
        intro u; rw [mul_pow]; ring
      simp only [this, intervalIntegral.integral_const_mul, integral_pow]
      rw [Nat.factorial_succ (k + 1)]
      push_cast
      field_simp
      ring

/-- **Stochasticity under bounded exit rates.** -/
theorem hasSum_Pmin_one {a : α} {Λ : ℝ} (hΛ : ∀ c, J.ReachPos a c → J.q c ≤ Λ) {t : ℝ}
    (ht : 0 ≤ t) : HasSum (fun b => J.Pmin t a b) 1 := by
  have hnn : ∀ b, 0 ≤ J.Pmin t a b := fun b => J.Pmin_nonneg t ht a b
  have hsum : Summable fun b => J.Pmin t a b :=
    summable_of_sum_le hnn fun F => J.sum_Pmin_le_one t ht a F
  have hle : ∑' b, J.Pmin t a b ≤ 1 :=
    hsum.tsum_le_of_sum_le fun F => J.sum_Pmin_le_one t ht a F
  have hge : 1 ≤ ∑' b, J.Pmin t a b := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop (Λ * t)
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    have hk1 := hk (k + 1) (Nat.le_succ k)
    have hdef := J.defect_le hΛ k a Relation.ReflTransGen.refl t ht
    have hmass : 1 - ε < J.mass k t a := by unfold defect at hdef; linarith
    have hPk : J.mass k t a ≤ ∑ b ∈ J.reachK k a, J.Pmin t a b :=
      Finset.sum_le_sum fun b _ =>
        (monotone_nat_of_le_succ fun j => J.P_mono j t ht a b).ge_of_tendsto
          (J.tendsto_P t ht a b) k
    have := hsum.sum_le_tsum (J.reachK k a) fun b _ => hnn b
    linarith
  exact (hsum.hasSum_iff.mpr (le_antisymm hle hge))

end JumpSystem

end CRNT
