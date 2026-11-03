import CRNT.Stochastic.MinimalSemigroupForward
import CRNT.Stochastic.ForwardCME

/-!
# The transition function of stochastic mass action solves the chemical master equation

For `t > 0` and `∑_c P(t)(n, c) λ(c) < ∞`, `∂ₜ P(t)(n, m) = cmeRHS(P(t)(n, ·))(m)`: the row
`P(t)(n, ·)` solves the forward chemical master equation (`hasDerivAt_transition_cme`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The chemical master equation** for the transition function. -/
theorem hasDerivAt_transition_cme (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 < t)
    (n m : S → ℕ) (hsum : Summable fun c => N.transition κ t n c * N.exitRate κ c) :
    HasDerivAt (fun s => N.transition κ s n m) (N.cmeRHS κ (fun c => N.transition κ t n c) m) t := by
  classical
  have h := (N.jumpSystem κ).hasDerivAt_Pmin_forward ht n m hsum
  convert h using 1
  · rfl
  set P : (S → ℕ) → ℝ := fun c => N.transition κ t n c with hP
  have hP0 : ∀ c, 0 ≤ P c := fun c => N.transition_nonneg κ ht.le n c
  have hP1 : ∀ c, P c ≤ 1 := fun c => N.transition_le_one κ ht.le n c
  -- rewrite `Q` through the reactions
  have hQ : ∀ c, P c * (N.jumpSystem κ).Q c m = ∑ r, P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then 1 else 0) - P c * N.exitRate κ c * (if c = m then 1 else 0) := by
    intro c
    have hj := N.sum_rate_mul_jumpNextCount κ (fun l => if l = m then (1 : ℝ) else 0) c
    show P c * (∑ r : N.R, N.stochasticMassActionRate κ c r *
      (if N.jumpNextCount c r = m then 1 else 0) - N.exitRate κ c * (if c = m then 1 else 0)) = _
    rw [hj, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun r _ => by ring
    · ring
  have hfire : ∀ r, Summable fun c => P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then (1 : ℝ) else 0) := fun r =>
    Summable.of_nonneg_of_le (fun c => mul_nonneg (mul_nonneg (hP0 c)
      (N.stochasticMassActionRate_nonneg κ c r)) (by split_ifs <;> norm_num))
      (fun c => by
        have h1 : (if N.fireCount c r = m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        have h2 : N.stochasticMassActionRate κ c r ≤ N.exitRate κ c :=
          Finset.single_le_sum (f := fun r => N.stochasticMassActionRate κ c r)
            (fun r _ => N.stochasticMassActionRate_nonneg κ c r) (Finset.mem_univ r)
        have h3 := mul_nonneg (hP0 c) (N.stochasticMassActionRate_nonneg κ c r)
        calc P c * N.stochasticMassActionRate κ c r * (if N.fireCount c r = m then (1 : ℝ) else 0)
            ≤ P c * N.stochasticMassActionRate κ c r * 1 := mul_le_mul_of_nonneg_left h1 h3
          _ ≤ P c * N.exitRate κ c := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 (hP0 c)) hsum
  have hdiag : Summable fun c => P c * N.exitRate κ c * (if c = m then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {m}) fun c hc => by
      rw [Finset.mem_singleton] at hc; rw [if_neg hc, mul_zero]
  have hin : ∀ r, ∑' c, P c * N.stochasticMassActionRate κ c r *
      (if N.fireCount c r = m then (1 : ℝ) else 0) = N.cmeInflow κ P m r := by
    intro r
    rw [(N.tsum_mul_rate_fire_eq κ P (fun l => if l = m then (1 : ℝ) else 0) r (hfire r)).2]
    rw [tsum_eq_single m fun l hl => by rw [if_neg hl, zero_mul]]
    simp
  show N.cmeRHS κ P m = ∑' c, P c * (N.jumpSystem κ).Q c m
  rw [tsum_congr hQ, (summable_sum fun r _ => hfire r).tsum_sub hdiag,
    Summable.tsum_finsetSum fun r _ => hfire r]
  rw [tsum_eq_single m fun c hc => by rw [if_neg hc, mul_zero]]
  simp only [hin, if_true, mul_one, cmeRHS]

end Network
end CRNT
