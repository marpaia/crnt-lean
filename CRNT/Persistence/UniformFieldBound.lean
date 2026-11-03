import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# A field lower bound uniform in bounded rate constants

`exists_field_lower_bound_uniform`: on the nonnegative part of a box, every mass-action field
whose rate constants are bounded by `K` satisfies `f_s(x) ≥ −L · x_s`, with `L` depending only on
`K` and the box.  Same proof as `Network.exists_field_lower_bound`, with `κ.k r` replaced by `K`
in the constant.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem exists_field_lower_bound_uniform (N : Network S) {K : ℝ} (hK0 : 0 ≤ K) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ κ : N.RateConstants, (∀ r, κ.k r ≤ K) →
      ∀ x : Concentration S, x.Nonnegative → (∀ s, x s ≤ B) →
      ∀ s, -(L * x s) ≤ N.massActionVectorField κ x s := by
  have hBmnn : (0:ℝ) ≤ max 1 B := le_trans zero_le_one (le_max_left _ _)
  have hBm1 : (1:ℝ) ≤ max 1 B := le_max_left _ _
  refine ⟨∑ s', ∑ r : N.R,
      K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|, ?_, ?_⟩
  · refine Finset.sum_nonneg fun s' _ => Finset.sum_nonneg fun r _ => ?_
    exact mul_nonneg (mul_nonneg hK0 (pow_nonneg hBmnn _)) (abs_nonneg _)
  · intro κ hK x hx hxB s
    rw [massActionVectorField_apply]
    have hxle : ∀ s', x s' ≤ max 1 B := fun s' => le_trans (hxB s') (le_max_right 1 B)
    have hcoef_nn : ∀ r : N.R,
        0 ≤ K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| :=
      fun r => mul_nonneg (mul_nonneg hK0 (pow_nonneg hBmnn _)) (abs_nonneg _)
    have hterm : ∀ r : N.R,
        -(K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s)
          ≤ N.massActionRate κ r x * N.reactionVector r s := by
      intro r
      by_cases hΔ : 0 ≤ N.reactionVector r s
      · have h1 : 0 ≤ N.massActionRate κ r x * N.reactionVector r s :=
          mul_nonneg (N.massActionRate_nonneg κ r hx) hΔ
        have h2 : 0 ≤ K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') *
            |N.reactionVector r s| * x s := mul_nonneg (hcoef_nn r) (hx s)
        linarith
      · rw [not_le] at hΔ
        -- consuming reaction: factor out `x s`
        have hts : (N.reaction r).target s < (N.reaction r).source s := by
          rw [reactionVector_apply] at hΔ
          have : ((N.reaction r).target s : ℝ) < ((N.reaction r).source s : ℝ) := by linarith
          exact_mod_cast this
        have hsrc1 : 1 ≤ (N.reaction r).source s := by omega
        have hmono_eq : (N.reaction r).source.massActionMonomial x
            = x s * (x s ^ ((N.reaction r).source s - 1)
                * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s') := by
          have h1 : (N.reaction r).source.massActionMonomial x
              = x s ^ (N.reaction r).source s
                * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s' := by
            show (∏ s', x s' ^ (N.reaction r).source s') = _
            exact (Finset.mul_prod_erase Finset.univ
              (fun s' => x s' ^ (N.reaction r).source s') (Finset.mem_univ s)).symm
          rw [h1]
          have h2 : x s ^ (N.reaction r).source s = x s * x s ^ ((N.reaction r).source s - 1) := by
            conv_lhs => rw [show (N.reaction r).source s = ((N.reaction r).source s - 1) + 1 from by omega]
            rw [pow_succ']
          rw [h2, mul_assoc]
        set P := x s ^ ((N.reaction r).source s - 1)
          * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s' with hP
        have hPnn : 0 ≤ P :=
          mul_nonneg (pow_nonneg (hx s) _) (Finset.prod_nonneg fun s' _ => pow_nonneg (hx s') _)
        have hPle : P ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') := by
          have h1 : x s ^ ((N.reaction r).source s - 1) ≤ (max 1 B) ^ ((N.reaction r).source s - 1) :=
            pow_le_pow_left₀ (hx s) (hxle s) _
          have h2 : (∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s')
              ≤ ∏ s' ∈ Finset.univ.erase s, (max 1 B) ^ (N.reaction r).source s' :=
            Finset.prod_le_prod₀ (fun s' _ => pow_nonneg (hx s') _)
              (fun s' _ => pow_le_pow_left₀ (hx s') (hxle s') _)
          have hsum_eq : (N.reaction r).source s + ∑ s' ∈ Finset.univ.erase s, (N.reaction r).source s'
              = ∑ s'', (N.reaction r).source s'' :=
            Finset.add_sum_erase Finset.univ (fun s' => (N.reaction r).source s') (Finset.mem_univ s)
          calc P ≤ (max 1 B) ^ ((N.reaction r).source s - 1)
                    * ∏ s' ∈ Finset.univ.erase s, (max 1 B) ^ (N.reaction r).source s' :=
                mul_le_mul h1 h2 (Finset.prod_nonneg fun s' _ => pow_nonneg (hx s') _)
                  (pow_nonneg hBmnn _)
            _ = (max 1 B) ^ ((N.reaction r).source s - 1
                  + ∑ s' ∈ Finset.univ.erase s, (N.reaction r).source s') := by
                rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
            _ ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') :=
                pow_le_pow_right₀ hBm1 (by omega)
        have hrate_eq : N.massActionRate κ r x = κ.k r * (x s * P) := by
          show κ.k r * (N.reaction r).source.massActionMonomial x = κ.k r * (x s * P)
          rw [hmono_eq]
        have hkey : -(K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|)
            ≤ κ.k r * P * N.reactionVector r s := by
          have hPbound : κ.k r * P ≤ K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') :=
            mul_le_mul (hK r) hPle hPnn hK0
          have hRHS : κ.k r * P * N.reactionVector r s
              = -(κ.k r * P * |N.reactionVector r s|) := by rw [abs_of_neg hΔ]; ring
          rw [hRHS]
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_right hPbound (abs_nonneg _)
        have e1 : -(K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s)
            = x s * -(K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|) := by
          ring
        have e2 : x s * (κ.k r * P * N.reactionVector r s)
            = N.massActionRate κ r x * N.reactionVector r s := by rw [hrate_eq]; ring
        rw [e1, ← e2]
        exact mul_le_mul_of_nonneg_left hkey (hx s)
    have hinner_le : (∑ r : N.R,
          K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|)
        ≤ ∑ s', ∑ r : N.R,
          K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'| :=
      Finset.single_le_sum
        (f := fun s' => ∑ r : N.R,
          K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|)
        (fun s' _ => Finset.sum_nonneg fun r _ =>
          mul_nonneg (mul_nonneg hK0 (pow_nonneg hBmnn _)) (abs_nonneg _))
        (Finset.mem_univ s)
    calc -((∑ s', ∑ r : N.R,
            K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|) * x s)
        ≤ -((∑ r : N.R,
            K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|) * x s) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_right hinner_le (hx s)
      _ = ∑ r : N.R,
            -(K * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      _ ≤ ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s :=
          Finset.sum_le_sum fun r _ => hterm r
end Network
end CRNT
