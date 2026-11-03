import CRNT.Multistationarity.OneReactionUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fully open networks with one non-flow reaction: existence (Joshi 2013, Theorem 4.1)

`oneRxn_exists_two_steadyStates`: if `∑_{i : b_i > a_i} a_i > 1`, the fully open network with the
single non-flow reaction `a → b` has rate constants with two distinct positive steady states.
Together with `oneRxn_unique_steadyState` this gives Joshi's characterization
`oneRxn_multistationary_iff`: multistationary iff `∑_{i : b_i > a_i} a_i > 1`.

The construction is explicit.  With `A = ∑_{b_i > a_i} a_i ≥ 2`, `B = ∑_{b_i < a_i} a_i`,
`M = 2^{B+1}` and `ρ₀ = (M 2^B)^{1/A} ∈ (1, M)`, the states `1` and
`ρ = (ρ₀ on b_i > a_i, 1/2 on b_i < a_i, 1 otherwise)` are both steady for the rates
`k = 1`, `l_i = d_i (M - 1)/(ρ_i - 1)` (`1` if `d_i = 0`), `k_i = l_i - d_i`, where
`d_i = b_i - a_i`: at `1` the reaction flux is `1`, at `ρ` it is `∏ ρ_i^{a_i} = M`.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Joshi 2013, Theorem 4.1 ("if").** -/
theorem oneRxn_exists_two_steadyStates (a b : Complex S)
    (hA : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s) :
    ∃ (κ : (oneRxn a b).fullyOpen.RateConstants) (x z : Concentration S),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x ∧
        (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z := by
  classical
  set A := ∑ s ∈ univ.filter (fun s => a s < b s), a s with hAdef
  set B := ∑ s ∈ (univ.filter (fun s => ¬ a s < b s)).filter (fun s => b s < a s), a s with hBdef
  set M : ℝ := 2 ^ (B + 1) with hM
  have hM1 : 1 < M := by rw [hM]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hA0 : A ≠ 0 := by omega
  set ρ₀ : ℝ := (M * 2 ^ B) ^ ((A : ℝ)⁻¹) with hρ₀
  have hρpow : ρ₀ ^ A = M * 2 ^ B := Real.rpow_inv_natCast_pow (by positivity) hA0
  have hρnn : 0 ≤ ρ₀ := by positivity
  have hρ1 : 1 < ρ₀ := by
    by_contra h; push Not at h
    have : ρ₀ ^ A ≤ 1 := pow_le_one₀ hρnn h
    have : (1 : ℝ) < M * 2 ^ B := by nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := B)]
    linarith
  have hρM : ρ₀ < M := by
    by_contra h; push Not at h
    have h1 : M ^ A ≤ ρ₀ ^ A := pow_le_pow_left₀ (by linarith) h A
    have h2 : M ^ 2 ≤ M ^ A := pow_le_pow_right₀ hM1.le (by omega)
    have h3 : M * 2 ^ B < M ^ 2 := by
      have : (2 : ℝ) ^ B < M := by rw [hM, pow_succ]; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) B]
      nlinarith
    linarith
  -- the second state and the rates
  set d : S → ℝ := fun s => (b s : ℝ) - a s with hd
  set ρ : S → ℝ := fun s => if a s < b s then ρ₀ else if b s < a s then 1 / 2 else 1 with hρ
  set l : S → ℝ := fun s => if a s < b s then d s * (M - 1) / (ρ₀ - 1)
    else if b s < a s then d s * (M - 1) / (1 / 2 - 1) else 1 with hl
  have hdpos : ∀ s, a s < b s → 0 < d s := fun s h => by
    have : (a s : ℝ) < b s := by exact_mod_cast h
    simp only [hd]; linarith
  have hdneg : ∀ s, b s < a s → d s < 0 := fun s h => by
    have : (b s : ℝ) < a s := by exact_mod_cast h
    simp only [hd]; linarith
  have hlpos : ∀ s, 0 < l s := by
    intro s; simp only [hl]
    split_ifs with h1 h2
    · exact div_pos (mul_pos (hdpos s h1) (by linarith)) (by linarith)
    · exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (hdneg s h2) (by linarith)) (by norm_num)
    · exact one_pos
  have hkpos : ∀ s, 0 < l s - d s := by
    intro s; simp only [hl]
    split_ifs with h1 h2
    · have hd1 := hdpos s h1
      rw [sub_pos, lt_div_iff₀ (by linarith)]
      nlinarith
    · have := hdneg s h2
      have : 0 < d s * (M - 1) / (1 / 2 - 1) :=
        div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos this (by linarith)) (by norm_num)
      linarith
    · have h0 : d s = 0 := by
        have : a s = b s := by omega
        simp only [hd, this, sub_self]
      rw [h0]; norm_num
  let κ : (oneRxn a b).fullyOpen.RateConstants :=
    ⟨Sum.elim (fun _ => 1) (Sum.elim (fun s => l s - d s) l), by
      rintro (r | s | s)
      · exact one_pos
      · exact hkpos s
      · exact hlpos s⟩
  -- the monomial at `ρ`
  have hmono : a.massActionMonomial ρ = M := by
    have h1 : a.massActionMonomial ρ = ∏ s, (if a s < b s then ρ₀ ^ a s else
        if b s < a s then (1 / 2 : ℝ) ^ a s else 1) := by
      unfold Complex.massActionMonomial
      refine prod_congr rfl fun s _ => ?_
      simp only [hρ]; split_ifs <;> simp
    rw [h1, prod_ite, prod_ite, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, prod_const_one, mul_one,
      ← hAdef, ← hBdef, hρpow, div_pow, one_pow]
    field_simp
  have hmono1 : a.massActionMonomial (fun _ => (1 : ℝ)) = 1 := by
    simp [Complex.massActionMonomial]
  refine ⟨κ, fun _ => 1, ρ, fun _ => one_pos, fun s => ?_, ?_, fun s => ?_, fun s => ?_⟩
  · simp only [hρ]; split_ifs <;> linarith
  · obtain ⟨s₀, hs₀⟩ : ∃ s₀, a s₀ < b s₀ := by
      by_contra hall; push Not at hall
      have : univ.filter (fun s => a s < b s) = ∅ :=
        filter_eq_empty_iff.mpr fun s _ => not_lt.mpr (hall s)
      rw [hAdef, this, sum_empty] at hA; omega
    intro h
    have := congrFun h s₀
    simp only [hρ, if_pos hs₀] at this
    linarith
  · rw [oneRxn_fullyOpen_field, hmono1]
    show (1 : ℝ) * 1 * d s + (l s - d s) - l s * 1 = 0
    ring
  · rw [oneRxn_fullyOpen_field, hmono]
    show (1 : ℝ) * M * d s + (l s - d s) - l s * ρ s = 0
    simp only [hl, hρ]
    split_ifs with h1 h2
    · have hne : ρ₀ - 1 ≠ 0 := by linarith
      field_simp; ring
    · field_simp; ring
    · have h0 : d s = 0 := by
        have : a s = b s := by omega
        simp only [hd, this, sub_self]
      rw [h0]; ring

/-- **Joshi 2013, Theorem 4.1 (irreversible case).** The fully open network with the single
non-flow reaction `a → b` admits two distinct positive steady states for some rate constants iff
`∑_{i : b_i > a_i} a_i > 1`. -/
theorem oneRxn_multistationary_iff (a b : Complex S) :
    (∃ (κ : (oneRxn a b).fullyOpen.RateConstants) (x z : Concentration S),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x ∧
        (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z) ↔
      1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s := by
  constructor
  · rintro ⟨κ, x, z, hx, hz, hne, hxs, hzs⟩
    by_contra h; push Not at h
    exact hne (oneRxn_unique_steadyState a b h κ hx hz hxs hzs)
  · exact oneRxn_exists_two_steadyStates a b

end Network
end CRNT
