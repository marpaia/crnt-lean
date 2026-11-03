import CRNT.Multistationarity.OneSpeciesCapacity

/-!
# Monostationarity of one-species networks without an alternating arrow pattern

Converse companion of `CRNT.Network.oneSpecies_multistationary_of_upDownUp`. If a one-species
network has neither an up–down–up nor a down–up–down arrow pattern at three increasing reactant
coefficients, then for every choice of rate constants whose steady-state polynomial is not
identically zero there is at most one positive steady state (Joshi–Shiu 2017, Theorem 3.6,
nondegenerate case). The identically-zero case is genuinely different: `A → 2A`, `A → 0` with
equal rates has every positive point as a steady state.

The polynomial step is an elementary one-sign-change Descartes argument: when the nonzero
coefficients change sign once, at degree `d`, the quantity `t^d p(s) − s^d p(t)` is strictly
positive for `0 < s < t`, so `p` cannot vanish at both.

Main results:
* `CRNT.Polynomial.no_two_pos_roots_of_no_alternation`.
* `CRNT.Network.oneSpecies_unique_positiveSteadyState_of_no_pattern`.
-/

namespace CRNT

open Polynomial
open scoped BigOperators

/-- An alternating sign triple among the coefficients of `P`. -/
def HasAlternatingTriple (P : ℝ[X]) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧
    ((0 < P.coeff a ∧ P.coeff b < 0 ∧ 0 < P.coeff c) ∨
      (P.coeff a < 0 ∧ 0 < P.coeff b ∧ P.coeff c < 0))

theorem hasAlternatingTriple_neg {P : ℝ[X]} : HasAlternatingTriple (-P) ↔ HasAlternatingTriple P := by
  unfold HasAlternatingTriple
  simp only [coeff_neg, neg_pos, neg_lt_zero]
  constructor <;> rintro ⟨a, b, c, hab, hbc, h⟩ <;> exact ⟨a, b, c, hab, hbc, h.symm⟩

theorem eval_eq_support_sum (P : ℝ[X]) (x : ℝ) :
    P.eval x = ∑ e ∈ P.support, P.coeff e * x ^ e := by
  rw [eval_eq_sum, Polynomial.sum_def]

/-- Core case: some positive coefficient lies below every negative one. -/
theorem no_two_pos_roots_aux (P : ℝ[X]) (d : ℕ)
    (hlow : ∀ e, 0 < P.coeff e → e < d) (hhigh : ∀ e, P.coeff e < 0 → d ≤ e)
    (hex : ∃ e, 0 < P.coeff e) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hps : P.eval s = 0) (hpt : P.eval t = 0) : False := by
  have ht : 0 < t := hs.trans hst
  have hF : ∑ e ∈ P.support, P.coeff e * (s ^ e * t ^ d - t ^ e * s ^ d) = 0 := by
    have : ∑ e ∈ P.support, P.coeff e * (s ^ e * t ^ d - t ^ e * s ^ d) =
        t ^ d * P.eval s - s ^ d * P.eval t := by
      rw [eval_eq_support_sum, eval_eq_support_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [this, hps, hpt]; ring
  have hterm : ∀ e ∈ P.support, 0 ≤ P.coeff e * (s ^ e * t ^ d - t ^ e * s ^ d) := by
    intro e _
    rcases lt_trichotomy (P.coeff e) 0 with hneg | hzero | hpos
    · have hde := hhigh e hneg
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
      have : s ^ (d + k) * t ^ d - t ^ (d + k) * s ^ d = s ^ d * t ^ d * (s ^ k - t ^ k) := by
        ring
      rw [this]
      have hk : s ^ k ≤ t ^ k := pow_le_pow_left₀ hs.le hst.le k
      have : s ^ d * t ^ d * (s ^ k - t ^ k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      nlinarith
    · rw [hzero, zero_mul]
    · have hed := hlow e hpos
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hed
      rw [hk]
      have : s ^ e * t ^ (e + k + 1) - t ^ e * s ^ (e + k + 1) =
          s ^ e * t ^ e * (t ^ (k + 1) - s ^ (k + 1)) := by ring
      rw [this]
      have : s ^ (k + 1) < t ^ (k + 1) := pow_lt_pow_left₀ hst hs.le (Nat.succ_ne_zero k)
      have : 0 ≤ s ^ e * t ^ e * (t ^ (k + 1) - s ^ (k + 1)) :=
        mul_nonneg (by positivity) (by linarith)
      positivity
  obtain ⟨e₀, he₀⟩ := hex
  have hmem : e₀ ∈ P.support := mem_support_iff.mpr he₀.ne'
  have hpos : 0 < P.coeff e₀ * (s ^ e₀ * t ^ d - t ^ e₀ * s ^ d) := by
    have hed := hlow e₀ he₀
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hed
    rw [hk]
    have : s ^ e₀ * t ^ (e₀ + k + 1) - t ^ e₀ * s ^ (e₀ + k + 1) =
        s ^ e₀ * t ^ e₀ * (t ^ (k + 1) - s ^ (k + 1)) := by ring
    rw [this]
    have : s ^ (k + 1) < t ^ (k + 1) := pow_lt_pow_left₀ hst hs.le (Nat.succ_ne_zero k)
    have : 0 < s ^ e₀ * t ^ e₀ * (t ^ (k + 1) - s ^ (k + 1)) :=
      mul_pos (by positivity) (by linarith)
    positivity
  have := Finset.sum_pos' hterm ⟨e₀, hmem, hpos⟩
  linarith

/-- **One-sign-change Descartes.** A nonzero real polynomial without an alternating sign triple
among its coefficients has at most one positive root. -/
theorem Polynomial.no_two_pos_roots_of_no_alternation {P : ℝ[X]} (hP : P ≠ 0)
    (hno : ¬ HasAlternatingTriple P) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hps : P.eval s = 0) (hpt : P.eval t = 0) : False := by
  classical
  have ht : 0 < t := hs.trans hst
  -- some coefficient is nonzero
  obtain ⟨e₀, he₀⟩ : ∃ e, P.coeff e ≠ 0 := by
    by_contra h; push Not at h; exact hP (Polynomial.ext fun n => by simp [h n])
  by_cases hposex : ∃ e, 0 < P.coeff e
  · by_cases hnegex : ∃ e, P.coeff e < 0
    · -- both signs occur
      obtain ⟨a, ha, hamin⟩ : ∃ a, 0 < P.coeff a ∧ ∀ e, 0 < P.coeff e → a ≤ e :=
        ⟨Nat.find hposex, Nat.find_spec hposex, fun e he => Nat.find_min' hposex he⟩
      obtain ⟨b, hb, hbmin⟩ : ∃ b, P.coeff b < 0 ∧ ∀ e, P.coeff e < 0 → b ≤ e :=
        ⟨Nat.find hnegex, Nat.find_spec hnegex, fun e he => Nat.find_min' hnegex he⟩
      have hab : a ≠ b := fun h => by rw [h] at ha; linarith
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · -- positives all below negatives
        refine no_two_pos_roots_aux P b (fun e he => ?_) (fun e he => hbmin e he) hposex hs hst
          hps hpt
        by_contra hle
        push Not at hle
        rcases hle.lt_or_eq with hlt' | heq
        · exact hno ⟨a, b, e, hlt, hlt', Or.inl ⟨ha, hb, he⟩⟩
        · rw [← heq] at he; linarith
      · -- negatives all below positives: apply the core case to `-P`
        have hneg : ¬ HasAlternatingTriple (-P) := by rwa [hasAlternatingTriple_neg]
        refine no_two_pos_roots_aux (-P) a (fun e he => ?_) (fun e he => ?_)
          ⟨b, by simpa using hb⟩ hs hst (by simp [hps]) (by simp [hpt])
        · rw [coeff_neg, neg_pos] at he
          by_contra hle
          push Not at hle
          rcases hle.lt_or_eq with hlt' | heq
          · exact hno ⟨b, a, e, hgt, hlt', Or.inr ⟨hb, ha, he⟩⟩
          · rw [← heq] at he; linarith
        · rw [coeff_neg, neg_lt_zero] at he
          exact hamin e he
    · -- all coefficients nonnegative, some positive: `P(s) > 0`
      push Not at hnegex
      obtain ⟨e₁, he₁⟩ := hposex
      have : 0 < P.eval s := by
        rw [eval_eq_support_sum]
        exact Finset.sum_pos' (fun e _ => mul_nonneg (hnegex e) (pow_nonneg hs.le _))
          ⟨e₁, mem_support_iff.mpr he₁.ne', mul_pos he₁ (pow_pos hs _)⟩
      linarith
  · -- all coefficients nonpositive, some negative: `P(s) < 0`
    push Not at hposex
    have he₁ : P.coeff e₀ < 0 := lt_of_le_of_ne (hposex e₀) he₀
    have : P.eval s < 0 := by
      rw [eval_eq_support_sum]
      exact Finset.sum_neg' (fun e _ => mul_nonpos_of_nonpos_of_nonneg (hposex e)
        (pow_nonneg hs.le _)) ⟨e₀, mem_support_iff.mpr he₀, mul_neg_of_neg_of_pos he₁ (pow_pos hs _)⟩
    linarith

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] [Unique S]

/-- Coefficients of the one-species polynomial. -/
theorem oneSpeciesPoly_coeff (N : Network S) (κ : RateConstants N) (m : ℕ) :
    (N.oneSpeciesPoly κ).coeff m =
      ∑ r ∈ Finset.univ.filter (fun r => (N.reaction r).source default = m),
        κ.k r * N.reactionVector r default := by
  rw [oneSpeciesPoly, finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1.symm) | (exfalso; exact h1 h2.symm)

/-- A positive (negative) coefficient needs an up (down) reaction at that reactant
coefficient. -/
theorem exists_reaction_of_coeff_pos (N : Network S) (κ : RateConstants N) {m : ℕ}
    (h : 0 < (N.oneSpeciesPoly κ).coeff m) :
    ∃ r, (N.reaction r).source default = m ∧ 0 < N.reactionVector r default := by
  rw [oneSpeciesPoly_coeff] at h
  by_contra hcon
  push Not at hcon
  have : ∑ r ∈ Finset.univ.filter (fun r => (N.reaction r).source default = m),
      κ.k r * N.reactionVector r default ≤ 0 :=
    Finset.sum_nonpos fun r hr => mul_nonpos_of_nonneg_of_nonpos (κ.positive r).le
      (hcon r (Finset.mem_filter.mp hr).2)
  linarith

theorem exists_reaction_of_coeff_neg (N : Network S) (κ : RateConstants N) {m : ℕ}
    (h : (N.oneSpeciesPoly κ).coeff m < 0) :
    ∃ r, (N.reaction r).source default = m ∧ N.reactionVector r default < 0 := by
  rw [oneSpeciesPoly_coeff] at h
  by_contra hcon
  push Not at hcon
  have : 0 ≤ ∑ r ∈ Finset.univ.filter (fun r => (N.reaction r).source default = m),
      κ.k r * N.reactionVector r default :=
    Finset.sum_nonneg fun r hr => mul_nonneg (κ.positive r).le
      (hcon r (Finset.mem_filter.mp hr).2)
  linarith

/-- An alternating arrow pattern: three reactions at increasing reactant coefficients that go
up, down, up or down, up, down. -/
def HasAlternatingArrowPattern (N : Network S) : Prop :=
  ∃ r₁ r₂ r₃ : N.R,
    (N.reaction r₁).source default < (N.reaction r₂).source default ∧
    (N.reaction r₂).source default < (N.reaction r₃).source default ∧
    ((0 < N.reactionVector r₁ default ∧ N.reactionVector r₂ default < 0 ∧
        0 < N.reactionVector r₃ default) ∨
      (N.reactionVector r₁ default < 0 ∧ 0 < N.reactionVector r₂ default ∧
        N.reactionVector r₃ default < 0))

/-- **No alternating pattern, no nondegenerate multistationarity.** -/
theorem oneSpecies_unique_positiveSteadyState_of_no_pattern (N : Network S)
    (hno : ¬ N.HasAlternatingArrowPattern) (κ : RateConstants N)
    (hP : N.oneSpeciesPoly κ ≠ 0) {x z : Concentration S} (hx : x.Positive) (hz : z.Positive)
    (hxs : N.IsMassActionSteadyState κ x) (hzs : N.IsMassActionSteadyState κ z) : x = z := by
  have hnoP : ¬ HasAlternatingTriple (N.oneSpeciesPoly κ) := by
    rintro ⟨a, b, c, hab, hbc, h⟩
    apply hno
    rcases h with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · obtain ⟨r₁, h1, u1⟩ := N.exists_reaction_of_coeff_pos κ ha
      obtain ⟨r₂, h2, u2⟩ := N.exists_reaction_of_coeff_neg κ hb
      obtain ⟨r₃, h3, u3⟩ := N.exists_reaction_of_coeff_pos κ hc
      exact ⟨r₁, r₂, r₃, by omega, by omega, Or.inl ⟨u1, u2, u3⟩⟩
    · obtain ⟨r₁, h1, u1⟩ := N.exists_reaction_of_coeff_neg κ ha
      obtain ⟨r₂, h2, u2⟩ := N.exists_reaction_of_coeff_pos κ hb
      obtain ⟨r₃, h3, u3⟩ := N.exists_reaction_of_coeff_neg κ hc
      exact ⟨r₁, r₂, r₃, by omega, by omega, Or.inr ⟨u1, u2, u3⟩⟩
  rw [eq_oneSpeciesConc x] at hxs ⊢
  rw [eq_oneSpeciesConc z] at hzs ⊢
  have hrx := (N.oneSpecies_steadyState_iff_isRoot κ _).mp hxs
  have hrz := (N.oneSpecies_steadyState_iff_isRoot κ _).mp hzs
  rcases lt_trichotomy (x default) (z default) with hlt | heq | hgt
  · exact (Polynomial.no_two_pos_roots_of_no_alternation hP hnoP (hx default) hlt hrx hrz).elim
  · rw [heq]
  · exact (Polynomial.no_two_pos_roots_of_no_alternation hP hnoP (hz default) hgt hrz hrx).elim

/-- **Joshi–Shiu characterization (nondegenerate one-species networks).** A one-species
network admits rate constants with a not identically zero steady-state polynomial and two
distinct positive steady states iff it has an alternating (up–down–up or down–up–down) arrow
pattern at three increasing reactant coefficients. -/
theorem oneSpecies_nondegenerate_multistationary_iff (N : Network S) :
    (∃ (κ : RateConstants N) (x z : Concentration S), N.oneSpeciesPoly κ ≠ 0 ∧
        x.Positive ∧ z.Positive ∧ x ≠ z ∧ N.IsMassActionSteadyState κ x ∧
          N.IsMassActionSteadyState κ z) ↔ N.HasAlternatingArrowPattern := by
  constructor
  · rintro ⟨κ, x, z, hP, hx, hz, hne, hxs, hzs⟩
    by_contra hno
    exact hne (N.oneSpecies_unique_positiveSteadyState_of_no_pattern hno κ hP hx hz hxs hzs)
  · rintro ⟨r₁, r₂, r₃, h12, h23, h | h⟩
    · obtain ⟨κ, x, z, hP, hx, hz, hne, -, hxs, hzs⟩ :=
        N.oneSpecies_multistationary_of_signed 1 one_ne_zero r₁ r₂ r₃ h12 h23
          (by linarith [h.1]) (by linarith [h.2.1]) (by linarith [h.2.2])
      exact ⟨κ, x, z, hP, hx, hz, hne, hxs, hzs⟩
    · obtain ⟨κ, x, z, hP, hx, hz, hne, -, hxs, hzs⟩ :=
        N.oneSpecies_multistationary_of_signed (-1) (by norm_num) r₁ r₂ r₃ h12 h23
          (by linarith [h.1]) (by linarith [h.2.1]) (by linarith [h.2.2])
      exact ⟨κ, x, z, hP, hx, hz, hne, hxs, hzs⟩

end Network

end CRNT
