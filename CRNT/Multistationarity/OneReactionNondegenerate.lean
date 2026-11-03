import CRNT.Multistationarity.OneReactionExistence
import CRNT.Multistationarity.TwoReactionNondegenerate
import CRNT.Open.Augmentation

/-!
# Nondegenerate multistationarity of fully open one-reaction networks (Joshi 2013)

The fully open network with the single non-flow reaction `a → b` has two distinct
**nondegenerate** positive steady states for some rate constants iff `∑_{i : b_i > a_i} a_i > 1`
(`oneRxn_nondegMultistationary_iff`).

The Jacobian at `x` is `u ↦ κ₀ (∇x^a · u) (b − a) − l ⊙ u` (`oneRxn_jacobian_apply`), so it is
injective as soon as `S(x) = κ₀ x^a ∑_j a_j (b_j − a_j)/(x_j l_j) ≠ 1`
(`oneRxn_nondegenerate_of_ne_one`). The steady states `1` and `ρ` of the existence construction
of `OneReactionExistence`, run with a free large parameter `M` in place of `2^{B+1}`, satisfy
`S(1) ≤ A(ρ₀ − 1)/(M − 1) < 1` and `S(ρ) = M (A(1 − 1/ρ₀) − B)/(M − 1) ≠ 1`
(`oneRxn_exists_two_nondegenerate_steadyStates`).
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The Jacobian of the fully open one-reaction network.** -/
theorem oneRxn_jacobian_apply (a b : Complex S) (κ : (oneRxn a b).fullyOpen.RateConstants)
    (x u : Concentration S) (s : S) :
    (oneRxn a b).fullyOpen.massActionJacobianCLM κ x u s =
      κ.k (Sum.inl ()) * (∑ j, massActionMonomialGrad a x j * u j) * ((b s : ℝ) - a s) -
        κ.k (Sum.inr (Sum.inr s)) * u s := by
  set g : Concentration S → Concentration S := fun x s =>
    κ.k (Sum.inl ()) * a.massActionMonomial x * ((b s : ℝ) - a s) +
      κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s with hg
  have hfg : (fun x => (oneRxn a b).fullyOpen.massActionVectorField κ x) = g := by
    funext x s; exact oneRxn_fullyOpen_field a b κ x s
  set d : Concentration S := fun s => (b s : ℝ) - a s with hd
  set Lgrad : Concentration S →L[ℝ] ℝ :=
    ∑ j, massActionMonomialGrad a x j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j
    with hLgrad
  set Ldiag : Concentration S →L[ℝ] Concentration S :=
    ContinuousLinearMap.pi fun s => κ.k (Sum.inr (Sum.inr s)) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hLdiag
  have h1 : HasFDerivAt (fun y : Concentration S => (κ.k (Sum.inl ()) * a.massActionMonomial y) • d)
      ((κ.k (Sum.inl ()) • Lgrad).smulRight d) x :=
    ((massActionMonomial_hasFDerivAt a x).const_mul (κ.k (Sum.inl ()))).smul_const d
  have h2 : HasFDerivAt (fun _ : Concentration S => fun s => κ.k (Sum.inr (Sum.inl s)))
      (0 : Concentration S →L[ℝ] Concentration S) x := hasFDerivAt_const _ _
  have h3 : HasFDerivAt (fun y : Concentration S => Ldiag y) Ldiag x := Ldiag.hasFDerivAt
  have h := (h1.add h2).sub h3
  have hgeq : (((fun y => (κ.k (Sum.inl ()) * a.massActionMonomial y) • d) +
      fun _ s => κ.k (Sum.inr (Sum.inl s))) - fun y => Ldiag y) = g := by
    funext y s
    simp only [hg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hLdiag,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, hd]
  rw [hgeq] at h
  have hJ := ((oneRxn a b).fullyOpen.massActionVectorField_hasFDerivAt κ x)
  rw [hfg] at hJ
  rw [hJ.unique h]
  simp [hLgrad, hLdiag, hd, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- The nondegeneracy index `S(x) = κ₀ x^a ∑_j a_j (b_j − a_j)/(x_j l_j)`. -/
noncomputable def oneRxnIndex (a b : Complex S) (κ : (oneRxn a b).fullyOpen.RateConstants)
    (x : Concentration S) : ℝ :=
  κ.k (Sum.inl ()) * a.massActionMonomial x *
    ∑ j, (a j : ℝ) * ((b j : ℝ) - a j) / (x j * κ.k (Sum.inr (Sum.inr j)))

/-- **Nondegeneracy criterion.** -/
theorem oneRxn_nondegenerate_of_ne_one (a b : Complex S)
    (κ : (oneRxn a b).fullyOpen.RateConstants) {x : Concentration S} (hx : x.Positive)
    (hS : oneRxnIndex a b κ x ≠ 1) : (oneRxn a b).fullyOpen.IsNondegenerateSteadyState κ x := by
  intro u _ hu
  set G := ∑ j, massActionMonomialGrad a x j * u j with hG
  have hl : ∀ s, 0 < κ.k (Sum.inr (Sum.inr s)) := fun s => κ.positive _
  have hus : ∀ s, u s = κ.k (Sum.inl ()) * G * ((b s : ℝ) - a s) / κ.k (Sum.inr (Sum.inr s)) := by
    intro s
    have h := congrFun hu s
    rw [oneRxn_jacobian_apply] at h
    simp only [Pi.zero_apply] at h
    rw [eq_div_iff (hl s).ne']
    linarith
  have hGS : G = G * oneRxnIndex a b κ x := by
    conv_lhs => rw [hG]
    simp only [massActionMonomialGrad_eq_of_pos a hx, hus, oneRxnIndex, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hxj := (hx j).ne'
    have hlj := (hl j).ne'
    field_simp
  have hG0 : G = 0 := by
    by_contra h
    exact hS (by
      have := hGS
      field_simp at this
      linarith [this])
  funext s
  rw [hus s, hG0]
  simp

set_option maxHeartbeats 1600000 in
/-- **Joshi 2013, nondegenerate form.** -/
theorem oneRxn_exists_two_nondegenerate_steadyStates (a b : Complex S)
    (hA : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s) :
    ∃ (κ : (oneRxn a b).fullyOpen.RateConstants) (x z : Concentration S),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x ∧
        (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z ∧
        (oneRxn a b).fullyOpen.IsNondegenerateSteadyState κ x ∧
        (oneRxn a b).fullyOpen.IsNondegenerateSteadyState κ z := by
  classical
  set A := ∑ s ∈ univ.filter (fun s => a s < b s), a s with hAdef
  set B := ∑ s ∈ (univ.filter (fun s => ¬ a s < b s)).filter (fun s => b s < a s), a s with hBdef
  set M : ℝ := 4 * (A : ℝ) ^ 2 * 2 ^ B + (A : ℝ) ^ A + 2 ^ B + 2 with hM
  have h2B : (0 : ℝ) < 2 ^ B := by positivity
  have hAA : (0 : ℝ) ≤ (A : ℝ) ^ A := by positivity
  have hA2 : (0 : ℝ) ≤ 4 * (A : ℝ) ^ 2 * 2 ^ B := by positivity
  have hM1 : 1 < M := by rw [hM]; linarith
  have hM2 : 2 < M := by rw [hM]; linarith
  have hM2B : (2 : ℝ) ^ B < M := by rw [hM]; linarith
  have hMA : (A : ℝ) ^ A < M := by rw [hM]; linarith
  have hM4 : 4 * (A : ℝ) ^ 2 * 2 ^ B ≤ M := by rw [hM]; linarith
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
    have h3 : M * 2 ^ B < M ^ 2 := by nlinarith
    linarith
  have hρA : (A : ℝ) < ρ₀ := by
    by_contra h; push Not at h
    have h1 : ρ₀ ^ A ≤ (A : ℝ) ^ A := pow_le_pow_left₀ hρnn h A
    have h2 : M ≤ M * 2 ^ B := le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  have hρsq : ρ₀ ^ 2 ≤ M * 2 ^ B := by
    rw [← hρpow]; exact pow_le_pow_right₀ hρ1.le (by omega)
  have hAρ : (A : ℝ) * ρ₀ ≤ M / 2 := by
    have h1 : ((A : ℝ) * ρ₀) ^ 2 ≤ (M / 2) ^ 2 := by
      have : ((A : ℝ) * ρ₀) ^ 2 = (A : ℝ) ^ 2 * ρ₀ ^ 2 := by ring
      rw [this]
      have h2 : (A : ℝ) ^ 2 * ρ₀ ^ 2 ≤ (A : ℝ) ^ 2 * (M * 2 ^ B) :=
        mul_le_mul_of_nonneg_left hρsq (by positivity)
      have h3 : (A : ℝ) ^ 2 * (M * 2 ^ B) ≤ M / 4 * M := by
        have : (A : ℝ) ^ 2 * 2 ^ B ≤ M / 4 := by linarith
        nlinarith
      nlinarith
    have h4 : 0 ≤ M / 2 := by linarith
    exact (pow_le_pow_iff_left₀ (by positivity) h4 (by norm_num)).mp h1
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
  have hρpos : ∀ s, 0 < ρ s := fun s => by simp only [hρ]; split_ifs <;> linarith
  refine ⟨κ, fun _ => 1, ρ, fun _ => one_pos, hρpos, ?_, fun s => ?_, fun s => ?_, ?_, ?_⟩
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
  · -- nondegeneracy at `1`
    refine oneRxn_nondegenerate_of_ne_one a b κ (fun _ => one_pos) (ne_of_lt ?_)
    have hk0 : κ.k (Sum.inl ()) = 1 := rfl
    have hlk : ∀ s, κ.k (Sum.inr (Sum.inr s)) = l s := fun s => rfl
    unfold oneRxnIndex
    rw [hk0, hmono1, one_mul, one_mul]
    simp only [hlk, one_mul]
    have hterm : ∀ j, (a j : ℝ) * ((b j : ℝ) - a j) / l j ≤
        if a j < b j then (a j : ℝ) * ((ρ₀ - 1) / (M - 1)) else 0 := by
      intro j
      have hlj := hlpos j
      simp only [hl]
      split_ifs with h1 h2
      · have hdj := hdpos j h1
        have hne : ρ₀ - 1 ≠ 0 := by linarith
        have hne' : M - 1 ≠ 0 := by linarith
        rw [div_le_iff₀ (by simpa [hl, h1] using hlj)]
        apply le_of_eq
        simp only [hd] at hdj ⊢
        field_simp
      · have hdj := hdneg j h2
        have : (a j : ℝ) * ((b j : ℝ) - a j) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by simp only [hd] at hdj; linarith)
        exact div_nonpos_of_nonpos_of_nonneg this (by simpa [hl, h1, h2] using hlj.le)
      · have h0 : (b j : ℝ) - a j = 0 := by
          have : a j = b j := by omega
          rw [this, sub_self]
        rw [h0]; simp
    have hsum : ∑ j, (a j : ℝ) * ((b j : ℝ) - a j) / l j ≤ (A : ℝ) * ((ρ₀ - 1) / (M - 1)) := by
      calc ∑ j, (a j : ℝ) * ((b j : ℝ) - a j) / l j
          ≤ ∑ j, (if a j < b j then (a j : ℝ) * ((ρ₀ - 1) / (M - 1)) else 0) :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = (A : ℝ) * ((ρ₀ - 1) / (M - 1)) := by
            rw [← Finset.sum_filter, ← Finset.sum_mul, hAdef]
            push_cast; rfl
    have hfin : (A : ℝ) * ((ρ₀ - 1) / (M - 1)) < 1 := by
      rw [← mul_div_assoc, div_lt_one (by linarith)]
      nlinarith
    linarith
  · -- nondegeneracy at `ρ`
    refine oneRxn_nondegenerate_of_ne_one a b κ hρpos ?_
    have hk0 : κ.k (Sum.inl ()) = 1 := rfl
    have hlk : ∀ s, κ.k (Sum.inr (Sum.inr s)) = l s := fun s => rfl
    unfold oneRxnIndex
    rw [hk0, hmono, one_mul]
    simp only [hlk]
    have hterm : ∀ j, (a j : ℝ) * ((b j : ℝ) - a j) / (ρ j * l j) =
        if a j < b j then (a j : ℝ) * ((ρ₀ - 1) / (ρ₀ * (M - 1)))
        else if b j < a j then -((a j : ℝ) / (M - 1)) else 0 := by
      intro j
      simp only [hρ, hl]
      split_ifs with h1 h2
      · have hdj := hdpos j h1
        have hne : ρ₀ - 1 ≠ 0 := by linarith
        have hne' : M - 1 ≠ 0 := by linarith
        have hρ0 : ρ₀ ≠ 0 := by linarith
        simp only [hd] at hdj ⊢
        field_simp
      · have hdj := hdneg j h2
        have hne' : M - 1 ≠ 0 := by linarith
        simp only [hd] at hdj ⊢
        have hne'' : (b j : ℝ) - a j ≠ 0 := by linarith
        field_simp
        ring
      · have h0 : (b j : ℝ) - a j = 0 := by
          have : a j = b j := by omega
          rw [this, sub_self]
        rw [h0]; simp
    have hsum : ∑ j, (a j : ℝ) * ((b j : ℝ) - a j) / (ρ j * l j) =
        (A : ℝ) * ((ρ₀ - 1) / (ρ₀ * (M - 1))) - (B : ℝ) / (M - 1) := by
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite, Finset.sum_ite,
        Finset.sum_const_zero, add_zero, ← Finset.sum_mul, Finset.sum_neg_distrib,
        ← Finset.sum_div, hAdef, hBdef]
      push_cast; ring
    rw [hsum]
    intro hcontra
    have hM1' : 0 < M - 1 := by linarith
    have hρ0 : 0 < ρ₀ := by linarith
    have key : M * ((A : ℝ) - A / ρ₀ - B) = M - 1 := by
      have e : M * ((A : ℝ) * ((ρ₀ - 1) / (ρ₀ * (M - 1))) - (B : ℝ) / (M - 1)) =
          M * ((A : ℝ) - A / ρ₀ - B) / (M - 1) := by
        field_simp
      rw [e, div_eq_one_iff_eq hM1'.ne'] at hcontra
      exact hcontra
    have hAρ' : (A : ℝ) / ρ₀ < 1 := by rw [div_lt_one hρ0]; exact hρA
    have hMρ : 1 < M / ρ₀ := by rw [one_lt_div hρ0]; exact hρM
    have hA2' : (2 : ℝ) ≤ A := by exact_mod_cast hA
    rcases le_or_gt A (B + 1) with hAB | hAB
    · have hAB' : (A : ℝ) - B ≤ 1 := by
        have : (A : ℝ) ≤ B + 1 := by exact_mod_cast hAB
        linarith
      have h1 : M * ((A : ℝ) - A / ρ₀ - B) ≤ M * (1 - A / ρ₀) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2 : M * (A / ρ₀) = (M / ρ₀) * A := by ring
      have h3 : (M / ρ₀) * A > A := by
        have := mul_lt_mul_of_pos_right hMρ (show (0 : ℝ) < A by linarith)
        linarith
      have h5 : M * (1 - A / ρ₀) = M - M * (A / ρ₀) := by ring
      linarith
    · have hAB' : (2 : ℝ) ≤ A - B := by
        have : (B : ℝ) + 2 ≤ A := by exact_mod_cast hAB
        linarith
      have h1 : M * (2 - A / ρ₀) ≤ M * ((A : ℝ) - A / ρ₀ - B) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2 : M * (A / ρ₀) < M := by
        have := mul_lt_mul_of_pos_left hAρ' (show (0 : ℝ) < M by linarith)
        linarith
      have h5 : M * (2 - A / ρ₀) = 2 * M - M * (A / ρ₀) := by ring
      linarith


/-- **Joshi 2013 (nondegenerate form).** The fully open network with the single non-flow reaction
`a → b` is nondegenerately multistationary iff `∑_{i : b_i > a_i} a_i > 1`. -/
theorem oneRxn_nondegMultistationary_iff (a b : Complex S) :
    (oneRxn a b).fullyOpen.HasNondegenerateMultistationarity ↔
      1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s := by
  constructor
  · intro h
    obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩ := h.capacity
    exact (oneRxn_multistationary_iff a b).mp ⟨κ, x, y, hx.2, hy.2, hne, hsx, hsy⟩
  · intro hA
    obtain ⟨κ, x, z, hx, hz, hne, hsx, hsz, hnx, hnz⟩ :=
      oneRxn_exists_two_nondegenerate_steadyStates a b hA
    have htop := stoichSubspace_fullyOpen_eq_top (oneRxn a b)
    refine ⟨κ, x, x, z, ⟨?_, hx⟩, ⟨?_, hz⟩, hsx, hsz, hne, hnx, hnz⟩
    · show x - x ∈ (oneRxn a b).fullyOpen.stoichSubspace
      rw [htop]; exact Submodule.mem_top
    · show z - x ∈ (oneRxn a b).fullyOpen.stoichSubspace
      rw [htop]; exact Submodule.mem_top

end Network
end CRNT
