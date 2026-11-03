import CRNT.Multistationarity.OneReactionExistence

/-!
# Fully open networks with one reversible non-flow reaction: existence (Joshi 2013, Thm 4.1(2))

`revPair_exists_two_steadyStates`: the fully open network with the reversible non-flow reaction
`a ⇌ b` has rate constants with two distinct positive steady states if
`∑_{i : b_i > a_i} a_i > 1` or `∑_{i : a_i > b_i} b_i > 1` (the "if" half of Joshi's
Theorem 4.1(2)).  The construction is explicit: the steady states are `1` and `ρ`, with net fluxes
`1` and `M`; the forward and backward rates `k_f = 1 + k_r`, `k_r = M / (P_b - P_a)` solve
the two flux equations, where `P_a = ∏ ρ_i^{a_i} = 2M` and `P_b = ∏ ρ_i^{b_i} > P_a`.

The "only if" half of Theorem 4.1(2) (uniqueness when both sums are `≤ 1`) is not proved here.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network `a ⇌ b` (reaction `0 : a → b`, `1 : b → a`). -/
abbrev revPair (a b : Complex S) : Network S :=
  ⟨Fin 2, inferInstance, inferInstance, fun i => if i = 0 then ⟨a, b⟩ else ⟨b, a⟩⟩

theorem revPair_fullyOpen_field (a b : Complex S) (κ : (revPair a b).fullyOpen.RateConstants)
    (x : Concentration S) (s : S) :
    (revPair a b).fullyOpen.massActionVectorField κ x s =
      κ.k (Sum.inl 0) * a.massActionMonomial x * ((b s : ℝ) - a s) +
        κ.k (Sum.inl 1) * b.massActionMonomial x * ((a s : ℝ) - b s) +
        κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s := by
  have hrin : ((revPair a b).fullyOpen.reaction (Sum.inr (Sum.inl s))) = inflowReaction s := rfl
  have hrout : ((revPair a b).fullyOpen.reaction (Sum.inr (Sum.inr s))) = outflowReaction s := rfl
  rw [massActionVectorField_apply]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [massActionRate]
  have h1 : (∑ r : (revPair a b).R, κ.k (Sum.inl r) *
      ((revPair a b).fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x *
        (revPair a b).fullyOpen.reactionVector (Sum.inl r) s) =
      κ.k (Sum.inl 0) * a.massActionMonomial x * ((b s : ℝ) - a s) +
        κ.k (Sum.inl 1) * b.massActionMonomial x * ((a s : ℝ) - b s) := by
    rw [Fin.sum_univ_two]; erw [reactionVector_apply, reactionVector_apply]; rfl
  have h2 : (∑ s' : S, κ.k (Sum.inr (Sum.inl s')) *
      ((revPair a b).fullyOpen.reaction (Sum.inr (Sum.inl s'))).source.massActionMonomial x *
        (revPair a b).fullyOpen.reactionVector (Sum.inr (Sum.inl s')) s) =
      κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_inflow]; simp [Pi.single_apply, Ne.symm hs']) (by simp)]
    erw [reactionVector_inflow, hrin]
    simp [inflowReaction]
  have h3 : (∑ s' : S, κ.k (Sum.inr (Sum.inr s')) *
      ((revPair a b).fullyOpen.reaction (Sum.inr (Sum.inr s'))).source.massActionMonomial x *
        (revPair a b).fullyOpen.reactionVector (Sum.inr (Sum.inr s')) s) =
      -(κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_outflow]; simp [Pi.single_apply, Ne.symm hs']) (by simp)]
    erw [reactionVector_outflow, hrout]
    simp [outflowReaction, Complex.massActionMonomial, singletonComplex, Pi.single_apply]
  rw [h1, h2, h3]; ring

/-- **Explicit two-state construction for `p ⇌ q`.** If `∑_{p_i < q_i} p_i > 1`, there are positive
`k_f, k_r, k_in, l` and distinct positive `x, z` solving the steady-state equations of the fully open
network with `p ⇌ q` (forward rate `k_f`, backward rate `k_r`). -/
theorem revPair_core (p q : Complex S) (hA : 1 < ∑ s ∈ univ.filter (fun s => p s < q s), p s) :
    ∃ (kf kr : ℝ) (kin l : S → ℝ) (x z : Concentration S), 0 < kf ∧ 0 < kr ∧
      (∀ s, 0 < kin s) ∧ (∀ s, 0 < l s) ∧ x.Positive ∧ z.Positive ∧ x ≠ z ∧
      (∀ s, kf * p.massActionMonomial x * ((q s : ℝ) - p s) +
        kr * q.massActionMonomial x * ((p s : ℝ) - q s) + kin s - l s * x s = 0) ∧
      (∀ s, kf * p.massActionMonomial z * ((q s : ℝ) - p s) +
        kr * q.massActionMonomial z * ((p s : ℝ) - q s) + kin s - l s * z s = 0) := by
  classical
  set A := ∑ s ∈ univ.filter (fun s => p s < q s), p s with hAdef
  set B := ∑ s ∈ (univ.filter (fun s => ¬ p s < q s)).filter (fun s => q s < p s), p s with hBdef
  set M : ℝ := 2 ^ (B + 2) with hM
  have hM1 : 1 < M := by rw [hM]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hA0 : A ≠ 0 := by omega
  set ρ₀ : ℝ := (2 * M * 2 ^ B) ^ ((A : ℝ)⁻¹) with hρ₀
  have hρpow : ρ₀ ^ A = 2 * M * 2 ^ B := Real.rpow_inv_natCast_pow (by positivity) hA0
  have hρnn : 0 ≤ ρ₀ := by positivity
  have h2B : (1 : ℝ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have hρ1 : 1 < ρ₀ := by
    by_contra h; push Not at h
    have : ρ₀ ^ A ≤ 1 := pow_le_one₀ hρnn h
    nlinarith
  have hρM : ρ₀ < M := by
    by_contra h; push Not at h
    have h1 : M ^ A ≤ ρ₀ ^ A := pow_le_pow_left₀ (by linarith) h A
    have h2 : M ^ 2 ≤ M ^ A := pow_le_pow_right₀ hM1.le (by omega)
    have h3 : 2 * M * 2 ^ B < M ^ 2 := by
      have : 2 * (2 : ℝ) ^ B < M := by
        rw [hM, pow_add]; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) B]
      nlinarith
    linarith
  set d : S → ℝ := fun s => (q s : ℝ) - p s with hd
  set ρ : S → ℝ := fun s => if p s < q s then ρ₀ else if q s < p s then 1 / 2 else 1 with hρ
  set l : S → ℝ := fun s => if p s < q s then d s * (M - 1) / (ρ₀ - 1)
    else if q s < p s then d s * (M - 1) / (1 / 2 - 1) else 1 with hl
  have hdpos : ∀ s, p s < q s → 0 < d s := fun s h => by
    have : (p s : ℝ) < q s := by exact_mod_cast h
    simp only [hd]; linarith
  have hdneg : ∀ s, q s < p s → d s < 0 := fun s h => by
    have : (q s : ℝ) < p s := by exact_mod_cast h
    simp only [hd]; linarith
  have hd0 : ∀ s, ¬ p s < q s → ¬ q s < p s → d s = 0 := fun s h1 h2 => by
    have : p s = q s := by omega
    simp only [hd, this, sub_self]
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
    · rw [hd0 s h1 h2]; norm_num
  -- the two monomials at `ρ`
  have hρpos : ∀ s, 0 < ρ s := fun s => by simp only [hρ]; split_ifs <;> linarith
  have hPa : p.massActionMonomial ρ = 2 * M := by
    have h1 : p.massActionMonomial ρ = ∏ s, (if p s < q s then ρ₀ ^ p s else
        if q s < p s then (1 / 2 : ℝ) ^ p s else 1) := by
      unfold Complex.massActionMonomial
      refine prod_congr rfl fun s _ => ?_
      simp only [hρ]; split_ifs <;> simp
    rw [h1, prod_ite, prod_ite, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, prod_const_one, mul_one,
      ← hAdef, ← hBdef, hρpow, div_pow, one_pow]
    field_simp
  have hPb : p.massActionMonomial ρ < q.massActionMonomial ρ := by
    unfold Complex.massActionMonomial
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, p s₀ < q s₀ := by
      by_contra hall; push Not at hall
      have : univ.filter (fun s => p s < q s) = ∅ :=
        filter_eq_empty_iff.mpr fun s _ => not_lt.mpr (hall s)
      rw [hAdef, this, sum_empty] at hA; omega
    refine prod_lt_prod₀ (fun s _ => pow_pos (hρpos s) _) (fun s _ => ?_)
      ⟨s₀, mem_univ _, ?_⟩
    · simp only [hρ]
      split_ifs with h1 h2
      · exact pow_le_pow_right₀ hρ1.le h1.le
      · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h2.le
      · have : p s = q s := by omega
        rw [this]
    · simp only [hρ, if_pos hs₀]
      exact pow_lt_pow_right₀ hρ1 hs₀
  set Pb := q.massActionMonomial ρ with hPbdef
  set kr : ℝ := M / (Pb - 2 * M) with hkr
  have hkrpos : 0 < kr := div_pos (by linarith) (by rw [← hPa]; linarith)
  have hmono1 : ∀ c : Complex S, c.massActionMonomial (fun _ => (1 : ℝ)) = 1 := fun c => by
    simp [Complex.massActionMonomial]
  refine ⟨1 + kr, kr, fun s => l s - d s, l, fun _ => 1, ρ, by linarith, hkrpos, hkpos, hlpos,
    fun _ => one_pos, hρpos, ?_, fun s => ?_, fun s => ?_⟩
  · obtain ⟨s₀, hs₀⟩ : ∃ s₀, p s₀ < q s₀ := by
      by_contra hall; push Not at hall
      have : univ.filter (fun s => p s < q s) = ∅ :=
        filter_eq_empty_iff.mpr fun s _ => not_lt.mpr (hall s)
      rw [hAdef, this, sum_empty] at hA; omega
    intro h
    have := congrFun h s₀
    simp only [hρ, if_pos hs₀] at this
    linarith
  · rw [hmono1, hmono1]; simp only [hd]; ring
  · rw [hPa]
    have hne : Pb - 2 * M ≠ 0 := by rw [← hPa]; linarith
    have hflux : (1 + kr) * (2 * M) - kr * Pb = M := by
      have h : kr * (Pb - 2 * M) = M := by rw [hkr]; exact div_mul_cancel₀ M hne
      linear_combination (-1 : ℝ) * h
    have e : (1 + kr) * (2 * M) * ((q s : ℝ) - p s) + kr * Pb * ((p s : ℝ) - q s) +
        (l s - d s) - l s * ρ s =
        ((1 + kr) * (2 * M) - kr * Pb) * d s + (l s - d s) - l s * ρ s := by
      simp only [hd]; ring
    rw [e, hflux]
    simp only [hl, hρ]
    split_ifs with h1 h2
    · have hne1 : ρ₀ - 1 ≠ 0 := by linarith
      field_simp; ring
    · field_simp; ring
    · rw [hd0 s h1 h2]; ring


/-- **Joshi 2013, Theorem 4.1(2) ("if").** The fully open network with the reversible non-flow
reaction `a ⇌ b` has rate constants with two distinct positive steady states whenever
`∑_{i : b_i > a_i} a_i > 1` or `∑_{i : a_i > b_i} b_i > 1`. -/
theorem revPair_exists_two_steadyStates (a b : Complex S)
    (h : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s ∨
      1 < ∑ s ∈ univ.filter (fun s => b s < a s), b s) :
    ∃ (κ : (revPair a b).fullyOpen.RateConstants) (x z : Concentration S),
      x.Positive ∧ z.Positive ∧ x ≠ z ∧ (revPair a b).fullyOpen.IsMassActionSteadyState κ x ∧
        (revPair a b).fullyOpen.IsMassActionSteadyState κ z := by
  rcases h with h | h
  · obtain ⟨kf, kr, kin, l, x, z, hkf, hkr, hkin, hl, hx, hz, hne, hxs, hzs⟩ := revPair_core a b h
    let κ : (revPair a b).fullyOpen.RateConstants :=
      ⟨Sum.elim (fun i => if i = 0 then kf else kr) (Sum.elim kin l), by
        rintro (i | s | s)
        · show 0 < (if i = 0 then kf else kr); split_ifs <;> assumption
        · exact hkin s
        · exact hl s⟩
    refine ⟨κ, x, z, hx, hz, hne, fun s => ?_, fun s => ?_⟩
    · rw [revPair_fullyOpen_field]; exact hxs s
    · rw [revPair_fullyOpen_field]; exact hzs s
  · obtain ⟨kf, kr, kin, l, x, z, hkf, hkr, hkin, hl, hx, hz, hne, hxs, hzs⟩ := revPair_core b a h
    let κ : (revPair a b).fullyOpen.RateConstants :=
      ⟨Sum.elim (fun i => if i = 0 then kr else kf) (Sum.elim kin l), by
        rintro (i | s | s)
        · show 0 < (if i = 0 then kr else kf); split_ifs <;> assumption
        · exact hkin s
        · exact hl s⟩
    refine ⟨κ, x, z, hx, hz, hne, fun s => ?_, fun s => ?_⟩
    · rw [revPair_fullyOpen_field]
      have := hxs s
      show kr * a.massActionMonomial x * ((b s : ℝ) - a s) +
        kf * b.massActionMonomial x * ((a s : ℝ) - b s) + kin s - l s * x s = 0
      linarith
    · rw [revPair_fullyOpen_field]
      have := hzs s
      show kr * a.massActionMonomial z * ((b s : ℝ) - a s) +
        kf * b.massActionMonomial z * ((a s : ℝ) - b s) + kin s - l s * z s = 0
      linarith

end Network
end CRNT
