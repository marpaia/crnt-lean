import CRNT.Multistationarity.Capacity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Networks with two reactions (Joshi–Shiu 2017, Theorem 5.1)

Joshi and Shiu ("Which small reaction networks are multistationary?", SIAM J. Appl. Dyn. Syst.
16, 2017, Theorem 5.1) classify the multistationary networks with two irreversible reactions
`y → y'` and `z → z'`: with `β_s = (y'_s − y_s)(z_s − y_s)`, the network is multistationary iff
(1) the reaction vectors are negative multiples of each other, `y' − y = −λ (z' − z)`, `λ > 0`,
and (2) `β` is zero or has a positive and a negative coordinate.

This module proves the theorem (`twoRxn_multistationary_iff`).

* `twoRxn y y' z z'`: the network.
* `twoRxn_negMultiple_of_steadyState`: a positive steady state forces (1).
* `twoRxn_beta_of_multistationary`: multistationarity forces (2). Along a class
  `x₁ + τ v`, the steady states are the solutions of `∑_s (z_s − y_s) log x_s = const`, and the
  derivative of the left side is `∑_s β_s / x_s`; if `β` has one sign and is not zero, it is
  strictly monotone.
* `twoRxn_multistationary_of_beta_zero`: if `β = 0` and (1) holds, every point of some class is a
  steady state.
* `twoRxn_multistationary_of_beta_mixed`: if `β` has both signs and (1) holds, two explicit
  positive points `a` and `a + (y' − y)` have the same value of `x^{z − y}`; matching `κ₁/κ₀` to
  it makes both steady states (`exists_log_step` solves for the coordinates of `a`).
* `twoRxn_multistationary_iff`: the theorem.

Not formalized here: the nondegeneracy statements (Joshi–Shiu Theorem 5.2) and the reversible
cases (Theorems 5.8, 5.12).
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network with the two reactions `y → y'` (index `0`) and `z → z'` (index `1`). -/
def twoRxn (y y' z z' : Complex S) : Network S :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨y, y'⟩ else ⟨z, z'⟩⟩

section

variable (y y' z z' : Complex S)

theorem twoRxn_reaction_zero : (twoRxn y y' z z').reaction (0 : Fin 2) = ⟨y, y'⟩ := rfl
theorem twoRxn_reaction_one : (twoRxn y y' z z').reaction (1 : Fin 2) = ⟨z, z'⟩ := rfl

theorem twoRxn_sum (g : (twoRxn y y' z z').R → ℝ) :
    ∑ r, g r = g (0 : Fin 2) + g (1 : Fin 2) := Fin.sum_univ_two g

/-- The reaction vectors `v = y' − y`, `w = z' − z` as real vectors. -/
noncomputable def rv (a b : Complex S) : S → ℝ := fun s => (b s : ℝ) - a s

/-- `β_s = (y'_s − y_s)(z_s − y_s)`. -/
noncomputable def twoBeta : S → ℝ := fun s => ((y' s : ℝ) - y s) * ((z s : ℝ) - y s)

theorem twoRxn_field (κ : RateConstants (twoRxn y y' z z')) (x : Concentration S) (s : S) :
    (twoRxn y y' z z').massActionVectorField κ x s =
      κ.k (0 : Fin 2) * y.massActionMonomial x * rv y y' s +
        κ.k (1 : Fin 2) * z.massActionMonomial x * rv z z' s := by
  rw [massActionVectorField_apply, twoRxn_sum]
  rfl

end

variable {y y' z z' : Complex S}

omit [DecidableEq S] [Fintype S] in
theorem exists_ne_of_complex_ne (h : y ≠ y') : ∃ s, rv y y' s ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  funext s
  have := hno s
  simp only [rv, sub_eq_zero] at this
  exact_mod_cast this.symm

/-- **Condition (1) is necessary.** A positive steady state forces `y' − y = −λ (z' − z)` with
`λ = κ₁ x^z / (κ₀ x^y) > 0`. -/
theorem twoRxn_negMultiple_of_steadyState (κ : RateConstants (twoRxn y y' z z'))
    {x : Concentration S} (hx : x.Positive)
    (hss : (twoRxn y y' z z').IsMassActionSteadyState κ x) :
    ∀ s, rv y y' s = -(κ.k (1 : Fin 2) * z.massActionMonomial x /
      (κ.k (0 : Fin 2) * y.massActionMonomial x)) * rv z z' s := by
  intro s
  have h := hss s
  have hfield := twoRxn_field y y' z z' κ x s
  have h0 : 0 < κ.k (0 : Fin 2) * y.massActionMonomial x :=
    mul_pos (κ.positive _) (Complex.massActionMonomial_pos hx _)
  rw [show (twoRxn y y' z z').massActionVectorField κ x s = 0 from h] at hfield
  have hB := h0.ne'
  calc rv y y' s = (κ.k (0 : Fin 2) * y.massActionMonomial x * rv y y' s) /
        (κ.k (0 : Fin 2) * y.massActionMonomial x) := (mul_div_cancel_left₀ _ hB).symm
    _ = (-(κ.k (1 : Fin 2) * z.massActionMonomial x * rv z z' s)) /
        (κ.k (0 : Fin 2) * y.massActionMonomial x) := by congr 1; linarith
    _ = _ := by ring

/-- The class of `x₁` contains `x₂` along the reaction vector `y' − y`. -/
theorem twoRxn_exists_line (κ : RateConstants (twoRxn y y' z z'))
    {x₁ x₂ : Concentration S} (hx₁ : x₁.Positive)
    (hss : (twoRxn y y' z z').IsMassActionSteadyState κ x₁)
    (hc : (twoRxn y y' z z').StoichCompatible x₁ x₂) :
    ∃ t : ℝ, x₂ = x₁ + t • rv y y' := by
  set c := κ.k (1 : Fin 2) * z.massActionMonomial x₁ / (κ.k (0 : Fin 2) * y.massActionMonomial x₁)
    with hcdef
  have hc0 : 0 < c := div_pos (mul_pos (κ.positive _) (Complex.massActionMonomial_pos hx₁ _))
    (mul_pos (κ.positive _) (Complex.massActionMonomial_pos hx₁ _))
  have hneg := twoRxn_negMultiple_of_steadyState κ hx₁ hss
  have hw : rv z z' = (-c⁻¹) • rv y y' := by
    funext s
    rw [Pi.smul_apply, smul_eq_mul, hneg s, ← hcdef]
    field_simp
  have hsub : (twoRxn y y' z z').stoichSubspace ≤ Submodule.span ℝ {rv y y'} := by
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    fin_cases r
    · show (twoRxn y y' z z').reactionVector (0 : Fin 2) ∈ _
      have : (twoRxn y y' z z').reactionVector (0 : Fin 2) = rv y y' := by
        funext s; rfl
      rw [this]; exact Submodule.mem_span_singleton_self _
    · show (twoRxn y y' z z').reactionVector (1 : Fin 2) ∈ _
      have : (twoRxn y y' z z').reactionVector (1 : Fin 2) = rv z z' := by
        funext s; rfl
      rw [this, hw]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : x₂ - x₁ ∈ Submodule.span ℝ {rv y y'} := hsub hc
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨t, by rw [ht]; abel⟩

omit [DecidableEq S] in
/-- `log (x^z / x^y) = ∑_s (z_s − y_s) log x_s` at positive `x`. -/
theorem log_ratio_monomial {x : Concentration S} (hx : x.Positive) :
    Real.log (z.massActionMonomial x / y.massActionMonomial x) =
      ∑ s, ((z s : ℝ) - y s) * Real.log (x s) := by
  have hlog : ∀ c : Complex S, Real.log (c.massActionMonomial x) = ∑ s, (c s : ℝ) * Real.log (x s) := by
    intro c
    rw [Complex.massActionMonomial, Real.log_prod (fun s _ => pow_ne_zero _ (hx s).ne')]
    exact Finset.sum_congr rfl fun s _ => by rw [Real.log_pow]
  rw [Real.log_div (Complex.massActionMonomial_pos hx _).ne' (Complex.massActionMonomial_pos hx _).ne',
    hlog, hlog, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Condition (2) is necessary.** If the two-reaction network is multistationary, `β` is zero or
has a positive and a negative coordinate. -/
theorem twoRxn_beta_of_multistationary (hyy : y ≠ y')
    (h : (twoRxn y y' z z').HasMultistationarityCapacity) :
    (∀ s, twoBeta y y' z s = 0) ∨ ((∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0) := by
  obtain ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩ := h
  have hc : (twoRxn y y' z z').StoichCompatible x₁ x₂ := hc₁.symm.trans hc₂
  obtain ⟨t, rfl⟩ := twoRxn_exists_line κ hp₁ hs₁ hc
  have ht : t ≠ 0 := by rintro rfl; simp at hne
  -- the ratio `x^z / x^y` agrees at the two steady states
  have hratio : z.massActionMonomial x₁ / y.massActionMonomial x₁ =
      z.massActionMonomial (x₁ + t • rv y y') / y.massActionMonomial (x₁ + t • rv y y') := by
    obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
    have e₁ := twoRxn_negMultiple_of_steadyState κ hp₁ hs₁ s₀
    have e₂ := twoRxn_negMultiple_of_steadyState κ hp₂ hs₂ s₀
    have hw : rv z z' s₀ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at e₁; exact hs₀ e₁
    have hk0 := κ.positive (0 : Fin 2)
    have hk1 := κ.positive (1 : Fin 2)
    have heq : κ.k (1 : Fin 2) * z.massActionMonomial x₁ / (κ.k (0 : Fin 2) * y.massActionMonomial x₁) =
        κ.k (1 : Fin 2) * z.massActionMonomial (x₁ + t • rv y y') /
          (κ.k (0 : Fin 2) * y.massActionMonomial (x₁ + t • rv y y')) := by
      have h12 := e₁.symm.trans e₂
      exact neg_inj.mp (mul_right_cancel₀ hw h12)
    have hy1 := (Complex.massActionMonomial_pos hp₁ y).ne'
    have hy2 := (Complex.massActionMonomial_pos hp₂ y).ne'
    field_simp at heq ⊢
    nlinarith [heq, hk0, hk1]
  -- the function along the segment
  set h : ℝ → ℝ := fun τ => ∑ s, ((z s : ℝ) - y s) * Real.log (x₁ s + τ * rv y y' s) with hh
  have hseg : ∀ τ, (0 ≤ τ / t ∧ τ / t ≤ 1) → (x₁ + τ • rv y y').Positive := by
    intro τ ⟨h0, h1⟩ s
    have e : x₁ s + τ * rv y y' s = (1 - τ / t) * x₁ s + (τ / t) * (x₁ s + t * rv y y' s) := by
      field_simp; ring
    have := hp₂ s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [e]
    rcases lt_or_eq_of_le h1 with h1 | h1
    · nlinarith [hp₁ s]
    · rw [h1]; simpa using this
  have hh0 : h 0 = Real.log (z.massActionMonomial x₁ / y.massActionMonomial x₁) := by
    rw [log_ratio_monomial hp₁]; simp [hh]
  have hht : h t = Real.log (z.massActionMonomial (x₁ + t • rv y y') /
      y.massActionMonomial (x₁ + t • rv y y')) := by
    rw [log_ratio_monomial hp₂]; simp [hh]
  have hderiv : ∀ τ, (x₁ + τ • rv y y').Positive →
      HasDerivAt h (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s)) τ := by
    intro τ hτ
    refine HasDerivAt.fun_sum fun s _ => ?_
    have hpos : 0 < x₁ s + τ * rv y y' s := by simpa using hτ s
    have hl : HasDerivAt (fun τ => x₁ s + τ * rv y y' s) (rv y y' s) τ := by
      simpa using ((hasDerivAt_id τ).mul_const (rv y y' s)).const_add (x₁ s)
    have := (hl.log hpos.ne').const_mul ((z s : ℝ) - y s)
    refine this.congr_deriv ?_
    simp only [twoBeta, rv]
    field_simp
  -- sign of the derivative
  by_contra hcon
  push Not at hcon
  obtain ⟨hnz, hmix⟩ := hcon
  obtain ⟨p, hp⟩ := hnz
  have hsign : (∀ s, 0 ≤ twoBeta y y' z s) ∨ (∀ s, twoBeta y y' z s ≤ 0) := by
    by_contra hns
    push Not at hns
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hns
    exact absurd (hmix ⟨j, hj⟩ i) (not_le.mpr hi)
  have hderiv_ne : ∀ τ, (x₁ + τ • rv y y').Positive →
      ∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s) ≠ 0 := by
    intro τ hτ
    have hpos : ∀ s, 0 < x₁ s + τ * rv y y' s := fun s => by simpa using hτ s
    rcases hsign with hall | hall
    · have hpp : 0 < twoBeta y y' z p := lt_of_le_of_ne (hall p) (Ne.symm hp)
      have : 0 < ∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s) :=
        lt_of_lt_of_le (div_pos hpp (hpos p))
          (Finset.single_le_sum (f := fun s => twoBeta y y' z s / (x₁ s + τ * rv y y' s))
            (fun s _ => div_nonneg (hall s) (hpos s).le) (Finset.mem_univ p))
      exact this.ne'
    · have hpp : twoBeta y y' z p < 0 := lt_of_le_of_ne (hall p) hp
      have : ∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s) < 0 := by
        have h1 := Finset.single_le_sum (f := fun s => -(twoBeta y y' z s / (x₁ s + τ * rv y y' s)))
          (fun s _ => neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hall s) (hpos s).le))
          (Finset.mem_univ p)
        rw [Finset.sum_neg_distrib] at h1
        have h2 : twoBeta y y' z p / (x₁ p + τ * rv y y' p) < 0 := div_neg_of_neg_of_pos hpp (hpos p)
        linarith
      exact this.ne
  -- mean value theorem on the segment between `0` and `t`
  have hcont : ∀ a b, (∀ τ ∈ Set.Icc a b, (x₁ + τ • rv y y').Positive) →
      ContinuousOn h (Set.Icc a b) := fun a b hab τ hτ =>
    (hderiv τ (hab τ hτ)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne ht with htn | htp
  · have hI : ∀ τ ∈ Set.Icc t 0, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg_of_nonpos hτ.2 htn.le, (div_le_one_of_neg htn).mpr hτ.1⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope h _ htn (hcont t 0 hI)
      (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hh0, hht, ← hratio, sub_self, zero_div] at hcd
    exact hderiv_ne c (hI c ⟨hc.1.le, hc.2.le⟩) hcd
  · have hI : ∀ τ ∈ Set.Icc 0 t, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg hτ.1 htp.le, (div_le_one htp).mpr hτ.2⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope h _ htp (hcont 0 t hI)
      (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hh0, hht, ← hratio, sub_self, zero_div] at hcd
    exact hderiv_ne c (hI c ⟨hc.1.le, hc.2.le⟩) hcd

/-- **Sufficiency when `β = 0`.** If `y' − y = −λ (z' − z)` with `λ > 0` and `β = 0`, then for
suitable rate constants every point of the class of the all-ones state is a steady state; in
particular the network is multistationary. -/
theorem twoRxn_multistationary_of_beta_zero (hyy : y ≠ y') {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) (hβ : ∀ s, twoBeta y y' z s = 0) :
    (twoRxn y y' z z').HasMultistationarityCapacity := by
  let κ : RateConstants (twoRxn y y' z z') :=
    ⟨fun (r : Fin 2) => if r = 0 then 1 else lam, fun (r : Fin 2) => by
      by_cases h : r = 0 <;> simp [h, hlam]⟩
  have hk0 : κ.k (0 : Fin 2) = 1 := rfl
  have hk1 : κ.k (1 : Fin 2) = lam := rfl
  set one : Concentration S := fun _ => 1
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  -- a small step stays positive
  obtain ⟨ε, hε, hεpos⟩ : ∃ ε : ℝ, 0 < ε ∧ (one + ε • rv y y').Positive := by
    set M : ℝ := ∑ s, |rv y y' s| + 1
    have hM : 0 < M := by positivity
    refine ⟨1 / (2 * M), by positivity, fun s => ?_⟩
    have hle : |rv y y' s| ≤ M - 1 := by
      have := Finset.single_le_sum (f := fun s => |rv y y' s|) (fun s _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [M]; linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one]
    have h1 : -(M - 1) ≤ rv y y' s := by linarith [neg_abs_le (rv y y' s)]
    have h2 : (1 / (2 * M)) * (-(M - 1)) ≤ 1 / (2 * M) * rv y y' s :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 / (2 * M)) * (-(M - 1)) > -1 := by
      rw [gt_iff_lt, div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)]; linarith
    linarith
  -- along the line through `1`, the two monomials agree
  have hmono : ∀ τ : ℝ, z.massActionMonomial (one + τ • rv y y') =
      y.massActionMonomial (one + τ • rv y y') := by
    intro τ
    unfold Complex.massActionMonomial
    refine Finset.prod_congr rfl fun s _ => ?_
    have := hβ s
    simp only [twoBeta] at this
    rcases mul_eq_zero.mp this with h | h
    · have hv : rv y y' s = 0 := by simp only [rv]; linarith
      simp [one, hv]
    · have : z s = y s := by exact_mod_cast (sub_eq_zero.mp h)
      rw [this]
  have hsteady : ∀ τ : ℝ, (twoRxn y y' z z').IsMassActionSteadyState κ (one + τ • rv y y') := by
    intro τ s
    show (twoRxn y y' z z').massActionVectorField κ _ s = 0
    rw [twoRxn_field, hk0, hk1, hmono τ, hneg s]
    have hw : lam * rv z z' s = -rv y y' s := by rw [hneg s]; ring
    nlinarith [hw]
  refine ⟨κ, one, one, one + ε • rv y y', ⟨StoichCompatible.refl _ _, fun _ => one_pos⟩,
    ⟨?_, hεpos⟩, by simpa using hsteady 0, hsteady ε, ?_⟩
  · show (one + ε • rv y y' - one) ∈ (twoRxn y y' z z').stoichSubspace
    rw [add_sub_cancel_left]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 2), ?_⟩)
    funext s; rfl
  · intro heq
    have := congrFun heq s₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have h0 : ε * rv y y' s₀ = 0 := by linarith
    exact hs₀ ((mul_eq_zero.mp h0).resolve_left hε.ne')

/-- Solving `d (log (a + v) − log a) = T` for `a > 0` with `a + v > 0`, when `T/d` and `v` have the
same sign. -/
theorem exists_log_step (v d T : ℝ) (hsgn : 0 < T / d * v) :
    ∃ a : ℝ, 0 < a ∧ 0 < a + v ∧ d * (Real.log (a + v) - Real.log a) = T := by
  have hd : d ≠ 0 := by rintro rfl; simp at hsgn
  set e := Real.exp (T / d) with he
  have he0 : 0 < e := Real.exp_pos _
  have hcase : (0 < v ∧ 1 < e) ∨ (v < 0 ∧ e < 1) := by
    rcases lt_trichotomy (T / d) 0 with h | h | h
    · right; exact ⟨by nlinarith, by rw [he]; exact Real.exp_lt_one_iff.mpr h⟩
    · rw [h, zero_mul] at hsgn; exact absurd hsgn (lt_irrefl 0)
    · left; exact ⟨by nlinarith, by rw [he]; exact Real.one_lt_exp_iff.mpr h⟩
  have he1 : e - 1 ≠ 0 := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  refine ⟨v / (e - 1), ?_, ?_, ?_⟩
  · rcases hcase with ⟨hv, h⟩ | ⟨hv, h⟩
    · exact div_pos hv (by linarith)
    · exact div_pos_of_neg_of_neg hv (by linarith)
  · have : v / (e - 1) + v = v * e / (e - 1) := by field_simp; ring
    rw [this]
    rcases hcase with ⟨hv, h⟩ | ⟨hv, h⟩
    · exact div_pos (mul_pos hv he0) (by linarith)
    · exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hv he0) (by linarith)
  · have hq : (v / (e - 1) + v) / (v / (e - 1)) = e := by
      have hv : v ≠ 0 := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact h.ne'; exact h.ne]
      field_simp; ring
    have ha : 0 < v / (e - 1) := by
      rcases hcase with ⟨hv, h⟩ | ⟨hv, h⟩
      · exact div_pos hv (by linarith)
      · exact div_pos_of_neg_of_neg hv (by linarith)
    have hb : 0 < v / (e - 1) + v := by
      have : v / (e - 1) + v = v * e / (e - 1) := by field_simp; ring
      rw [this]
      rcases hcase with ⟨hv, h⟩ | ⟨hv, h⟩
      · exact div_pos (mul_pos hv he0) (by linarith)
      · exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hv he0) (by linarith)
    rw [← Real.log_div hb.ne' ha.ne', hq, he, Real.log_exp]
    field_simp

/-- **Sufficiency when `β` has both signs.** If `y' − y = −λ (z' − z)` with `λ > 0` and `β` has
a positive and a negative coordinate, the network is multistationary: there are two positive
points `a` and `a + (y' − y)` with the same value of `x^{z − y}`, and for `κ₁ / κ₀` matched to that
value both are steady states. -/
theorem twoRxn_multistationary_of_beta_mixed {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) {p q : S} (hp : 0 < twoBeta y y' z p)
    (hq : twoBeta y y' z q < 0) : (twoRxn y y' z z').HasMultistationarityCapacity := by
  classical
  set v : S → ℝ := rv y y' with hvdef
  set d : S → ℝ := fun s => (z s : ℝ) - y s with hddef
  have hβ : ∀ s, twoBeta y y' z s = v s * d s := fun s => rfl
  have hpq : p ≠ q := by rintro rfl; linarith
  have hdp : d p ≠ 0 := by intro h; rw [hβ, h, mul_zero] at hp; exact lt_irrefl 0 hp
  have hdq : d q ≠ 0 := by intro h; rw [hβ, h, mul_zero] at hq; exact lt_irrefl 0 hq
  -- the other coordinates
  set C : ℝ := ∑ s ∈ (Finset.univ.erase p).erase q,
    d s * (Real.log (|v s| + 1 + v s) - Real.log (|v s| + 1)) with hC
  set K : ℝ := |C| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hsq : ∀ (T : ℝ) (s : S), d s ≠ 0 → T / d s * v s = T * (v s * d s) / d s ^ 2 := by
    intro T s hds; field_simp
  obtain ⟨aq, haq, haqv, hTq⟩ := exists_log_step (v q) (d q) (-K) (by
    rw [hsq _ _ hdq, ← hβ]
    exact div_pos (mul_pos_of_neg_of_neg (by linarith) hq) (by positivity))
  obtain ⟨ap, hap, hapv, hTp⟩ := exists_log_step (v p) (d p) (K - C) (by
    rw [hsq _ _ hdp, ← hβ]
    have : 0 < K - C := by have := le_abs_self C; linarith
    exact div_pos (mul_pos this hp) (by positivity))
  set a : Concentration S := fun s => if s = p then ap else if s = q then aq else |v s| + 1
    with hadef
  have ha_p : a p = ap := by simp [hadef]
  have ha_q : a q = aq := by simp [hadef, Ne.symm hpq]
  have ha_o : ∀ s, s ≠ p → s ≠ q → a s = |v s| + 1 := fun s h1 h2 => by simp [hadef, h1, h2]
  have hpos1 : a.Positive := by
    intro s
    by_cases h1 : s = p
    · subst h1; rw [ha_p]; exact hap
    by_cases h2 : s = q
    · subst h2; rw [ha_q]; exact haq
    rw [ha_o s h1 h2]; positivity
  set b : Concentration S := a + v with hbdef
  have hpos2 : b.Positive := by
    intro s
    simp only [hbdef, Pi.add_apply]
    by_cases h1 : s = p
    · subst h1; rw [ha_p]; exact hapv
    by_cases h2 : s = q
    · subst h2; rw [ha_q]; exact haqv
    rw [ha_o s h1 h2]
    have := neg_abs_le (v s)
    linarith
  -- equal values of `x^{z − y}`
  have hsum : ∑ s, d s * (Real.log (b s) - Real.log (a s)) = 0 := by
    have hq_mem : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
      ← Finset.add_sum_erase _ _ hq_mem]
    have hrest : ∑ s ∈ (Finset.univ.erase p).erase q, d s * (Real.log (b s) - Real.log (a s)) = C := by
      rw [hC]
      refine Finset.sum_congr rfl fun s hs => ?_
      have h2 : s ≠ q := Finset.ne_of_mem_erase hs
      have h1 : s ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs)
      simp only [hbdef, Pi.add_apply, ha_o s h1 h2]
    rw [hrest]
    simp only [hbdef, Pi.add_apply, ha_p, ha_q]
    rw [hTp, hTq]
    ring
  have hratio : z.massActionMonomial a / y.massActionMonomial a =
      z.massActionMonomial b / y.massActionMonomial b := by
    have h1 := log_ratio_monomial (z := z) (y := y) hpos1
    have h2 := log_ratio_monomial (z := z) (y := y) hpos2
    have hdiff : Real.log (z.massActionMonomial b / y.massActionMonomial b) -
        Real.log (z.massActionMonomial a / y.massActionMonomial a) = 0 := by
      rw [h1, h2, ← Finset.sum_sub_distrib, ← hsum]
      exact Finset.sum_congr rfl fun s _ => by simp only [hddef]; ring
    have hpa := div_pos (Complex.massActionMonomial_pos hpos1 z) (Complex.massActionMonomial_pos hpos1 y)
    have hpb := div_pos (Complex.massActionMonomial_pos hpos2 z) (Complex.massActionMonomial_pos hpos2 y)
    exact (Real.log_injOn_pos (Set.mem_Ioi.mpr hpa) (Set.mem_Ioi.mpr hpb) (by linarith)).symm ▸ rfl
  -- rate constants
  have hmya := Complex.massActionMonomial_pos hpos1 y
  have hmza := Complex.massActionMonomial_pos hpos1 z
  set k1 : ℝ := lam * y.massActionMonomial a / z.massActionMonomial a with hk1
  have hk1pos : 0 < k1 := div_pos (mul_pos hlam hmya) hmza
  let κ : RateConstants (twoRxn y y' z z') :=
    ⟨fun (r : Fin 2) => if r = 0 then 1 else k1, fun (r : Fin 2) => by
      by_cases h : r = 0 <;> simp [h, hk1pos]⟩
  have hk0 : κ.k (0 : Fin 2) = 1 := rfl
  have hk1' : κ.k (1 : Fin 2) = k1 := rfl
  have hw : ∀ s, rv z z' s = -(v s) / lam := fun s => by
    have := hneg s
    field_simp
    linarith
  have hsteady : ∀ x : Concentration S, x.Positive →
      z.massActionMonomial x / y.massActionMonomial x =
        z.massActionMonomial a / y.massActionMonomial a →
      (twoRxn y y' z z').IsMassActionSteadyState κ x := by
    intro x hx hrx s
    show (twoRxn y y' z z').massActionVectorField κ x s = 0
    rw [twoRxn_field, hk0, hk1', hw s]
    have hmy := Complex.massActionMonomial_pos hx y
    have hmz := (Complex.massActionMonomial_pos hx z)
    have hz : z.massActionMonomial x = z.massActionMonomial a / y.massActionMonomial a *
        y.massActionMonomial x := by
      rw [← hrx]; field_simp
    rw [hz, hk1]
    field_simp
    ring
  refine ⟨κ, a, a, b, ⟨StoichCompatible.refl _ _, hpos1⟩, ⟨?_, hpos2⟩,
    hsteady a hpos1 rfl, hsteady b hpos2 hratio.symm, ?_⟩
  · show (a + v - a) ∈ (twoRxn y y' z z').stoichSubspace
    rw [add_sub_cancel_left]
    exact Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
  · intro heq
    have := congrFun heq p
    simp only [hbdef, Pi.add_apply] at this
    have hvp : v p = 0 := by linarith
    rw [hβ, hvp, zero_mul] at hp
    exact lt_irrefl 0 hp

/-- **Joshi–Shiu 2017, Theorem 5.1.** The network with two reactions `y → y'` and `z → z'`
(`y ≠ y'`) is multistationary iff `y' − y = −λ (z' − z)` for some `λ > 0` and
`β = (y' − y) ∗ (z − y)` is zero or has a positive and a negative coordinate. -/
theorem twoRxn_multistationary_iff (hyy : y ≠ y') :
    (twoRxn y y' z z').HasMultistationarityCapacity ↔
      (∃ lam : ℝ, 0 < lam ∧ ∀ s, rv y y' s = -lam * rv z z' s) ∧
        ((∀ s, twoBeta y y' z s = 0) ∨
          ((∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0)) := by
  constructor
  · intro h
    refine ⟨?_, twoRxn_beta_of_multistationary hyy h⟩
    obtain ⟨κ, x₀, x₁, x₂, ⟨_, hp₁⟩, _, hs₁, _, _⟩ := h
    refine ⟨_, div_pos (mul_pos (κ.positive _) (Complex.massActionMonomial_pos hp₁ _))
      (mul_pos (κ.positive _) (Complex.massActionMonomial_pos hp₁ _)),
      twoRxn_negMultiple_of_steadyState κ hp₁ hs₁⟩
  · rintro ⟨⟨lam, hlam, hneg⟩, hβ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩⟩
    · exact twoRxn_multistationary_of_beta_zero hyy hlam hneg hβ
    · exact twoRxn_multistationary_of_beta_mixed hlam hneg hp hq

end Network

end CRNT
