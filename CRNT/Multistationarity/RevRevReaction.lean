import CRNT.Multistationarity.RankOneLifting

/-!
# Two reversible reactions (Joshi–Shiu 2017, Theorem 5.12)

For the network `y ⇌ y'`, `z ⇌ z'` (`y ≠ y'`, `z ≠ z'`; reactions `0 : y → y'`, `1 : y' → y`,
`2 : z → z'`, `3 : z' → z`), Joshi and Shiu (Theorem 5.12, building on Boros) show: the network is
multistationary iff `z' − z = μ (y' − y)` for some `μ ≠ 0` and, for some species `i`, the
coordinate intervals of the two pairs are disjoint and nondegenerate:
`min {y_i, y'_i} < max {y_i, y'_i} < min {z_i, z'_i} < max {z_i, z'_i}` or the same with the pairs
exchanged.

This module proves the theorem directly.

* Not parallel: every positive steady state is detailed balanced, and the Birch argument
  (`∑ (x₂ − x₁)_s (log x₂ − log x₁)_s = 0`) gives uniqueness in each class.
* Parallel with `μ > 0` and no separated species: along a class line the ratio
  `(κ₁ x^{y'} + μκ₃ x^{z'}) / (κ₀ x^y + μκ₂ x^z)` is strictly increasing (every exponent difference
  `a − b`, `a ∈ {y', z'}`, `b ∈ {y, z}`, has the sign of the line direction coordinatewise), so a
  class contains at most one steady state. `μ < 0` reduces to this by exchanging `z` and `z'`.
* Sufficiency is `revRev_multistationary_of_separated` (alternating triple lifting).

* `revRev_field`, `revRev_not_multistationary_of_not_parallel`,
  `revRev_not_multistationary_of_not_separated`, `revRev_multistationary_iff`.
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

variable {y y' z z' : Complex S}

theorem revRev_field (κ : RateConstants (revRev y y' z z')) (x : Concentration S) (s : S) :
    (revRev y y' z z').massActionVectorField κ x s =
      (κ.k (0 : Fin 4) * y.massActionMonomial x - κ.k (1 : Fin 4) * y'.massActionMonomial x) *
          rv y y' s +
        (κ.k (2 : Fin 4) * z.massActionMonomial x - κ.k (3 : Fin 4) * z'.massActionMonomial x) *
          rv z z' s := by
  rw [massActionVectorField_apply]
  change ∑ r : Fin 4, _ = _
  rw [Fin.sum_univ_four]
  show κ.k (0 : Fin 4) * y.massActionMonomial x * ((y' s : ℝ) - y s) +
      κ.k (1 : Fin 4) * y'.massActionMonomial x * ((y s : ℝ) - y' s) +
      κ.k (2 : Fin 4) * z.massActionMonomial x * ((z' s : ℝ) - z s) +
      κ.k (3 : Fin 4) * z'.massActionMonomial x * ((z s : ℝ) - z' s) = _
  simp only [rv]; ring

omit [DecidableEq S] in
theorem monomial_eq_exp_sum_log (c : Complex S) {x : Concentration S} (hx : x.Positive) :
    c.massActionMonomial x = Real.exp (∑ s, (c s : ℝ) * Real.log (x s)) := by
  rw [Real.exp_sum, Complex.massActionMonomial]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (hx s), mul_comm]

/-- The class `x₀` relabeled by exchanging the second pair has the same capacity. -/
theorem revRev_capacity_swap_imp (h : (revRev y y' z z').HasMultistationarityCapacity) :
    (revRev y y' z' z).HasMultistationarityCapacity := by
  obtain ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩ := h
  let κ' : RateConstants (revRev y y' z' z) :=
    ⟨fun (r : Fin 4) => if r = 0 then κ.k (0 : Fin 4) else if r = 1 then κ.k (1 : Fin 4)
      else if r = 2 then κ.k (3 : Fin 4) else κ.k (2 : Fin 4),
      fun (r : Fin 4) => by fin_cases r <;> simp <;> exact κ.positive _⟩
  have hfield : ∀ x s, (revRev y y' z' z).massActionVectorField κ' x s =
      (revRev y y' z z').massActionVectorField κ x s := by
    intro x s
    rw [revRev_field, revRev_field]
    have hk0 : κ'.k (0 : Fin 4) = κ.k (0 : Fin 4) := rfl
    have hk1 : κ'.k (1 : Fin 4) = κ.k (1 : Fin 4) := rfl
    have hk2 : κ'.k (2 : Fin 4) = κ.k (3 : Fin 4) := rfl
    have hk3 : κ'.k (3 : Fin 4) = κ.k (2 : Fin 4) := rfl
    rw [hk0, hk1, hk2, hk3]
    simp only [rv]; ring
  have hS : (revRev y y' z' z).stoichSubspace = (revRev y y' z z').stoichSubspace := by
    have key : ∀ (p p' : Complex S), (revRev y y' p' p).stoichSubspace ≤
        (revRev y y' p p').stoichSubspace := by
      intro p p'
      apply Submodule.span_le.2
      rintro _ ⟨r, rfl⟩
      fin_cases r
      · exact (revRev y y' p p').reactionVector_mem_stoichSubspace (0 : Fin 4)
      · exact (revRev y y' p p').reactionVector_mem_stoichSubspace (1 : Fin 4)
      · exact (revRev y y' p p').reactionVector_mem_stoichSubspace (3 : Fin 4)
      · exact (revRev y y' p p').reactionVector_mem_stoichSubspace (2 : Fin 4)
    exact le_antisymm (key z z') (key z' z)
  have hss : ∀ x, (revRev y y' z z').IsMassActionSteadyState κ x →
      (revRev y y' z' z).IsMassActionSteadyState κ' x := fun x hx s => by
    show (revRev y y' z' z).massActionVectorField κ' x s = 0
    rw [hfield]; exact hx s
  have hcomp : ∀ a b, (revRev y y' z z').StoichCompatible a b →
      (revRev y y' z' z).StoichCompatible a b := fun a b h => by
    show b - a ∈ (revRev y y' z' z).stoichSubspace
    rw [hS]; exact h
  exact ⟨κ', x₀, x₁, x₂, ⟨hcomp _ _ hc₁, hp₁⟩, ⟨hcomp _ _ hc₂, hp₂⟩, hss _ hs₁, hss _ hs₂, hne⟩

/-- **Not parallel ⇒ not multistationary.** If `z' − z` is not a multiple of `y' − y`, every
positive steady state is detailed balanced and a class contains at most one of them. -/
theorem revRev_not_multistationary_of_not_parallel (hyy : y ≠ y')
    (hpar : ¬ ∃ μ : ℝ, ∀ s, rv z z' s = μ * rv y y' s) :
    ¬ (revRev y y' z z').HasMultistationarityCapacity := by
  rintro ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  -- both brackets vanish at a positive steady state
  have hbal : ∀ x : Concentration S, (revRev y y' z z').IsMassActionSteadyState κ x →
      κ.k (0 : Fin 4) * y.massActionMonomial x = κ.k (1 : Fin 4) * y'.massActionMonomial x ∧
        κ.k (2 : Fin 4) * z.massActionMonomial x = κ.k (3 : Fin 4) * z'.massActionMonomial x := by
    intro x hx
    set R₁ := κ.k (0 : Fin 4) * y.massActionMonomial x - κ.k (1 : Fin 4) * y'.massActionMonomial x
    set R₂ := κ.k (2 : Fin 4) * z.massActionMonomial x - κ.k (3 : Fin 4) * z'.massActionMonomial x
    have h : ∀ s, R₁ * rv y y' s + R₂ * rv z z' s = 0 := fun s => by
      rw [← revRev_field]; exact hx s
    have hR₂ : R₂ = 0 := by
      by_contra hR
      apply hpar
      exact ⟨-R₁ / R₂, fun s => by have := h s; field_simp; linarith⟩
    have hR₁ : R₁ = 0 := by
      have := h s₀; rw [hR₂, zero_mul, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hs₀
    exact ⟨by linarith, by linarith⟩
  obtain ⟨h₁a, h₁b⟩ := hbal x₁ hs₁
  obtain ⟨h₂a, h₂b⟩ := hbal x₂ hs₂
  -- the log differences are orthogonal to the reaction vectors
  set Δ : S → ℝ := fun s => Real.log (x₂ s) - Real.log (x₁ s) with hΔ
  have hlogeq : ∀ (a b : Complex S) (ka kb : ℝ), 0 < ka → 0 < kb →
      ka * a.massActionMonomial x₁ = kb * b.massActionMonomial x₁ →
      ka * a.massActionMonomial x₂ = kb * b.massActionMonomial x₂ →
      ∑ s, ((b s : ℝ) - a s) * Δ s = 0 := by
    intro a b ka kb hka hkb e1 e2
    have l1 := congrArg Real.log e1
    have l2 := congrArg Real.log e2
    rw [Real.log_mul hka.ne' (Complex.massActionMonomial_pos hp₁ a).ne',
      Real.log_mul hkb.ne' (Complex.massActionMonomial_pos hp₁ b).ne',
      monomial_eq_exp_sum_log a hp₁, monomial_eq_exp_sum_log b hp₁, Real.log_exp,
      Real.log_exp] at l1
    rw [Real.log_mul hka.ne' (Complex.massActionMonomial_pos hp₂ a).ne',
      Real.log_mul hkb.ne' (Complex.massActionMonomial_pos hp₂ b).ne',
      monomial_eq_exp_sum_log a hp₂, monomial_eq_exp_sum_log b hp₂, Real.log_exp,
      Real.log_exp] at l2
    have : ∑ s, ((b s : ℝ) - a s) * Δ s =
        (∑ s, (b s : ℝ) * Real.log (x₂ s) - ∑ s, (a s : ℝ) * Real.log (x₂ s)) -
          (∑ s, (b s : ℝ) * Real.log (x₁ s) - ∑ s, (a s : ℝ) * Real.log (x₁ s)) := by
      simp only [hΔ, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this]; linarith
  have hv : ∑ s, rv y y' s * Δ s = 0 :=
    hlogeq y y' _ _ (κ.positive _) (κ.positive _) h₁a h₂a
  have hw : ∑ s, rv z z' s * Δ s = 0 :=
    hlogeq z z' _ _ (κ.positive _) (κ.positive _) h₁b h₂b
  -- the class difference is orthogonal to `Δ`
  let ℓ : (S → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ s, u s * Δ s
      map_add' := fun u u' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c u => by simp [Finset.mul_sum, mul_assoc] }
  have hker : (revRev y y' z z').stoichSubspace ≤ LinearMap.ker ℓ := by
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    show ∑ s, (revRev y y' z z').reactionVector r s * Δ s = 0
    fin_cases r
    · exact hv
    · show ∑ s, ((y s : ℝ) - y' s) * Δ s = 0
      have : ∑ s, ((y s : ℝ) - y' s) * Δ s = -(∑ s, rv y y' s * Δ s) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by simp only [rv]; ring
      rw [this, hv, neg_zero]
    · exact hw
    · show ∑ s, ((z s : ℝ) - z' s) * Δ s = 0
      have : ∑ s, ((z s : ℝ) - z' s) * Δ s = -(∑ s, rv z z' s * Δ s) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by simp only [rv]; ring
      rw [this, hw, neg_zero]
  have hdiff : (revRev y y' z z').StoichCompatible x₁ x₂ := hc₁.symm.trans hc₂
  have hzero : ∑ s, (x₂ s - x₁ s) * Δ s = 0 := hker hdiff
  apply hne
  funext s
  have hterm : ∀ s, 0 ≤ (x₂ s - x₁ s) * Δ s := by
    intro s
    simp only [hΔ]
    rcases le_total (x₁ s) (x₂ s) with h | h
    · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log (hp₁ s) h])
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
        (by linarith [Real.log_le_log (hp₂ s) h])
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hterm s).mp hzero s (Finset.mem_univ s)
  rcases mul_eq_zero.mp h0 with h | h
  · linarith
  · simp only [hΔ] at h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (hp₂ s)) (Set.mem_Ioi.mpr (hp₁ s)) (by linarith)
    exact this.symm

omit [DecidableEq S] in
theorem hasDerivAt_lineLog (c : Complex S) (x₁ v : S → ℝ) {τ : ℝ}
    (hpos : ∀ s, 0 < x₁ s + τ * v s) :
    HasDerivAt (fun τ => ∑ s, (c s : ℝ) * Real.log (x₁ s + τ * v s))
      (∑ s, (c s : ℝ) * v s / (x₁ s + τ * v s)) τ := by
  refine HasDerivAt.fun_sum fun s _ => ?_
  have hl : HasDerivAt (fun τ => x₁ s + τ * v s) (v s) τ := by
    simpa using ((hasDerivAt_id τ).mul_const (v s)).const_add (x₁ s)
  have := (hl.log (hpos s).ne').const_mul (c s : ℝ)
  refine this.congr_deriv ?_
  field_simp

/-- **Monotone ratio ⇒ not multistationary.** If `z' − z = μ (y' − y)` with `μ > 0` and every
exponent difference `y' − z`, `z' − y` has, coordinatewise, the sign of `y' − y`, a class contains
at most one positive steady state. -/
theorem revRev_not_multistationary_of_monotone (hyy : y ≠ y') {μ : ℝ} (hμ : 0 < μ)
    (hw : ∀ s, rv z z' s = μ * rv y y' s)
    (hmono : ∀ s, 0 ≤ ((y' s : ℝ) - z s) * rv y y' s ∧ 0 ≤ ((z' s : ℝ) - y s) * rv y y' s) :
    ¬ (revRev y y' z z').HasMultistationarityCapacity := by
  rintro ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩
  set v := rv y y' with hv
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  -- steady states: `κ₀ x^y + μκ₂ x^z = κ₁ x^{y'} + μκ₃ x^{z'}`
  have hsteady : ∀ x : Concentration S, (revRev y y' z z').IsMassActionSteadyState κ x →
      κ.k (0 : Fin 4) * y.massActionMonomial x + μ * κ.k (2 : Fin 4) * z.massActionMonomial x =
        κ.k (1 : Fin 4) * y'.massActionMonomial x + μ * κ.k (3 : Fin 4) * z'.massActionMonomial x := by
    intro x hx
    have h : (revRev y y' z z').massActionVectorField κ x s₀ = 0 := hx s₀
    rw [revRev_field, hw s₀] at h
    have : (κ.k (0 : Fin 4) * y.massActionMonomial x - κ.k (1 : Fin 4) * y'.massActionMonomial x +
        μ * (κ.k (2 : Fin 4) * z.massActionMonomial x -
          κ.k (3 : Fin 4) * z'.massActionMonomial x)) * v s₀ = 0 := by
      rw [← h]; ring
    have := (mul_eq_zero.mp this).resolve_right hs₀
    linarith
  -- the class line
  have hS : (revRev y y' z z').stoichSubspace ≤ Submodule.span ℝ {v} := by
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    have hwv : rv z z' = μ • v := by funext s; rw [Pi.smul_apply, smul_eq_mul, hw s]
    fin_cases r
    · show (revRev y y' z z').reactionVector (0 : Fin 4) ∈ _
      have : (revRev y y' z z').reactionVector (0 : Fin 4) = v := by funext s; rfl
      rw [this]; exact Submodule.mem_span_singleton_self _
    · show (revRev y y' z z').reactionVector (1 : Fin 4) ∈ _
      have : (revRev y y' z z').reactionVector (1 : Fin 4) = (-1 : ℝ) • v := by
        funext s; show ((y s : ℝ) - y' s) = _; simp [hv, rv]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · show (revRev y y' z z').reactionVector (2 : Fin 4) ∈ _
      have : (revRev y y' z z').reactionVector (2 : Fin 4) = rv z z' := by funext s; rfl
      rw [this, hwv]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · show (revRev y y' z z').reactionVector (3 : Fin 4) ∈ _
      have : (revRev y y' z z').reactionVector (3 : Fin 4) = (-μ) • v := by
        funext s; show ((z s : ℝ) - z' s) = _
        have := hw s; simp only [rv] at this; simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination -this
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hS (hc₁.symm.trans hc₂))
  have hx₂ : x₂ = x₁ + t • v := by rw [ht]; abel
  subst hx₂
  have ht0 : t ≠ 0 := by rintro rfl; simp at hne
  -- the log-ratio along the line
  let Lc : Complex S → ℝ → ℝ := fun c τ => ∑ s, (c s : ℝ) * Real.log (x₁ s + τ * v s)
  let Nf : ℝ → ℝ := fun τ => κ.k (1 : Fin 4) * Real.exp (Lc y' τ) +
    μ * κ.k (3 : Fin 4) * Real.exp (Lc z' τ)
  let Pf : ℝ → ℝ := fun τ => κ.k (0 : Fin 4) * Real.exp (Lc y τ) +
    μ * κ.k (2 : Fin 4) * Real.exp (Lc z τ)
  have hNpos : ∀ τ, 0 < Nf τ := fun τ => by
    have := κ.positive (1 : Fin 4); have := κ.positive (3 : Fin 4)
    have := Real.exp_pos (Lc y' τ); have := Real.exp_pos (Lc z' τ)
    simp only [Nf]; positivity
  have hPpos : ∀ τ, 0 < Pf τ := fun τ => by
    have := κ.positive (0 : Fin 4); have := κ.positive (2 : Fin 4)
    have := Real.exp_pos (Lc y τ); have := Real.exp_pos (Lc z τ)
    simp only [Pf]; positivity
  let G : ℝ → ℝ := fun τ => Real.log (Nf τ) - Real.log (Pf τ)
  have hLc : ∀ c τ, (x₁ + τ • v).Positive →
      Real.exp (Lc c τ) = c.massActionMonomial (x₁ + τ • v) := by
    intro c τ hτ
    rw [monomial_eq_exp_sum_log c hτ]
    rfl
  have hG : ∀ τ, (x₁ + τ • v).Positive →
      (revRev y y' z z').IsMassActionSteadyState κ (x₁ + τ • v) → G τ = 0 := by
    intro τ hτ hss
    have h := hsteady _ hss
    simp only [G, Nf, Pf, hLc _ τ hτ]
    rw [← h, sub_self]
  have hG0 : G 0 = 0 := hG 0 (by simpa using hp₁) (by simpa using hs₁)
  have hGt : G t = 0 := hG t hp₂ hs₂
  -- positivity on the segment
  have hseg : ∀ τ, (0 ≤ τ / t ∧ τ / t ≤ 1) → (x₁ + τ • v).Positive := by
    intro τ ⟨h0, h1⟩ s
    have e : x₁ s + τ * v s = (1 - τ / t) * x₁ s + (τ / t) * (x₁ s + t * v s) := by
      field_simp; ring
    have := hp₂ s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [e]
    rcases lt_or_eq_of_le h1 with h1 | h1
    · nlinarith [hp₁ s]
    · rw [h1]; simpa using this
  -- the derivative of `G`
  let D : Complex S → ℝ → ℝ := fun c τ => ∑ s, (c s : ℝ) * v s / (x₁ s + τ * v s)
  have hGd : ∀ τ, (x₁ + τ • v).Positive → HasDerivAt G
      ((κ.k (1 : Fin 4) * Real.exp (Lc y' τ) * D y' τ +
          μ * κ.k (3 : Fin 4) * Real.exp (Lc z' τ) * D z' τ) / Nf τ -
        (κ.k (0 : Fin 4) * Real.exp (Lc y τ) * D y τ +
          μ * κ.k (2 : Fin 4) * Real.exp (Lc z τ) * D z τ) / Pf τ) τ := by
    intro τ hτ
    have hpos : ∀ s, 0 < x₁ s + τ * v s := fun s => by simpa using hτ s
    have hL := fun c => hasDerivAt_lineLog c x₁ v hpos
    have hN : HasDerivAt Nf (κ.k (1 : Fin 4) * Real.exp (Lc y' τ) * D y' τ +
        μ * κ.k (3 : Fin 4) * Real.exp (Lc z' τ) * D z' τ) τ := by
      have := ((hL y').exp.const_mul (κ.k (1 : Fin 4))).add
        ((hL z').exp.const_mul (μ * κ.k (3 : Fin 4)))
      refine this.congr_deriv ?_
      simp only [D]; ring
    have hP : HasDerivAt Pf (κ.k (0 : Fin 4) * Real.exp (Lc y τ) * D y τ +
        μ * κ.k (2 : Fin 4) * Real.exp (Lc z τ) * D z τ) τ := by
      have := ((hL y).exp.const_mul (κ.k (0 : Fin 4))).add
        ((hL z).exp.const_mul (μ * κ.k (2 : Fin 4)))
      refine this.congr_deriv ?_
      simp only [D]; ring
    exact (hN.log (hNpos τ).ne').sub (hP.log (hPpos τ).ne')
  have hGd_pos : ∀ τ, (x₁ + τ • v).Positive →
      0 < (κ.k (1 : Fin 4) * Real.exp (Lc y' τ) * D y' τ +
          μ * κ.k (3 : Fin 4) * Real.exp (Lc z' τ) * D z' τ) / Nf τ -
        (κ.k (0 : Fin 4) * Real.exp (Lc y τ) * D y τ +
          μ * κ.k (2 : Fin 4) * Real.exp (Lc z τ) * D z τ) / Pf τ := by
    intro τ hτ
    have hpos : ∀ s, 0 < x₁ s + τ * v s := fun s => by simpa using hτ s
    have hDiff : ∀ a b : Complex S, D a τ - D b τ =
        ∑ s, ((a s : ℝ) - b s) * v s / (x₁ s + τ * v s) := by
      intro a b; simp only [D, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hnn : ∀ a b : Complex S, (∀ s, 0 ≤ ((a s : ℝ) - b s) * v s) → 0 ≤ D a τ - D b τ := by
      intro a b hab
      rw [hDiff]; exact Finset.sum_nonneg fun s _ => div_nonneg (hab s) (hpos s).le
    have h11 : 0 < D y' τ - D y τ := by
      rw [hDiff]
      refine lt_of_lt_of_le (div_pos ?_ (hpos s₀)) (Finset.single_le_sum
        (f := fun s => ((y' s : ℝ) - y s) * v s / (x₁ s + τ * v s))
        (fun s _ => div_nonneg (by rw [show ((y' s : ℝ) - y s) = v s from rfl]; nlinarith)
          (hpos s).le) (Finset.mem_univ s₀))
      rw [show ((y' s₀ : ℝ) - y s₀) = v s₀ from rfl]; exact mul_self_pos.mpr hs₀
    have h12 : 0 ≤ D y' τ - D z τ := hnn y' z fun s => (hmono s).1
    have h21 : 0 ≤ D z' τ - D y τ := hnn z' y fun s => (hmono s).2
    have h22 : 0 ≤ D z' τ - D z τ := hnn z' z fun s => by
      have := hw s; simp only [rv] at this; rw [this]; nlinarith [sq_nonneg (v s)]
    set N₁ := κ.k (1 : Fin 4) * Real.exp (Lc y' τ)
    set N₂ := μ * κ.k (3 : Fin 4) * Real.exp (Lc z' τ)
    set P₁ := κ.k (0 : Fin 4) * Real.exp (Lc y τ)
    set P₂ := μ * κ.k (2 : Fin 4) * Real.exp (Lc z τ)
    have hN₁ : 0 < N₁ := mul_pos (κ.positive _) (Real.exp_pos _)
    have hN₂ : 0 < N₂ := mul_pos (mul_pos hμ (κ.positive _)) (Real.exp_pos _)
    have hP₁ : 0 < P₁ := mul_pos (κ.positive _) (Real.exp_pos _)
    have hP₂ : 0 < P₂ := mul_pos (mul_pos hμ (κ.positive _)) (Real.exp_pos _)
    have hNf : Nf τ = N₁ + N₂ := rfl
    have hPf : Pf τ = P₁ + P₂ := rfl
    rw [hNf, hPf, div_sub_div _ _ (by positivity) (by positivity)]
    apply div_pos _ (by positivity)
    have : (N₁ * D y' τ + N₂ * D z' τ) * (P₁ + P₂) - (N₁ + N₂) * (P₁ * D y τ + P₂ * D z τ) =
        N₁ * P₁ * (D y' τ - D y τ) + N₁ * P₂ * (D y' τ - D z τ) +
          N₂ * P₁ * (D z' τ - D y τ) + N₂ * P₂ * (D z' τ - D z τ) := by ring
    rw [this]
    have := mul_pos (mul_pos hN₁ hP₁) h11
    have := mul_nonneg (mul_pos hN₁ hP₂).le h12
    have := mul_nonneg (mul_pos hN₂ hP₁).le h21
    have := mul_nonneg (mul_pos hN₂ hP₂).le h22
    linarith
  -- mean value theorem
  have hcont : ∀ a b, (∀ τ ∈ Set.Icc a b, (x₁ + τ • v).Positive) →
      ContinuousOn G (Set.Icc a b) := fun a b hab τ hτ =>
    (hGd τ (hab τ hτ)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne ht0 with htn | htp
  · have hI : ∀ τ ∈ Set.Icc t 0, (x₁ + τ • v).Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg_of_nonpos hτ.2 htn.le, (div_le_one_of_neg htn).mpr hτ.1⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G _ htn (hcont t 0 hI)
      (fun τ hτ => hGd τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hG0, hGt, sub_self, zero_div] at hcd
    exact (hGd_pos c (hI c ⟨hc.1.le, hc.2.le⟩)).ne' hcd
  · have hI : ∀ τ ∈ Set.Icc 0 t, (x₁ + τ • v).Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg hτ.1 htp.le, (div_le_one htp).mpr hτ.2⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G _ htp (hcont 0 t hI)
      (fun τ hτ => hGd τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hG0, hGt, sub_self, zero_div] at hcd
    exact (hGd_pos c (hI c ⟨hc.1.le, hc.2.le⟩)).ne' hcd

/-- Non-separated coordinate intervals with the same orientation give the sign conditions of
`revRev_not_multistationary_of_monotone`. -/
theorem nonseparated_signs {a a' b b' : ℕ} {va vb : ℝ} (hva : va = (a' : ℝ) - a)
    (hvb : vb = (b' : ℝ) - b) (hsame : 0 < va * vb)
    (hns : ¬ max a a' < min b b' ∧ ¬ max b b' < min a a') :
    0 ≤ ((a' : ℝ) - b) * va ∧ 0 ≤ ((b' : ℝ) - a) * va := by
  rcases lt_trichotomy va 0 with h | h | h
  · have hvb' : vb < 0 := by nlinarith
    have h1 : a' < a := by have : (a' : ℝ) < a := by linarith
                           exact_mod_cast this
    have h2 : b' < b := by have : (b' : ℝ) < b := by linarith
                           exact_mod_cast this
    have h3 : b' ≤ a := by omega
    have h4 : a' ≤ b := by omega
    have h3' : (b' : ℝ) ≤ a := by exact_mod_cast h3
    have h4' : (a' : ℝ) ≤ b := by exact_mod_cast h4
    exact ⟨mul_nonneg_of_nonpos_of_nonpos (by linarith) h.le,
      mul_nonneg_of_nonpos_of_nonpos (by linarith) h.le⟩
  · rw [h, zero_mul] at hsame; exact absurd hsame (lt_irrefl 0)
  · have hvb' : 0 < vb := by nlinarith
    have h1 : a < a' := by have : (a : ℝ) < a' := by linarith
                           exact_mod_cast this
    have h2 : b < b' := by have : (b : ℝ) < b' := by linarith
                           exact_mod_cast this
    have h3 : b ≤ a' := by omega
    have h4 : a ≤ b' := by omega
    have h3' : (b : ℝ) ≤ a' := by exact_mod_cast h3
    have h4' : (a : ℝ) ≤ b' := by exact_mod_cast h4
    exact ⟨mul_nonneg (by linarith) h.le, mul_nonneg (by linarith) h.le⟩

/-- **Joshi–Shiu 2017, Theorem 5.12.** The network `y ⇌ y'`, `z ⇌ z'` (`y ≠ y'`, `z ≠ z'`) is
multistationary iff `z' − z = μ (y' − y)` for some `μ ≠ 0` and, for some species `i`, the
coordinate intervals of the two reversible pairs are disjoint and nondegenerate:
`y_i ≠ y'_i` and `max {y_i, y'_i} < min {z_i, z'_i}` or `max {z_i, z'_i} < min {y_i, y'_i}`. -/
theorem revRev_multistationary_iff (hyy : y ≠ y') (hzz : z ≠ z') :
    (revRev y y' z z').HasMultistationarityCapacity ↔
      (∃ μ : ℝ, μ ≠ 0 ∧ ∀ s, rv z z' s = μ * rv y y' s) ∧
        ∃ i, y i ≠ y' i ∧
          (max (y i) (y' i) < min (z i) (z' i) ∨ max (z i) (z' i) < min (y i) (y' i)) := by
  constructor
  · intro h
    have hpar : ∃ μ : ℝ, ∀ s, rv z z' s = μ * rv y y' s := by
      by_contra hno
      exact revRev_not_multistationary_of_not_parallel hyy hno h
    obtain ⟨μ, hw⟩ := hpar
    have hμ : μ ≠ 0 := by
      rintro rfl
      obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hzz
      exact hs₀ (by rw [hw s₀, zero_mul])
    refine ⟨⟨μ, hμ, hw⟩, ?_⟩
    by_contra hno
    push Not at hno
    have hns : ∀ s, y s ≠ y' s →
        ¬ max (y s) (y' s) < min (z s) (z' s) ∧ ¬ max (z s) (z' s) < min (y s) (y' s) :=
      fun s hs => by
        have := hno s hs
        exact ⟨not_lt.mpr this.1, not_lt.mpr this.2⟩
    rcases lt_or_gt_of_ne hμ with hneg | hpos
    · -- exchange `z` and `z'`
      have hw' : ∀ s, rv z' z s = -μ * rv y y' s := fun s => by
        have := hw s; simp only [rv] at this ⊢; linarith
      refine revRev_not_multistationary_of_monotone hyy (by linarith) hw' (fun s => ?_)
        (revRev_capacity_swap_imp h)
      by_cases hs : y s = y' s
      · have : rv y y' s = 0 := by simp [rv, hs]
        simp [this]
      · have h1 := hns s hs
        rw [max_comm (z s) (z' s), min_comm (z s) (z' s)] at h1
        exact nonseparated_signs (a := y s) (a' := y' s) (b := z' s) (b' := z s) rfl rfl
          (by
            have : rv z' z s * rv y y' s = -μ * (rv y y' s) ^ 2 := by rw [hw' s]; ring
            have hv : rv y y' s ≠ 0 := by
              simp only [rv]; intro h0; apply hs; exact_mod_cast (sub_eq_zero.mp h0).symm
            show 0 < rv y y' s * rv z' z s
            rw [mul_comm, this]
            exact mul_pos (by linarith) (by positivity))
          ⟨h1.1, h1.2⟩
    · refine revRev_not_multistationary_of_monotone hyy hpos hw (fun s => ?_) h
      by_cases hs : y s = y' s
      · have : rv y y' s = 0 := by simp [rv, hs]
        simp [this]
      · exact nonseparated_signs (a := y s) (a' := y' s) (b := z s) (b' := z' s) rfl rfl
          (by
            have hv : rv y y' s ≠ 0 := by
              simp only [rv]; intro h0; apply hs; exact_mod_cast (sub_eq_zero.mp h0).symm
            show 0 < rv y y' s * rv z z' s
            rw [hw s]
            have : rv y y' s * (μ * rv y y' s) = μ * (rv y y' s) ^ 2 := by ring
            rw [this]; positivity)
          (hns s hs)
  · rintro ⟨⟨μ, hμ, hw⟩, i, hyi, hsep⟩
    exact revRev_multistationary_of_separated hμ hw i hyi hsep

end Network

end CRNT
