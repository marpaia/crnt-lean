import CRNT.Multistationarity.TwoReactionNondegenerate

/-!
# One reversible and one irreversible reaction (Joshi–Shiu 2017, Theorem 5.8)

For the network `y ⇌ y'`, `z → z'` (reactions `0 : y → y'`, `1 : y' → y`, `2 : z → z'`),
Joshi and Shiu (Theorem 5.8, building on Boros) show: the network is multistationary iff
`y' − y = −λ (z' − z)` for some `λ ≠ 0`, and, after switching `y` and `y'` if necessary so that
`λ > 0`, `β_i = (y'_i − y_i)(z_i − y_i) < 0` for some species `i`.

This module proves the theorem directly, without the deficiency-one algorithm. Write
`v = y' − y`, `d = z − y`. With `v = −λ (z' − z)`, `λ > 0`, the positive steady states solve
`κ₀ = κ₁ x^{v} + (κ₂/λ) x^{d}`; along a class line `x₁ + τ v` the right side has derivative
`κ₁ x^v ∑ v_s²/x_s + (κ₂/λ) x^d ∑ β_s/x_s`.

* If `β ≥ 0`, the right side is strictly increasing: at most one steady state per class.
* If `β_i < 0`, freeze every other species at a large value `M`. The equation tends, as `M → ∞`,
  to the one-species equation `κ₀ = |d_i| u^{v_i} + |v_i| u^{d_i}` in `u = x_i`, whose right side
  (exponents of opposite signs) has a strict minimum at `u = 1`; three sample points and the
  intermediate value theorem give two steady states for large `M`.

* `revIrr`, `revIrr_field`.
* `revIrr_parallel_of_steadyState`: a positive steady state forces `y' − y = −λ (z' − z)`, `λ ≠ 0`.
* `revIrr_not_multistationary_of_beta_nonneg`, `revIrr_multistationary_of_beta_neg`.
* `revIrr_multistationary_iff`: Theorem 5.8.
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network `y ⇌ y'`, `z → z'`: reactions `0 : y → y'`, `1 : y' → y`, `2 : z → z'`. -/
def revIrr (y y' z z' : Complex S) : Network S :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨y, y'⟩ else if r = 1 then ⟨y', y⟩ else ⟨z, z'⟩⟩

section

variable (y y' z z' : Complex S)

theorem revIrr_field (κ : RateConstants (revIrr y y' z z')) (x : Concentration S) (s : S) :
    (revIrr y y' z z').massActionVectorField κ x s =
      (κ.k (0 : Fin 3) * y.massActionMonomial x - κ.k (1 : Fin 3) * y'.massActionMonomial x) *
          rv y y' s + κ.k (2 : Fin 3) * z.massActionMonomial x * rv z z' s := by
  rw [massActionVectorField_apply]
  change ∑ r : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  show κ.k (0 : Fin 3) * y.massActionMonomial x * ((y' s : ℝ) - y s) +
      κ.k (1 : Fin 3) * y'.massActionMonomial x * ((y s : ℝ) - y' s) +
      κ.k (2 : Fin 3) * z.massActionMonomial x * ((z' s : ℝ) - z s) = _
  simp only [rv]; ring

end

variable {y y' z z' : Complex S}

/-- **Consistency.** A positive steady state forces `y' − y = −λ (z' − z)` with `λ ≠ 0`. -/
theorem revIrr_parallel_of_steadyState (hzz : z ≠ z') (κ : RateConstants (revIrr y y' z z'))
    {x : Concentration S} (hx : x.Positive)
    (hss : (revIrr y y' z z').IsMassActionSteadyState κ x) :
    ∃ lam : ℝ, lam ≠ 0 ∧ ∀ s, rv y y' s = -lam * rv z z' s := by
  set A := κ.k (0 : Fin 3) * y.massActionMonomial x - κ.k (1 : Fin 3) * y'.massActionMonomial x
  have hC : 0 < κ.k (2 : Fin 3) * z.massActionMonomial x :=
    mul_pos (κ.positive _) (Complex.massActionMonomial_pos hx z)
  have h : ∀ s, A * rv y y' s + κ.k (2 : Fin 3) * z.massActionMonomial x * rv z z' s = 0 :=
    fun s => by rw [← revIrr_field]; exact hss s
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hzz
  have hA : A ≠ 0 := by
    intro hA0; have := h s₀; rw [hA0, zero_mul, zero_add] at this
    exact hs₀ ((mul_eq_zero.mp this).resolve_left hC.ne')
  refine ⟨κ.k (2 : Fin 3) * z.massActionMonomial x / A, div_ne_zero hC.ne' hA, fun s => ?_⟩
  have := h s
  field_simp
  linarith

/-- Positive steady states under the orientation `y' − y = −λ (z' − z)`, `λ > 0`:
`κ₀ x^y = κ₁ x^{y'} + (κ₂/λ) x^z`. -/
theorem revIrr_steady_iff (hyy : y ≠ y') {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) (κ : RateConstants (revIrr y y' z z'))
    (x : Concentration S) :
    (revIrr y y' z z').IsMassActionSteadyState κ x ↔
      κ.k (0 : Fin 3) * y.massActionMonomial x =
        κ.k (1 : Fin 3) * y'.massActionMonomial x +
          κ.k (2 : Fin 3) / lam * z.massActionMonomial x := by
  have hw : ∀ s, rv z z' s = -(rv y y' s) / lam := fun s => by
    have := hneg s; field_simp; linarith
  have hF : ∀ s, (revIrr y y' z z').massActionVectorField κ x s =
      (κ.k (0 : Fin 3) * y.massActionMonomial x - κ.k (1 : Fin 3) * y'.massActionMonomial x -
        κ.k (2 : Fin 3) / lam * z.massActionMonomial x) * rv y y' s := by
    intro s; rw [revIrr_field, hw s]; field_simp; ring
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  constructor
  · intro h
    have h0 : (revIrr y y' z z').massActionVectorField κ x s₀ = 0 := h s₀
    rw [hF s₀] at h0
    have := (mul_eq_zero.mp h0).resolve_right hs₀
    linarith
  · intro h s
    show (revIrr y y' z z').massActionVectorField κ x s = 0
    rw [hF s]
    have : κ.k (0 : Fin 3) * y.massActionMonomial x - κ.k (1 : Fin 3) * y'.massActionMonomial x -
        κ.k (2 : Fin 3) / lam * z.massActionMonomial x = 0 := by linarith
    rw [this, zero_mul]

theorem revIrr_stoichSubspace_le {lam : ℝ} (hneg : ∀ s, rv y y' s = -lam * rv z z' s)
    (hlam : lam ≠ 0) :
    (revIrr y y' z z').stoichSubspace ≤ Submodule.span ℝ {rv y y'} := by
  apply Submodule.span_le.2
  rintro _ ⟨r, rfl⟩
  have hw : rv z z' = (-lam⁻¹) • rv y y' := by
    funext s; rw [Pi.smul_apply, smul_eq_mul, hneg s]; field_simp
  fin_cases r
  · show (revIrr y y' z z').reactionVector (0 : Fin 3) ∈ _
    have : (revIrr y y' z z').reactionVector (0 : Fin 3) = rv y y' := by funext s; rfl
    rw [this]; exact Submodule.mem_span_singleton_self _
  · show (revIrr y y' z z').reactionVector (1 : Fin 3) ∈ _
    have : (revIrr y y' z z').reactionVector (1 : Fin 3) = (-1 : ℝ) • rv y y' := by
      funext s; show ((y s : ℝ) - y' s) = _; simp [rv]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · show (revIrr y y' z z').reactionVector (2 : Fin 3) ∈ _
    have : (revIrr y y' z z').reactionVector (2 : Fin 3) = rv z z' := by funext s; rfl
    rw [this, hw]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Necessity of a negative `β`.** With `y' − y = −λ (z' − z)`, `λ > 0`, and `β ≥ 0`, a class
contains at most one positive steady state. -/
theorem revIrr_not_multistationary_of_beta_nonneg (hyy : y ≠ y') {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) (hβ : ∀ s, 0 ≤ twoBeta y y' z s) :
    ¬ (revIrr y y' z z').HasMultistationarityCapacity := by
  rintro ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩
  have hc : x₂ - x₁ ∈ Submodule.span ℝ {rv y y'} :=
    revIrr_stoichSubspace_le hneg hlam.ne' (hc₁.symm.trans hc₂)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hc
  have hx₂ : x₂ = x₁ + t • rv y y' := by rw [ht]; abel
  subst hx₂
  have ht0 : t ≠ 0 := by rintro rfl; simp at hne
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  set c := κ.k (2 : Fin 3) / lam with hcdef
  have hc0 : 0 < c := div_pos (κ.positive _) hlam
  -- the steady-state function along the line
  let P : ℝ → ℝ := fun τ => κ.k (1 : Fin 3) * Real.exp (lineH y y' x₁ (rv y y') τ) +
    c * Real.exp (lineH y z x₁ (rv y y') τ)
  have hPval : ∀ τ, (x₁ + τ • rv y y').Positive →
      P τ * y.massActionMonomial (x₁ + τ • rv y y') =
        κ.k (1 : Fin 3) * y'.massActionMonomial (x₁ + τ • rv y y') +
          c * z.massActionMonomial (x₁ + τ • rv y y') := by
    intro τ hτ
    have hmy := Complex.massActionMonomial_pos hτ y
    simp only [P, lineH_eq_log _ _ hτ]
    rw [Real.exp_log (div_pos (Complex.massActionMonomial_pos hτ _) hmy),
      Real.exp_log (div_pos (Complex.massActionMonomial_pos hτ _) hmy)]
    field_simp
  have hP0 : P 0 = κ.k (0 : Fin 3) := by
    have h := (revIrr_steady_iff hyy hlam hneg κ x₁).mp hs₁
    have h1 := hPval 0 (by simpa using hp₁)
    simp only [zero_smul, add_zero] at h1
    have hmy := (Complex.massActionMonomial_pos hp₁ y).ne'
    apply mul_right_cancel₀ hmy; rw [h1, h]
  have hPt : P t = κ.k (0 : Fin 3) := by
    have h := (revIrr_steady_iff hyy hlam hneg κ _).mp hs₂
    have h1 := hPval t hp₂
    have hmy := (Complex.massActionMonomial_pos hp₂ y).ne'
    apply mul_right_cancel₀ hmy; rw [h1, h]
  -- positivity on the segment
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
  -- the derivative is positive
  have hderiv : ∀ τ, (x₁ + τ • rv y y').Positive → HasDerivAt P
      (κ.k (1 : Fin 3) * Real.exp (lineH y y' x₁ (rv y y') τ) *
          (∑ s, twoBeta y y' y' s / (x₁ s + τ * rv y y' s)) +
        c * Real.exp (lineH y z x₁ (rv y y') τ) *
          (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s))) τ := by
    intro τ hτ
    have hpos : ∀ s, 0 < x₁ s + τ * rv y y' s := fun s => by simpa using hτ s
    exact (((hasDerivAt_lineH x₁ hpos).exp.const_mul _).add
      ((hasDerivAt_lineH x₁ hpos).exp.const_mul _)).congr_deriv (by ring)
  have hderiv_pos : ∀ τ, (x₁ + τ • rv y y').Positive →
      0 < κ.k (1 : Fin 3) * Real.exp (lineH y y' x₁ (rv y y') τ) *
          (∑ s, twoBeta y y' y' s / (x₁ s + τ * rv y y' s)) +
        c * Real.exp (lineH y z x₁ (rv y y') τ) *
          (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s)) := by
    intro τ hτ
    have hpos : ∀ s, 0 < x₁ s + τ * rv y y' s := fun s => by simpa using hτ s
    have hA : 0 < ∑ s, twoBeta y y' y' s / (x₁ s + τ * rv y y' s) := by
      have hsq : ∀ s, twoBeta y y' y' s = rv y y' s ^ 2 := fun s => by simp [twoBeta, rv]; ring
      refine lt_of_lt_of_le (div_pos (by rw [hsq]; positivity) (hpos s₀))
        (Finset.single_le_sum (f := fun s => twoBeta y y' y' s / (x₁ s + τ * rv y y' s))
          (fun s _ => div_nonneg (by rw [hsq]; positivity) (hpos s).le) (Finset.mem_univ s₀))
    have hB : 0 ≤ ∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s) :=
      Finset.sum_nonneg fun s _ => div_nonneg (hβ s) (hpos s).le
    have h1 : 0 < κ.k (1 : Fin 3) * Real.exp (lineH y y' x₁ (rv y y') τ) *
        (∑ s, twoBeta y y' y' s / (x₁ s + τ * rv y y' s)) :=
      mul_pos (mul_pos (κ.positive _) (Real.exp_pos _)) hA
    have h2 : 0 ≤ c * Real.exp (lineH y z x₁ (rv y y') τ) *
        (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s)) :=
      mul_nonneg (mul_nonneg hc0.le (Real.exp_pos _).le) hB
    linarith
  -- mean value theorem
  have hcont : ∀ a b, (∀ τ ∈ Set.Icc a b, (x₁ + τ • rv y y').Positive) →
      ContinuousOn P (Set.Icc a b) := fun a b hab τ hτ =>
    (hderiv τ (hab τ hτ)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne ht0 with htn | htp
  · have hI : ∀ τ ∈ Set.Icc t 0, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg_of_nonpos hτ.2 htn.le, (div_le_one_of_neg htn).mpr hτ.1⟩
    obtain ⟨c', hc', hcd⟩ := exists_hasDerivAt_eq_slope P _ htn (hcont t 0 hI)
      (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hP0, hPt, sub_self, zero_div] at hcd
    exact (hderiv_pos c' (hI c' ⟨hc'.1.le, hc'.2.le⟩)).ne' hcd
  · have hI : ∀ τ ∈ Set.Icc 0 t, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg hτ.1 htp.le, (div_le_one htp).mpr hτ.2⟩
    obtain ⟨c', hc', hcd⟩ := exists_hasDerivAt_eq_slope P _ htp (hcont 0 t hI)
      (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hP0, hPt, sub_self, zero_div] at hcd
    exact (hderiv_pos c' (hI c' ⟨hc'.1.le, hc'.2.le⟩)).ne' hcd

omit [DecidableEq S] in
/-- `log (M + c) − log M → 0` as `M → ∞`. -/
theorem tendsto_log_add_sub_log (c : ℝ) :
    Tendsto (fun M : ℝ => Real.log (M + c) - Real.log M) atTop (𝓝 0) := by
  have h0 : Tendsto (fun M : ℝ => c / M) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun M : ℝ => 1 + c / M) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  have h2 : Tendsto (fun M : ℝ => Real.log (1 + c / M)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    exact this
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (|c|)] with M hM
  have hM0 : 0 < M := lt_of_le_of_lt (abs_nonneg c) hM
  have hMc : 0 < M + c := by have := neg_abs_le c; linarith
  rw [← Real.log_div hMc.ne' hM0.ne']
  congr 1; field_simp

/-- The point with species `i` at `1` and every other species at `M`, moved by `t (y' − y)`. -/
noncomputable def frozenPoint (i : S) (v : S → ℝ) (M t : ℝ) : Concentration S :=
  fun s => (if s = i then 1 else M) + t * v s

/-- **The frozen-species limit of a monomial ratio.** For exponents `e`, the rescaled
`exp (∑_s e_s log x_s − ∑_{s ≠ i} e_s log M)` at `frozenPoint i v M t` tends to
`exp (e_i log (1 + t v_i))`. -/
theorem tendsto_frozen (i : S) (v e : S → ℝ) (t : ℝ) :
    Tendsto (fun M : ℝ => Real.exp (∑ s, e s * Real.log (frozenPoint i v M t s) -
        ∑ s ∈ Finset.univ.erase i, e s * Real.log M)) atTop
      (𝓝 (Real.exp (e i * Real.log (1 + t * v i)))) := by
  have hsplit : ∀ M : ℝ, ∑ s, e s * Real.log (frozenPoint i v M t s) -
      ∑ s ∈ Finset.univ.erase i, e s * Real.log M =
      e i * Real.log (1 + t * v i) +
        ∑ s ∈ Finset.univ.erase i, e s * (Real.log (M + t * v s) - Real.log M) := by
    intro M
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hi : frozenPoint i v M t i = 1 + t * v i := by simp [frozenPoint]
    have ho : ∀ s ∈ Finset.univ.erase i, frozenPoint i v M t s = M + t * v s := by
      intro s hs; simp [frozenPoint, Finset.ne_of_mem_erase hs]
    rw [hi, Finset.sum_congr rfl fun s hs => by rw [ho s hs]]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [hsplit]
  refine (Real.continuous_exp.tendsto _).comp ?_
  have := tendsto_finsetSum (Finset.univ.erase i) fun s _ =>
    (tendsto_log_add_sub_log (t * v s)).const_mul (e s)
  simpa using tendsto_const_nhds.add this

/-- `exp (a) − 1 > a` for `a ≠ 0`, in the form used below. -/
theorem frozen_min_gap {a b : ℝ} (hab : a * b < 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    |a| + |b| < |b| * Real.exp (σ * a) + |a| * Real.exp (σ * b) := by
  have ha : a ≠ 0 := by rintro rfl; simp at hab
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have e1 := Real.add_one_lt_exp (mul_ne_zero hσ0 ha)
  have e2 := Real.add_one_lt_exp (mul_ne_zero hσ0 hb)
  have hzero : |b| * (σ * a) + |a| * (σ * b) = 0 := by
    rcases lt_or_gt_of_ne ha with ha' | ha'
    · have hb' : 0 < b := by nlinarith
      rw [abs_of_neg ha', abs_of_pos hb']; ring
    · have hb' : b < 0 := by nlinarith
      rw [abs_of_pos ha', abs_of_neg hb']; ring
  have h1 : |b| * (σ * a + 1) ≤ |b| * Real.exp (σ * a) :=
    mul_le_mul_of_nonneg_left e1.le (abs_nonneg _)
  have h2 : |a| * (σ * b + 1) < |a| * Real.exp (σ * b) :=
    mul_lt_mul_of_pos_left e2 (abs_pos.mpr ha)
  nlinarith

/-- **Sufficiency of a negative `β`.** With `y' − y = −λ (z' − z)`, `λ > 0`, and `β_i < 0` for some
species `i`, the network is multistationary. -/
theorem revIrr_multistationary_of_beta_neg (hyy : y ≠ y') {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) {i : S} (hi : twoBeta y y' z i < 0) :
    (revIrr y y' z z').HasMultistationarityCapacity := by
  classical
  set v := rv y y' with hv
  set d : S → ℝ := fun s => (z s : ℝ) - y s with hd
  set a := v i with ha
  set b := d i with hb
  have hab : a * b < 0 := hi
  have ha0 : a ≠ 0 := by rintro h; rw [h, zero_mul] at hab; exact lt_irrefl 0 hab
  -- the limit one-species function and the level
  let f : ℝ → ℝ := fun σ => |b| * Real.exp (σ * a) + |a| * Real.exp (σ * b)
  have hf0 : f 0 = |a| + |b| := by
    show |b| * Real.exp (0 * a) + |a| * Real.exp (0 * b) = _
    simp; ring
  have hfp : |a| + |b| < f 1 := frozen_min_gap hab 1 (Or.inl rfl)
  have hfm : |a| + |b| < f (-1) := frozen_min_gap hab (-1) (Or.inr rfl)
  set L := ((|a| + |b|) + min (f 1) (f (-1))) / 2 with hL
  have hmin := lt_min hfp hfm
  have hL0 : |a| + |b| < L := by rw [hL]; linarith
  have hL1 : L < f 1 := by rw [hL]; have := min_le_left (f 1) (f (-1)); linarith
  have hL2 : L < f (-1) := by rw [hL]; have := min_le_right (f 1) (f (-1)); linarith
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL0
  -- sample parameters along the line: `1 + t a = e^{σ}`
  let tσ : ℝ → ℝ := fun σ => (Real.exp σ - 1) / a
  have htσ : ∀ σ, 1 + tσ σ * a = Real.exp σ := fun σ => by simp only [tσ]; field_simp; ring
  -- the rescaled ratios
  let Φ : ℝ → ℝ → ℝ := fun M t =>
    |b| * Real.exp (∑ s, v s * Real.log (frozenPoint i v M t s) -
        ∑ s ∈ Finset.univ.erase i, v s * Real.log M) +
    |a| * Real.exp (∑ s, d s * Real.log (frozenPoint i v M t s) -
        ∑ s ∈ Finset.univ.erase i, d s * Real.log M)
  have hlim : ∀ σ, Tendsto (fun M => Φ M (tσ σ)) atTop (𝓝 (f σ)) := by
    intro σ
    have e1 := tendsto_frozen i v v (tσ σ)
    have e2 := tendsto_frozen i v d (tσ σ)
    rw [htσ σ, Real.log_exp] at e1 e2
    have := (e1.const_mul |b|).add (e2.const_mul |a|)
    have hval : f σ = |b| * Real.exp (v i * σ) + |a| * Real.exp (d i * σ) := by
      show |b| * Real.exp (σ * a) + |a| * Real.exp (σ * b) = _
      rw [mul_comm σ a, mul_comm σ b]
    rw [hval]
    exact this
  -- choose `M` large
  set T : ℝ := |tσ 1| + |tσ (-1)| with hT
  set V : ℝ := ∑ s, |v s| + 1 with hV
  have hV0 : 0 < V := by positivity
  obtain ⟨M, hM1, hM0, hMm, hMb⟩ : ∃ M : ℝ, L < Φ M (tσ 1) ∧ Φ M (tσ 0) < L ∧
      L < Φ M (tσ (-1)) ∧ T * V + 1 < M := by
    have h1 := (hlim 1).eventually (lt_mem_nhds hL1)
    have h0 := (hlim 0).eventually (gt_mem_nhds (by rw [hf0]; exact hL0))
    have h2 := (hlim (-1)).eventually (lt_mem_nhds hL2)
    exact ((h1.and h0).and (h2.and (eventually_gt_atTop (T * V + 1)))).exists.imp
      fun M h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hMpos : 0 < M := by
    have : 0 ≤ T * V := mul_nonneg (by positivity) hV0.le
    linarith
  -- positivity along the line between the sample points
  have hposline : ∀ t, |t| ≤ T → (∀ s, s ≠ i → 0 < frozenPoint i v M t s) := by
    intro t ht s hs
    simp only [frozenPoint, hs, ↓reduceIte]
    have hvs : |v s| ≤ V := by
      have := Finset.single_le_sum (f := fun s => |v s|) (fun s _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [hV]; linarith
    have : |t * v s| ≤ T * V := by
      rw [abs_mul]; exact mul_le_mul ht hvs (abs_nonneg _) (by positivity)
    have := neg_abs_le (t * v s)
    linarith
  -- the interval: `tl < 0 < tr`, with values above `L` at both ends
  obtain ⟨tl, tr, htl, htr, hΦl, hΦr, hTl, hTr, hcoordi⟩ : ∃ tl tr : ℝ, tl < 0 ∧ 0 < tr ∧
      L < Φ M tl ∧ L < Φ M tr ∧ |tl| ≤ T ∧ |tr| ≤ T ∧
      ∀ t, tl ≤ t → t ≤ tr → Real.exp (-1) ≤ 1 + t * a := by
    have hT1 : |tσ 1| ≤ T := by rw [hT]; have := abs_nonneg (tσ (-1)); linarith
    have hT2 : |tσ (-1)| ≤ T := by rw [hT]; have := abs_nonneg (tσ 1); linarith
    have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    have he2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rcases lt_or_gt_of_ne ha0 with hneg' | hpos'
    · refine ⟨tσ 1, tσ (-1), ?_, ?_, hM1, hMm, hT1, hT2, fun t _ h2 => ?_⟩
      · simp only [tσ]; exact div_neg_of_pos_of_neg (by linarith) hneg'
      · simp only [tσ]; exact div_pos_of_neg_of_neg (by linarith) hneg'
      · have := htσ (-1)
        have : tσ (-1) * a ≤ t * a := mul_le_mul_of_nonpos_right h2 hneg'.le
        linarith
    · refine ⟨tσ (-1), tσ 1, ?_, ?_, hMm, hM1, hT2, hT1, fun t h1 _ => ?_⟩
      · simp only [tσ]; exact div_neg_of_neg_of_pos (by linarith) hpos'
      · simp only [tσ]; exact div_pos (by linarith) hpos'
      · have := htσ (-1)
        have : tσ (-1) * a ≤ t * a := mul_le_mul_of_nonneg_right h1 hpos'.le
        linarith
  have hΦ0 : Φ M 0 < L := by simpa [tσ] using hM0
  -- positivity of the point on `[tl, tr]`
  have hptpos : ∀ t, tl ≤ t → t ≤ tr → (frozenPoint i v M t).Positive := by
    intro t h1 h2 s
    by_cases hs : s = i
    · subst hs
      have := hcoordi t h1 h2
      simp only [frozenPoint, ↓reduceIte]
      rw [← ha]; linarith [Real.exp_pos (-1)]
    · refine hposline t ?_ s hs
      rw [abs_le]; constructor
      · have := (abs_le.mp hTl).1; linarith
      · have := (abs_le.mp hTr).2; linarith
  -- continuity of `Φ M` on `[tl, tr]`
  have hcont : ContinuousOn (Φ M) (Set.Icc tl tr) := by
    have hlogc : ∀ s, ContinuousOn (fun τ => Real.log (frozenPoint i v M τ s)) (Set.Icc tl tr) := by
      intro s
      have hlin : Continuous (fun τ => frozenPoint i v M τ s) := by
        simp only [frozenPoint]; fun_prop
      exact hlin.continuousOn.log fun t ht => (hptpos t ht.1 ht.2 s).ne'
    exact (continuousOn_const.mul (((continuousOn_finsetSum _ fun s _ =>
      continuousOn_const.mul (hlogc s)).sub continuousOn_const).rexp)).add
      (continuousOn_const.mul (((continuousOn_finsetSum _ fun s _ =>
        continuousOn_const.mul (hlogc s)).sub continuousOn_const).rexp))
  -- two solutions of `Φ M t = L`
  obtain ⟨τ₁, hτ₁, hΦτ₁⟩ := intermediate_value_Ioo' htl.le
    (hcont.mono (Set.Icc_subset_Icc le_rfl htr.le)) ⟨hΦ0, hΦl⟩
  obtain ⟨τ₂, hτ₂, hΦτ₂⟩ := intermediate_value_Ioo htr.le
    (hcont.mono (Set.Icc_subset_Icc htl.le le_rfl)) ⟨hΦ0, hΦr⟩
  -- the rate constants
  set k₁ : ℝ := |b| * Real.exp (-(∑ s ∈ Finset.univ.erase i, v s * Real.log M)) with hk₁
  set k₂ : ℝ := lam * (|a| * Real.exp (-(∑ s ∈ Finset.univ.erase i, d s * Real.log M)))
    with hk₂
  have hb0 : b ≠ 0 := by rintro h; rw [h, mul_zero] at hab; exact lt_irrefl 0 hab
  have hk₁pos : 0 < k₁ := mul_pos (abs_pos.mpr hb0) (Real.exp_pos _)
  have hk₂pos : 0 < k₂ := mul_pos hlam (mul_pos (abs_pos.mpr ha0) (Real.exp_pos _))
  let κ : RateConstants (revIrr y y' z z') :=
    ⟨fun (r : Fin 3) => if r = 0 then L else if r = 1 then k₁ else k₂, fun (r : Fin 3) => by
      fin_cases r <;> simp [hLpos, hk₁pos, hk₂pos]⟩
  have hκ0 : κ.k (0 : Fin 3) = L := rfl
  have hκ1 : κ.k (1 : Fin 3) = k₁ := rfl
  have hκ2 : κ.k (2 : Fin 3) = k₂ := rfl
  -- steady states on the line are the solutions of `Φ M t = L`
  have hsteady : ∀ t, (frozenPoint i v M t).Positive → Φ M t = L →
      (revIrr y y' z z').IsMassActionSteadyState κ (frozenPoint i v M t) := by
    intro t hpos hΦ
    rw [revIrr_steady_iff hyy hlam hneg κ, hκ0, hκ1, hκ2]
    have hmy := Complex.massActionMonomial_pos hpos y
    have r1 : y'.massActionMonomial (frozenPoint i v M t) / y.massActionMonomial (frozenPoint i v M t)
        = Real.exp (∑ s, v s * Real.log (frozenPoint i v M t s)) := by
      rw [show (∑ s, v s * Real.log (frozenPoint i v M t s)) =
          ∑ s, ((y' s : ℝ) - y s) * Real.log (frozenPoint i v M t s) from rfl,
        ← log_ratio_monomial hpos, Real.exp_log (div_pos (Complex.massActionMonomial_pos hpos _) hmy)]
    have r2 : z.massActionMonomial (frozenPoint i v M t) / y.massActionMonomial (frozenPoint i v M t)
        = Real.exp (∑ s, d s * Real.log (frozenPoint i v M t s)) := by
      rw [show (∑ s, d s * Real.log (frozenPoint i v M t s)) =
          ∑ s, ((z s : ℝ) - y s) * Real.log (frozenPoint i v M t s) from rfl,
        ← log_ratio_monomial hpos, Real.exp_log (div_pos (Complex.massActionMonomial_pos hpos _) hmy)]
    have hΦ' : k₁ * (y'.massActionMonomial (frozenPoint i v M t) /
          y.massActionMonomial (frozenPoint i v M t)) +
        k₂ / lam * (z.massActionMonomial (frozenPoint i v M t) /
          y.massActionMonomial (frozenPoint i v M t)) = L := by
      rw [r1, r2, ← hΦ]
      simp only [Φ, hk₁, hk₂, sub_eq_add_neg, Real.exp_add]
      have := hlam.ne'
      field_simp
      simp only [mul_comm (Real.log M)]
      ring
    have hmy' := hmy.ne'
    rw [← hΦ']
    field_simp
  have hp₁ := hptpos τ₁ (by linarith [hτ₁.1]) (by linarith [hτ₁.2])
  have hp₂ := hptpos τ₂ (by linarith [hτ₂.1]) (by linarith [hτ₂.2])
  refine ⟨κ, frozenPoint i v M τ₁, frozenPoint i v M τ₁, frozenPoint i v M τ₂,
    ⟨StoichCompatible.refl _ _, hp₁⟩, ⟨?_, hp₂⟩, hsteady τ₁ hp₁ hΦτ₁, hsteady τ₂ hp₂ hΦτ₂, ?_⟩
  · show frozenPoint i v M τ₂ - frozenPoint i v M τ₁ ∈ (revIrr y y' z z').stoichSubspace
    have : frozenPoint i v M τ₂ - frozenPoint i v M τ₁ = (τ₂ - τ₁) • v := by
      funext s; simp only [frozenPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    have hv0 : (revIrr y y' z z').reactionVector (0 : Fin 3) = v := by funext s; rfl
    rw [← hv0]
    exact Submodule.smul_mem _ _ ((revIrr y y' z z').reactionVector_mem_stoichSubspace _)
  · intro heq
    have := congrFun heq i
    simp only [frozenPoint, ↓reduceIte, add_right_inj] at this
    have : τ₁ = τ₂ := mul_right_cancel₀ ha0 this
    linarith [hτ₁.2, hτ₂.1]

/-- Swapping the two complexes of the reversible pair permutes the reactions. -/
theorem revIrr_stoichSubspace_swap :
    (revIrr y' y z z').stoichSubspace = (revIrr y y' z z').stoichSubspace := by
  have key : ∀ (p p' : Complex S), (revIrr p' p z z').stoichSubspace ≤
      (revIrr p p' z z').stoichSubspace := by
    intro p p'
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    fin_cases r
    · exact (revIrr p p' z z').reactionVector_mem_stoichSubspace (1 : Fin 3)
    · exact (revIrr p p' z z').reactionVector_mem_stoichSubspace (0 : Fin 3)
    · exact (revIrr p p' z z').reactionVector_mem_stoichSubspace (2 : Fin 3)
  exact le_antisymm (key y y') (key y' y)

theorem revIrr_capacity_swap_imp (h : (revIrr y y' z z').HasMultistationarityCapacity) :
    (revIrr y' y z z').HasMultistationarityCapacity := by
  obtain ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne⟩ := h
  let κ' : RateConstants (revIrr y' y z z') :=
    ⟨fun (r : Fin 3) => if r = 0 then κ.k (1 : Fin 3) else if r = 1 then κ.k (0 : Fin 3)
      else κ.k (2 : Fin 3), fun (r : Fin 3) => by fin_cases r <;> simp <;> exact κ.positive _⟩
  have hfield : ∀ x s, (revIrr y' y z z').massActionVectorField κ' x s =
      (revIrr y y' z z').massActionVectorField κ x s := by
    intro x s
    rw [revIrr_field, revIrr_field]
    show (κ.k (1 : Fin 3) * y'.massActionMonomial x - κ.k (0 : Fin 3) * y.massActionMonomial x) *
        rv y' y s + κ.k (2 : Fin 3) * z.massActionMonomial x * rv z z' s = _
    simp only [rv]; ring
  have hss : ∀ x, (revIrr y y' z z').IsMassActionSteadyState κ x →
      (revIrr y' y z z').IsMassActionSteadyState κ' x := fun x hx s => by
    show (revIrr y' y z z').massActionVectorField κ' x s = 0
    rw [hfield]; exact hx s
  have hcomp : ∀ a b, (revIrr y y' z z').StoichCompatible a b →
      (revIrr y' y z z').StoichCompatible a b := fun a b h => by
    show b - a ∈ (revIrr y' y z z').stoichSubspace
    rw [revIrr_stoichSubspace_swap]; exact h
  exact ⟨κ', x₀, x₁, x₂, ⟨hcomp _ _ hc₁, hp₁⟩, ⟨hcomp _ _ hc₂, hp₂⟩, hss _ hs₁, hss _ hs₂, hne⟩

theorem revIrr_capacity_swap :
    (revIrr y' y z z').HasMultistationarityCapacity ↔
      (revIrr y y' z z').HasMultistationarityCapacity :=
  ⟨revIrr_capacity_swap_imp, revIrr_capacity_swap_imp⟩

/-- **Joshi–Shiu 2017, Theorem 5.8.** The network `y ⇌ y'`, `z → z'` (`y ≠ y'`, `z ≠ z'`) is
multistationary iff `y' − y = −λ (z' − z)` for some `λ ≠ 0` and, orienting the reversible pair so
that `λ > 0`, `β_i = (y'_i − y_i)(z_i − y_i) < 0` for some species `i`. -/
theorem revIrr_multistationary_iff (hyy : y ≠ y') (hzz : z ≠ z') :
    (revIrr y y' z z').HasMultistationarityCapacity ↔
      (∃ lam : ℝ, 0 < lam ∧ (∀ s, rv y y' s = -lam * rv z z' s) ∧
          ∃ i, twoBeta y y' z i < 0) ∨
        (∃ lam : ℝ, 0 < lam ∧ (∀ s, rv y' y s = -lam * rv z z' s) ∧
          ∃ i, twoBeta y' y z i < 0) := by
  constructor
  · intro h
    have h0 := h
    obtain ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, -, hs₁, -, -⟩ := h0
    obtain ⟨lam, hlam0, hneg⟩ := revIrr_parallel_of_steadyState hzz κ hp₁ hs₁
    rcases lt_or_gt_of_ne hlam0 with hl | hl
    · right
      have hneg' : ∀ s, rv y' y s = -(-lam) * rv z z' s := fun s => by
        have := hneg s; simp only [rv] at this ⊢; linarith
      refine ⟨-lam, by linarith, hneg', ?_⟩
      by_contra hno
      push Not at hno
      exact revIrr_not_multistationary_of_beta_nonneg (Ne.symm hyy) (by linarith) hneg' hno
        (revIrr_capacity_swap_imp h)
    · left
      refine ⟨lam, hl, hneg, ?_⟩
      by_contra hno
      push Not at hno
      exact revIrr_not_multistationary_of_beta_nonneg hyy hl hneg hno h
  · rintro (⟨lam, hl, hneg, i, hi⟩ | ⟨lam, hl, hneg, i, hi⟩)
    · exact revIrr_multistationary_of_beta_neg hyy hl hneg hi
    · exact revIrr_capacity_swap.mp (revIrr_multistationary_of_beta_neg (Ne.symm hyy) hl hneg hi)

end Network

end CRNT
