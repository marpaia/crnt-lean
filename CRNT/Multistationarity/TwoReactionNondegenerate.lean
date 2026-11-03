import CRNT.Multistationarity.TwoReaction
import CRNT.Kinetics.MassActionJacobian

/-!
# Nondegenerate multistationarity of two-reaction networks (Joshi–Shiu 2017, Theorem 5.2)

A positive steady state `x` is **nondegenerate** when the Jacobian of the mass-action field is
injective on the stoichiometric subspace (equivalently, `Im (df(x)|_S) = S`). Joshi and Shiu,
Theorem 5.2: the network `y → y'`, `z → z'` is nondegenerately multistationary (two nondegenerate
positive steady states in one class) iff

1. `y' − y = −λ (z' − z)` with `λ > 0`,
2. `β = (y' − y) ∗ (z − y)` has a positive and a negative coordinate, and
3. if `β` has exactly one positive coordinate `p` and exactly one negative coordinate `q`, then the
   projection of the reactant polytope `[y, z]` to the `(p, q)`-plane does not have slope `−1`,
   i.e. `(z − y)_p + (z − y)_q ≠ 0`.

Along a class line `x(τ) = x₁ + τ (y' − y)` the steady states solve
`h(τ) = ∑_s (z_s − y_s) log x_s(τ) = const`, with `h' = ∑_s β_s / x_s` and
`h'' = −∑_s β_s v_s / x_s²`. A steady state is nondegenerate iff `h' ≠ 0` there
(`twoRxn_nondegenerate_iff`).

* `IsNondegenerateSteadyState`, `HasNondegenerateMultistationarity`.
* `twoRxn_nondegenerate_iff`: the nondegeneracy criterion.
* `twoRxn_nondegMultistationary_necessary`: necessity of 1–3.
* `twoRxn_nondegMultistationary_sufficient`, `twoRxn_nondegMultistationary_iff`: Theorem 5.2.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A positive steady state is **nondegenerate** when the Jacobian is injective on the
stoichiometric subspace. -/
def IsNondegenerateSteadyState (N : Network S) (κ : RateConstants N) (x : Concentration S) :
    Prop :=
  ∀ u ∈ N.stoichSubspace, N.massActionJacobianCLM κ x u = 0 → u = 0

/-- **Nondegenerate multistationarity**: two distinct nondegenerate positive steady states in one
positive compatibility class, for some rate constants. -/
def HasNondegenerateMultistationarity (N : Network S) : Prop :=
  ∃ (κ : RateConstants N) (x₀ x y : Concentration S),
    x ∈ N.positiveCompatibilityClass x₀ ∧ y ∈ N.positiveCompatibilityClass x₀ ∧
      N.IsMassActionSteadyState κ x ∧ N.IsMassActionSteadyState κ y ∧ x ≠ y ∧
        N.IsNondegenerateSteadyState κ x ∧ N.IsNondegenerateSteadyState κ y

theorem HasNondegenerateMultistationarity.capacity {N : Network S}
    (h : N.HasNondegenerateMultistationarity) : N.HasMultistationarityCapacity := by
  obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne, -, -⟩ := h
  exact ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩

theorem massActionJacobianCLM_apply_sum (N : Network S) (κ : RateConstants N)
    (x u : Concentration S) :
    N.massActionJacobianCLM κ x u =
      ∑ r : N.R, (κ.k r * ∑ j, massActionMonomialGrad (N.reaction r).source x j * u j) •
        N.reactionVector r := by
  simp [massActionJacobianCLM, smul_eq_mul]

theorem massActionMonomialGrad_eq_of_pos (y : Complex S) {x : Concentration S}
    (hx : x.Positive) (j : S) :
    massActionMonomialGrad y x j = (y j : ℝ) * y.massActionMonomial x / x j := by
  rw [eq_div_iff (hx j).ne', massActionMonomialGrad_mul_coord]

variable {y y' z z' : Complex S}

theorem twoRxn_sum_vec (g : (twoRxn y y' z z').R → (S → ℝ)) :
    ∑ r, g r = g (0 : Fin 2) + g (1 : Fin 2) := Fin.sum_univ_two g

theorem twoRxn_reactionVector_zero :
    (twoRxn y y' z z').reactionVector (0 : Fin 2) = rv y y' := by
  funext s; rfl

theorem twoRxn_reactionVector_one :
    (twoRxn y y' z z').reactionVector (1 : Fin 2) = rv z z' := by
  funext s; rfl

/-- A positive steady state forces the stoichiometric subspace to be the line `span {y' − y}`. -/
theorem twoRxn_stoichSubspace_eq (κ : RateConstants (twoRxn y y' z z')) {x : Concentration S}
    (hx : x.Positive) (hss : (twoRxn y y' z z').IsMassActionSteadyState κ x) :
    (twoRxn y y' z z').stoichSubspace = Submodule.span ℝ {rv y y'} := by
  apply le_antisymm
  · intro u hu
    obtain ⟨t, ht⟩ := twoRxn_exists_line κ hx hss (x₂ := x + u) (by
      show x + u - x ∈ _; rw [add_sub_cancel_left]; exact hu)
    have : u = t • rv y y' := by
      have := congrArg (· - x) ht; simpa using this
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    rw [← twoRxn_reactionVector_zero]
    exact (twoRxn y y' z z').reactionVector_mem_stoichSubspace (0 : Fin 2)

/-- The Jacobian along `y' − y` at a positive steady state:
`J(x)(y' − y) = −κ₀ x^y (∑_s β_s / x_s) (y' − y)`. -/
theorem twoRxn_jacobian_rv (κ : RateConstants (twoRxn y y' z z')) {x : Concentration S}
    (hx : x.Positive) (hss : (twoRxn y y' z z').IsMassActionSteadyState κ x) :
    (twoRxn y y' z z').massActionJacobianCLM κ x (rv y y') =
      (-(κ.k (0 : Fin 2) * y.massActionMonomial x * ∑ s, twoBeta y y' z s / x s)) • rv y y' := by
  have hneg := twoRxn_negMultiple_of_steadyState κ hx hss
  have hmy := Complex.massActionMonomial_pos hx y
  have hmz := Complex.massActionMonomial_pos hx z
  have hk0 := κ.positive (0 : Fin 2)
  have hk1 := κ.positive (1 : Fin 2)
  have hw : rv z z' = (-(κ.k (0 : Fin 2) * y.massActionMonomial x /
      (κ.k (1 : Fin 2) * z.massActionMonomial x))) • rv y y' := by
    funext s
    rw [Pi.smul_apply, smul_eq_mul, hneg s]
    field_simp
  rw [massActionJacobianCLM_apply_sum, twoRxn_sum_vec, twoRxn_reactionVector_zero,
    twoRxn_reactionVector_one, hw, smul_smul, ← add_smul]
  congr 1
  show κ.k (0 : Fin 2) * ∑ j, massActionMonomialGrad y x j * rv y y' j +
      (κ.k (1 : Fin 2) * ∑ j, massActionMonomialGrad z x j * rv y y' j) *
        -(κ.k (0 : Fin 2) * y.massActionMonomial x / (κ.k (1 : Fin 2) * z.massActionMonomial x)) =
    -(κ.k (0 : Fin 2) * y.massActionMonomial x * ∑ s, twoBeta y y' z s / x s)
  have e1 : ∑ j, massActionMonomialGrad y x j * rv y y' j =
      y.massActionMonomial x * ∑ j, (y j : ℝ) * rv y y' j / x j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [massActionMonomialGrad_eq_of_pos _ hx]; ring
  have e2 : ∑ j, massActionMonomialGrad z x j * rv y y' j =
      z.massActionMonomial x * ∑ j, (z j : ℝ) * rv y y' j / x j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [massActionMonomialGrad_eq_of_pos _ hx]; ring
  have e3 : ∑ s, twoBeta y y' z s / x s =
      ∑ j, (z j : ℝ) * rv y y' j / x j - ∑ j, (y j : ℝ) * rv y y' j / x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [twoBeta, rv]; ring
  rw [e1, e2, e3]
  field_simp
  ring

/-- **Nondegeneracy criterion.** A positive steady state of the two-reaction network is
nondegenerate iff `∑_s β_s / x_s ≠ 0`. -/
theorem twoRxn_nondegenerate_iff (hyy : y ≠ y') (κ : RateConstants (twoRxn y y' z z'))
    {x : Concentration S} (hx : x.Positive)
    (hss : (twoRxn y y' z z').IsMassActionSteadyState κ x) :
    (twoRxn y y' z z').IsNondegenerateSteadyState κ x ↔ ∑ s, twoBeta y y' z s / x s ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  have hv : rv y y' ≠ 0 := fun h => hs₀ (congrFun h s₀)
  have hJ := twoRxn_jacobian_rv κ hx hss
  have hc : 0 < κ.k (0 : Fin 2) * y.massActionMonomial x :=
    mul_pos (κ.positive _) (Complex.massActionMonomial_pos hx y)
  constructor
  · intro hnd h0
    apply hv
    apply hnd _ (by rw [twoRxn_stoichSubspace_eq κ hx hss]; exact Submodule.mem_span_singleton_self _)
    rw [hJ, h0, mul_zero, neg_zero, zero_smul]
  · intro hne u hu hJu
    rw [twoRxn_stoichSubspace_eq κ hx hss, Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [map_smul, hJ, smul_smul] at hJu
    have hcoef : c * -(κ.k (0 : Fin 2) * y.massActionMonomial x *
        ∑ s, twoBeta y y' z s / x s) = 0 := (smul_eq_zero.mp hJu).resolve_right hv
    have : c = 0 := by
      rcases mul_eq_zero.mp hcoef with h | h
      · exact h
      · exfalso; apply hne
        have := neg_eq_zero.mp h
        exact (mul_eq_zero.mp this).resolve_left hc.ne'
    rw [this, zero_smul]

/-- `h(τ) = ∑_s (z_s − y_s) log (x₁_s + τ v_s)`: the steady-state function along a class line. -/
noncomputable def lineH (y z : Complex S) (x₁ v : S → ℝ) (τ : ℝ) : ℝ :=
  ∑ s, ((z s : ℝ) - y s) * Real.log (x₁ s + τ * v s)

omit [DecidableEq S] in
theorem hasDerivAt_lineH (x₁ : S → ℝ) {τ : ℝ} (hpos : ∀ s, 0 < x₁ s + τ * rv y y' s) :
    HasDerivAt (lineH y z x₁ (rv y y')) (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s)) τ := by
  refine HasDerivAt.fun_sum fun s _ => ?_
  have hl : HasDerivAt (fun τ => x₁ s + τ * rv y y' s) (rv y y' s) τ := by
    simpa using ((hasDerivAt_id τ).mul_const (rv y y' s)).const_add (x₁ s)
  have := (hl.log (hpos s).ne').const_mul ((z s : ℝ) - y s)
  refine this.congr_deriv ?_
  simp only [twoBeta, rv]
  field_simp

omit [DecidableEq S] in
theorem lineH_eq_log (x₁ : Concentration S) (τ : ℝ) (hpos : (x₁ + τ • rv y y').Positive) :
    lineH y z x₁ (rv y y') τ = Real.log (z.massActionMonomial (x₁ + τ • rv y y') /
      y.massActionMonomial (x₁ + τ • rv y y')) := by
  rw [log_ratio_monomial hpos]; simp [lineH]

/-- At two positive steady states the ratio `x^z / x^y` agrees. -/
theorem twoRxn_ratio_eq (hyy : y ≠ y') (κ : RateConstants (twoRxn y y' z z'))
    {x₁ x₂ : Concentration S} (hp₁ : x₁.Positive) (hp₂ : x₂.Positive)
    (hs₁ : (twoRxn y y' z z').IsMassActionSteadyState κ x₁)
    (hs₂ : (twoRxn y y' z z').IsMassActionSteadyState κ x₂) :
    z.massActionMonomial x₁ / y.massActionMonomial x₁ =
      z.massActionMonomial x₂ / y.massActionMonomial x₂ := by
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  have e₁ := twoRxn_negMultiple_of_steadyState κ hp₁ hs₁ s₀
  have e₂ := twoRxn_negMultiple_of_steadyState κ hp₂ hs₂ s₀
  have hw : rv z z' s₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e₁; exact hs₀ e₁
  have hk0 := κ.positive (0 : Fin 2)
  have hk1 := κ.positive (1 : Fin 2)
  have heq : κ.k (1 : Fin 2) * z.massActionMonomial x₁ / (κ.k (0 : Fin 2) * y.massActionMonomial x₁) =
      κ.k (1 : Fin 2) * z.massActionMonomial x₂ / (κ.k (0 : Fin 2) * y.massActionMonomial x₂) :=
    neg_inj.mp (mul_right_cancel₀ hw (e₁.symm.trans e₂))
  have hy1 := (Complex.massActionMonomial_pos hp₁ y).ne'
  have hy2 := (Complex.massActionMonomial_pos hp₂ y).ne'
  field_simp at heq ⊢
  nlinarith [heq, hk0, hk1]

/-- **A critical point between two steady states.** If `x₁` and `x₁ + t (y' − y)` (`t ≠ 0`) are
positive steady states, then `∑_s β_s / x_s = 0` at some point `x₁ + c (y' − y)` strictly between
them. -/
theorem twoRxn_exists_critical (hyy : y ≠ y') (κ : RateConstants (twoRxn y y' z z'))
    {x₁ : Concentration S} {t : ℝ} (ht : t ≠ 0) (hp₁ : x₁.Positive)
    (hp₂ : (x₁ + t • rv y y').Positive)
    (hs₁ : (twoRxn y y' z z').IsMassActionSteadyState κ x₁)
    (hs₂ : (twoRxn y y' z z').IsMassActionSteadyState κ (x₁ + t • rv y y')) :
    ∃ c : ℝ, (x₁ + c • rv y y').Positive ∧ ∑ s, twoBeta y y' z s / (x₁ s + c * rv y y' s) = 0 := by
  have hratio := twoRxn_ratio_eq hyy κ hp₁ hp₂ hs₁ hs₂
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
  have hh0 : lineH y z x₁ (rv y y') 0 = Real.log (z.massActionMonomial x₁ / y.massActionMonomial x₁) := by
    rw [lineH_eq_log x₁ 0 (by simpa using hp₁)]; simp
  have hht := lineH_eq_log (z := z) x₁ t hp₂
  have hderiv : ∀ τ, (x₁ + τ • rv y y').Positive →
      HasDerivAt (lineH y z x₁ (rv y y')) (∑ s, twoBeta y y' z s / (x₁ s + τ * rv y y' s)) τ :=
    fun τ hτ => hasDerivAt_lineH x₁ fun s => by simpa using hτ s
  have hcont : ∀ a b, (∀ τ ∈ Set.Icc a b, (x₁ + τ • rv y y').Positive) →
      ContinuousOn (lineH y z x₁ (rv y y')) (Set.Icc a b) := fun a b hab τ hτ =>
    (hderiv τ (hab τ hτ)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne ht with htn | htp
  · have hI : ∀ τ ∈ Set.Icc t 0, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg_of_nonpos hτ.2 htn.le, (div_le_one_of_neg htn).mpr hτ.1⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (lineH y z x₁ (rv y y')) _ htn
      (hcont t 0 hI) (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hh0, hht, ← hratio, sub_self, zero_div] at hcd
    exact ⟨c, hI c ⟨hc.1.le, hc.2.le⟩, hcd⟩
  · have hI : ∀ τ ∈ Set.Icc 0 t, (x₁ + τ • rv y y').Positive := fun τ hτ =>
      hseg τ ⟨div_nonneg hτ.1 htp.le, (div_le_one htp).mpr hτ.2⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (lineH y z x₁ (rv y y')) _ htp
      (hcont 0 t hI) (fun τ hτ => hderiv τ (hI τ ⟨hτ.1.le, hτ.2.le⟩))
    rw [hh0, hht, ← hratio, sub_self, zero_div] at hcd
    exact ⟨c, hI c ⟨hc.1.le, hc.2.le⟩, hcd⟩

/-- **Necessity in Theorem 5.2.** A nondegenerately multistationary two-reaction network satisfies
conditions 1–3. -/
theorem twoRxn_nondegMultistationary_necessary (hyy : y ≠ y')
    (h : (twoRxn y y' z z').HasNondegenerateMultistationarity) :
    (∃ lam : ℝ, 0 < lam ∧ ∀ s, rv y y' s = -lam * rv z z' s) ∧
      ((∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0) ∧
      ∀ p q, 0 < twoBeta y y' z p → twoBeta y y' z q < 0 →
        (∀ s, 0 < twoBeta y y' z s → s = p) → (∀ s, twoBeta y y' z s < 0 → s = q) →
        ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0 := by
  have hcap := h.capacity
  obtain ⟨h1, h2⟩ := (twoRxn_multistationary_iff hyy).mp hcap
  obtain ⟨κ, x₀, x₁, x₂, ⟨hc₁, hp₁⟩, ⟨hc₂, hp₂⟩, hs₁, hs₂, hne, hnd₁, hnd₂⟩ := h
  have hcrit₁ := (twoRxn_nondegenerate_iff hyy κ hp₁ hs₁).mp hnd₁
  refine ⟨h1, ?_, ?_⟩
  · rcases h2 with hz | hm
    · exfalso; apply hcrit₁; simp [hz]
    · exact hm
  · intro p q hp hq hpu hqu hslope
    have hpq : p ≠ q := by rintro rfl; linarith
    have hzero : ∀ s, s ≠ p → s ≠ q → twoBeta y y' z s = 0 := by
      intro s hsp hsq
      rcases lt_trichotomy (twoBeta y y' z s) 0 with h' | h' | h'
      · exact absurd (hqu s h') hsq
      · exact h'
      · exact absurd (hpu s h') hsp
    have hc : (twoRxn y y' z z').StoichCompatible x₁ x₂ := hc₁.symm.trans hc₂
    obtain ⟨t, rfl⟩ := twoRxn_exists_line κ hp₁ hs₁ hc
    have ht : t ≠ 0 := by rintro rfl; simp at hne
    obtain ⟨c, hcpos, hcz⟩ := twoRxn_exists_critical hyy κ ht hp₁ hp₂ hs₁ hs₂
    -- the two-term form of `∑ β_s / x_s`
    have htwo : ∀ w : S → ℝ, ∑ s, twoBeta y y' z s / w s =
        twoBeta y y' z p / w p + twoBeta y y' z q / w q := fun w =>
      Fintype.sum_eq_add p q hpq fun s ⟨hsp, hsq⟩ => by rw [hzero s hsp hsq, zero_div]
    set dp : ℝ := (z p : ℝ) - y p
    have hβp : twoBeta y y' z p = rv y y' p * dp := by simp [twoBeta, rv, dp]
    have hβq : twoBeta y y' z q = -(rv y y' q * dp) := by
      have : (z q : ℝ) - y q = -dp := by linarith
      simp only [twoBeta, rv]; rw [this]; ring
    have hdp : dp ≠ 0 := by intro h0; rw [hβp, h0, mul_zero] at hp; exact lt_irrefl 0 hp
    have hxp := hcpos p
    have hxq := hcpos q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxp hxq
    rw [htwo, hβp, hβq] at hcz
    have hK : rv y y' p * x₁ q = rv y y' q * x₁ p := by
      have h3 := hcz
      rw [div_add_div _ _ hxp.ne' hxq.ne', div_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · have h4 : dp * (rv y y' p * (x₁ q + c * rv y y' q) -
            rv y y' q * (x₁ p + c * rv y y' p)) = 0 := by linear_combination h3
        have h5 := (mul_eq_zero.mp h4).resolve_left hdp
        linear_combination h5
      · exact absurd h3 (mul_pos hxp hxq).ne'
    apply hcrit₁
    rw [htwo, hβp, hβq, div_add_div _ _ (hp₁ p).ne' (hp₁ q).ne', div_eq_zero_iff]
    left
    linear_combination dp * hK

/-- **Two regular points at one level near a nondegenerate critical point.** Let `g` have
derivative `G τ` on `(-δ, δ)`, `G 0 = 0`, and let `G` have nonzero derivative at `0`. Then there are
`t₁ < 0 < t₂` in `(-δ, δ)` with `g t₁ = g t₂`, `G t₁ ≠ 0`, `G t₂ ≠ 0`. -/
theorem exists_two_regular_level {g G : ℝ → ℝ} {δ G' : ℝ} (hδ : 0 < δ)
    (hg : ∀ τ, -δ < τ → τ < δ → HasDerivAt g (G τ) τ) (hG0 : G 0 = 0)
    (hG : HasDerivAt G G' 0) (hG' : G' ≠ 0) :
    ∃ t₁ t₂, -δ < t₁ ∧ t₁ < 0 ∧ 0 < t₂ ∧ t₂ < δ ∧ g t₁ = g t₂ ∧ G t₁ ≠ 0 ∧ G t₂ ≠ 0 := by
  -- reduce to `G' < 0` by negating `g`
  wlog hneg : G' < 0 generalizing g G G'
  · have h' := this (g := fun τ => -g τ) (G := fun τ => -G τ) (G' := -G')
      (fun τ h1 h2 => (hg τ h1 h2).neg) (by simp [hG0]) hG.neg (neg_ne_zero.mpr hG')
      (by push Not at hneg; exact neg_neg_of_pos (lt_of_le_of_ne hneg (Ne.symm hG')))
    obtain ⟨t₁, t₂, h1, h2, h3, h4, h5, h6, h7⟩ := h'
    exact ⟨t₁, t₂, h1, h2, h3, h4, neg_inj.mp h5, fun h => h6 (by simp [h]),
      fun h => h7 (by simp [h])⟩
  -- the sign of `G` on each side
  have hslope : ∀ᶠ τ in nhdsWithin (0 : ℝ) {0}ᶜ, G τ / τ < 0 := by
    have := (hasDerivAt_iff_tendsto_slope.mp hG).eventually (gt_mem_nhds hneg)
    filter_upwards [this] with τ hτ
    rwa [slope_def_field, hG0, sub_zero, sub_zero] at hτ
  have hleft : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Iio 0), 0 < G τ := by
    filter_upwards [hslope.filter_mono (nhdsLT_le_nhdsNE 0), self_mem_nhdsWithin]
      with τ h (hτ : τ < 0)
    by_contra hc; push Not at hc
    have : 0 ≤ G τ / τ := div_nonneg_of_nonpos hc hτ.le
    linarith
  have hright : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), G τ < 0 := by
    filter_upwards [hslope.filter_mono (nhdsGT_le_nhdsNE 0), self_mem_nhdsWithin]
      with τ h (hτ : 0 < τ)
    by_contra hc; push Not at hc
    have : 0 ≤ G τ / τ := div_nonneg hc hτ.le
    linarith
  obtain ⟨a, ha, hasub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp
    (hleft.and (Ioo_mem_nhdsLT (show -δ < 0 by linarith)))
  obtain ⟨b, hb, hbsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp
    (hright.and (Ioo_mem_nhdsGT hδ))
  -- interior points of the two sides
  set τ₁ := a / 2 with hτ₁
  set τ₂ := b / 2 with hτ₂
  have ha0 : a < 0 := ha
  have hb0 : 0 < b := hb
  have hτ₁neg : τ₁ < 0 := by rw [hτ₁]; linarith
  have hτ₂pos : 0 < τ₂ := by rw [hτ₂]; linarith
  have hL : ∀ τ, a < τ → τ < 0 → 0 < G τ ∧ -δ < τ := fun τ h1 h2 =>
    let h := hasub ⟨h1, h2⟩; ⟨h.1, h.2.1⟩
  have hR : ∀ τ, 0 < τ → τ < b → G τ < 0 ∧ τ < δ := fun τ h1 h2 =>
    let h := hbsub ⟨h1, h2⟩; ⟨h.1, h.2.2⟩
  have hdom : ∀ τ, τ₁ ≤ τ → τ ≤ τ₂ → -δ < τ ∧ τ < δ := by
    intro τ h1 h2
    constructor
    · have := (hL τ₁ (by rw [hτ₁]; linarith) hτ₁neg).2; linarith
    · have := (hR τ₂ hτ₂pos (by rw [hτ₂]; linarith)).2; linarith
  have hcont : ContinuousOn g (Set.Icc τ₁ τ₂) := fun τ hτ =>
    (hg τ (hdom τ hτ.1 hτ.2).1 (hdom τ hτ.1 hτ.2).2).continuousAt.continuousWithinAt
  -- `g` increases on `[τ₁, 0]` and decreases on `[0, τ₂]`
  have hup : g τ₁ < g 0 := by
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g G hτ₁neg
      (hcont.mono (Set.Icc_subset_Icc le_rfl hτ₂pos.le))
      (fun τ hτ => hg τ (hdom τ hτ.1.le (by linarith [hτ.2])).1
        (hdom τ hτ.1.le (by linarith [hτ.2])).2)
    have hGc := (hL c (by linarith [hc.1, hτ₁, ha0]) hc.2).1
    rw [hcd] at hGc
    have : 0 < g 0 - g τ₁ := by
      have h0 : 0 < 0 - τ₁ := by linarith
      exact (div_pos_iff_of_pos_right h0).mp hGc
    linarith
  have hdown : g τ₂ < g 0 := by
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g G hτ₂pos
      (hcont.mono (Set.Icc_subset_Icc hτ₁neg.le le_rfl))
      (fun τ hτ => hg τ (hdom τ (by linarith [hτ.1]) hτ.2.le).1
        (hdom τ (by linarith [hτ.1]) hτ.2.le).2)
    have hGc := (hR c hc.1 (by linarith [hc.2, hτ₂, hb0])).1
    rw [hcd] at hGc
    have : g τ₂ - g 0 < 0 := by
      have h0 : 0 < τ₂ - 0 := by linarith
      exact (div_neg_iff.mp hGc).resolve_left (fun h => absurd h.2 (not_lt.mpr h0.le)) |>.1
    linarith
  -- a common level just below the maximum
  set L := max (g τ₁) (g τ₂) with hLdef
  set M := (L + g 0) / 2 with hM
  have hLM : L < M := by rw [hM]; have := max_lt hup hdown; linarith
  have hMg : M < g 0 := by rw [hM]; have := max_lt hup hdown; linarith
  obtain ⟨t₁, ht₁, hgt₁⟩ := intermediate_value_Ioo hτ₁neg.le
    (hcont.mono (Set.Icc_subset_Icc le_rfl hτ₂pos.le))
    ⟨lt_of_le_of_lt (le_max_left _ _) hLM, hMg⟩
  obtain ⟨t₂, ht₂, hgt₂⟩ := intermediate_value_Ioo' hτ₂pos.le
    (hcont.mono (Set.Icc_subset_Icc hτ₁neg.le le_rfl))
    ⟨lt_of_le_of_lt (le_max_right _ _) hLM, hMg⟩
  refine ⟨t₁, t₂, (hdom t₁ ht₁.1.le (by linarith [ht₁.2])).1, ht₁.2, ht₂.1,
    (hdom t₂ (by linarith [ht₂.1]) ht₂.2.le).2, hgt₁.trans hgt₂.symm, ?_, ?_⟩
  · exact (hL t₁ (by linarith [ht₁.1, hτ₁, ha0]) ht₁.2).1.ne'
  · exact (hR t₂ ht₂.1 (by linarith [ht₂.2, hτ₂, hb0])).1.ne

/-- Rate constants making every positive point with a prescribed ratio `x^z / x^y` a steady state. -/
theorem twoRxn_exists_rates_of_ratio {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s) {a : Concentration S} (ha : a.Positive) :
    ∃ κ : RateConstants (twoRxn y y' z z'), ∀ x : Concentration S, x.Positive →
      z.massActionMonomial x / y.massActionMonomial x =
        z.massActionMonomial a / y.massActionMonomial a →
      (twoRxn y y' z z').IsMassActionSteadyState κ x := by
  have hmya := Complex.massActionMonomial_pos ha y
  have hmza := Complex.massActionMonomial_pos ha z
  set k1 : ℝ := lam * y.massActionMonomial a / z.massActionMonomial a with hk1
  have hk1pos : 0 < k1 := div_pos (mul_pos hlam hmya) hmza
  let κ : RateConstants (twoRxn y y' z z') :=
    ⟨fun (r : Fin 2) => if r = 0 then 1 else k1, fun (r : Fin 2) => by
      by_cases h : r = 0 <;> simp [h, hk1pos]⟩
  have hk0 : κ.k (0 : Fin 2) = 1 := rfl
  have hk1' : κ.k (1 : Fin 2) = k1 := rfl
  have hw : ∀ s, rv z z' s = -(rv y y' s) / lam := fun s => by
    have := hneg s
    field_simp
    linarith
  refine ⟨κ, fun x hx hrx s => ?_⟩
  show (twoRxn y y' z z').massActionVectorField κ x s = 0
  rw [twoRxn_field, hk0, hk1', hw s]
  have hmy := Complex.massActionMonomial_pos hx y
  have hz : z.massActionMonomial x = z.massActionMonomial a / y.massActionMonomial a *
      y.massActionMonomial x := by
    rw [← hrx]; field_simp
  rw [hz, hk1]
  field_simp
  ring

/-- A pair of species with nonzero `β` whose `(z − y)`-coordinates do not cancel. -/
theorem exists_pair_of_conditions
    (hmix : (∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0)
    (h3 : ∀ p q, 0 < twoBeta y y' z p → twoBeta y y' z q < 0 →
        (∀ s, 0 < twoBeta y y' z s → s = p) → (∀ s, twoBeta y y' z s < 0 → s = q) →
        ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0) :
    ∃ a b, a ≠ b ∧ twoBeta y y' z a ≠ 0 ∧ twoBeta y y' z b ≠ 0 ∧
      ((z a : ℝ) - y a) + ((z b : ℝ) - y b) ≠ 0 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hmix
  have hpq : p ≠ q := by rintro rfl; linarith
  have hdp : (z p : ℝ) - y p ≠ 0 := by
    intro h; simp only [twoBeta] at hp; rw [h, mul_zero] at hp; exact lt_irrefl 0 hp
  have hdq : (z q : ℝ) - y q ≠ 0 := by
    intro h; simp only [twoBeta] at hq; rw [h, mul_zero] at hq; exact lt_irrefl 0 hq
  by_cases hpq' : ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0
  · exact ⟨p, q, hpq, hp.ne', hq.ne, hpq'⟩
  push Not at hpq'
  by_contra hno
  push Not at hno
  apply h3 p q hp hq
  · intro s hs
    by_contra hsp
    have h1 := hno s q (by rintro rfl; linarith) hs.ne' hq.ne
    have h2 := hno p s (Ne.symm hsp) hp.ne' hs.ne'
    have hds : (z s : ℝ) - y s ≠ 0 := by
      intro h; simp only [twoBeta] at hs; rw [h, mul_zero] at hs; exact lt_irrefl 0 hs
    apply hdp; linarith
  · intro s hs
    by_contra hsq
    have h1 := hno p s (by rintro rfl; linarith) hp.ne' hs.ne
    have h2 := hno q s (Ne.symm hsq) hq.ne hs.ne
    apply hdq; linarith
  · exact hpq'

/-- **The critical point.** Under conditions 2 and 3 there is `ρ > 0` with `∑ β_s ρ_s = 0` and
`∑ β_s v_s ρ_s² ≠ 0` (Joshi–Shiu, Lemma 5.7 and Theorem 4.8). -/
theorem exists_rho (hmix : (∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0)
    (h3 : ∀ p q, 0 < twoBeta y y' z p → twoBeta y y' z q < 0 →
        (∀ s, 0 < twoBeta y y' z s → s = p) → (∀ s, twoBeta y y' z s < 0 → s = q) →
        ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0) :
    ∃ ρ : S → ℝ, (∀ s, 0 < ρ s) ∧ ∑ s, twoBeta y y' z s * ρ s = 0 ∧
      ∑ s, twoBeta y y' z s * rv y y' s * ρ s ^ 2 ≠ 0 := by
  classical
  set β := twoBeta y y' z with hβdef
  set v := rv y y' with hvdef
  set d : S → ℝ := fun s => (z s : ℝ) - y s with hddef
  have hβvd : ∀ s, β s = v s * d s := fun s => rfl
  -- a balanced positive vector
  set P := Finset.univ.filter fun s => 0 < β s with hP
  set Ng := Finset.univ.filter fun s => β s < 0 with hNg
  obtain ⟨⟨p0, hp0⟩, ⟨q0, hq0⟩⟩ := hmix
  have hPn : (0 : ℝ) < P.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩⟩
  have hNn : (0 : ℝ) < Ng.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩⟩
  set ρ0 : S → ℝ := fun s =>
    if 0 < β s then 1 / (β s * P.card) else if β s < 0 then 1 / (-β s * Ng.card) else 1 with hρ0
  have hρ0pos : ∀ s, 0 < ρ0 s := by
    intro s; simp only [hρ0]
    split_ifs with h1 h2
    · positivity
    · have : 0 < -β s := by linarith
      positivity
    · exact one_pos
  have hbal : ∑ s, β s * ρ0 s = 0 := by
    have hterm : ∀ s, β s * ρ0 s =
        (if 0 < β s then 1 / (P.card : ℝ) else 0) - (if β s < 0 then 1 / (Ng.card : ℝ) else 0) := by
      intro s
      have hP0 := hPn.ne'
      have hN0 := hNn.ne'
      rcases lt_trichotomy (β s) 0 with h | h | h
      · have h1 : ¬ 0 < β s := by linarith
        simp only [hρ0, h1, h, ↓reduceIte]
        have : β s ≠ 0 := h.ne
        field_simp
        ring
      · simp [hρ0, h]
      · have h2 : ¬ β s < 0 := by linarith
        simp only [hρ0, h, h2, ↓reduceIte]
        have : β s ≠ 0 := h.ne'
        field_simp
        ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← hP, ← hNg]
    field_simp
    ring
  -- the quadratic form
  set Q : (S → ℝ) → ℝ := fun ρ => ∑ s, β s * v s * ρ s ^ 2 with hQ
  by_cases hQ0 : Q ρ0 ≠ 0
  · exact ⟨ρ0, hρ0pos, hbal, hQ0⟩
  push Not at hQ0
  -- a direction in the balance hyperplane with `Q ≠ 0`
  obtain ⟨a, b, hab, ha, hb, hd⟩ := exists_pair_of_conditions ⟨⟨p0, hp0⟩, ⟨q0, hq0⟩⟩ h3
  set w : S → ℝ := fun s => if s = a then β b else if s = b then -β a else 0 with hw
  have hwbal : ∑ s, β s * w s = 0 := by
    rw [Fintype.sum_eq_add a b hab (fun s ⟨hsa, hsb⟩ => by simp [hw, hsa, hsb])]
    simp [hw, Ne.symm hab]; ring
  have hQw : Q w ≠ 0 := by
    have hval : Q w = β a * v a * β b ^ 2 + β b * v b * β a ^ 2 := by
      simp only [hQ]
      rw [Fintype.sum_eq_add a b hab (fun s ⟨hsa, hsb⟩ => by simp [hw, hsa, hsb])]
      simp [hw, Ne.symm hab]
    have hfac : Q w = v a ^ 2 * v b ^ 2 * d a * d b * (d a + d b) := by
      rw [hval, hβvd a, hβvd b]; ring
    have hva : v a ≠ 0 := by intro h; apply ha; change β a = 0; rw [hβvd, h, zero_mul]
    have hvb : v b ≠ 0 := by intro h; apply hb; change β b = 0; rw [hβvd, h, zero_mul]
    have hda : d a ≠ 0 := by intro h; apply ha; change β a = 0; rw [hβvd, h, mul_zero]
    have hdb : d b ≠ 0 := by intro h; apply hb; change β b = 0; rw [hβvd, h, mul_zero]
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hva)
      (pow_ne_zero _ hvb)) hda) hdb) hd
  -- the quadratic in `ε`
  set B : ℝ := ∑ s, β s * v s * ρ0 s * w s with hB
  have hexp : ∀ ε : ℝ, Q (fun s => ρ0 s + ε * w s) = ε * (2 * B + ε * Q w) := by
    intro ε
    have : Q (fun s => ρ0 s + ε * w s) = Q ρ0 + ε * (2 * B) + ε ^ 2 * Q w := by
      simp only [hQ, hB, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, hQ0]; ring
  -- a small step keeping positivity
  obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ ρ0 s := by
    obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ ρ0 ⟨p0, Finset.mem_univ _⟩
    exact ⟨ρ0 s₀, hρ0pos s₀, fun s => hs₀ s (Finset.mem_univ s)⟩
  set W : ℝ := ∑ s, |w s| + 1 with hW
  have hW0 : 0 < W := by positivity
  set E : ℝ := m / (2 * W) with hE
  have hE0 : 0 < E := by positivity
  have hpos_of : ∀ ε : ℝ, 0 < ε → ε ≤ E → ∀ s, 0 < ρ0 s + ε * w s := by
    intro ε hε hεE s
    have hws : |w s| ≤ W := by
      have := Finset.single_le_sum (f := fun s => |w s|) (fun s _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [hW]; linarith
    have h1 : ε * |w s| ≤ E * W := mul_le_mul hεE hws (abs_nonneg _) hE0.le
    have h2 : E * W = m / 2 := by rw [hE]; field_simp
    have h3 : -(ε * |w s|) ≤ ε * w s := by
      have := neg_abs_le (w s); nlinarith
    linarith [hmle s]
  have hbalε : ∀ ε : ℝ, ∑ s, β s * (ρ0 s + ε * w s) = 0 := by
    intro ε
    simp only [mul_add, Finset.sum_add_distrib, hbal, zero_add]
    rw [show (∑ s, β s * (ε * w s)) = ε * ∑ s, β s * w s by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring, hwbal, mul_zero]
  by_cases hE1 : 2 * B + E * Q w = 0
  · refine ⟨fun s => ρ0 s + (E / 2) * w s, hpos_of _ (by positivity) (by linarith), hbalε _, ?_⟩
    show Q (fun s => ρ0 s + (E / 2) * w s) ≠ 0
    rw [hexp]
    have : 2 * B + E / 2 * Q w = -(E / 2 * Q w) := by linarith
    rw [this]
    exact mul_ne_zero (by positivity) (neg_ne_zero.mpr (mul_ne_zero (by positivity) hQw))
  · refine ⟨fun s => ρ0 s + E * w s, hpos_of _ hE0 le_rfl, hbalε _, ?_⟩
    show Q (fun s => ρ0 s + E * w s) ≠ 0
    rw [hexp]
    exact mul_ne_zero hE0.ne' hE1

/-- **Sufficiency in Theorem 5.2.** Conditions 1–3 give two nondegenerate positive steady states
in one class. -/
theorem twoRxn_nondegMultistationary_sufficient (hyy : y ≠ y') {lam : ℝ} (hlam : 0 < lam)
    (hneg : ∀ s, rv y y' s = -lam * rv z z' s)
    (hmix : (∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0)
    (h3 : ∀ p q, 0 < twoBeta y y' z p → twoBeta y y' z q < 0 →
        (∀ s, 0 < twoBeta y y' z s → s = p) → (∀ s, twoBeta y y' z s < 0 → s = q) →
        ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0) :
    (twoRxn y y' z z').HasNondegenerateMultistationarity := by
  classical
  obtain ⟨ρ, hρpos, hρbal, hρQ⟩ := exists_rho hmix h3
  set v := rv y y' with hv
  set xs : Concentration S := fun s => 1 / ρ s with hxs
  have hxspos : xs.Positive := fun s => by simp only [hxs]; exact one_div_pos.mpr (hρpos s)
  obtain ⟨s₀, hs₀⟩ := exists_ne_of_complex_ne hyy
  -- a positivity radius along the line
  obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ xs s := by
    obtain ⟨s₁, -, hs₁⟩ := Finset.exists_min_image Finset.univ xs ⟨s₀, Finset.mem_univ _⟩
    exact ⟨xs s₁, hxspos s₁, fun s => hs₁ s (Finset.mem_univ s)⟩
  set V : ℝ := ∑ s, |v s| + 1 with hV
  have hV0 : 0 < V := by positivity
  set δ : ℝ := m / V with hδ
  have hδ0 : 0 < δ := by positivity
  have hlinepos : ∀ τ, -δ < τ → τ < δ → ∀ s, 0 < xs s + τ * v s := by
    intro τ h1 h2 s
    have hvs : |v s| ≤ V := by
      have := Finset.single_le_sum (f := fun s => |v s|) (fun s _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [hV]; linarith
    have hτ : |τ| < δ := abs_lt.mpr ⟨h1, h2⟩
    have h4 : |τ * v s| < m := by
      rw [abs_mul]
      calc |τ| * |v s| ≤ |τ| * V := mul_le_mul_of_nonneg_left hvs (abs_nonneg _)
        _ < δ * V := mul_lt_mul_of_pos_right hτ hV0
        _ = m := by rw [hδ]; field_simp
    have := neg_abs_le (τ * v s)
    linarith [hmle s]
  -- `G = h'` and its derivative at `0`
  set G : ℝ → ℝ := fun τ => ∑ s, twoBeta y y' z s / (xs s + τ * v s) with hG
  have hg : ∀ τ, -δ < τ → τ < δ → HasDerivAt (lineH y z xs v) (G τ) τ :=
    fun τ h1 h2 => hasDerivAt_lineH xs (hlinepos τ h1 h2)
  have hG0 : G 0 = 0 := by
    simp only [hG, zero_mul, add_zero, hxs, one_div, div_inv_eq_mul]
    exact hρbal
  have hGd : HasDerivAt G (-∑ s, twoBeta y y' z s * v s * ρ s ^ 2) 0 := by
    have hterm : ∀ s, HasDerivAt (fun τ => twoBeta y y' z s / (xs s + τ * v s))
        (-(twoBeta y y' z s * v s * ρ s ^ 2)) 0 := by
      intro s
      have hl : HasDerivAt (fun τ => xs s + τ * v s) (v s) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v s)).const_add (xs s)
      have hne : xs s + 0 * v s ≠ 0 := by simpa using (hxspos s).ne'
      have := (hl.inv hne).const_mul (twoBeta y y' z s)
      refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall
        fun τ => by simp [div_eq_mul_inv])
      simp only [zero_mul, add_zero, hxs]
      have := (hρpos s).ne'
      field_simp
    have := HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hterm s
    simpa [hG, Finset.sum_neg_distrib] using this
  have hGd0 : -∑ s, twoBeta y y' z s * v s * ρ s ^ 2 ≠ 0 := neg_ne_zero.mpr hρQ
  obtain ⟨t₁, t₂, h1, h2, h3', h4, hgeq, hG1, hG2⟩ :=
    exists_two_regular_level hδ0 hg hG0 hGd hGd0
  -- the two points
  set X₁ : Concentration S := xs + t₁ • v with hX₁
  set X₂ : Concentration S := xs + t₂ • v with hX₂
  have hX₁pos : X₁.Positive := fun s => by
    simpa [hX₁] using hlinepos t₁ h1 (by linarith) s
  have hX₂pos : X₂.Positive := fun s => by
    simpa [hX₂] using hlinepos t₂ (by linarith) h4 s
  have hratio : z.massActionMonomial X₂ / y.massActionMonomial X₂ =
      z.massActionMonomial X₁ / y.massActionMonomial X₁ := by
    have e1 := lineH_eq_log (z := z) xs t₁ hX₁pos
    have e2 := lineH_eq_log (z := z) xs t₂ hX₂pos
    have hl : Real.log (z.massActionMonomial X₂ / y.massActionMonomial X₂) =
        Real.log (z.massActionMonomial X₁ / y.massActionMonomial X₁) := by
      rw [← e1, ← e2]; exact hgeq.symm
    have hp1 := div_pos (Complex.massActionMonomial_pos hX₁pos z)
      (Complex.massActionMonomial_pos hX₁pos y)
    have hp2 := div_pos (Complex.massActionMonomial_pos hX₂pos z)
      (Complex.massActionMonomial_pos hX₂pos y)
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hp2) (Set.mem_Ioi.mpr hp1) hl
  obtain ⟨κ, hκ⟩ := twoRxn_exists_rates_of_ratio hlam hneg hX₁pos
  have hss₁ := hκ X₁ hX₁pos rfl
  have hss₂ := hκ X₂ hX₂pos hratio
  have hGX : ∀ t : ℝ, ∑ s, twoBeta y y' z s / (xs + t • v) s = G t := by
    intro t; simp [hG]
  refine ⟨κ, X₁, X₁, X₂, ⟨StoichCompatible.refl _ _, hX₁pos⟩, ⟨?_, hX₂pos⟩, hss₁, hss₂, ?_,
    (twoRxn_nondegenerate_iff hyy κ hX₁pos hss₁).mpr (by rw [hX₁, hGX]; exact hG1),
    (twoRxn_nondegenerate_iff hyy κ hX₂pos hss₂).mpr (by rw [hX₂, hGX]; exact hG2)⟩
  · show X₂ - X₁ ∈ (twoRxn y y' z z').stoichSubspace
    have : X₂ - X₁ = (t₂ - t₁) • v := by
      simp only [hX₁, hX₂, sub_smul]; abel
    rw [this, hv, ← twoRxn_reactionVector_zero]
    exact Submodule.smul_mem _ _ ((twoRxn y y' z z').reactionVector_mem_stoichSubspace _)
  · intro heq
    have := congrFun heq s₀
    simp only [hX₁, hX₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    have : t₁ = t₂ := mul_right_cancel₀ hs₀ this
    linarith

/-- **Joshi–Shiu 2017, Theorem 5.2.** The network with two reactions `y → y'` and `z → z'`
(`y ≠ y'`) is nondegenerately multistationary iff (1) `y' − y = −λ (z' − z)` for some `λ > 0`,
(2) `β = (y' − y) ∗ (z − y)` has a positive and a negative coordinate, and (3) if `β` has exactly
one positive coordinate `p` and exactly one negative coordinate `q`, then the projection of the
reactant polytope to the `(p, q)`-plane does not have slope `−1`: `(z − y)_p + (z − y)_q ≠ 0`. -/
theorem twoRxn_nondegMultistationary_iff (hyy : y ≠ y') :
    (twoRxn y y' z z').HasNondegenerateMultistationarity ↔
      (∃ lam : ℝ, 0 < lam ∧ ∀ s, rv y y' s = -lam * rv z z' s) ∧
        ((∃ i, 0 < twoBeta y y' z i) ∧ ∃ j, twoBeta y y' z j < 0) ∧
        ∀ p q, 0 < twoBeta y y' z p → twoBeta y y' z q < 0 →
          (∀ s, 0 < twoBeta y y' z s → s = p) → (∀ s, twoBeta y y' z s < 0 → s = q) →
          ((z p : ℝ) - y p) + ((z q : ℝ) - y q) ≠ 0 := by
  constructor
  · exact twoRxn_nondegMultistationary_necessary hyy
  · rintro ⟨⟨lam, hlam, hneg⟩, hmix, h3⟩
    exact twoRxn_nondegMultistationary_sufficient hyy hlam hneg hmix h3

end Network

end CRNT
