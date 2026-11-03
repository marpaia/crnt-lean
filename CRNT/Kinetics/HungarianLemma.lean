import CRNT.Deficiency.KineticSubspace

/-!
# The Hungarian lemma (Hárs–Tóth 1979)

A polynomial vector field `f_i(x) = ∑_{m ∈ M} c i m · x^m` is the mass-action vector field of some
reaction network with positive rate constants **iff** every monomial with a negative coefficient
in `f_i` contains `x_i`, i.e. `c i m < 0 → 1 ≤ m i`.

* `exists_massAction_realization` (sufficiency): for each nonzero coefficient add the reaction
  `m → m + e_i` (if `c i m > 0`) or `m → m - e_i` (if `c i m < 0`, possible since `m i ≥ 1`)
  with rate `|c i m|`; each reaction contributes exactly `c i m · x^m` to coordinate `i`.
* `negTerm_contains_of_massAction` (necessity): the coefficient of `x^m` in the `i`-th coordinate
  of a mass-action field is `∑_{r : source r = m} κ r (y'_r - y_r)_i`, which can be negative only
  if some reaction with source `m` consumes species `i`, forcing `m i ≥ 1`.  Coefficients are
  determined by the values on the positive orthant (`MvPolynomial.funext_set`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The polynomial vector field with monomials `M` and coefficients `c`. -/
noncomputable def polyField (M : Finset (Complex S)) (c : S → Complex S → ℝ)
    (x : Concentration S) : S → ℝ :=
  fun i => ∑ m ∈ M, c i m * m.massActionMonomial x

open Classical in
/-- The realizing network of the Hungarian lemma: one reaction per nonzero coefficient. -/
noncomputable def hungarianNetwork (M : Finset (Complex S)) (c : S → Complex S → ℝ) :
    Network S where
  R := {p : S × M // c p.1 p.2.1 ≠ 0}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction p :=
    if 0 < c p.1.1 p.1.2.1 then ⟨p.1.2.1, p.1.2.1 + Pi.single p.1.1 1⟩
    else ⟨p.1.2.1, Function.update p.1.2.1 p.1.1 (p.1.2.1 p.1.1 - 1)⟩

/-- Its rate constants `|c i m|`. -/
noncomputable def hungarianRates (M : Finset (Complex S)) (c : S → Complex S → ℝ) :
    (hungarianNetwork M c).RateConstants :=
  ⟨fun p => |c p.1.1 p.1.2.1|, fun p => abs_pos.mpr p.2⟩

/-- **Sufficiency.** -/
theorem exists_massAction_realization (M : Finset (Complex S)) (c : S → Complex S → ℝ)
    (hneg : ∀ i, ∀ m ∈ M, c i m < 0 → 1 ≤ m i) :
    ∃ (N : Network S) (κ : N.RateConstants), ∀ x : Concentration S,
      N.massActionVectorField κ x = polyField M c x := by
  classical
  refine ⟨hungarianNetwork M c, hungarianRates M c, fun x => ?_⟩
  funext s
  set N := hungarianNetwork M c
  -- each reaction contributes `c i m · x^m` to coordinate `i` only
  have hterm : ∀ p : N.R, N.massActionRate (hungarianRates M c) p x * N.reactionVector p s =
      if s = p.1.1 then c p.1.1 p.1.2.1 * p.1.2.1.massActionMonomial x else 0 := by
    intro p
    obtain ⟨⟨i, ⟨m, hm⟩⟩, hc⟩ := p
    simp only [massActionRate, reactionVector_apply, hungarianRates]
    change |c i m| * (N.reaction _).source.massActionMonomial x *
      (((N.reaction _).target s : ℝ) - ((N.reaction _).source s : ℝ)) = _
    simp only [N, hungarianNetwork]
    by_cases hpos : 0 < c i m
    · simp only [if_pos hpos, abs_of_pos hpos]
      by_cases hs : s = i
      · subst hs; simp
      · simp [hs, Pi.single_apply]
    · have hlt : c i m < 0 := lt_of_le_of_ne (not_lt.mp hpos) hc
      have hmi := hneg i m hm hlt
      simp only [if_neg hpos, abs_of_neg hlt]
      by_cases hs : s = i
      · subst hs
        simp only [Function.update_self, if_true]
        rw [Nat.cast_sub hmi]; ring
      · simp [hs, Function.update_of_ne hs]
  rw [massActionVectorField_apply, Finset.sum_congr rfl (fun p _ => hterm p)]
  -- sum over the nonzero coefficients = sum over all `(i, m)`
  change ∑ p : {p : S × M // c p.1 p.2.1 ≠ 0},
      (if s = p.1.1 then c p.1.1 p.1.2.1 * p.1.2.1.massActionMonomial x else 0) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : S × M => c p.1 p.2.1 ≠ 0))
    (fun p => by simp) (fun p : S × M =>
      if s = p.1 then c p.1 p.2.1 * p.2.1.massActionMonomial x else 0)]
  rw [Finset.sum_filter_of_ne (fun p _ hne => by
      intro hzero; apply hne; split_ifs <;> simp [hzero])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [polyField]
  rw [← Finset.sum_coe_sort M]

/-- The coefficient of `x^{m₀}` in a finite polynomial sum. -/
theorem coeff_polySum (T : Finset (Complex S)) (a : Complex S → ℝ) (m₀ : Complex S) :
    (∑ m ∈ T, MvPolynomial.monomial (complexFinsuppExp m) (a m)).coeff (complexFinsuppExp m₀) =
      if m₀ ∈ T then a m₀ else 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_congr rfl (fun m _ => show (if complexFinsuppExp m = complexFinsuppExp m₀ then
      a m else 0) = (if m = m₀ then a m else 0) by
    by_cases h : m = m₀
    · subst h; simp
    · rw [if_neg (fun he => h (complexFinsuppExp_injective he)), if_neg h])]
  exact Finset.sum_ite_eq' T m₀ a

theorem eval_polySum (T : Finset (Complex S)) (a : Complex S → ℝ) (x : Concentration S) :
    MvPolynomial.eval x (∑ m ∈ T, MvPolynomial.monomial (complexFinsuppExp m) (a m)) =
      ∑ m ∈ T, a m * m.massActionMonomial x := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial (complexFinsuppExp m) (a m) =
      MvPolynomial.C (a m) * MvPolynomial.monomial (complexFinsuppExp m) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [map_mul, MvPolynomial.eval_C, eval_monomial_complexFinsuppExp]

/-- **Necessity.** -/
theorem negTerm_contains_of_massAction (N : Network S) (κ : N.RateConstants)
    (M : Finset (Complex S)) (c : S → Complex S → ℝ)
    (h : ∀ x : Concentration S, x.Positive → N.massActionVectorField κ x = polyField M c x) :
    ∀ i, ∀ m ∈ M, c i m < 0 → 1 ≤ m i := by
  classical
  intro i m₀ hm₀ hneg
  -- the mass-action field as a polynomial with source monomials
  set T : Finset (Complex S) := Finset.univ.image fun r : N.R => (N.reaction r).source with hT
  set d : Complex S → ℝ := fun m =>
    ∑ r : N.R, if (N.reaction r).source = m then κ.k r * N.reactionVector r i else 0 with hd
  have hfield : ∀ x : Concentration S, N.massActionVectorField κ x i =
      ∑ m ∈ T, d m * m.massActionMonomial x := by
    intro x
    rw [massActionVectorField_apply]
    simp only [hd, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single (N.reaction r).source]
    · simp [massActionRate]; ring
    · intro m _ hne; rw [if_neg (Ne.symm hne)]; ring
    · intro hnot; exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ r)) hnot
  -- the two polynomials agree on the positive orthant, hence coincide
  set p := (∑ m ∈ M, MvPolynomial.monomial (complexFinsuppExp m) (c i m)) +
    ∑ m ∈ T, MvPolynomial.monomial (complexFinsuppExp m) (-d m) with hp
  have hp0 : p = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0)
    intro x hx
    have hxpos : Concentration.Positive x := fun s => hx s (Set.mem_univ s)
    rw [map_zero, hp, map_add, eval_polySum, eval_polySum]
    have h1 := hfield x
    have h2 := congrFun (h x hxpos) i
    rw [h2] at h1
    simp only [polyField] at h1
    rw [h1, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ => by ring
  have hcoef : p.coeff (complexFinsuppExp m₀) = 0 := by
    rw [hp0]; simp
  rw [hp, MvPolynomial.coeff_add, coeff_polySum, coeff_polySum, if_pos hm₀] at hcoef
  have hdneg : d m₀ < 0 := by
    split_ifs at hcoef with hmT
    · linarith [hneg]
    · linarith [hneg]
  -- some reaction with source `m₀` consumes species `i`
  obtain ⟨r, -, hr⟩ : ∃ r ∈ (Finset.univ : Finset N.R),
      (if (N.reaction r).source = m₀ then κ.k r * N.reactionVector r i else 0) < 0 := by
    by_contra hall
    push Not at hall
    exact absurd (Finset.sum_nonneg hall) (not_le.mpr hdneg)
  split_ifs at hr with hsrc
  · have hvec : N.reactionVector r i < 0 := by
      by_contra hge; push Not at hge
      exact absurd (mul_nonneg (κ.positive r).le hge) (not_le.mpr hr)
    rw [reactionVector_apply, hsrc] at hvec
    have : ((N.reaction r).target i : ℝ) < (m₀ i : ℝ) := by linarith
    have : (N.reaction r).target i < m₀ i := by exact_mod_cast this
    omega
  · exact absurd hr (lt_irrefl 0)

/-- **The Hungarian lemma.** -/
theorem exists_massAction_realization_iff (M : Finset (Complex S)) (c : S → Complex S → ℝ) :
    (∃ (N : Network S) (κ : N.RateConstants), ∀ x : Concentration S, x.Positive →
      N.massActionVectorField κ x = polyField M c x) ↔
      ∀ i, ∀ m ∈ M, c i m < 0 → 1 ≤ m i := by
  constructor
  · rintro ⟨N, κ, h⟩
    exact negTerm_contains_of_massAction N κ M c h
  · intro hneg
    obtain ⟨N, κ, h⟩ := exists_massAction_realization M c hneg
    exact ⟨N, κ, fun x _ => h x⟩

end Network
end CRNT
