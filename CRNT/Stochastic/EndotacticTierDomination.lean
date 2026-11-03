import CRNT.Stochastic.EndotacticTierPositiveRecurrence

/-!
# Restricted count-tier balance and falling-factorial obstructions

Comparison lemmas expose the enabled-region obstruction to naive tier
domination on the count lattice. `CountTierBalance` supplies additional
same-source matching and inward-consumption data; these give drift and
recurrence results under the displayed assumptions. This is a sufficient
restricted class. Universal recurrence/non-explosion for several-species
strongly endotactic networks is false (arXiv:1808.05328, Examples 3.1–3.2).
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The falling factorial on the count lattice -/

/-- **Monotonicity of the falling factorial.**  For `k + 1 ≤ n` the falling factorial
`n.descFactorial k` does not decrease when `k` is replaced by `k + 1`: the factor that is
gained, `n - k`, is at least `1`. -/
theorem descFactorial_mono_step {n k : ℕ} (hk : k + 1 ≤ n) :
    n.descFactorial k ≤ n.descFactorial (k + 1) := by
  rw [Nat.descFactorial_succ]
  have h1 : 1 ≤ n - k := by omega
  simpa using (Nat.mul_le_mul h1 (le_refl (n.descFactorial k)))

/-- **Strict monotonicity of the falling factorial.**  For `k + 2 ≤ n` the increase is strict:
the factor `n - k` is at least `2` and the falling factorial is positive. -/
theorem descFactorial_lt_step {n k : ℕ} (hk : k + 2 ≤ n) :
    n.descFactorial k < n.descFactorial (k + 1) := by
  rw [Nat.descFactorial_succ]
  have h1 : 1 < n - k := by omega
  have h2 : 0 < n.descFactorial k := (Nat.descFactorial_pos).2 (by omega)
  simpa using (Nat.mul_lt_mul_of_pos_right h1 h2)

/-- **Monotonicity of the falling factorial on the range where it does not truncate.**  If
`k ≤ m ≤ n` then `n.descFactorial k ≤ n.descFactorial m`. -/
theorem descFactorial_mono {n k m : ℕ} (hk : k ≤ m) (hm : m ≤ n) :
    n.descFactorial k ≤ n.descFactorial m := by
  induction m generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      simp
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hk with rfl | h
      · exact le_rfl
      · have hkm : k ≤ m := by omega
        have hmn : m + 1 ≤ n := by omega
        exact (ih hkm (by omega)).trans (descFactorial_mono_step hmn)

/-- **Strict monotonicity of the falling factorial on the range where it does not truncate.**
If `k < m` and `m + 1 ≤ n` then `n.descFactorial k < n.descFactorial m`.  The unit of slack
`m + 1 ≤ n` is needed: for `k = m - 1 = n - 1` the two falling factorials coincide. -/
theorem descFactorial_lt_of_lt {n k m : ℕ} (hk : k < m) (hm : m + 1 ≤ n) :
    n.descFactorial k < n.descFactorial m := by
  induction m generalizing k with
  | zero =>
      exact absurd hk (Nat.not_lt_zero _)
  | succ m ih =>
      have hkm : k ≤ m := Nat.lt_succ_iff.mp hk
      rcases Nat.eq_or_lt_of_le hkm with rfl | h
      · -- k = m : the strict increase is `descFactorial_lt_step`
        exact descFactorial_lt_step (by omega)
      · -- k < m : use the induction hypothesis and the monotone step
        have hmn : m + 1 ≤ n := by omega
        exact lt_of_lt_of_le (ih h (by omega)) (descFactorial_mono_step hmn)

/-- A complex is **nonempty** when it contains at least one molecule. -/
def ComplexNonempty (y : Complex S) : Prop := ∃ s, y s ≠ 0

/-- The **count-lattice falling factorial** of a complex `y` at the count `n`: the product of
the per-species falling factorials.  This is the count-lattice analogue of the mass-action
monomial `x^y`, and the factor that occurs in the stochastic propensity. -/
noncomputable def countDescFactorial (y : Complex S) (n : S → ℕ) : ℕ :=
  ∏ s : S, (n s).descFactorial (y s)

/-- The count-lattice falling factorial is the factor of the stochastic propensity. -/
theorem stochasticMassActionRate_eq_countDescFactorial (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) :
    N.stochasticMassActionRate κ n r = κ.k r * ((countDescFactorial (N.reaction r).source n : ℝ)) := by
  unfold stochasticMassActionRate countDescFactorial
  rw [Nat.cast_prod]

/-- Splitting the count-lattice falling factorial at one species. -/
theorem countDescFactorial_eq_mul_descFactorial {y : Complex S} {n : S → ℕ} (s₀ : S) :
    countDescFactorial y n =
      (n s₀).descFactorial (y s₀) *
        ∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s) := by
  classical
  unfold countDescFactorial
  have hmem : s₀ ∈ (Finset.univ : Finset S) := Finset.mem_univ s₀
  rw [← Finset.prod_erase_mul _ _ hmem]
  ring

/-! ## 2. The falling-factorial comparison -/

omit [DecidableEq S] in
/-- **Falling-factorial comparison.**  If the complex `z` is coordinatewise below the complex
`y` and the count `n` *enables* `y` (`y ≤ n` coordinatewise), then the count-lattice falling
factorial of `y` dominates that of `z`.  This is the count-lattice counterpart of the
deterministic inequality `x^y ≫ x^z` for `y ≥ z`. -/
theorem countDescFactorial_mono {y z : Complex S} {n : S → ℕ}
    (hzy : ∀ s, z s ≤ y s) (hyn : ∀ s, y s ≤ n s) :
    countDescFactorial z n ≤ countDescFactorial y n := by
  classical
  unfold countDescFactorial
  refine Finset.prod_le_prod fun s _ => ?_
  exact descFactorial_mono (hzy s) (hyn s)

/-- **Strict falling-factorial comparison.**  Under the hypotheses of `countDescFactorial_mono`
the inequality is strict as soon as `z` is strictly below `y` in some species and the count has
one unit of slack in that species (`y s + 1 ≤ n s`).  This is the "relevant region" of the
tier domination: the extra species must not sit exactly at its capacity. -/
theorem countDescFactorial_lt_of_lt {y z : Complex S} {n : S → ℕ}
    (hzy : ∀ s, z s ≤ y s) (hyn : ∀ s, y s ≤ n s)
    (hne : ∃ s, z s < y s) (hslack : ∀ s, z s < y s → y s + 1 ≤ n s) :
    countDescFactorial z n < countDescFactorial y n := by
  classical
  obtain ⟨s₀, hs₀⟩ := hne
  have hlt : (n s₀).descFactorial (z s₀) < (n s₀).descFactorial (y s₀) :=
    descFactorial_lt_of_lt hs₀ (hslack s₀ hs₀)
  have hrest : (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s)) ≤
      ∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s) :=
    Finset.prod_le_prod fun s _ => descFactorial_mono (hzy s) (hyn s)
  have hrestpos : 0 < ∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s) :=
    Finset.prod_pos fun s _ => (Nat.descFactorial_pos).2 (hyn s)
  rw [countDescFactorial_eq_mul_descFactorial s₀, countDescFactorial_eq_mul_descFactorial s₀]
  have h1 : (n s₀).descFactorial (z s₀) *
      (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s)) ≤
      (n s₀).descFactorial (z s₀) *
      (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s)) :=
    Nat.mul_le_mul_left _ hrest
  have h2 : (n s₀).descFactorial (z s₀) *
      (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s)) <
      (n s₀).descFactorial (y s₀) *
      (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s)) :=
    Nat.mul_lt_mul_of_pos_right hlt hrestpos
  exact lt_of_le_of_lt h1 h2

/-- **Quantitative asymptotic domination.**  Under the hypotheses of `countDescFactorial_mono`
the count-lattice falling factorial of `y` dominates that of `z` by a factor that is a power
of the count of the extra species `s₀` (`z s₀ < y s₀`); the exponent is the difference of the
two molecularities.  In particular the ratio of the two falling factorials tends to infinity
with the count of `s₀`. -/
theorem countDescFactorial_ge_mul_descFactorial {y z : Complex S} {n : S → ℕ}
    (hzy : ∀ s, z s ≤ y s) (hyn : ∀ s, y s ≤ n s)
    (s₀ : S) (h₀ : z s₀ < y s₀) :
    countDescFactorial y n ≥ countDescFactorial z n * ((n s₀ + 1 - y s₀) ^ (y s₀ - z s₀)) := by
  classical
  have hle : z s₀ ≤ n s₀ := le_trans (hzy s₀) (hyn s₀)
  have hyz : y s₀ ≤ n s₀ := hyn s₀
  have hdf : (n s₀).descFactorial (y s₀) =
      (n s₀).descFactorial (z s₀) * (n s₀ - z s₀).descFactorial (y s₀ - z s₀) := by
    have h := Nat.descFactorial_mul_descFactorial (k := z s₀) (m := y s₀) (n := n s₀)
      (le_of_lt h₀)
    rw [Nat.mul_comm] at h
    exact h.symm
  have hrest : (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s)) ≤
      ∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s) :=
    Finset.prod_le_prod fun s _ => descFactorial_mono (hzy s) (hyn s)
  have hlow : (n s₀ - z s₀ + 1 - (y s₀ - z s₀)) ^ (y s₀ - z s₀) ≤
      (n s₀ - z s₀).descFactorial (y s₀ - z s₀) :=
    Nat.pow_sub_le_descFactorial _ _
  have hbase : n s₀ - z s₀ + 1 - (y s₀ - z s₀) = n s₀ + 1 - y s₀ := by omega
  have hA : (n s₀ + 1 - y s₀) ^ (y s₀ - z s₀) ≤
      (n s₀ - z s₀).descFactorial (y s₀ - z s₀) := by
    rw [hbase] at hlow
    exact hlow
  have h1 : ((n s₀ + 1 - y s₀) ^ (y s₀ - z s₀)) *
        (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s)) ≤
      (n s₀ - z s₀).descFactorial (y s₀ - z s₀) *
        (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s)) :=
    Nat.le_trans
      (Nat.mul_le_mul_left ((n s₀ + 1 - y s₀) ^ (y s₀ - z s₀)) hrest)
      (Nat.mul_le_mul_right _ hA)
  rw [countDescFactorial_eq_mul_descFactorial s₀, countDescFactorial_eq_mul_descFactorial s₀,
    hdf]
  calc
    ((n s₀).descFactorial (z s₀) *
        (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s))) *
        ((n s₀ + 1 - y s₀) ^ (y s₀ - z s₀)) =
      (n s₀).descFactorial (z s₀) *
        (((n s₀ + 1 - y s₀) ^ (y s₀ - z s₀)) *
          (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (z s))) := by ring
    _ ≤ (n s₀).descFactorial (z s₀) *
        ((n s₀ - z s₀).descFactorial (y s₀ - z s₀) *
          (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s))) := by
          exact Nat.mul_le_mul_left _ h1
    _ = ((n s₀).descFactorial (z s₀) * (n s₀ - z s₀).descFactorial (y s₀ - z s₀)) *
        (∏ s ∈ (Finset.univ : Finset S).erase s₀, (n s).descFactorial (y s)) := by ring

/-- **Asymptotic domination.**  The ratio of the count-lattice falling factorials of `y` and
`z` (`z ≤ y` coordinatewise, `z ≠ y`) is bounded below by a power of the count of the extra
species `s₀`, and hence tends to infinity with that count.  This is the count-lattice
counterpart of `x^y ≫ x^z` for large `x`. -/
theorem countDescFactorial_div_lower_bound {y z : Complex S} {n : S → ℕ}
    (hzy : ∀ s, z s ≤ y s) (hyn : ∀ s, y s ≤ n s)
    (s₀ : S) (h₀ : z s₀ < y s₀) :
    (countDescFactorial y n : ℝ) / (countDescFactorial z n : ℝ) ≥
      (((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ (y s₀ - z s₀)) := by
  have hmul := countDescFactorial_ge_mul_descFactorial hzy hyn s₀ h₀
  have hyz : y s₀ ≤ n s₀ := hyn s₀
  have hpos : 0 < (countDescFactorial z n : ℝ) := by
    have h : 0 < countDescFactorial z n := by
      unfold countDescFactorial
      refine Finset.prod_pos fun s _ => ?_
      exact (Nat.descFactorial_pos).2 (le_trans (hzy s) (hyn s))
    exact_mod_cast h
  have hmul' : (countDescFactorial y n : ℝ) ≥ (countDescFactorial z n : ℝ) *
      (((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ (y s₀ - z s₀)) := by
    have hcast : ((n s₀ + 1 - y s₀ : ℕ) : ℝ) =
        ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) := by
      have hsub : n s₀ + 1 - y s₀ = (n s₀ + 1) - y s₀ := by omega
      rw [hsub, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hmul2 : (countDescFactorial y n : ℝ) ≥ (countDescFactorial z n : ℝ) *
        (((n s₀ + 1 - y s₀ : ℕ) : ℝ) ^ (y s₀ - z s₀)) := by
      exact_mod_cast hmul
    rw [hcast] at hmul2
    simpa using hmul2
  have hstep : (countDescFactorial z n : ℝ) *
      (((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ (y s₀ - z s₀)) ≤ (countDescFactorial y n : ℝ) := by
    linarith [hmul']
  rw [ge_iff_le, le_div_iff₀ hpos]
  simpa [mul_comm] using hstep

/-- **Asymptotic domination, unbounded form.**  The ratio of the count-lattice falling
factorials of `y` and `z` (`z ≤ y` coordinatewise, `z ≠ y`) exceeds every bound `M` as soon as
the count of the extra species `s₀` is large enough. -/
theorem countDescFactorial_ratio_gt_of_count {y z : Complex S} {n : S → ℕ} {M : ℝ}
    (hM : 0 < M) (hzy : ∀ s, z s ≤ y s) (hyn : ∀ s, y s ≤ n s)
    (s₀ : S) (h₀ : z s₀ < y s₀) (hn : (n s₀ : ℝ) ≥ M + (y s₀ : ℝ)) :
    (countDescFactorial y n : ℝ) / (countDescFactorial z n : ℝ) > M := by
  have hd : 0 < y s₀ - z s₀ := by omega
  have hbase : 1 ≤ ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) := by
    have : 1 < (n s₀ : ℝ) + 1 - (y s₀ : ℝ) := by linarith
    linarith
  have hpow : ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ (y s₀ - z s₀) ≥
      ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) := by
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show 1 ≤ y s₀ - z s₀ by omega)
    rw [he, pow_add, pow_one]
    have h1 : (1 : ℝ) ≤ ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ e := one_le_pow₀ hbase
    nlinarith
  have hlb := countDescFactorial_div_lower_bound hzy hyn s₀ h₀
  have hstrict : M < ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) ^ (y s₀ - z s₀) := by
    have h2 : M < ((n s₀ : ℝ) + 1 - (y s₀ : ℝ)) := by linarith
    linarith [hpow]
  linarith

/-! ## 3. The count-lattice tier domination -/

/-- The complex `y` **dominates** the complex `z` on the count lattice when `z ≤ y`
coordinatewise: the count-lattice falling factorial of `y` then dominates that of `z` on the
region where `y` is *enabled*. -/
def CountComplexDominates (y z : Complex S) : Prop := ∀ s, z s ≤ y s

/-- The **ascending** reactions of `N` for the tier weight `w`: those whose `w`-rate is
positive, i.e. those that increase the tier potential. -/
noncomputable def countTierAscending (N : Network S) (w : S → ℝ) : Finset N.R :=
  Finset.univ.filter fun r => 0 < N.wRate w r

/-- The **descending** reactions of `N` for the tier weight `w`: those whose `w`-rate is
negative, i.e. those that decrease the tier potential. -/
noncomputable def countTierDescending (N : Network S) (w : S → ℝ) : Finset N.R :=
  Finset.univ.filter fun r => N.wRate w r < 0

omit [DecidableEq S] in
/-- **The count-lattice tier domination.**  Let `y` be the source complex of a top-tier
reaction of `N` for the direction `w` and `z` the source complex of any reaction of `N`.  If
`y` dominates `z` (`z ≤ y` coordinatewise), then on the region where the top-tier reaction is
*enabled* (`y ≤ n` coordinatewise) the count-lattice falling factorial of `y` — the
count-lattice monomial of the top tier — dominates that of `z`. -/
theorem countTierDescFactorial_dominates {y z : Complex S} {n : S → ℕ}
    (hdom : CountComplexDominates y z) (hen : ∀ s, y s ≤ n s) :
    countDescFactorial z n ≤ countDescFactorial y n :=
  countDescFactorial_mono hdom hen

/-- **The count-lattice rate domination.**  Under the hypotheses of
`countTierDescFactorial_dominates`, and provided the rate constant of the top-tier reaction is
at least that of the other reaction, the *propensity* of the top-tier reaction dominates the
propensity of the other reaction on the region where the top-tier reaction is enabled. -/
theorem countTierRate_dominates {N : Network S} {κ : N.RateConstants}
    {r_y r_z : N.R} {n : S → ℕ}
    (hdom : CountComplexDominates (N.reaction r_y).source (N.reaction r_z).source)
    (hen : ∀ s, (N.reaction r_y).source s ≤ n s)
    (hk : κ.k r_z ≤ κ.k r_y) :
    N.stochasticMassActionRate κ n r_z ≤ N.stochasticMassActionRate κ n r_y := by
  have h1 : (countDescFactorial (N.reaction r_z).source n : ℝ) ≤
      (countDescFactorial (N.reaction r_y).source n : ℝ) := by
    exact_mod_cast (countTierDescFactorial_dominates hdom hen)
  have h2 : 0 ≤ (countDescFactorial (N.reaction r_z).source n : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h3 : (countDescFactorial (N.reaction r_z).source n : ℝ) * (κ.k r_y : ℝ) ≤
      (countDescFactorial (N.reaction r_y).source n : ℝ) * (κ.k r_y : ℝ) :=
    mul_le_mul_of_nonneg_right h1 (κ.positive r_y).le
  have h4 : (countDescFactorial (N.reaction r_z).source n : ℝ) * (κ.k r_z : ℝ) ≤
      (countDescFactorial (N.reaction r_z).source n : ℝ) * (κ.k r_y : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hk) h2
  have h5 : (κ.k r_z : ℝ) * (countDescFactorial (N.reaction r_z).source n : ℝ) ≤
      (κ.k r_y : ℝ) * (countDescFactorial (N.reaction r_y).source n : ℝ) := by
    linarith
  rw [stochasticMassActionRate_eq_countDescFactorial N κ n r_z,
    stochasticMassActionRate_eq_countDescFactorial N κ n r_y]
  exact h5

end Network

/-! ## 4. The obstruction: a strongly endotactic counterexample -/

namespace Examples
namespace EndotacticCounterexample

open Network

/-- The two-species network `0 → A`, `A → 0`, `0 → B`, `B → 0`: two independent
birth--death channels.  It is strongly endotactic, and it is the simplest example in which the
"top-tier monomial dominates the lower-tier monomials" step of the tier route fails. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0, 0], ![1, 0]⟩ else if r = 1 then ⟨![1, 0], ![0, 0]⟩
    else if r = 2 then ⟨![0, 0], ![0, 1]⟩ else ⟨![0, 1], ![0, 0]⟩⟩

/-- **The network is endotactic.**  For every direction `w` the `w`-maximal source complex
carries only descending reactions: the `w`-maximal source is `A` when `w 0` is the largest
weight, `B` when `w 1` is, and the empty complex when both weights are non-positive. -/
theorem endotactic : net.Endotactic := by
  intro w r hmax
  fin_cases r
  · -- the source of `0 → A` is the empty complex
    have h1 := hmax 1
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply, exponentVector] at h1 ⊢
    linarith
  · -- the source of `A → 0` is `A`
    have h0 := hmax 0
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply, exponentVector] at h0 ⊢
    linarith
  · -- the source of `0 → B` is the empty complex
    have h3 := hmax 3
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply, exponentVector] at h3 ⊢
    linarith
  · -- the source of `B → 0` is `B`
    have h0 := hmax 0
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply, exponentVector] at h0 ⊢
    linarith

/-- **The network is strongly endotactic in the standard sense.**  For every stoichiometrically
active direction there is a `w`-maximal reaction with a strictly negative `w`-rate. -/
theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨endotactic, ?_⟩
  intro w hactive
  by_cases hA : 0 < w 0
  · by_cases hB : w 1 ≤ w 0
    · -- the top tier is `A`
      refine ⟨1, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hA]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hA]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hB]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
        linarith
    · -- the top tier is `B`
      refine ⟨3, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hA, hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hA, hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hA, hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
        linarith
  · by_cases hB : 0 < w 1
    · -- the top tier is `B`
      refine ⟨3, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith [hB]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
        linarith
    · -- the top tier is the empty complex
      by_cases hA' : w 0 < 0
      · refine ⟨0, ?_, ?_⟩
        · intro r'
          fin_cases r'
          · simp [Network.wValue, Network.dotProduct, exponentVector]
          · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith
          · simp [Network.wValue, Network.dotProduct, exponentVector]
          · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
          linarith
      · by_cases hB' : w 1 < 0
        · refine ⟨2, ?_, ?_⟩
          · intro r'
            fin_cases r'
            · simp [Network.wValue, Network.dotProduct, exponentVector]
            · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith
            · simp [Network.wValue, Network.dotProduct, exponentVector]
            · simp [Network.wValue, Network.dotProduct, exponentVector] ; linarith
          · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
            linarith
        · exfalso
          have hz0 : w 0 = 0 := le_antisymm (le_of_not_gt hA) (le_of_not_gt hA')
          have hz1 : w 1 = 0 := le_antisymm (le_of_not_gt hB) (le_of_not_gt hB')
          have hall : ∀ r : net.R, net.wRate w r = 0 := by
            intro r
            unfold Network.wRate Network.dotProduct
            rw [Finset.sum_eq_zero]
            intro s _
            fin_cases s
            · simp [hz0]
            · simp [hz1]
          obtain ⟨r, hr⟩ := hactive
          rw [hall r] at hr
          exact absurd hr (by simp)

/-- The tier weight `w = (2, 1)`: the count of `A` is weighted twice as much as the count of
`B`, so that `A` is the top tier and `B` a strictly lower tier. -/
def tierWeight : Fin 2 → ℝ := fun s => if s = 0 then 2 else 1

theorem tierWeight_zero : tierWeight 0 = 2 := by
  simp [tierWeight]

theorem tierWeight_one : tierWeight 1 = 1 := by
  simp [tierWeight]

/-- For the tier weight `w = (2, 1)` the complex `A` is a `w`-maximal source: it is the top
tier. -/
theorem isMaxSource_A : net.IsMaxSource tierWeight 1 := by
  intro r'
  fin_cases r'
  · simp [Network.wValue, Network.dotProduct, exponentVector] ;
      linarith [tierWeight_zero]
  · simp [Network.wValue, Network.dotProduct, exponentVector]
  · simp [Network.wValue, Network.dotProduct, exponentVector] ;
      linarith [tierWeight_zero]
  · simp [Network.wValue, Network.dotProduct, exponentVector] ;
      linarith [tierWeight_zero, tierWeight_one]

/-- For the tier weight `w = (2, 1)` the complex `B` is *not* a `w`-maximal source: it lies in
a strictly lower tier. -/
theorem not_isMaxSource_B : ¬ net.IsMaxSource tierWeight 3 := by
  intro h
  have h1 := h 1
  simp [Network.wValue, Network.dotProduct, exponentVector] at h1
  linarith [tierWeight_zero, tierWeight_one]

/-- The escape direction `n k = (0, k)`: the count of `A` stays at zero while the count of `B`
grows without bound. -/
def escapeCount (k : ℕ) : Fin 2 → ℕ := fun s => if s = 0 then 0 else k

/-- Along the escape direction the count-lattice falling factorial of the **top tier** `A`
vanishes: the count of `A` stays at zero, so the falling factorial truncates. -/
theorem countDescFactorial_A_escape (k : ℕ) :
    countDescFactorial (net.reaction 1).source (escapeCount k) = 0 := by
  simp [countDescFactorial, escapeCount, Nat.descFactorial_succ, Nat.descFactorial_zero]

/-- Along the escape direction the count-lattice falling factorial of the **lower tier** `B`
grows linearly with the count of `B`. -/
theorem countDescFactorial_B_escape (k : ℕ) :
    countDescFactorial (net.reaction 3).source (escapeCount k) = k := by
  simp [countDescFactorial, escapeCount]

/-- **The obstruction.**  On the count lattice the domination of the lower-tier monomials by
the top-tier ones *fails* along the escape direction: the lower tier `B` has a strictly larger
count-lattice falling factorial than the top tier `A`, for every count along the escape
direction.  This is the precise content of the remark of the field map. -/
theorem topTier_does_not_dominate (k : ℕ) (hk : 1 ≤ k) :
    countDescFactorial (net.reaction 3).source (escapeCount k) >
      countDescFactorial (net.reaction 1).source (escapeCount k) := by
  rw [countDescFactorial_B_escape, countDescFactorial_A_escape]
  omega

/-- **The obstruction, at the level of the propensities.**  The propensity of the lower-tier
reaction `B → 0` strictly exceeds that of the top-tier reaction `A → 0` along the escape
direction. -/
theorem propensity_topTier_not_dominate (κ : net.RateConstants) (k : ℕ) (hk : 1 ≤ k) :
    net.stochasticMassActionRate κ (escapeCount k) 3 >
      net.stochasticMassActionRate κ (escapeCount k) 1 := by
  rw [stochasticMassActionRate_eq_countDescFactorial net κ (escapeCount k) 3,
    stochasticMassActionRate_eq_countDescFactorial net κ (escapeCount k) 1,
    countDescFactorial_B_escape, countDescFactorial_A_escape]
  have hk3 : 0 < (κ.k 3 : ℝ) := κ.positive 3
  have hk3k : 0 < (κ.k 3 : ℝ) * (k : ℝ) := mul_pos hk3 (by exact_mod_cast (show 0 < k by omega))
  simp only [Nat.cast_zero]
  rw [mul_zero]
  exact hk3k

/-- The top-tier complex `A` and the lower-tier complex `B` are **incomparable** in the
coordinatewise order: this is the structural reason why the falling-factorial comparison
cannot be applied to them. -/
theorem source_A_not_dominate_source_B :
    ¬ CountComplexDominates (net.reaction 1).source (net.reaction 3).source := by
  intro h
  have h1 := h 1
  simp at h1

/-- **The same network does admit a count-lattice tier structure** — for the weight
`w = (1, 1)`, in which `A` and `B` are both in the top tier, the ascending reactions `0 → A`
and `0 → B` have the empty source complex (hence count-independent propensity) and the species
`A`, `B` are consumed by the strictly descending top-tier reactions `A → 0`, `B → 0`.  The
obstruction of `topTier_does_not_dominate` is therefore a property of the *weight*, not of the
network. -/
noncomputable def countTier : CountTier net where
  w := fun _ => 1
  hw := by intro s; simp
  chain := countTierChain_of_linear net (fun _ => 1)
  descent := countTierDescent_of_stronglyEndotacticStd stronglyEndotacticStd (by
    refine ⟨0, ?_⟩
    simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply])
  inflow := by
    intro r hr s
    have hcases : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
    rcases hcases with h | h | h | h
    · -- the birth channel `0 → A`
      have hr0 : r = 0 := Fin.ext h
      subst hr0
      have hsrc : ∀ t : Fin 2, (net.reaction 0).source t = 0 := by decide
      exact hsrc s
    · -- the death channel `A → 0`: its tier rate is negative
      have hr1 : r = 1 := Fin.ext h
      subst hr1
      have hr' : net.wRate (fun _ => (1 : ℝ)) 1 ≤ 0 := by
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
      linarith
    · -- the birth channel `0 → B`
      have hr2 : r = 2 := Fin.ext h
      subst hr2
      have hsrc : ∀ t : Fin 2, (net.reaction 2).source t = 0 := by decide
      exact hsrc s
    · -- the death channel `B → 0`: its tier rate is negative
      have hr3 : r = 3 := Fin.ext h
      subst hr3
      have hr' : net.wRate (fun _ => (1 : ℝ)) 3 ≤ 0 := by
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
      linarith
  coverage := by
    intro s
    have hcases : s.val = 0 ∨ s.val = 1 := by omega
    rcases hcases with h | h
    · -- the species `A`, consumed by the top-tier reaction `A → 0`
      have hs0 : s = 0 := Fin.ext h
      subst hs0
      refine ⟨1, ?_, ?_, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
      · have hne : (net.reaction 1).source 0 ≠ 0 := by decide
        exact hne
      · intro t ht
        have hdec : ∀ u : Fin 2, u ≠ 0 → (net.reaction 1).source u = 0 := by decide
        exact hdec t ht
    · -- the species `B`, consumed by the top-tier reaction `B → 0`
      have hs1 : s = 1 := Fin.ext h
      subst hs1
      refine ⟨3, ?_, ?_, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
        · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
      · have hne : (net.reaction 3).source 1 ≠ 0 := by decide
        exact hne
      · intro t ht
        have hdec : ∀ u : Fin 2, u ≠ 1 → (net.reaction 3).source u = 0 := by decide
        exact hdec t ht

end EndotacticCounterexample
end Examples

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 5. The balanced count-lattice tier structure and the ACK drift -/

/-- **A balanced count-lattice tier structure.**  This is the count-lattice analogue of the
deterministic tier structure of Anderson--Cappelletti--Kim--Nguyen, with the one restriction
that the *tier separation* of `CRNT.Network.CountTier` (every ascending reaction has the empty
source complex) is replaced by the weaker **balance** condition:

* the tier weight `w` is strictly positive;
* the top tier does not ascend the tier potential and descends it strictly in at least one
  reaction (`descent`);
* every **ascending** reaction (`wRate w r > 0`) with a **nonempty** source complex is
  *balanced* by a **descending** reaction with the **same source complex**
  (`partner`): the two reactions have the *same* falling factorial — the truncation
  obstruction of §4 cannot occur, because the two complexes coincide — and the descending
  partner has at least as much rate capacity as the ascending reaction;
* every species is consumed by a strictly descending **top-tier** reaction supported on that
  species alone (`inward`), which produces the strictly negative drift in every coordinate of
  the count lattice.

The partners of distinct ascending reactions are distinct, and no inward reaction is used as a
partner; these two conditions make the bookkeeping of the drift exact. -/
structure CountTierBalance (N : Network S) (κ : N.RateConstants) where
  /-- The tier weight. -/
  w : S → ℝ
  /-- The tier weight is strictly positive. -/
  hw : ∀ s, 0 < w s
  /-- The top tier does not ascend the tier potential and descends it strictly. -/
  descent : CountTierDescent N w
  /-- The partner of an ascending reaction with a nonempty source complex. -/
  partner : N.R → N.R
  /-- The partner is a descending reaction with the *same* source complex and at least as much
  rate capacity as the ascending reaction. -/
  hpartner : ∀ r : N.R, N.wRate w r > 0 → ComplexNonempty (N.reaction r).source →
    N.wRate w (partner r) < 0 ∧
      (N.reaction (partner r)).source = (N.reaction r).source ∧
      κ.k (partner r) * |N.wRate w (partner r)| ≥ κ.k r * N.wRate w r
  /-- The partner map is injective on the ascending reactions with a nonempty source. -/
  hpartner_injective : ∀ r₁ r₂ : N.R,
    N.wRate w r₁ > 0 → ComplexNonempty (N.reaction r₁).source →
    N.wRate w r₂ > 0 → ComplexNonempty (N.reaction r₂).source →
    partner r₁ = partner r₂ → r₁ = r₂
  /-- The inward reaction of a species. -/
  inward : S → N.R
  /-- The inward reaction is a strictly descending top-tier reaction supported on that species
  alone. -/
  hinward : ∀ s : S, N.IsMaxSource w (inward s) ∧ N.wRate w (inward s) < 0 ∧
    (N.reaction (inward s)).source s ≠ 0 ∧
    ∀ t, t ≠ s → (N.reaction (inward s)).source t = 0
  /-- The inward reactions of distinct species are distinct. -/
  hinward_ne : ∀ s t : S, s ≠ t → inward s ≠ inward t
  /-- The inward reactions are never used as partners. -/
  hinward_not_partner : ∀ r : N.R, ∀ s : S,
    N.wRate w r > 0 → ComplexNonempty (N.reaction r).source → inward s ≠ partner r

/-- The species type of a balanced count-lattice tier structure is inhabited: the tier
potential of every complex vanishes when there is no species, and the top tier cannot descend
strictly in that case. -/
theorem CountTierBalance.nonempty_species {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) : Nonempty S := by
  by_contra h
  have hnot : ¬ (Finset.univ : Finset S).Nonempty := by
    rintro ⟨a, ha⟩
    exact h ⟨a⟩
  have hU : (Finset.univ : Finset S) = ∅ :=
    (Finset.not_nonempty_iff_eq_empty (s := (Finset.univ : Finset S))).mp hnot
  obtain ⟨r, _, hneg⟩ := B.descent.2
  have hzero : N.wRate B.w r = 0 := by
    unfold Network.wRate Network.dotProduct
    rw [hU, Finset.sum_empty]
  linarith

/-- The number of molecules of `s` consumed by the inward reaction of `s`. -/
noncomputable def CountTierBalance.inwardMol {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (s : S) : ℕ :=
  (N.reaction (B.inward s)).source s

/-- The inward reaction of `s` consumes at least one molecule of `s`. -/
theorem CountTierBalance.inwardMol_pos {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (s : S) :
    0 < B.inwardMol s :=
  Nat.pos_of_ne_zero (B.hinward s).2.2.1

/-- The inward drift weight of the species `s`. -/
noncomputable def CountTierBalance.inwardWeight {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (s : S) : ℝ :=
  κ.k (B.inward s) * |N.wRate B.w (B.inward s)|

/-- The inward drift weight of a species is strictly positive. -/
theorem CountTierBalance.inwardWeight_pos {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (s : S) :
    0 < B.inwardWeight s := by
  unfold CountTierBalance.inwardWeight
  exact mul_pos (κ.positive (B.inward s))
    (abs_pos.mpr (ne_of_lt (B.hinward s).2.1))

/-- If all the terms of a sum are nonpositive, the sum over a superset is at most the sum over
a subset: the omitted terms are nonpositive. -/
private theorem sum_le_sum_of_subset_of_nonpos {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (A B : Finset ι) (hBA : B ⊆ A) (hf : ∀ i ∈ A, f i ≤ 0) :
    ∑ i ∈ A, f i ≤ ∑ i ∈ B, f i := by
  classical
  have hfilter : A.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hBA h, h⟩
  have hsplit : (∑ i ∈ A, f i) = (∑ i ∈ A.filter (fun i => i ∈ B), f i) +
      (∑ i ∈ A.filter (fun i => i ∉ B), f i) :=
    (Finset.sum_filter_add_sum_filter_not A (fun i => i ∈ B) f).symm
  rw [hsplit, hfilter]
  have hrest : (∑ i ∈ A.filter (fun i => i ∉ B), f i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => hf i (Finset.mem_filter.mp hi).1
  linarith

/-- **The ACK drift of a balanced count-lattice tier structure.**  The count-lattice Lyapunov
function `V n = ∑_s w_s n_s` of a balanced count-lattice tier structure satisfies the
multiplicative Foster--Lyapunov drift

`Q V (n) ≤ -ε · V (n) + K`   with `ε > 0` and `K ≥ 0`.

This is the count-lattice counterpart of the deterministic tier dissipation of leaf D9: the
ascending reactions with a nonempty source complex are cancelled by their partners (which have
the same source complex, hence the same falling factorial), while the inward reactions produce
the strictly negative drift in every coordinate of the count lattice. -/
theorem tierBalanceDrift_multiplicative {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : S → ℕ, N.observableGenerator κ (linearObservable B.w) n ≤
        -ε * linearObservable B.w n + K := by
  classical
  set w : S → ℝ := B.w with hwdef
  -- the generator of the tier Lyapunov function
  have hgen : ∀ n : S → ℕ,
      N.observableGenerator κ (linearObservable w) n =
        ∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r := by
    intro n
    rw [N.observableGenerator_linear]
    apply Finset.sum_congr rfl
    intro r _
    rw [N.wRate_eq]
    have h : (∑ s : S, w s * N.reactionVector r s) =
        ∑ s : S, w s * (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Network.reactionVector_apply]
    rw [h]
  -- the groups of reactions
  set Aup : Finset N.R := Finset.univ.filter fun r => 0 < N.wRate w r with hAupdef
  set A0 : Finset N.R := Aup.filter fun r => ¬ ComplexNonempty (N.reaction r).source with hA0def
  set A1 : Finset N.R := Aup.filter fun r => ComplexNonempty (N.reaction r).source with hA1def
  set Dn : Finset N.R := Finset.univ.filter fun r => N.wRate w r < 0 with hDndef
  set P : Finset N.R := A1.image B.partner with hPdef
  have hA0_mem : ∀ r : N.R, r ∈ A0 ↔
      (0 < N.wRate w r ∧ ¬ ComplexNonempty (N.reaction r).source) := by
    intro r
    simp [hA0def, hAupdef]
  have hA1_mem : ∀ r : N.R, r ∈ A1 ↔
      (0 < N.wRate w r ∧ ComplexNonempty (N.reaction r).source) := by
    intro r
    simp [hA1def, hAupdef]
  have hDn_mem : ∀ r : N.R, r ∈ Dn ↔ N.wRate w r < 0 := by
    intro r
    simp [hDndef]
  have hA0_sub : A0 ⊆ Aup := by
    intro r hr
    rw [hAupdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hA0_mem r).mp hr).1⟩
  have hA1_sub : A1 ⊆ Aup := by
    intro r hr
    rw [hAupdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hA1_mem r).mp hr).1⟩
  have hAup_eq : Aup = A0 ∪ A1 := by
    ext r
    constructor
    · intro hr
      rw [hAupdef] at hr
      have hmem := (Finset.mem_filter.mp hr).2
      by_cases h : ComplexNonempty (N.reaction r).source
      · exact Finset.mem_union_right _ ((hA1_mem r).mpr ⟨hmem, h⟩)
      · exact Finset.mem_union_left _ ((hA0_mem r).mpr ⟨hmem, by simpa using h⟩)
    · intro hr
      rw [Finset.mem_union] at hr
      rcases hr with hr1 | hr2
      · rw [hAupdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hA0_mem r).mp hr1).1⟩
      · rw [hAupdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hA1_mem r).mp hr2).1⟩
  have hA0_disj_A1 : Disjoint A0 A1 := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have h1 := ((hA0_mem r).mp hr1).2
    have h2 := ((hA1_mem r).mp hr2).2
    exact absurd h2 h1
  have hAup_disj_Dn : Disjoint Aup Dn := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    rw [hAupdef] at hr1
    have h1 := (Finset.mem_filter.mp hr1).2
    have h2 := (hDn_mem r).mp hr2
    linarith
  have hP_sub_Dn : P ⊆ Dn := by
    intro r hr
    rw [hPdef] at hr
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hr
    have hmem : N.wRate B.w r' > 0 := by
      simpa [hwdef] using ((hA1_mem r').mp hr').1
    have hne : ComplexNonempty (N.reaction r').source := ((hA1_mem r').mp hr').2
    have h := (B.hpartner r' hmem hne).1
    exact (hDn_mem (B.partner r')).mpr (by simpa [hwdef] using h)
  have hinj : Set.InjOn B.partner A1 := by
    intro r₁ hr₁ r₂ hr₂ heq
    have h1 := (hA1_mem r₁).mp hr₁
    have h2 := (hA1_mem r₂).mp hr₂
    rw [hwdef] at h1 h2
    exact B.hpartner_injective r₁ r₂ h1.1 h1.2 h2.1 h2.2 heq
  have hinj_inward : Set.InjOn B.inward (Finset.univ : Finset S) := by
    intro s _ t _ heq
    by_contra hne
    exact (B.hinward_ne s t hne) heq
  -- the main estimate
  have hmain : ∀ (n : S → ℕ),
      (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r)
        ≤ (∑ r ∈ A0, κ.k r * N.wRate w r)
          + (∑ s : S, N.stochasticMassActionRate κ n (B.inward s) * N.wRate w (B.inward s)) := by
    intro n
    set f : N.R → ℝ := fun r => N.stochasticMassActionRate κ n r * N.wRate w r with hfdef
    -- a balanced ascending reaction is cancelled by its partner
    have hpair : ∀ r : N.R, r ∈ A1 →
        f r + f (B.partner r) ≤ 0 := by
      intro r hr
      have hmem : N.wRate w r > 0 := ((hA1_mem r).mp hr).1
      have hne : ComplexNonempty (N.reaction r).source := ((hA1_mem r).mp hr).2
      have hmem' : N.wRate B.w r > 0 := by simpa [hwdef] using hmem
      obtain ⟨hdesc, hsrc, hbal⟩ := B.hpartner r hmem' hne
      have hdesc' : N.wRate w (B.partner r) < 0 := by simpa [hwdef] using hdesc
      have hbal' : (κ.k (B.partner r) : ℝ) * |N.wRate w (B.partner r)| ≥
          (κ.k r : ℝ) * N.wRate w r := by
        simpa [hwdef] using hbal
      have hbalLE : (κ.k r : ℝ) * N.wRate w r ≤
          (κ.k (B.partner r) : ℝ) * |N.wRate w (B.partner r)| := (ge_iff_le.mp hbal')
      have hprop : N.stochasticMassActionRate κ n r =
          κ.k r * ((countDescFactorial (N.reaction r).source n : ℝ)) :=
        stochasticMassActionRate_eq_countDescFactorial N κ n r
      have hprop' : N.stochasticMassActionRate κ n (B.partner r) =
          κ.k (B.partner r) * ((countDescFactorial (N.reaction (B.partner r)).source n : ℝ)) :=
        stochasticMassActionRate_eq_countDescFactorial N κ n (B.partner r)
      have hcdf : countDescFactorial (N.reaction (B.partner r)).source n =
          countDescFactorial (N.reaction r).source n := by rw [hsrc]
      have hC : 0 ≤ (countDescFactorial (N.reaction r).source n : ℝ) := by
        exact_mod_cast Nat.zero_le _
      have hbal'' : (κ.k r : ℝ) * N.wRate w r ≤
          (κ.k (B.partner r) : ℝ) * |N.wRate w (B.partner r)| := by
        rw [abs_of_nonpos hdesc'.le] at hbalLE
        rw [abs_of_nonpos hdesc'.le]
        exact hbalLE
      have hcp : |N.wRate w (B.partner r)| = -N.wRate w (B.partner r) := abs_of_nonpos hdesc'.le
      simp only [hfdef]
      rw [hprop, hprop', hcdf]
      calc
        (κ.k r : ℝ) * (countDescFactorial (N.reaction r).source n : ℝ) * N.wRate w r +
            (κ.k (B.partner r) : ℝ) * (countDescFactorial (N.reaction r).source n : ℝ) *
              N.wRate w (B.partner r) =
          (countDescFactorial (N.reaction r).source n : ℝ) *
            ((κ.k r : ℝ) * N.wRate w r + (κ.k (B.partner r) : ℝ) * N.wRate w (B.partner r)) := by
              ring
        _ = (countDescFactorial (N.reaction r).source n : ℝ) *
            ((κ.k r : ℝ) * N.wRate w r -
              (κ.k (B.partner r) : ℝ) * |N.wRate w (B.partner r)|) := by rw [hcp]; ring
        _ ≤ 0 := by
          have h2 : (κ.k r : ℝ) * N.wRate w r - (κ.k (B.partner r) : ℝ) * |N.wRate w (B.partner r)| ≤ 0 :=
            by linarith [hbal'']
          exact mul_nonpos_of_nonneg_of_nonpos hC h2
    -- the sum over the ascending reactions with a nonempty source is bounded by the negative
    -- of the sum over their partners
    have hA1_bound : (∑ r ∈ A1, f r) ≤ -(∑ r ∈ P, f r) := by
      have hstep : ∀ r ∈ A1, f r ≤ -f (B.partner r) := by
        intro r hr
        have := hpair r hr
        linarith
      have hsum : (∑ r ∈ A1, f r) ≤ ∑ r ∈ A1, -f (B.partner r) :=
        Finset.sum_le_sum fun r hr => hstep r hr
      have himage : (∑ r ∈ P, f r) = ∑ r ∈ A1, f (B.partner r) := by
        rw [hPdef, Finset.sum_image hinj]
      rw [Finset.sum_neg_distrib, ← himage] at hsum
      linarith
    -- the split of the drift
    have hsplit : (∑ r : N.R, f r) = (∑ r ∈ A0, f r) + (∑ r ∈ A1, f r) + (∑ r ∈ Dn, f r) := by
      have hzero : ∀ r ∈ (Finset.univ : Finset N.R) \ (Aup ∪ Dn), f r = 0 := by
        intro r hr
        have h1 : r ∉ Aup ∪ Dn := (Finset.mem_sdiff.mp hr).2
        have h3 : ¬ (0 < N.wRate w r) := by
          intro h
          rw [hAupdef] at h1
          exact h1 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
        have h4 : ¬ (N.wRate w r < 0) := by
          intro h
          rw [hDndef] at h1
          exact h1 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
        have h5 : N.wRate w r = 0 := by linarith
        simp only [hfdef, h5, mul_zero]
      have h1 : (∑ r : N.R, f r) = (∑ r ∈ (Finset.univ : Finset N.R) \ (Aup ∪ Dn), f r) +
          (∑ r ∈ Aup ∪ Dn, f r) := by
        symm
        exact Finset.sum_sdiff (s₁ := Aup ∪ Dn) (s₂ := (Finset.univ : Finset N.R))
          (f := f) (Finset.subset_univ _)
      have hz : (∑ r ∈ (Finset.univ : Finset N.R) \ (Aup ∪ Dn), f r) = 0 := by
        rw [Finset.sum_eq_zero]
        intro r hr
        exact hzero r hr
      rw [h1, hz, zero_add, Finset.sum_union hAup_disj_Dn, hAup_eq,
        Finset.sum_union hA0_disj_A1]
    -- the descending reactions that are not partners
    have hD_split : (∑ r ∈ Dn, f r) = (∑ r ∈ P, f r) + (∑ r ∈ Dn \ P, f r) := by
      have h := Finset.sum_sdiff (s₁ := P) (s₂ := Dn) (f := f) hP_sub_Dn
      linarith
    -- the inward reactions are among the descending reactions that are not partners
    have hinward_sub : (Finset.univ : Finset S).image B.inward ⊆ Dn \ P := by
      intro r hr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact (hDn_mem (B.inward s)).mpr (B.hinward s).2.1
      · intro hcon
        rw [hPdef] at hcon
        obtain ⟨r', hr', heq⟩ := Finset.mem_image.mp hcon
        exact B.hinward_not_partner r' s
          ((hA1_mem r').mp hr').1 ((hA1_mem r').mp hr').2 heq.symm
    have hnonpos : ∀ r ∈ Dn \ P, f r ≤ 0 := by
      intro r hr
      have h1 := (hDn_mem r).mp (Finset.mem_sdiff.mp hr).1
      simp only [hfdef]
      exact mul_nonpos_of_nonneg_of_nonpos (N.stochasticMassActionRate_nonneg κ n r) h1.le
    have hrest : (∑ r ∈ Dn \ P, f r) ≤ ∑ r ∈ (Finset.univ : Finset S).image B.inward, f r :=
      sum_le_sum_of_subset_of_nonpos f (Dn \ P) ((Finset.univ : Finset S).image B.inward)
        hinward_sub hnonpos
    have hinward_sum : (∑ r ∈ (Finset.univ : Finset S).image B.inward, f r) =
        ∑ s : S, f (B.inward s) := by
      rw [Finset.sum_image hinj_inward]
    -- the ascending reactions with an empty source complex have a count-independent propensity
    have hA0rate : ∀ (r : N.R), r ∈ A0 →
        N.stochasticMassActionRate κ n r = κ.k r := by
      intro r hr
      have hne : ∀ s, (N.reaction r).source s = 0 := by
        intro s
        by_contra hcon
        have : ComplexNonempty (N.reaction r).source := ⟨s, hcon⟩
        exact ((hA0_mem r).mp hr).2 this
      unfold stochasticMassActionRate
      have hprod : (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = 1 := by
        apply Finset.prod_eq_one
        intro s _
        rw [hne s, Nat.descFactorial_zero]
        norm_num
      rw [hprod]
      simp
    have hA0eq : (∑ r ∈ A0, f r) = ∑ r ∈ A0, κ.k r * N.wRate w r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [hfdef]
      rw [hA0rate r hr]
    -- assemble
    have h2 : (∑ r : N.R, f r) ≤ (∑ r ∈ A0, κ.k r * N.wRate w r) + (∑ s : S, f (B.inward s)) := by
      rw [hsplit, hD_split, hA0eq]
      have hA1b := hA1_bound
      have hr := hrest
      have his := hinward_sum
      linarith
    exact h2
  -- the per-species inward contribution
  have hspec : ∀ (n : S → ℕ) (s : S),
      N.stochasticMassActionRate κ n (B.inward s) * N.wRate w (B.inward s) ≤
        -B.inwardWeight s * (n s : ℝ) + B.inwardWeight s * ((B.inwardMol s : ℝ) - 1) := by
    intro n s
    have hdesc : N.wRate w (B.inward s) < 0 := (B.hinward s).2.1
    have hsrc' : ∀ t, t ≠ s → (N.reaction (B.inward s)).source t = 0 :=
      (B.hinward s).2.2.2
    have hrate : N.stochasticMassActionRate κ n (B.inward s) =
        κ.k (B.inward s) * ((n s).descFactorial (B.inwardMol s) : ℝ) :=
      stochasticMassActionRate_eq_descFactorial N κ n (B.inward s) s hsrc'
    have habs : |N.wRate w (B.inward s)| = -N.wRate w (B.inward s) := abs_of_nonpos hdesc.le
    have hβ : B.inwardWeight s = κ.k (B.inward s) * (-N.wRate w (B.inward s)) := by
      unfold CountTierBalance.inwardWeight
      rw [habs]
    rw [hrate]
    by_cases hkn : B.inwardMol s ≤ n s
    · have hd : (n s : ℝ) ≤ ((n s).descFactorial (B.inwardMol s) : ℝ) := by
        have h1 : 1 ≤ B.inwardMol s := B.inwardMol_pos s
        exact_mod_cast nat_descFactorial_ge_self h1 hkn
      have h1 : ((n s).descFactorial (B.inwardMol s) : ℝ) * N.wRate w (B.inward s) ≤
          (n s : ℝ) * N.wRate w (B.inward s) :=
        mul_le_mul_of_nonpos_right hd hdesc.le
      have h2 : κ.k (B.inward s) *
            ((n s).descFactorial (B.inwardMol s) : ℝ) * N.wRate w (B.inward s) ≤
          κ.k (B.inward s) * (n s : ℝ) * N.wRate w (B.inward s) := by
        have hz := mul_le_mul_of_nonneg_left h1 (κ.positive (B.inward s)).le
        have hz' : κ.k (B.inward s) *
              (((n s).descFactorial (B.inwardMol s) : ℝ) * N.wRate w (B.inward s)) ≤
            κ.k (B.inward s) * ((n s : ℝ) * N.wRate w (B.inward s)) := hz
        simpa [mul_assoc] using hz'
      have h3 : κ.k (B.inward s) * (n s : ℝ) * N.wRate w (B.inward s) =
          -B.inwardWeight s * (n s : ℝ) := by
        rw [hβ]
        ring
      have h4 : 0 ≤ B.inwardWeight s * ((B.inwardMol s : ℝ) - 1) := by
        have hp := B.inwardWeight_pos s
        have hk : (1 : ℝ) ≤ (B.inwardMol s : ℝ) := by exact_mod_cast B.inwardMol_pos s
        exact mul_nonneg hp.le (by linarith)
      linarith
    · have hz : ((n s).descFactorial (B.inwardMol s) : ℝ) = 0 := by
        have h1 : (n s).descFactorial (B.inwardMol s) = 0 :=
          (Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)
        exact_mod_cast h1
      have hp : 0 < B.inwardWeight s := B.inwardWeight_pos s
      have hk : (n s : ℝ) ≤ (B.inwardMol s : ℝ) - 1 := by
        have h1 : n s + 1 ≤ B.inwardMol s := by omega
        have h2 : ((n s + 1 : ℕ) : ℝ) ≤ (B.inwardMol s : ℝ) := by exact_mod_cast h1
        rw [Nat.cast_add, Nat.cast_one] at h2
        linarith
      rw [hz, mul_zero]
      have : 0 ≤ B.inwardWeight s * ((B.inwardMol s : ℝ) - 1 - (n s : ℝ)) := by
        exact mul_nonneg hp.le (by linarith)
      linarith
  -- the multiplicative coefficient
  obtain ⟨s0⟩ := B.nonempty_species
  have hvalsne :
      ((Finset.univ : Finset S).image (fun s : S => B.inwardWeight s / w s)).Nonempty := by
    refine ⟨B.inwardWeight s0 / w s0, ?_⟩
    exact Finset.mem_image.mpr ⟨s0, Finset.mem_univ s0, rfl⟩
  set ε : ℝ :=
    ((Finset.univ : Finset S).image (fun s : S => B.inwardWeight s / w s)).min' hvalsne
    with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have hmem := Finset.min'_mem _ hvalsne
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.mp hmem
    have heq : ((Finset.univ : Finset S).image (fun t : S => B.inwardWeight t / w t)).min' hvalsne
        = B.inwardWeight b / w b := hfb.symm
    rw [heq]
    exact div_pos (B.inwardWeight_pos b) (B.hw b)
  have hεle : ∀ s : S, ε ≤ B.inwardWeight s / w s := by
    intro s
    rw [hεdef]
    exact Finset.min'_le _ (B.inwardWeight s / w s)
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)
  have hεw : ∀ s : S, ε * w s ≤ B.inwardWeight s := by
    intro s
    have h1 : ε * w s ≤ (B.inwardWeight s / w s) * w s :=
      mul_le_mul_of_nonneg_right (hεle s) (B.hw s).le
    have h2 : (B.inwardWeight s / w s) * w s = B.inwardWeight s :=
      div_mul_cancel₀ _ (ne_of_gt (B.hw s))
    linarith
  -- the constant
  set K1 : ℝ := ∑ s : S, B.inwardWeight s * ((B.inwardMol s : ℝ) - 1) with hK1def
  have hK1 : 0 ≤ K1 := by
    rw [hK1def]
    exact Finset.sum_nonneg fun s _ => by
      have hp := B.inwardWeight_pos s
      have hk : (1 : ℝ) ≤ (B.inwardMol s : ℝ) := by exact_mod_cast B.inwardMol_pos s
      exact mul_nonneg hp.le (by linarith)
  refine ⟨ε, hεpos, (∑ r ∈ A0, κ.k r * N.wRate w r) + K1, ?_, ?_⟩
  · -- the constant is nonnegative
    have hK0 : 0 ≤ ∑ r ∈ A0, κ.k r * N.wRate w r :=
      Finset.sum_nonneg fun r hr => by
        have h1 := (hA0_mem r).mp hr
        exact mul_nonneg (κ.positive r).le h1.1.le
    exact add_nonneg hK0 hK1
  · intro n
    have hV : linearObservable w = linearObservable B.w := by
      simp [hwdef]
    rw [hV, hgen]
    have h1 : (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r) ≤
        (∑ r ∈ A0, κ.k r * N.wRate w r) +
          (∑ s : S, (N.stochasticMassActionRate κ n (B.inward s) *
            N.wRate w (B.inward s))) :=
      hmain n
    have h2 : (∑ s : S, (N.stochasticMassActionRate κ n (B.inward s) *
          N.wRate w (B.inward s))) ≤
        ∑ s : S, (-B.inwardWeight s * (n s : ℝ) +
          B.inwardWeight s * ((B.inwardMol s : ℝ) - 1)) :=
      Finset.sum_le_sum fun s _ => hspec n s
    have h3 : (∑ s : S, (-B.inwardWeight s * (n s : ℝ) +
          B.inwardWeight s * ((B.inwardMol s : ℝ) - 1))) =
        -∑ s : S, B.inwardWeight s * (n s : ℝ) + K1 := by
      rw [Finset.sum_add_distrib, hK1def]
      have hneg : (∑ s : S, -B.inwardWeight s * (n s : ℝ)) =
          -∑ s : S, B.inwardWeight s * (n s : ℝ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hneg]
    have h4 : ε * (∑ s : S, w s * (n s : ℝ)) ≤ ∑ s : S, B.inwardWeight s * (n s : ℝ) := by
      have hnonneg : ∀ s : S, 0 ≤ (n s : ℝ) := fun s => Nat.cast_nonneg _
      calc ε * (∑ s : S, w s * (n s : ℝ)) = ∑ s : S, ε * (w s * (n s : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ s : S, (ε * (w s * (n s : ℝ)) +
              (B.inwardWeight s - ε * w s) * (n s : ℝ)) := by
            apply Finset.sum_le_sum
            intro s _
            exact le_add_of_nonneg_right (mul_nonneg (by linarith [hεw s]) (hnonneg s))
        _ = ∑ s : S, B.inwardWeight s * (n s : ℝ) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
    have hVsum : linearObservable w n = ∑ s : S, w s * (n s : ℝ) := by
      simp [linearObservable]
    rw [hVsum]
    linarith [h1]

end Network

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 6. Non-explosion, Foster's hitting time and positive recurrence -/

/-- The count-lattice Lyapunov function of a balanced count-lattice tier structure is
nonnegative. -/
theorem balanceLyapunov_nonneg {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (n : S → ℕ) :
    0 ≤ linearObservable B.w n :=
  linearObservable_nonneg_of_positive B.hw n

/-- The count-lattice Lyapunov function of a balanced count-lattice tier structure has finite
sublevel sets. -/
theorem balanceLyapunov_finiteSublevel {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {κ : N.RateConstants} (B : CountTierBalance N κ) (R : ℝ) :
    {n | linearObservable B.w n ≤ R}.Finite :=
  finite_linearObservable_le B.w B.hw R

/-- **The Anderson--Cappelletti--Kim--Nguyen drift condition for a balanced count-lattice tier
structure.**  The tier Lyapunov function `V n = ∑_s w_s n_s` is nonnegative, has finite sublevel
sets, and its drift is bounded above by `-c` outside a finite set of counts. -/
theorem tierBalanceDrift_le_of {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ) :
    ∃ V : (S → ℕ) → ℝ, (∀ n, 0 ≤ V n) ∧ (∀ R : ℝ, {n | V n ≤ R}.Finite) ∧
      ∃ C : Set (S → ℕ), C.Finite ∧ ∃ c : ℝ, 0 < c ∧
        ∀ n ∉ C, N.observableGenerator κ V n ≤ -c := by
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierBalanceDrift_multiplicative N κ B
  set V : (S → ℕ) → ℝ := linearObservable B.w with hVdef
  have hV : ∀ n, 0 ≤ V n := balanceLyapunov_nonneg B
  have hfinV : ∀ R : ℝ, {n | V n ≤ R}.Finite := balanceLyapunov_finiteSublevel B
  refine ⟨V, hV, hfinV, {n | V n ≤ (K + 1) / ε}, ?_, 1, one_pos, ?_⟩
  · exact hfinV _
  · intro n hn
    have hV' : (K + 1) / ε < V n := by
      simpa [hVdef, Set.mem_ofPred_eq] using hn
    have hεV : K + 1 < ε * V n := by
      have h := (div_lt_iff₀ hε).mp hV'
      linarith
    have h := hdrift n
    linarith

/-- **Non-explosion of a balanced count-lattice tier structure.**  The minimal transition
function of the stochastic mass-action chain is stochastic: the chain makes only finitely many
jumps in a finite time interval. -/
theorem tierBalance_nonExplosion {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ)
    {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierBalanceDrift_multiplicative N κ B
  have hV : ∀ m : S → ℕ, 0 ≤ linearObservable B.w m := balanceLyapunov_nonneg B
  have hfinV : ∀ R : ℝ, {m | linearObservable B.w m ≤ R}.Finite :=
    balanceLyapunov_finiteSublevel B
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable B.w) hV hfinV
    (le_refl 0) hK (fun m => ?_) ht n
  rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) m]
  have h := hdrift m
  have := mul_nonneg hε.le (hV m)
  linarith

/-- **Foster's criterion for a balanced count-lattice tier structure.**  Under the drift
condition, the chain enters the finite set of exceptional counts with probability one and the
expected time of entry is bounded by `V (a) / (c t)` after time `t`. -/
theorem tierBalanceFoster_hitting_time {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ)
    {c : ℝ} (hc : 0 < c) {C : Set (S → ℕ)} (hC : C.Finite)
    (hdrift : ∀ n, n ∉ C → N.observableGenerator κ (linearObservable B.w) n ≤ -c)
    (a : S → ℕ) :
    (∀ t, 0 < t →
        1 - ∑ b ∈ hC.toFinset, ((N.jumpSystem κ).stopOn hC.toFinset).Pmin t a b ≤
          linearObservable B.w a / (c * t)) ∧
      Tendsto (fun t => ∑ b ∈ hC.toFinset, ((N.jumpSystem κ).stopOn hC.toFinset).Pmin t a b)
        atTop (𝓝 1) := by
  classical
  set CF : Finset (S → ℕ) := hC.toFinset with hCFdef
  have hgen : ∀ n, n ∉ CF → (N.jumpSystem κ).drift (linearObservable B.w) n ≤ -c := by
    intro n hn
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) n]
    apply hdrift n
    intro hmem
    exact hn ((Set.Finite.mem_toFinset hC).mpr hmem)
  refine ⟨fun t ht => ?_, ?_⟩
  · exact (N.jumpSystem κ).notAbsorbed_le CF (linearObservable B.w)
      (balanceLyapunov_nonneg B) (balanceLyapunov_finiteSublevel B) hc hgen ht a
  · exact (N.jumpSystem κ).tendsto_absorbed_one CF (linearObservable B.w)
      (balanceLyapunov_nonneg B) (balanceLyapunov_finiteSublevel B) hc hgen a

/-- **Positive recurrence of a balanced count-lattice tier structure.**  The stochastic
mass-action chain of a network carrying a balanced count-lattice tier structure is
*geometrically ergodic*: it has a unique stationary probability `π` which charges every count,
and the chain converges to `π`. -/
theorem tierBalance_positiveRecurrence {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ)
    (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : S → ℕ, Tendsto (fun t => N.transition κ t a a) atTop (𝓝 (π a))) := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierBalanceDrift_multiplicative N κ B
  have hV : ∀ n : S → ℕ, 0 ≤ linearObservable B.w n := balanceLyapunov_nonneg B
  have hstoch : ∀ t, 0 ≤ t → ∀ c : S → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable B.w) hV
      (balanceLyapunov_finiteSublevel B) (le_refl 0) hK (fun m => ?_) ht c
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) m]
    have h := hdrift m
    have := mul_nonneg hε.le (hV m)
    linarith
  have hfinf : ∀ R : ℝ, {x | ε * linearObservable B.w x ≤ R}.Finite := by
    intro R
    refine (balanceLyapunov_finiteSublevel B (R / ε)).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hε]
    linarith
  have hdrift' : ∀ x : S → ℕ,
      (N.jumpSystem κ).drift (linearObservable B.w) x ≤
        -(ε * linearObservable B.w x) + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) x]
    have h := hdrift x
    linarith
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, -⟩ :=
    (N.jumpSystem κ).foster_lyapunov_ergodic (linearObservable B.w)
      (fun x => ε * linearObservable B.w x) hV (fun x => mul_nonneg hε.le (hV x)) hfinf hK
      hdrift' hstoch (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun _ _ _ _ => hirr _ _) (Set.mem_univ (fun _ => 0))
  refine ⟨π, hπ0, hπ1, hπinv, fun b => hπpos b (Set.mem_univ b), ?_⟩
  intro a
  have hlim : Tendsto (fun t => (N.jumpSystem κ).Pmin t a a) atTop (𝓝 (π a)) :=
    (N.jumpSystem κ).tendsto_Pmin_of_invariant
      (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ => hirr _ _)
      (fun t ht c _ => hstoch t ht c) hπ0 (fun b h => (h (Set.mem_univ b)).elim) hπ1 hπinv
      (Set.mem_univ a) a
  simpa only [Network.transition] using hlim

/-- **Geometric ergodicity of a balanced count-lattice tier structure.** -/
theorem tierBalance_geometricErgodic {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ)
    (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * linearObservable B.w b) ≤
          C₀ * (1 + linearObservable B.w a) * ρ ^ ⌊t⌋₊ := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierBalanceDrift_multiplicative N κ B
  have hV : ∀ n : S → ℕ, 0 ≤ linearObservable B.w n := balanceLyapunov_nonneg B
  have hstoch : ∀ t, 0 ≤ t → ∀ c : S → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable B.w) hV
      (balanceLyapunov_finiteSublevel B) (le_refl 0) hK (fun m => ?_) ht c
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) m]
    have h := hdrift m
    have := mul_nonneg hε.le (hV m)
    linarith
  have hdrift' : ∀ x : S → ℕ,
      (N.jumpSystem κ).drift (linearObservable B.w) x ≤
        -ε * linearObservable B.w x + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (linearObservable B.w) x]
    exact hdrift x
  exact (N.jumpSystem κ).geometric_ergodic (linearObservable B.w) hV
    (balanceLyapunov_finiteSublevel B) hε hK hdrift' hstoch hirr

/-! ## 7. An instance -/

namespace Examples
namespace EndotacticBalancedTetramer

/-- The empty complex. -/
def zeroC : Fin 1 → ℕ := fun _ => 0

/-- The complex `X`. -/
def oneC : Fin 1 → ℕ := fun _ => 1

/-- The complex `2X`. -/
def twoC : Fin 1 → ℕ := fun _ => 2

/-- The one-species network `0 → X`, `X → 0`, `X → 2X`, `2X → X`: a birth channel, a death
channel, a dimerisation channel and a dissociation channel.  The ascending reaction `X → 2X` has
a *nonempty* source complex, and it is balanced by the descending reaction `X → 0`, which has the
*same* source complex; the descending top-tier reaction `2X → X` consumes the species `X`. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r.val = 0 then ⟨zeroC, oneC⟩ else if r.val = 1 then ⟨oneC, zeroC⟩
    else if r.val = 2 then ⟨oneC, twoC⟩ else ⟨twoC, oneC⟩⟩

/-- The tier potential of the source of the birth channel `0 → X`. -/
theorem wValue_zero (w : Fin 1 → ℝ) : net.wValue w 0 = 0 := by
  norm_num [Network.wValue, Network.dotProduct, exponentVector, zeroC]

/-- The tier potential of the source `X` of the death channel `X → 0`. -/
theorem wValue_one (w : Fin 1 → ℝ) : net.wValue w 1 = w 0 := by
  norm_num [Network.wValue, Network.dotProduct, exponentVector, oneC]

/-- The tier potential of the source `X` of the dimerisation channel `X → 2X`. -/
theorem wValue_two (w : Fin 1 → ℝ) : net.wValue w 2 = w 0 := by
  norm_num [Network.wValue, Network.dotProduct, exponentVector, oneC]

/-- The tier potential of the source `2X` of the dissociation channel `2X → X`: the top tier. -/
theorem wValue_three (w : Fin 1 → ℝ) : net.wValue w 3 = 2 * w 0 := by
  norm_num [Network.wValue, Network.dotProduct, exponentVector, twoC]
  ring

/-- The tier rate of the birth channel `0 → X`: it ascends the tier potential. -/
theorem wRate_zero (w : Fin 1 → ℝ) : net.wRate w 0 = w 0 := by
  norm_num [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC]

/-- The tier rate of the death channel `X → 0`: it descends the tier potential. -/
theorem wRate_one (w : Fin 1 → ℝ) : net.wRate w 1 = -w 0 := by
  norm_num [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC]

/-- The tier rate of the dimerisation channel `X → 2X`: it ascends the tier potential. -/
theorem wRate_two (w : Fin 1 → ℝ) : net.wRate w 2 = w 0 := by
  norm_num [Network.wRate, Network.dotProduct, Network.reactionVector_apply, oneC, twoC]

/-- The tier rate of the dissociation channel `2X → X`: it descends the tier potential. -/
theorem wRate_three (w : Fin 1 → ℝ) : net.wRate w 3 = -w 0 := by
  norm_num [Network.wRate, Network.dotProduct, Network.reactionVector_apply, oneC, twoC]

/-- **The instance is endotactic.** -/
theorem endotactic : net.Endotactic := by
  intro w r hmax
  fin_cases r
  · -- the source of `0 → X` is the empty complex
    have h1 := hmax 1
    have h3 := hmax 3
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, zeroC, oneC, twoC] at h1 h3 ⊢
    nlinarith
  · -- the source of `X → 0` is `X`
    have h0 := hmax 0
    have h3 := hmax 3
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, zeroC, oneC, twoC] at h0 h3 ⊢
    nlinarith
  · -- the source of `X → 2X` is `X`
    have h0 := hmax 0
    have h3 := hmax 3
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, zeroC, oneC, twoC] at h0 h3 ⊢
    nlinarith
  · -- the source of `2X → X` is `2X`
    have h0 := hmax 0
    have h1 := hmax 1
    simp [Network.wValue, Network.wRate, Network.dotProduct, Network.reactionVector_apply,
      exponentVector, zeroC, oneC, twoC] at h0 h1 ⊢
    nlinarith

/-- **The instance is strongly endotactic in the standard sense.** -/
theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨endotactic, ?_⟩
  intro w hactive
  by_cases hA : 0 < w 0
  · -- the top tier is `2X`
    refine ⟨3, ?_, ?_⟩
    · intro r'
      fin_cases r'
      · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, twoC] ;
          nlinarith [hA]
      · simp [Network.wValue, Network.dotProduct, exponentVector, oneC, twoC] ;
          nlinarith [hA]
      · simp [Network.wValue, Network.dotProduct, exponentVector, oneC, twoC] ;
          nlinarith [hA]
      · simp [Network.wValue, Network.dotProduct, exponentVector, twoC]
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC, twoC]
      nlinarith
  · by_cases hA' : w 0 < 0
    · -- the top tier is the empty complex
      refine ⟨0, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, oneC, twoC]
        · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, oneC, twoC]; nlinarith
        · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, oneC, twoC]; nlinarith
        · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, oneC, twoC]; nlinarith
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC, twoC]
        nlinarith
    · exfalso
      have hz : w 0 = 0 := le_antisymm (le_of_not_gt hA) (le_of_not_gt hA')
      obtain ⟨r, hr⟩ := hactive
      fin_cases r <;>
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, hz] at hr

/-- **The only ascending reaction with a nonempty source complex is `X → 2X`.** -/
theorem ascending_nonempty_source (r : net.R)
    (hr : 0 < net.wRate (fun _ => (1 : ℝ)) r)
    (hne : Network.ComplexNonempty (net.reaction r).source) : r = 2 := by
  have hcases : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hr0 : r = 0 := Fin.ext h0
    subst hr0
    have hne' : Network.ComplexNonempty (net.reaction 0).source := hne
    simp [Network.ComplexNonempty, zeroC] at hne'
  · have hr1 : r = 1 := Fin.ext h1
    subst hr1
    exfalso
    have hr' : net.wRate (fun _ => (1 : ℝ)) 1 ≤ 0 := by
      simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, oneC, zeroC]
    linarith
  · exact Fin.ext h2
  · have hr3 : r = 3 := Fin.ext h3
    subst hr3
    exfalso
    have hr' : net.wRate (fun _ => (1 : ℝ)) 3 ≤ 0 := by
      simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, twoC, oneC]
    linarith

/-- **The balanced count-lattice tier structure of the instance.**  The tier weight is the
total-count direction; the top tier is the complex `2X`, whose reaction `2X → X` descends
strictly; the ascending reaction `X → 2X` has the nonempty source complex `X` and is balanced by
the descending reaction `X → 0`, which has the *same* source complex; the species `X` is consumed
by the strictly descending top-tier reaction `2X → X`. -/
noncomputable def balance (κ : net.RateConstants) (hbal : κ.k 1 ≥ κ.k 2) :
    CountTierBalance net κ where
  w := fun _ => 1
  hw := by intro s; simp
  descent := countTierDescent_of_stronglyEndotacticStd stronglyEndotacticStd (by
    refine ⟨0, ?_⟩
    simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC])
  partner := fun _ => 1
  hpartner := by
    intro r hr hne
    have hr2 : r = 2 := ascending_nonempty_source r hr hne
    subst hr2
    refine ⟨?_, ?_, ?_⟩
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, oneC, zeroC]
    · simp [net, oneC, zeroC]
    · norm_num [Network.wRate, Network.dotProduct, Network.reactionVector_apply, zeroC, oneC, twoC]
      simpa using hbal
  hpartner_injective := by
    intro r₁ r₂ h₁ h₂ h₃ h₄ heq
    have hr1 : r₁ = 2 := ascending_nonempty_source r₁ h₁ h₂
    have hr2 : r₂ = 2 := ascending_nonempty_source r₂ h₃ h₄
    exact hr1.trans hr2.symm
  inward := fun _ => 3
  hinward := by
    intro s
    fin_cases s
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r'
      fin_cases r'
      · simp [Network.wValue, Network.dotProduct, exponentVector, zeroC, twoC]
      · simp [Network.wValue, Network.dotProduct, exponentVector, oneC, twoC]
      · simp [Network.wValue, Network.dotProduct, exponentVector, oneC, twoC]
      · simp [Network.wValue, Network.dotProduct, exponentVector, twoC]
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, oneC, twoC]
    · simp [net, twoC]
    · intro t ht
      fin_cases t
      simp at ht
  hinward_ne := by
    intro s t hst
    fin_cases s
    fin_cases t
    exact absurd rfl hst
  hinward_not_partner := by
    intro r s hr hne
    have hr2 : r = 2 := ascending_nonempty_source r hr hne
    subst hr2
    fin_cases s
    simp [net]

/-- **Reachability of the instance.**  The embedded jump chain of the instance is irreducible:
from any count one may reach any other count by firing the birth channel `0 → X` and the death
channel `X → 0`. -/
theorem reachPos (κ : net.RateConstants) (a b : Fin 1 → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  have ha : a = fun _ => a 0 := by funext s; fin_cases s; rfl
  have hb : b = fun _ => b 0 := by funext s; fin_cases s; rfl
  rw [ha, hb]
  have toZero : ∀ m : ℕ, (net.jumpSystem κ).ReachPos (fun _ => m) (fun _ => 0) := by
    intro m
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        have hen : net.Enabled (fun _ => m + 1) (1 : Fin 4) := by
          intro s; fin_cases s; simp [oneC]
        have hrate : 0 < (net.jumpSystem κ).rate (1 : Fin 4) (fun _ => m + 1) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (1 : Fin 4) (fun _ => m + 1) = (fun _ => m) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net, oneC, zeroC, twoC]
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(1 : Fin 4), hrate, hnext.symm⟩) ih
  have fromZero : ∀ n : ℕ, (net.jumpSystem κ).ReachPos (fun _ => 0) (fun _ => n) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        have hen : net.Enabled (fun _ => n) (0 : Fin 4) := by
          intro s; fin_cases s; simp [zeroC]
        have hrate : 0 < (net.jumpSystem κ).rate (0 : Fin 4) (fun _ => n) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (0 : Fin 4) (fun _ => n) = (fun _ => n + 1) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net, oneC, zeroC, twoC]
        exact Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(0 : Fin 4), hrate, hnext.symm⟩)
  exact Relation.ReflTransGen.trans (toZero (a 0)) (fromZero (b 0))

/-- **Non-explosion of the instance.** -/
theorem nonExplosion (κ : net.RateConstants) (hbal : κ.k 1 ≥ κ.k 2) {t : ℝ} (ht : 0 ≤ t)
    (n : Fin 1 → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 :=
  tierBalance_nonExplosion net κ (balance κ hbal) ht n

/-- **Positive recurrence of the instance.**  The stochastic mass-action chain of
`0 → X`, `X → 0`, `X → 2X`, `2X → X` is non-explosive and positively recurrent: it has a
stationary probability which charges every count, and the probability of being at the starting
count converges to a strictly positive limit. -/
theorem positiveRecurrence (κ : net.RateConstants) (hbal : κ.k 1 ≥ κ.k 2) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : Fin 1 → ℕ, Tendsto (fun t => net.transition κ t a a) atTop (𝓝 (π a))) :=
  tierBalance_positiveRecurrence net κ (balance κ hbal) (fun a b => reachPos κ a b)

/-- **Geometric ergodicity of the instance.** -/
theorem geometricErgodic (κ : net.RateConstants) (hbal : κ.k 1 ≥ κ.k 2) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(net.jumpSystem κ).Pmin t a b - π b| *
            (1 + β * linearObservable (fun _ => 1) b) ≤
          C₀ * (1 + linearObservable (fun _ => 1) a) * ρ ^ ⌊t⌋₊ :=
  tierBalance_geometricErgodic net κ (balance κ hbal) (fun a b => reachPos κ a b)

end EndotacticBalancedTetramer
end Examples

end Network

end CRNT
