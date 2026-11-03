import CRNT.Stochastic.MinimalSemigroupExpect
import CRNT.Stochastic.ProductFormErgodic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Algebra.Order.Chebyshev
import CRNT.Multistationarity.InheritanceAddReactions

/-!
# Kurtz's law of large numbers for conservative networks (fixed times)

Volume-scaled rate constants `κ_r V^{1 − |y_r|}` (`volumeScale`) give the density-dependent
propensities `V ρ_r(c)`, `ρ_r(c) = κ_r ∏_s (c_s)_{(y_s)} / V^{y_s}` (`stochasticRate_volumeScale`),
which differ from the mass-action rate at `c/V` by `O(1/V)` on bounded sets
(`abs_descFactorial_div_pow_sub`). For a conservative network (a positive linear conservation law)
the chain stays in the finite class of its initial count, and the mean squared distance
`D(t) = E_n |X^V(t)/V − x(t)|²` to a solution `x` of the mass-action equation satisfies
`D' ≤ C₁ D + C₂/V`; hence `D(t) ≤ gronwallBound D(0) C₁ (C₂/V) t` with constants independent of
`V` and of the initial count (`conservative_lln`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace CRNT

/-- **Telescoping bound for products.** -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) {M : ℝ}
    (hM : 1 ≤ M) (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ M ^ s.card * ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      have ha' : ∀ i ∈ s, |a i| ≤ M := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hb' : ∀ i ∈ s, |b i| ≤ M := fun i hi => hb i (Finset.mem_insert_of_mem hi)
      have hpb : |∏ i ∈ s, b i| ≤ M ^ s.card := by
        rw [Finset.abs_prod]
        calc ∏ i ∈ s, |b i| ≤ ∏ _i ∈ s, M :=
              Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hb'
          _ = M ^ s.card := Finset.prod_const _
      have h := ih ha' hb'
      have haj := ha j (Finset.mem_insert_self _ _)
      have hM0 : 0 ≤ M := by linarith
      have hMs : M ^ s.card ≤ M ^ (s.card + 1) := pow_le_pow_right₀ hM (by omega)
      have hsum0 : 0 ≤ ∑ i ∈ s, |a i - b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj,
        Finset.sum_insert hj]
      calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
          = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
        _ ≤ |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ M * (M ^ s.card * ∑ i ∈ s, |a i - b i|) + |a j - b j| * M ^ s.card :=
            add_le_add (mul_le_mul haj h (abs_nonneg _) hM0)
              (mul_le_mul_of_nonneg_left hpb (abs_nonneg _))
        _ ≤ M ^ (s.card + 1) * (|a j - b j| + ∑ i ∈ s, |a i - b i|) := by
            have h3 : |a j - b j| * M ^ s.card ≤ |a j - b j| * M ^ (s.card + 1) :=
              mul_le_mul_of_nonneg_left hMs (abs_nonneg _)
            have h4 : M * (M ^ s.card * ∑ i ∈ s, |a i - b i|) =
                M ^ (s.card + 1) * ∑ i ∈ s, |a i - b i| := by rw [pow_succ]; ring
            rw [h4, mul_add]; linarith

theorem cast_descFactorial_eq_prod (c k : ℕ) :
    (c.descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((c : ℝ) - i) := by
  rcases Nat.lt_or_ge c k with hck | hkc
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hck, Nat.cast_zero]
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr hck) (sub_self _)).symm
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]

/-- **Falling factorials against powers.** -/
theorem abs_descFactorial_div_pow_sub (c k : ℕ) {V R : ℝ} (hV : 1 ≤ V) (hR : 0 ≤ R)
    (hc : (c : ℝ) ≤ R * V) :
    |(c.descFactorial k : ℝ) / V ^ k - ((c : ℝ) / V) ^ k| ≤ (R + k + 1) ^ k * (k ^ 2 / V) := by
  have hV0 : 0 < V := by linarith
  have hcV : (c : ℝ) / V ≤ R := by rw [div_le_iff₀ hV0]; linarith
  have hc0 : 0 ≤ (c : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
  have e1 : (c.descFactorial k : ℝ) / V ^ k = ∏ i ∈ Finset.range k, (((c : ℝ) - i) / V) := by
    rw [cast_descFactorial_eq_prod, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_range]
  have e2 : ((c : ℝ) / V) ^ k = ∏ _i ∈ Finset.range k, ((c : ℝ) / V) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [e1, e2]
  have hM : 1 ≤ R + k + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have h := abs_prod_sub_prod_le (Finset.range k) (fun i => ((c : ℝ) - i) / V)
    (fun _ => (c : ℝ) / V) hM (fun i hi => ?_) (fun i _ => ?_)
  · rw [Finset.card_range] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc ∑ i ∈ Finset.range k, |((c : ℝ) - i) / V - (c : ℝ) / V|
        = ∑ i ∈ Finset.range k, (i : ℝ) / V := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← sub_div, sub_sub_cancel_left, abs_div, abs_neg, abs_of_pos hV0,
            abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ ∑ _i ∈ Finset.range k, (k : ℝ) / V := by
          refine Finset.sum_le_sum fun i hi => div_le_div_of_nonneg_right ?_ hV0.le
          exact_mod_cast (Finset.mem_range.mp hi).le
      _ = (k : ℝ) ^ 2 / V := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  · have hi' : (i : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hi).le
    have hiV : (i : ℝ) / V ≤ k := by
      rw [div_le_iff₀ hV0]; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    rw [sub_div, abs_le]
    have : (0 : ℝ) ≤ i / V := div_nonneg (Nat.cast_nonneg _) hV0.le
    constructor <;> linarith
  · rw [abs_of_nonneg hc0]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Forward equation on a finite closed class**, for a time-dependent observable. -/
theorem hasDerivAt_sum_finite (a : α) (R : Finset α)
    (hsupp : ∀ τ, ∀ b, b ∉ R → J.Pmin τ a b = 0)
    (hclosed : ∀ c ∈ R, ∀ i, 0 < J.rate i c → J.next i c ∈ R)
    (g g' : ℝ → α → ℝ) {t : ℝ} (ht : 0 < t) (hg : ∀ b ∈ R, HasDerivAt (fun τ => g τ b) (g' t b) t) :
    HasDerivAt (fun τ => ∑ b ∈ R, J.Pmin τ a b * g τ b)
      (∑ c ∈ R, J.Pmin t a c * (J.drift (g t) c + g' t c)) t := by
  have hsum : Summable fun c => J.Pmin t a c * J.q c :=
    summable_of_ne_finset_zero (s := R) fun c hc => by rw [hsupp t c hc, zero_mul]
  have hterm : ∀ b ∈ R, HasDerivAt (fun τ => J.Pmin τ a b * g τ b)
      ((∑' c, J.Pmin t a c * J.Q c b) * g t b + J.Pmin t a b * g' t b) t := fun b hb =>
    (J.hasDerivAt_Pmin_forward ht a b hsum).mul (hg b hb)
  have hmain := HasDerivAt.fun_sum (u := R) (A := fun b τ => J.Pmin τ a b * g τ b)
    (A' := fun b => (∑' c, J.Pmin t a c * J.Q c b) * g t b + J.Pmin t a b * g' t b) hterm
  convert hmain using 1
  -- identify the derivative
  have hQ : ∀ c ∈ R, ∑ b ∈ R, J.Q c b * g t b = J.drift (g t) c := by
    intro c hc
    rw [← J.tsum_Q_mul (g t) c]
    refine (tsum_eq_sum fun b hb => ?_).symm
    have hcb : c ≠ b := fun h => hb (h ▸ hc)
    have : J.Q c b = 0 := by
      unfold Q
      rw [if_neg hcb, mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : J.next i c = b
      · rw [if_pos hi, mul_one]
        by_contra hne
        exact hb (hi ▸ hclosed c hc i (lt_of_le_of_ne (J.rate_nonneg i c) (Ne.symm hne)))
      · rw [if_neg hi, mul_zero]
    rw [this, zero_mul]
  have htsum : ∀ b, ∑' c, J.Pmin t a c * J.Q c b = ∑ c ∈ R, J.Pmin t a c * J.Q c b := fun b =>
    tsum_eq_sum fun c hc => by rw [hsupp t c hc, zero_mul]
  have e1 : ∑ b ∈ R, ((∑' c, J.Pmin t a c * J.Q c b) * g t b + J.Pmin t a b * g' t b) =
      ∑ b ∈ R, ∑ c ∈ R, J.Pmin t a c * J.Q c b * g t b + ∑ b ∈ R, J.Pmin t a b * g' t b := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [htsum, Finset.sum_mul]
  have e2 : ∑ b ∈ R, ∑ c ∈ R, J.Pmin t a c * J.Q c b * g t b =
      ∑ c ∈ R, J.Pmin t a c * J.drift (g t) c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← hQ c hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The molecularity of a source. -/
def srcMol (N : Network S) (r : N.R) : ℕ := ∑ s, (N.reaction r).source s

/-- **Volume-scaled rate constants** `κ_r V^{1 − |y_r|}`. -/
noncomputable def volumeScale (N : Network S) (κ : RateConstants N) (V : ℝ) (hV : 0 < V) :
    RateConstants N :=
  ⟨fun r => κ.k r * V ^ ((1 : ℤ) - (N.srcMol r : ℤ)),
    fun r => mul_pos (κ.positive r) (zpow_pos hV _)⟩

/-- The density-dependent rate `ρ_r(c) = κ_r ∏_s (c_s)_{(y_s)} / V^{y_s}`. -/
noncomputable def densRate (N : Network S) (κ : RateConstants N) (V : ℝ) (r : N.R) (c : S → ℕ) :
    ℝ :=
  κ.k r * ∏ s, ((c s).descFactorial ((N.reaction r).source s) : ℝ) / V ^ ((N.reaction r).source s)

theorem stochasticRate_volumeScale (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (c : S → ℕ) (r : N.R) :
    N.stochasticMassActionRate (N.volumeScale κ V hV) c r = V * N.densRate κ V r c := by
  unfold stochasticMassActionRate densRate volumeScale srcMol
  simp only
  rw [zpow_sub₀ hV.ne', zpow_one, zpow_natCast, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_div_distrib]
  field_simp

theorem densRate_nonneg (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V) (r : N.R)
    (c : S → ℕ) : 0 ≤ N.densRate κ V r c :=
  mul_nonneg (κ.positive r).le (Finset.prod_nonneg fun s _ => by positivity)

theorem densRate_factor_bounds (N : Network S) (r : N.R) {V R : ℝ} (hV : 1 ≤ V) (hR : 0 ≤ R)
    (c : S → ℕ) (hc : ∀ s, (c s : ℝ) ≤ R * V) (s : S) :
    0 ≤ ((c s).descFactorial ((N.reaction r).source s) : ℝ) / V ^ ((N.reaction r).source s) ∧
      ((c s).descFactorial ((N.reaction r).source s) : ℝ) / V ^ ((N.reaction r).source s) ≤
        ((c s : ℝ) / V) ^ ((N.reaction r).source s) ∧
      ((c s : ℝ) / V) ^ ((N.reaction r).source s) ≤ (R + N.srcMol r + 1) ^ N.srcMol r := by
  have hV0 : 0 < V := by linarith
  set y := (N.reaction r).source s
  have hy : y ≤ N.srcMol r := Finset.single_le_sum (f := fun s => (N.reaction r).source s)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have hcV : (c s : ℝ) / V ≤ R := by rw [div_le_iff₀ hV0]; linarith [hc s]
  have hc0 : 0 ≤ (c s : ℝ) / V := div_nonneg (Nat.cast_nonneg _) hV0.le
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Nat.descFactorial_le_pow (c s) y
  · have hY : (1 : ℝ) ≤ R + N.srcMol r + 1 := by
      have : (0 : ℝ) ≤ N.srcMol r := Nat.cast_nonneg _; linarith
    calc ((c s : ℝ) / V) ^ y ≤ (R + N.srcMol r + 1) ^ y :=
          pow_le_pow_left₀ hc0 (by have : (0 : ℝ) ≤ N.srcMol r := Nat.cast_nonneg _; linarith) y
      _ ≤ (R + N.srcMol r + 1) ^ N.srcMol r := pow_le_pow_right₀ hY hy

/-- The density-dependent rate is bounded on `{c/V ≤ R}`. -/
theorem densRate_le (N : Network S) (κ : RateConstants N) (r : N.R) {V R : ℝ} (hV : 1 ≤ V)
    (hR : 0 ≤ R) (c : S → ℕ) (hc : ∀ s, (c s : ℝ) ≤ R * V) :
    N.densRate κ V r c ≤ κ.k r * ((R + N.srcMol r + 1) ^ N.srcMol r) ^ Fintype.card S := by
  unfold densRate
  refine mul_le_mul_of_nonneg_left ?_ (κ.positive r).le
  calc ∏ s, ((c s).descFactorial ((N.reaction r).source s) : ℝ) / V ^ ((N.reaction r).source s)
      ≤ ∏ _s : S, (R + N.srcMol r + 1) ^ N.srcMol r :=
        Finset.prod_le_prod₀ (fun s _ => (densRate_factor_bounds N r hV hR c hc s).1) fun s _ =>
          (densRate_factor_bounds N r hV hR c hc s).2.1.trans
            (densRate_factor_bounds N r hV hR c hc s).2.2
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- **The density-dependent rate is the mass-action rate at `c/V` up to `O(1/V)`.** -/
theorem abs_densRate_sub (N : Network S) (κ : RateConstants N) (r : N.R) {V R : ℝ} (hV : 1 ≤ V)
    (hR : 0 ≤ R) (c : S → ℕ) (hc : ∀ s, (c s : ℝ) ≤ R * V) :
    |N.densRate κ V r c - N.massActionRate κ r (fun s => (c s : ℝ) / V)| ≤
      κ.k r * (((R + N.srcMol r + 1) ^ N.srcMol r) ^ (Fintype.card S + 1) *
        (Fintype.card S * (N.srcMol r : ℝ) ^ 2)) / V := by
  have hV0 : 0 < V := by linarith
  set M := (R + N.srcMol r + 1) ^ N.srcMol r with hMdef
  have hY : (1 : ℝ) ≤ R + N.srcMol r + 1 := by
    have : (0 : ℝ) ≤ N.srcMol r := Nat.cast_nonneg _; linarith
  have hM : 1 ≤ M := one_le_pow₀ hY
  set a : S → ℝ := fun s =>
    ((c s).descFactorial ((N.reaction r).source s) : ℝ) / V ^ ((N.reaction r).source s)
  set b : S → ℝ := fun s => ((c s : ℝ) / V) ^ ((N.reaction r).source s)
  have hab := densRate_factor_bounds N r hV hR c hc
  have hdiff : N.densRate κ V r c - N.massActionRate κ r (fun s => (c s : ℝ) / V) =
      κ.k r * (∏ s, a s - ∏ s, b s) := by
    unfold densRate massActionRate Complex.massActionMonomial; ring
  have hA := abs_prod_sub_prod_le Finset.univ a b hM
    (fun s _ => by rw [abs_of_nonneg (hab s).1]; exact (hab s).2.1.trans (hab s).2.2)
    (fun s _ => by rw [abs_of_nonneg (by positivity)]; exact (hab s).2.2)
  rw [Finset.card_univ] at hA
  have hterm : ∀ s, |a s - b s| ≤ M * ((N.srcMol r : ℝ) ^ 2 / V) := by
    intro s
    have hy : (N.reaction r).source s ≤ N.srcMol r :=
      Finset.single_le_sum (f := fun s => (N.reaction r).source s) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s)
    have h1 := abs_descFactorial_div_pow_sub (c s) ((N.reaction r).source s) hV hR (hc s)
    have hyR : (((N.reaction r).source s : ℕ) : ℝ) ≤ N.srcMol r := by exact_mod_cast hy
    have h2 : (R + ((N.reaction r).source s : ℕ) + 1) ^ ((N.reaction r).source s) ≤ M :=
      (pow_le_pow_left₀ (by positivity) (by linarith) _).trans (pow_le_pow_right₀ hY hy)
    have h3 : (((N.reaction r).source s : ℕ) : ℝ) ^ 2 / V ≤ (N.srcMol r : ℝ) ^ 2 / V :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hyR 2) hV0.le
    exact h1.trans (mul_le_mul h2 h3 (by positivity) (by positivity))
  have hsum : ∑ s, |a s - b s| ≤ Fintype.card S * (M * ((N.srcMol r : ℝ) ^ 2 / V)) := by
    calc ∑ s, |a s - b s| ≤ ∑ _s : S, M * ((N.srcMol r : ℝ) ^ 2 / V) :=
          Finset.sum_le_sum fun s _ => hterm s
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdiff, abs_mul, abs_of_pos (κ.positive r)]
  have hM0 : 0 ≤ M ^ Fintype.card S := by positivity
  calc κ.k r * |∏ s, a s - ∏ s, b s|
      ≤ κ.k r * (M ^ Fintype.card S * (Fintype.card S * (M * ((N.srcMol r : ℝ) ^ 2 / V)))) :=
        mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hsum hM0))
          (κ.positive r).le
    _ = _ := by rw [pow_succ]; field_simp; ring

theorem densRate_eq_zero_of_not_enabled (N : Network S) (κ : RateConstants N) (V : ℝ) {c : S → ℕ}
    {r : N.R} (h : ¬ N.Enabled c r) : N.densRate κ V r c = 0 := by
  unfold Enabled at h
  push Not at h
  obtain ⟨s, hs⟩ := h
  unfold densRate
  rw [Finset.prod_eq_zero (Finset.mem_univ s) (by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hs, Nat.cast_zero, zero_div]), mul_zero]

/-- The constant of the `O(1/V)` rate error. -/
noncomputable def rateErr (N : Network S) (κ : RateConstants N) (R : ℝ) : ℝ :=
  ∑ r, κ.k r * (((R + N.srcMol r + 1) ^ N.srcMol r) ^ (Fintype.card S + 1) *
    (Fintype.card S * (N.srcMol r : ℝ) ^ 2)) * ‖N.reactionVector r‖

/-- The constant of the noise term. -/
noncomputable def noiseConst (N : Network S) (κ : RateConstants N) (R : ℝ) : ℝ :=
  ∑ r, κ.k r * ((R + N.srcMol r + 1) ^ N.srcMol r) ^ Fintype.card S *
    ∑ s, N.reactionVector r s ^ 2

/-- **The pointwise drift bound** for `g(c) = |c/V − z|²` along the mass-action field. -/
theorem drift_dist_sq_le (N : Network S) (κ : RateConstants N) {V R Rb : ℝ} (hV : 1 ≤ V)
    (hR : 0 ≤ R) (hRb : R ≤ Rb) {L : ℝ≥0}
    (hL : LipschitzOnWith L (N.massActionVectorField κ) (Icc 0 fun _ => Rb))
    (c : S → ℕ) (hc : ∀ s, (c s : ℝ) ≤ R * V) (z : Concentration S)
    (hz : z ∈ Icc (0 : Concentration S) fun _ => Rb) :
    (N.jumpSystem (N.volumeScale κ V (by linarith))).drift
        (fun b => ∑ s, ((b s : ℝ) / V - z s) ^ 2) c +
      ∑ s, 2 * ((c s : ℝ) / V - z s) * -(N.massActionVectorField κ z s) ≤
    (1 + 2 * Fintype.card S * L) * ∑ s, ((c s : ℝ) / V - z s) ^ 2 +
      (Fintype.card S * N.rateErr κ R ^ 2 + N.noiseConst κ R) / V := by
  have hV0 : 0 < V := by linarith
  set d := (Fintype.card S : ℝ) with hd
  set e : S → ℝ := fun s => (c s : ℝ) / V - z s with he
  set g := ∑ s, e s ^ 2 with hg
  set ρ : N.R → ℝ := fun r => N.densRate κ V r c with hρ
  set u : Concentration S := fun s => (c s : ℝ) / V with hu
  -- the drift
  have hdrift : (N.jumpSystem (N.volumeScale κ V hV0)).drift
      (fun b => ∑ s, ((b s : ℝ) / V - z s) ^ 2) c =
        ∑ r, ρ r * ∑ s, (2 * e s * N.reactionVector r s + N.reactionVector r s ^ 2 / V) := by
    show ∑ r : N.R, N.stochasticMassActionRate (N.volumeScale κ V hV0) c r *
      (∑ s, ((N.jumpNextCount c r s : ℝ) / V - z s) ^ 2 - ∑ s, ((c s : ℝ) / V - z s) ^ 2) = _
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [stochasticRate_volumeScale N κ hV0]
    by_cases hen : N.Enabled c r
    · have hnext : ∀ s, (N.jumpNextCount c r s : ℝ) = c s + N.reactionVector r s := by
        intro s
        unfold jumpNextCount
        rw [Nat.cast_add, Nat.cast_sub (hen s), reactionVector_apply]; ring
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hnext s]
      simp only [he, hρ]
      field_simp
      ring
    · simp only [hρ, densRate_eq_zero_of_not_enabled N κ V hen, mul_zero, zero_mul]
  -- the noise term
  have hnoise : ∑ r, ρ r * ∑ s, N.reactionVector r s ^ 2 / V ≤ N.noiseConst κ R / V := by
    rw [noiseConst, Finset.sum_div]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [← Finset.sum_div, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hV0.le
    exact mul_le_mul_of_nonneg_right (densRate_le N κ r hV hR c hc)
      (Finset.sum_nonneg fun s _ => sq_nonneg _)
  -- `G_s = ∑_r ρ_r v_rs`
  set G : S → ℝ := fun s => ∑ r, ρ r * N.reactionVector r s with hG
  have hsplit : ∑ r, ρ r * ∑ s, (2 * e s * N.reactionVector r s + N.reactionVector r s ^ 2 / V) =
      ∑ s, 2 * e s * G s + ∑ r, ρ r * ∑ s, N.reactionVector r s ^ 2 / V := by
    simp only [hG, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => by ring
  -- the rate error
  have hGerr : ∀ s, |G s - N.massActionVectorField κ u s| ≤ N.rateErr κ R / V := by
    intro s
    simp only [hG, massActionVectorField_apply, ← Finset.sum_sub_distrib, ← sub_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [rateErr, Finset.sum_div]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [abs_mul]
    have h1 := abs_densRate_sub N κ r hV hR c hc
    have h2 : |N.reactionVector r s| ≤ ‖N.reactionVector r‖ := by
      have := norm_le_pi_norm (N.reactionVector r) s; rwa [Real.norm_eq_abs] at this
    calc |ρ r - N.massActionRate κ r u| * |N.reactionVector r s|
        ≤ (κ.k r * (((R + N.srcMol r + 1) ^ N.srcMol r) ^ (Fintype.card S + 1) *
            (Fintype.card S * (N.srcMol r : ℝ) ^ 2)) / V) * ‖N.reactionVector r‖ :=
          mul_le_mul h1 h2 (abs_nonneg _) (div_nonneg (mul_nonneg (κ.positive r).le
            (by positivity)) hV0.le)
      _ = _ := by ring
  -- the Lipschitz part
  have hu : u ∈ Icc (0 : Concentration S) fun _ => Rb := by
    refine ⟨fun s => div_nonneg (Nat.cast_nonneg _) hV0.le, fun s => ?_⟩
    show (c s : ℝ) / V ≤ Rb
    rw [div_le_iff₀ hV0]; nlinarith [hc s]
  have hnorm : ‖u - z‖ ≤ ∑ j, |e j| :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).mpr fun j => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun j => |e j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
  have hFlip : ∀ s, |N.massActionVectorField κ u s - N.massActionVectorField κ z s| ≤
      L * ∑ j, |e j| := by
    intro s
    have h1 := hL.dist_le_mul u hu z hz
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 := norm_le_pi_norm (N.massActionVectorField κ u - N.massActionVectorField κ z) s
    rw [Real.norm_eq_abs, Pi.sub_apply] at h2
    exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left hnorm L.2))
  -- combine
  have hmain : ∑ s, 2 * e s * G s + ∑ s, 2 * e s * -(N.massActionVectorField κ z s) ≤
      g + d * (N.rateErr κ R) ^ 2 / V + 2 * d * L * g := by
    have hcomb : ∑ s, 2 * e s * G s + ∑ s, 2 * e s * -(N.massActionVectorField κ z s) =
        ∑ s, 2 * e s * (G s - N.massActionVectorField κ u s) +
          ∑ s, 2 * e s * (N.massActionVectorField κ u s - N.massActionVectorField κ z s) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hcomb]
    set A := N.rateErr κ R with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun r _ => mul_nonneg (mul_nonneg (κ.positive r).le
      (by positivity)) (norm_nonneg _)
    have h1 : ∑ s, 2 * e s * (G s - N.massActionVectorField κ u s) ≤ g + d * A ^ 2 / V := by
      have hpt : ∀ s, 2 * e s * (G s - N.massActionVectorField κ u s) ≤ e s ^ 2 + A ^ 2 / V := by
        intro s
        have hb := hGerr s
        have hAV : A / V ≤ A := div_le_self hA0 hV
        have habs : 2 * e s * (G s - N.massActionVectorField κ u s) ≤ 2 * |e s| * (A / V) := by
          calc 2 * e s * (G s - N.massActionVectorField κ u s)
              ≤ |2 * e s * (G s - N.massActionVectorField κ u s)| := le_abs_self _
            _ = 2 * |e s| * |G s - N.massActionVectorField κ u s| := by
                rw [abs_mul, abs_mul, abs_two]
            _ ≤ 2 * |e s| * (A / V) := mul_le_mul_of_nonneg_left hb (by positivity)
        have hsq : 2 * |e s| * (A / V) ≤ e s ^ 2 + (A / V) ^ 2 := by
          nlinarith [sq_nonneg (|e s| - A / V), sq_abs (e s)]
        have hAV2 : (A / V) ^ 2 ≤ A ^ 2 / V := by
          rw [div_pow, div_le_div_iff₀ (by positivity) hV0]
          have : 0 ≤ A ^ 2 * (V ^ 2 - V) := mul_nonneg (sq_nonneg A) (by nlinarith)
          nlinarith
        linarith
      calc _ ≤ ∑ s, (e s ^ 2 + A ^ 2 / V) := Finset.sum_le_sum fun s _ => hpt s
        _ = g + d * A ^ 2 / V := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have h2 : ∑ s, 2 * e s * (N.massActionVectorField κ u s - N.massActionVectorField κ z s) ≤
        2 * d * L * g := by
      have hpt : ∀ s, 2 * e s * (N.massActionVectorField κ u s - N.massActionVectorField κ z s) ≤
          2 * |e s| * (L * ∑ j, |e j|) := by
        intro s
        calc _ ≤ |2 * e s * (N.massActionVectorField κ u s - N.massActionVectorField κ z s)| :=
              le_abs_self _
          _ = 2 * |e s| * |N.massActionVectorField κ u s - N.massActionVectorField κ z s| := by
              rw [abs_mul, abs_mul, abs_two]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hFlip s) (by positivity)
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |e j|)
      simp only [Finset.card_univ, sq_abs] at hcs
      calc _ ≤ ∑ s, 2 * |e s| * (L * ∑ j, |e j|) := Finset.sum_le_sum fun s _ => hpt s
        _ = 2 * L * (∑ j, |e j|) ^ 2 := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
        _ ≤ 2 * L * (d * g) := mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = 2 * d * L * g := by ring
    linarith
  rw [hdrift, hsplit]
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  calc ∑ s, 2 * e s * G s + ∑ r, ρ r * ∑ s, N.reactionVector r s ^ 2 / V +
        ∑ s, 2 * e s * -(N.massActionVectorField κ z s)
      ≤ g + d * N.rateErr κ R ^ 2 / V + 2 * d * L * g + N.noiseConst κ R / V := by linarith
    _ = (1 + 2 * d * L) * g + (d * N.rateErr κ R ^ 2 + N.noiseConst κ R) / V := by ring

/-- Conservation of a P-invariant along reachable counts. -/
theorem weight_of_reachPos (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : N.IsPInvariant w) {n c : S → ℕ} (h : (N.jumpSystem κ).ReachPos n c) :
    ∑ s, w s * (c s : ℝ) = ∑ s, w s * (n s : ℝ) := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      obtain ⟨r, hr, rfl⟩ := hxy
      exact (N.weight_jumpNextCount κ hw hr).trans ih

/-- **Kurtz's law of large numbers for conservative networks, at fixed times.** For a network with
a positive linear conservation law `w`, volume-scaled rate constants `κ_r V^{1 − |y_r|}`, and a
solution `x` of the mass-action equation on `[0, T]` with values in `[0, R_x]^S`, there are
constants `C₁, C₂ ≥ 0` such that for every `V ≥ 1`, every initial count `n` with `w · n ≤ M V`,
and every `t ∈ [0, T]`,

`E_n |X^V(t)/V − x(t)|² ≤ gronwallBound (|n/V − x(0)|²) C₁ (C₂/V) t`. -/
theorem conservative_lln (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (V : ℝ) (hV : 1 ≤ V) (n : S → ℕ),
      ∑ s, w s * (n s : ℝ) ≤ M * V → ∀ t ∈ Icc 0 T,
        ∑' m, N.transition (N.volumeScale κ V (by linarith)) t n m *
            ∑ s, ((m s : ℝ) / V - x t s) ^ 2 ≤
          gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) t := by
  classical
  set R := ∑ s, M / w s with hRdef
  have hR : 0 ≤ R := Finset.sum_nonneg fun s _ => div_nonneg hM (hwpos s).le
  set Rb := max R Rx with hRb
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn
    (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  set C₁ := 1 + 2 * (Fintype.card S : ℝ) * L with hC₁
  set C₂ := (Fintype.card S : ℝ) * N.rateErr κ R ^ 2 + N.noiseConst κ R with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => mul_nonneg
      (mul_nonneg (κ.positive r).le (by positivity)) (Finset.sum_nonneg fun s _ => sq_nonneg _))
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun V hV n hn t ht => ?_⟩
  have hV0 : 0 < V := by linarith
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  have hcons : N.IsConservative := ⟨w, hwinv, hwpos⟩
  set Rset := N.reachClass κV hcons n with hRset
  have hsupp : ∀ τ, ∀ b, b ∉ Rset → J.Pmin τ n b = 0 := fun τ b hb =>
    J.Pmin_eq_zero_of_not_reachPos τ fun h => hb ((N.mem_reachClass κV hcons).mpr h)
  have hclosed : ∀ c ∈ Rset, ∀ i, 0 < J.rate i c → J.next i c ∈ Rset := by
    intro c hc i hi
    rw [N.mem_reachClass κV hcons] at hc ⊢
    exact hc.tail ⟨i, hi, rfl⟩
  have hnR : n ∈ Rset := (N.mem_reachClass κV hcons).mpr Relation.ReflTransGen.refl
  have hcR : ∀ c ∈ Rset, ∀ s, (c s : ℝ) ≤ R * V := by
    intro c hc s
    have hw := N.weight_of_reachPos κV hwinv ((N.mem_reachClass κV hcons).mp hc)
    have h1 : w s * (c s : ℝ) ≤ M * V := by
      rw [← hw] at hn
      refine le_trans ?_ hn
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ M / w s * V := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (hwpos s)]; linarith
    have h3 : M / w s ≤ R := Finset.single_le_sum (f := fun s => M / w s)
      (fun s _ => div_nonneg hM (hwpos s).le) (Finset.mem_univ s)
    exact h2.trans (mul_le_mul_of_nonneg_right h3 hV0.le)
  -- the observable and the mean squared distance
  set g : ℝ → (S → ℕ) → ℝ := fun τ b => ∑ s, ((b s : ℝ) / V - x τ s) ^ 2 with hg
  set g' : ℝ → (S → ℕ) → ℝ := fun τ b =>
    ∑ s, 2 * ((b s : ℝ) / V - x τ s) * -(N.massActionVectorField κ (x τ) s) with hg'
  set D : ℝ → ℝ := fun τ => ∑ b ∈ Rset, J.Pmin τ n b * g τ b with hD
  have hDeq : ∀ τ, ∑' m, N.transition κV τ n m * g τ m = D τ := fun τ =>
    tsum_eq_sum fun b hb => by
      show J.Pmin τ n b * g τ b = 0
      rw [hsupp τ b hb, zero_mul]
  -- derivative and differential inequality
  have hgder : ∀ τ ∈ Ioo 0 T, ∀ b, HasDerivAt (fun τ => g τ b) (g' τ b) τ := by
    intro τ hτ b
    have hxτ := hasDerivAt_pi.mp (hx τ hτ)
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun τ => (b s : ℝ) / V - x τ s) (-(N.massActionVectorField κ (x τ) s))
        τ := by simpa using (hxτ s).const_sub ((b s : ℝ) / V)
    convert h1.pow 2 using 1
    push_cast; ring
  have hDder : ∀ τ ∈ Ioo 0 T, HasDerivAt D
      (∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c)) τ := fun τ hτ =>
    J.hasDerivAt_sum_finite n Rset hsupp hclosed g g' hτ.1 fun b _ => hgder τ hτ b
  have hbound : ∀ τ ∈ Ioo 0 T,
      ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c) ≤ C₁ * D τ + C₂ / V := by
    intro τ hτ
    have hxτB : x τ ∈ Icc (0 : Concentration S) fun _ => Rb := by
      obtain ⟨h1, h2⟩ := hxB τ (Ioo_subset_Icc_self hτ)
      exact ⟨h1, fun s => (h2 s).trans (le_max_right _ _)⟩
    have hpt : ∀ c ∈ Rset, J.drift (g τ) c + g' τ c ≤ C₁ * g τ c + C₂ / V := fun c hc =>
      N.drift_dist_sq_le κ hV hR (le_max_left _ _) hL c (hcR c hc) (x τ) hxτB
    calc ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c)
        ≤ ∑ c ∈ Rset, J.Pmin τ n c * (C₁ * g τ c + C₂ / V) :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hpt c hc)
            (J.Pmin_nonneg τ hτ.1.le n c)
      _ = C₁ * D τ + C₂ / V * ∑ c ∈ Rset, J.Pmin τ n c := by
          simp only [hD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ C₁ * D τ + C₂ / V := by
          have h1 := J.sum_Pmin_le_one τ hτ.1.le n Rset
          have h2 : 0 ≤ C₂ / V := div_nonneg hC₂0 hV0.le
          nlinarith
  -- continuity
  have hDc : ContinuousOn D (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ((J.continuousOn_Pmin n b).mono fun τ hτ => hτ.1).mul ?_
    refine continuousOn_finsetSum _ fun s _ => ?_
    exact (continuousOn_const.sub ((continuous_apply s).comp_continuousOn hxc)).pow 2
  have hD0 : D 0 = g 0 n := by
    simp only [hD, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun h => absurd hnR h)]
    simp
  rw [hDeq]
  rcases ht.1.eq_or_lt with h0 | htpos
  · subst h0; rw [hD0, gronwallBound_x0]
  · -- Grönwall on `[ε, t]`, then `ε → 0⁺`
    have hT : 0 < T := lt_of_lt_of_le htpos ht.2
    have hgron : ∀ ε ∈ Ioo (0 : ℝ) t, D t ≤ gronwallBound (D ε) C₁ (C₂ / V) (t - ε) := by
      intro ε hε
      have hsub : Icc ε t ⊆ Icc 0 T := Icc_subset_Icc hε.1.le ht.2
      have h := le_gronwallBound_of_liminf_deriv_right_le (f := D)
        (f' := fun τ => ∑ c ∈ Rset, J.Pmin τ n c * (J.drift (g τ) c + g' τ c))
        (δ := D ε) (K := C₁) (ε := C₂ / V) (a := ε) (b := t) (hDc.mono hsub)
        (fun τ hτ r hr => ((hDder τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩
          ).hasDerivWithinAt).liminf_right_slope_le hr) le_rfl
        (fun τ hτ => hbound τ ⟨lt_of_lt_of_le hε.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩)
      exact h t ⟨hε.2.le, le_rfl⟩
    have hC₁ne : C₁ ≠ 0 := by positivity
    have hcont : Tendsto (fun ε => gronwallBound (D ε) C₁ (C₂ / V) (t - ε)) (𝓝[>] 0)
        (𝓝 (gronwallBound (D 0) C₁ (C₂ / V) (t - 0))) := by
      simp only [gronwallBound_of_K_ne_0 hC₁ne]
      have hD0t : Tendsto D (𝓝[>] 0) (𝓝 (D 0)) := by
        have hw := hDc 0 ⟨le_rfl, hT.le⟩
        refine hw.tendsto.mono_left ?_
        refine nhdsWithin_le_of_mem ?_
        exact mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
      have hlin : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝 (t - 0)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      have hexp := (Real.continuous_exp.tendsto _).comp (hlin.const_mul C₁)
      exact (hD0t.mul hexp).add (tendsto_const_nhds.mul (hexp.sub tendsto_const_nhds))
    have hle := ge_of_tendsto hcont (by
      filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε using hgron ε hε)
    rw [hD0, sub_zero] at hle
    exact hle

theorem tendsto_gronwallBound {δ ε : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) (K t : ℝ) :
    Tendsto (fun k => gronwallBound (δ k) K (ε k) t) atTop (𝓝 0) := by
  unfold gronwallBound
  split_ifs with hK
  · simpa using hδ.add (hε.mul_const t)
  · simpa using (hδ.mul_const (Real.exp (K * t))).add
      ((hε.div_const K).mul_const (Real.exp (K * t) - 1))

/-- **The law of large numbers as `V → ∞`.** With `V = k + 1` and initial counts `n_k` satisfying
`w · n_k ≤ M V` and `n_k / V → x(0)`, the mean squared distance `E |X^V(t)/V − x(t)|²` tends to
`0` for every `t ∈ [0, T]`. -/
theorem conservative_lln_tendsto (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ) (hn : ∀ k, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun k : ℕ => ∑' m, N.transition (N.volumeScale κ ((k : ℝ) + 1)
        (by positivity)) t (n k) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - x t s) ^ 2) atTop
      (𝓝 0) := by
  obtain ⟨C₁, C₂, -, -, hbd⟩ := conservative_lln N κ hwinv hwpos (Rx := Rx) hM x hxc hx hxB
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hε : Tendsto (fun k : ℕ => C₂ / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hup := tendsto_gronwallBound hn0 hε C₁ t
  refine squeeze_zero (fun k => tsum_nonneg fun m => mul_nonneg
    ((N.jumpSystem _).Pmin_nonneg t ht.1 _ _) (Finset.sum_nonneg fun s _ => sq_nonneg _))
    (fun k => hbd ((k : ℝ) + 1) (hV k) (n k) (hn k) t ht) hup

end Network

namespace Examples
namespace Dimerization

open Network

/-- `2X ⇌ Y` (species `X = 0`, `Y = 1`). -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0], ![0, 1]⟩ else ⟨![0, 1], ![2, 0]⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The conserved quantity `x + 2y`. -/
def w : Fin 2 → ℝ := ![1, 2]

theorem w_inv : net.IsPInvariant w := by
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro _ ⟨r, rfl⟩
  fin_cases r <;>
    simp [w, Fin.sum_univ_two, Network.reactionVector, Reaction.vector]

theorem w_pos : ∀ s, 0 < w s := by
  intro s; fin_cases s <;> simp [w]

/-- The equilibrium `(1, 1)`. -/
def xstar : Concentration (Fin 2) := fun _ => 1

theorem equilibrium : net.massActionVectorField κ xstar = 0 := by
  funext u
  rw [massActionVectorField_apply]
  fin_cases u <;>
    simp [Fin.sum_univ_two, massActionRate, κ, xstar, Complex.massActionMonomial,
      Network.reactionVector, Reaction.vector]

/-- **LLN instance for the bimolecular network `2X ⇌ Y`.** Started from `(V, V)` molecules at
volume `V = k + 1`, `E |X^V(t)/V − (1, 1)|² → 0` for every `t ∈ [0, 1]`. -/
theorem lln {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun k : ℕ => ∑' m, net.transition (net.volumeScale κ ((k : ℝ) + 1) (by positivity))
        t (fun _ => k + 1) m * ∑ s, ((m s : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2) atTop (𝓝 0) := by
  refine conservative_lln_tendsto net κ w_inv w_pos (M := 3) (Rx := 1) (by norm_num)
    (fun _ => xstar) continuousOn_const (fun t _ => by rw [equilibrium]; exact hasDerivAt_const _ _)
    (fun t _ => ⟨fun _ => by simp [xstar], fun _ => le_refl _⟩) (fun k _ => k + 1)
    (fun k => ?_) ?_ ht
  · simp [w, Fin.sum_univ_two]; linarith
  · have h : ∀ k : ℕ, ∑ s, ((((fun _ : Fin 2 => k + 1) s : ℕ) : ℝ) / ((k : ℝ) + 1) - xstar s) ^ 2 = 0 := by
      intro k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp [xstar, Fin.sum_univ_two, hk]
    simp only [h]
    exact tendsto_const_nhds

end Dimerization
end Examples

end CRNT
