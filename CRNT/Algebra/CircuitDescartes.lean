import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.SignVariations
import CRNT.Algebra.CircuitBound

/-!
# Generalized Descartes' rule for real exponents (Bihan–Dickenstein sign-variation bound)

Leaf A3 of the field map ("real root bounds and mixed volumes") is *partial*: the `n + 1` bound
for circuits is proved in `CRNT.Algebra.CircuitBound` (`card_circuit_solutions_le`,
`card_circuit_solutions_le_monomial`), but the **sign-variation refinement** of
Bihan–Dickenstein is missing.  This file supplies it.

## 1. Sign variations

`listSignVariations l` is the number of sign changes in a list of real coefficients, where zero
entries are skipped (so `[1, 0, -2, 3, 3]` has two sign variations), and
`signVariations c` is the same count for a `Fin (n + 1)`-indexed family of coefficients.
This is Mathlib's `List.signVariations` (`Mathlib/Data/List/SignVariations.lean`), the very
counting device behind Mathlib's polynomial Descartes rule
`Polynomial.roots_countP_pos_le_signVariations`.

Basic facts proved here:

* `signVariations_nonneg`, `signVariations_le_length` (`≤ n + 1`);
* invariance under inserting zeros (`signVariations_zero_cons`, `signVariations_cons_zero_cons`,
  `signVariations_filter_ne_zero`);
* `signVariations_cons`: prepending a coefficient with the opposite strict sign adds one
  variation;
* `signVariations_map_mul_pos`: multiplying all coefficients by positive numbers does not
  change the count.

## 2. The generalized Descartes rule for exponential sums

For real exponents `w_0 < w_1 < … < w_n` and coefficients `c_k`, put

`Φ t = ∑_k c_k e^{w_k t}`.

**Theorem (`card_zeros_exp_sum_le`).** The number of *distinct* real zeros of `Φ` is at most
`signVariations c` (provided `Φ` is not identically zero).

*Proof.* This is Descartes' rule for exponential sums (also called the generalized rule of
signs for generalized polynomials `g(y) = ∑_k c_k y^{w_k}`, since `Φ t = g(e^t)` and
`t ↦ e^t` is a bijection `ℝ → (0,∞)`).

The proof is the classical Budan–Fourier / Rolle induction.  After removing the zero
coefficients and factoring out the smallest exponent, one is left with

`Ψ t = c_0 + ∑_{k ≥ 1} c_k e^{μ_k t}`,  `0 < μ_1 < μ_2 < …`,

whose derivative is `Ψ' t = ∑_{k ≥ 1} c_k μ_k e^{μ_k t}`: the positive exponents `μ_k` do not
change the signs of the coefficients, so `Ψ'` has at most `signVariations (c_1, …, c_n)` zeros
by induction.  Rolle then gives `#zeros Ψ ≤ #zeros Ψ' + 1`.  The missing `−1` is supplied by
the **end signs**: `Ψ t → c_0` as `t → −∞` and `Ψ' t` has the sign of `c_1` for `t` sufficiently
negative.  If `c_0` and `c_1` have the same sign, the mean value theorem between a very
negative point `a` (where `Ψ a` still has the sign of `c_0`) and the least zero `z` of `Ψ`
produces a point `s ∈ (a, z)` where `Ψ' s` has the sign of `−c_0`, i.e. the *opposite* sign of
`Ψ' a`; the intermediate value theorem then produces a zero of `Ψ'` in `(−∞, z)`, which is an
extra zero of the derivative, not "used up" by Rolle.  Hence in that case
`#zeros Ψ ≤ #zeros Ψ'`, and in the opposite case `#zeros Ψ ≤ #zeros Ψ' + 1`; both are exactly
the sign-variation count of `(c_0, c_1, …, c_n)`.

## 3. Consequences for circuits

* `card_pos_roots_exp_le_signVariations`: a generalized polynomial `g(y) = ∑_k c_k y^{w_k}`
  (real exponents) has at most `signVariations c` positive roots.
* `CRNT.Circuit.card_le_signVariations_roots`: the polynomial form of Descartes' rule
  (Mathlib's `Polynomial.roots_countP_pos_le_signVariations`).
* `CRNT.Circuit.card_log_affine_zeros_le_signVariations`: the number of zeros of the
  log-affine function `φ` of a circuit is at most `signVariations (circuitPoly p q μ) + 1`.
* `CRNT.Circuit.card_circuit_solutions_le_signVariations`: the number of positive solutions
  of a circuit system is at most `signVariations (circuitPoly p q μ) + 1`, refining the
  `n + 1` bound of `CRNT.Circuit.card_circuit_solutions_le`.

## 4. Relation to leaf A3

Leaf A3 asks for real root bounds and mixed volumes.  What is proved here is the
sign-variation half: the classical Descartes bound (in its generalized, real-exponent form)
and the resulting refinement of Bihan's `n + 1` bound for circuits.  What is *not* proved
here is the BKK mixed-volume bound, and the full row-wise Bihan–Dickenstein bound for
circuits (which counts sign variations in the rows of the coefficient matrix, not in the
coefficients of the numerator polynomial `circuitPoly`).

## 5. Examples

`CRNT.CircuitDescartes.Example` checks the bound on concrete generalized polynomials:
the coefficients `1, -1, 1` have two sign variations (and `1 - y + y²` has no positive
root), while `1, 1, -1` have one sign variation (and `1 + y - y²` has exactly the positive
root `(1 + √5)/2`, so the bound is attained).
-/

open scoped BigOperators Topology

namespace CRNT
namespace CircuitDescartes

open SignType

/-! ### Sign variations -/

/-- Two real numbers have *opposite strict signs*. -/
abbrev oppositeSigns (a b : ℝ) : Prop := (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)

theorem oppositeSigns_iff {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oppositeSigns a b ↔ SignType.sign a = -SignType.sign b := by
  have hne : ∀ x : ℝ, x ≠ 0 → SignType.sign x = 1 ∨ SignType.sign x = -1 := by
    intro x hx
    rcases SignType.trichotomy (SignType.sign x) with h | h | h
    · exact Or.inr h
    · exact absurd h (by simpa [sign_eq_zero_iff] using hx)
    · exact Or.inl h
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · simp [sign_pos h1, sign_neg h2]
    · simp [sign_neg h1, sign_pos h2]
  · intro h
    rcases hne a ha with hsa | hsa <;> rcases hne b hb with hsb | hsb
    · rw [hsa, hsb] at h
      simp at h
    · exact Or.inl ⟨sign_eq_one_iff.mp hsa, sign_eq_neg_one_iff.mp hsb⟩
    · exact Or.inr ⟨sign_eq_neg_one_iff.mp hsa, sign_eq_one_iff.mp hsb⟩
    · rw [hsa, hsb] at h
      simp at h

/-- Sign variations of a list of real coefficients: the number of adjacent sign changes once
all zero entries have been removed. -/
noncomputable def listSignVariations (l : List ℝ) : ℕ := List.signVariations l

/-- Sign variations of a `Fin (n + 1)`-indexed coefficient family. -/
noncomputable def signVariations {n : ℕ} (c : Fin (n + 1) → ℝ) : ℕ :=
  listSignVariations ((List.finRange (n + 1)).map c)

@[simp]
theorem listSignVariations_nil : listSignVariations ([] : List ℝ) = 0 := rfl

@[simp]
theorem listSignVariations_singleton (a : ℝ) : listSignVariations [a] = 0 := by
  simp [listSignVariations]

theorem listSignVariations_nonneg (l : List ℝ) : 0 ≤ listSignVariations l := Nat.zero_le _

theorem listSignVariations_le_length (l : List ℝ) : listSignVariations l ≤ l.length := by
  have h1 : (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length
      ≤ ((l.map SignType.sign).filter (· ≠ 0)).length :=
    (List.destutter_sublist (· ≠ ·) _).length_le
  have h2 : ((l.map SignType.sign).filter (· ≠ 0)).length ≤ l.length := by
    calc ((l.map SignType.sign).filter (· ≠ 0)).length ≤ (l.map SignType.sign).length :=
        List.length_filter_le _ _
      _ = l.length := List.length_map _
  unfold listSignVariations List.signVariations
  calc (((((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1) : ℕ)
      ≤ (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length := Nat.sub_le _ _
    _ ≤ l.length := h1.trans h2

/-- A leading zero does not change the sign variations. -/
@[simp]
theorem listSignVariations_zero_cons (l : List ℝ) :
    listSignVariations (0 :: l) = listSignVariations l := by
  simp [listSignVariations]

/-- A zero in second position does not change the sign variations. -/
@[simp]
theorem listSignVariations_cons_zero_cons (a : ℝ) (l : List ℝ) :
    listSignVariations (a :: 0 :: l) = listSignVariations (a :: l) := by
  simp [listSignVariations]

/-- Removing the zero coefficients does not change the sign variations. -/
theorem listSignVariations_filter_ne_zero (l : List ℝ) :
    listSignVariations (l.filter (fun x => x ≠ 0)) = listSignVariations l := by
  have h : l.filter (fun x => x ≠ 0) = l.filter (fun x => !decide (x = 0)) := by
    simp
  unfold listSignVariations
  rw [h, List.signVariations_filter_ne_zero]

/-- A trailing zero does not change the sign variations. -/
theorem listSignVariations_append_zero (l : List ℝ) :
    listSignVariations (l ++ [0]) = listSignVariations l := by
  have h : (l ++ [0]).filter (fun x => !decide (x = 0)) = l.filter (fun x => !decide (x = 0)) := by
    simp
  unfold listSignVariations
  rw [← List.signVariations_filter_ne_zero (l ++ [0]), ← List.signVariations_filter_ne_zero l, h]

/-- Prepending a nonzero coefficient with the opposite strict sign adds one sign variation. -/
theorem listSignVariations_cons_cons (a b : ℝ) (l : List ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    listSignVariations (a :: b :: l) =
      listSignVariations (b :: l) + (if oppositeSigns a b then 1 else 0) := by
  have hA : SignType.sign a = SignType.sign b -> ¬ oppositeSigns a b := by
    intro hs h
    have h3 : SignType.sign b = 0 := by
      have h4 := (oppositeSigns_iff ha hb).mp h
      rw [hs] at h4
      simpa using h4
    exact absurd (sign_eq_zero_iff.mp h3) hb
  have hB : ¬ (SignType.sign a = SignType.sign b) -> oppositeSigns a b := by
    intro hn
    exact (oppositeSigns_iff ha hb).mpr
      ((sign_eq_sign_or_eq_neg ha hb).resolve_left hn)
  have h : (if SignType.sign a = SignType.sign b then 0 else 1) =
      (if oppositeSigns a b then 1 else 0) := by
    by_cases h' : SignType.sign a = SignType.sign b
    · simp [h', hA h']
    · simp [h', hB h']
  unfold listSignVariations
  rw [List.signVariations_cons_cons_of_ne_zero l ha hb, h]

/-- Multiplying all coefficients by positive numbers does not change the sign variations. -/
theorem listSignVariations_map_mul_pos (l : List ℝ) (f : ℝ → ℝ) (hf : ∀ x, 0 < f x) :
    listSignVariations (l.map fun x => x * f x) = listSignVariations l := by
  refine List.signVariations_map (fun x => ?_) l
  simp only [sign_mul, sign_pos (hf x), mul_one]

/-- Negating all coefficients does not change the sign variations. -/
theorem listSignVariations_map_neg (l : List ℝ) :
    listSignVariations (l.map (-·)) = listSignVariations l := by
  refine List.signVariations_map_of_sign_eq_neg (fun x => ?_) l
  exact Left.sign_neg x

/-- The sign variations of a `Fin (n+1)`-indexed family are nonnegative. -/
theorem signVariations_nonneg {n : ℕ} (c : Fin (n + 1) → ℝ) : 0 ≤ signVariations c :=
  listSignVariations_nonneg _

/-- The sign variations of a `Fin (n+1)`-indexed family are at most `n + 1`. -/
theorem signVariations_le_length {n : ℕ} (c : Fin (n + 1) → ℝ) : signVariations c ≤ n + 1 := by
  unfold signVariations
  calc listSignVariations ((List.finRange (n + 1)).map c)
      ≤ ((List.finRange (n + 1)).map c).length := listSignVariations_le_length _
    _ = (List.finRange (n + 1)).length := List.length_map _
    _ = n + 1 := List.length_finRange

/-- Prepending a real number to a `Fin (n+1)`-indexed family of real numbers. -/
def finCons {n : ℕ} (a : ℝ) (c : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ :=
  @Fin.cons (n := n + 1) (α := fun _ => ℝ) a c

@[simp]
theorem finCons_zero {n : ℕ} (a : ℝ) (c : Fin (n + 1) → ℝ) : finCons a c 0 = a := rfl

theorem finCons_succ {n : ℕ} (a : ℝ) (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finCons a c i.succ = c i := @Fin.cons_succ (n := n + 1) (α := fun _ => ℝ) a c i

/-- The list of coefficients of a `Fin (n+1)`-indexed family, with a coefficient prepended. -/
theorem finRange_map_finCons (n : ℕ) (a : ℝ) (c : Fin (n + 1) → ℝ) :
    (List.finRange (n + 2)).map (finCons a c) = a :: (List.finRange (n + 1)).map c := by
  rw [List.finRange_succ, List.map_cons, List.map_map]
  have h0 : finCons a c 0 = a := rfl
  rw [h0]
  congr 1


/-- Prepending a zero coefficient does not change the sign variations. -/
theorem signVariations_cons_zero {n : ℕ} (c : Fin (n + 1) → ℝ) :
    signVariations (finCons 0 c) = signVariations c := by
  have h := finRange_map_finCons n 0 c
  unfold signVariations
  rw [h, listSignVariations_zero_cons]

/-- Prepending a nonzero coefficient adds one sign variation exactly when the two coefficients
have opposite strict signs. -/
theorem signVariations_cons {n : ℕ} (a : ℝ) (c : Fin (n + 1) → ℝ) (ha : a ≠ 0) (h0 : c 0 ≠ 0) :
    signVariations (finCons a c) = signVariations c + (if oppositeSigns a (c 0) then 1 else 0) := by
  have h1 := finRange_map_finCons n a c
  have h2 : (List.finRange (n + 1)).map c = c 0 :: (List.finRange n).map (fun k => c k.succ) := by
    rw [List.finRange_succ, List.map_cons, List.map_map]
    congr 1
  unfold signVariations
  rw [h1, h2]
  exact listSignVariations_cons_cons a (c 0) _ ha h0

/-- Multiplying all coefficients by positive numbers does not change the sign variations. -/
theorem signVariations_map_mul_pos {n : ℕ} (c : Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∀ k, 0 < w k) : signVariations (fun k => c k * w k) = signVariations c := by
  unfold signVariations
  apply List.signVariations_congr
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro k hk
  simp [sign_mul, sign_pos (hw k), mul_one]


/-! ### Exponential sums -/

/-- The sum of `f p` over a list of (exponent, coefficient) pairs. -/
def pairSum (l : List (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : ℝ :=
  l.foldr (fun p acc => f p + acc) 0

@[simp]
theorem pairSum_nil (f : ℝ × ℝ → ℝ) : pairSum ([] : List (ℝ × ℝ)) f = 0 := rfl

@[simp]
theorem pairSum_cons (p : ℝ × ℝ) (rest : List (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    pairSum (p :: rest) f = f p + pairSum rest f := rfl

/-- The exponential sum `∑ p.2 * exp (p.1 * t)` attached to a list of (exponent, coefficient)
pairs. -/
noncomputable def expSum (l : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  pairSum l fun p => p.2 * Real.exp (p.1 * t)

/-- The derivative of `expSum`: `∑ p.2 * p.1 * exp (p.1 * t)`. -/
noncomputable def expSumDeriv (l : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  pairSum l fun p => p.2 * p.1 * Real.exp (p.1 * t)

/-- Shift the exponents of a list of (exponent, coefficient) pairs down by `a`. -/
def shiftDown (l : List (ℝ × ℝ)) (a : ℝ) : List (ℝ × ℝ) := l.map fun p => (p.1 - a, p.2)

/-- Shift the exponents of a list of (exponent, coefficient) pairs down by `a` and multiply the
coefficients by the new exponents; the exponential sum of the resulting list is the derivative
of the exponential sum of the shifted list. -/
def shiftDownDeriv (l : List (ℝ × ℝ)) (a : ℝ) : List (ℝ × ℝ) :=
  l.map fun p => (p.1 - a, p.2 * (p.1 - a))

theorem hasDerivAt_expSum (l : List (ℝ × ℝ)) (t : ℝ) :
    HasDerivAt (expSum l) (expSumDeriv l t) t := by
  induction l with
  | nil =>
      have h1 : expSum ([] : List (ℝ × ℝ)) = fun _ => 0 := by funext t; rfl
      have h2 : expSumDeriv ([] : List (ℝ × ℝ)) t = 0 := rfl
      rw [h1, h2]
      exact hasDerivAt_const t (0 : ℝ)
  | cons p rest ih =>
      have h1 : HasDerivAt (fun t => p.2 * Real.exp (p.1 * t)) (p.2 * p.1 * Real.exp (p.1 * t)) t := by
        have h0 : HasDerivAt (fun t => p.1 * t) p.1 t := by
          convert (hasDerivAt_id t).const_mul p.1 using 1 <;> simp
        have h1' := (Real.hasDerivAt_exp (p.1 * t)).comp t h0
        have h2' := h1'.const_mul p.2
        have h5 : (fun y => p.2 * (Real.exp ∘ HMul.hMul p.1) y) = fun y => p.2 * Real.exp (p.1 * y) := by
          funext y; simp
        rw [h5] at h2'
        convert h2' using 1 <;> ring
      have h2 : HasDerivAt (expSum rest) (expSumDeriv rest t) t := ih
      have h3 : expSum (p :: rest) = fun s => p.2 * Real.exp (p.1 * s) + expSum rest s := by
        funext s; rfl
      have h4 : expSumDeriv (p :: rest) t = p.2 * p.1 * Real.exp (p.1 * t) + expSumDeriv rest t := rfl
      rw [h3, h4]
      exact h1.add h2

theorem continuous_expSum (l : List (ℝ × ℝ)) : Continuous (expSum l) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_expSum l t).continuousAt

theorem expSum_mul_exp_neg (l : List (ℝ × ℝ)) (a t : ℝ) :
    expSum l t * Real.exp (-(a * t)) = expSum (shiftDown l a) t := by
  induction l with
  | nil =>
      have h1 : expSum ([] : List (ℝ × ℝ)) t = 0 := rfl
      have h2 : expSum (shiftDown ([] : List (ℝ × ℝ)) a) t = 0 := rfl
      rw [h1, h2]
      ring
  | cons p rest ih =>
      have h3 : expSum (p :: rest) t = p.2 * Real.exp (p.1 * t) + expSum rest t := rfl
      have h4 : expSum (shiftDown (p :: rest) a) t
          = (p.1 - a, p.2).2 * Real.exp ((p.1 - a, p.2).1 * t) + expSum (shiftDown rest a) t := rfl
      rw [h3, h4, add_mul, ih]
      congr 1
      calc p.2 * Real.exp (p.1 * t) * Real.exp (-(a * t))
          = p.2 * (Real.exp (p.1 * t) * Real.exp (-(a * t))) := by ring
        _ = p.2 * Real.exp (p.1 * t + -(a * t)) := by rw [Real.exp_add]
        _ = (p.1 - a, p.2).2 * Real.exp ((p.1 - a, p.2).1 * t) := by
            congr 1
            ring

theorem expSum_cons_shiftDown (p : ℝ × ℝ) (rest : List (ℝ × ℝ)) (t : ℝ) :
    expSum (p :: rest) t
      = Real.exp (p.1 * t) * (p.2 + expSum (shiftDown rest p.1) t) := by
  have h := expSum_mul_exp_neg rest p.1 t
  have h3 : expSum (p :: rest) t = p.2 * Real.exp (p.1 * t) + expSum rest t := rfl
  have hexp : Real.exp (p.1 * t) * Real.exp (-(p.1 * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [h3, ← h]
  calc p.2 * Real.exp (p.1 * t) + expSum rest t
      = p.2 * Real.exp (p.1 * t)
          + expSum rest t * (Real.exp (p.1 * t) * Real.exp (-(p.1 * t))) := by
        rw [hexp]; ring
    _ = Real.exp (p.1 * t) * (p.2 + expSum rest t * Real.exp (-(p.1 * t))) := by ring

theorem expSumDeriv_shiftDownDeriv (l : List (ℝ × ℝ)) (a t : ℝ) :
    expSumDeriv (shiftDown l a) t = expSum (shiftDownDeriv l a) t := by
  induction l with
  | nil =>
      have h1 : expSumDeriv (shiftDown ([] : List (ℝ × ℝ)) a) t = 0 := rfl
      have h2 : expSum (shiftDownDeriv ([] : List (ℝ × ℝ)) a) t = 0 := rfl
      rw [h1, h2]
  | cons p rest ih =>
      have h3 : expSumDeriv (shiftDown (p :: rest) a) t
          = (p.1 - a, p.2).2 * (p.1 - a, p.2).1 * Real.exp ((p.1 - a, p.2).1 * t)
            + expSumDeriv (shiftDown rest a) t := rfl
      have h4 : expSum (shiftDownDeriv (p :: rest) a) t
          = (p.1 - a, p.2 * (p.1 - a)).2 * Real.exp ((p.1 - a, p.2 * (p.1 - a)).1 * t)
            + expSum (shiftDownDeriv rest a) t := rfl
      rw [h3, h4, ih]

theorem hasDerivAt_expSum_shiftDown (l : List (ℝ × ℝ)) (a t : ℝ) :
    HasDerivAt (fun s => expSum (shiftDown l a) s) (expSum (shiftDownDeriv l a) t) t := by
  rw [← expSumDeriv_shiftDownDeriv l a t]
  exact hasDerivAt_expSum (shiftDown l a) t

/-! ### Limits at `-∞` -/

theorem tendsto_mul_const_atBot (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => a * t) Filter.atBot Filter.atBot := by
  have hmain : ∀ (x : ℝ), ∀ᶠ t in Filter.atBot, a * t ≤ x := by
    intro x
    have hev : ∀ᶠ t in Filter.atBot, a * t ≤ x :=
      Filter.eventually_atBot.2 ⟨x / a, fun t ht => by
        have h := mul_le_mul_of_nonneg_left (a := a) (b := t) (c := x / a) ht ha.le
        rwa [mul_div_cancel₀ _ (ne_of_gt ha)] at h⟩
    exact hev
  exact (Filter.tendsto_atBot).2 hmain

theorem tendsto_exp_mul_atBot (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => Real.exp (a * t)) Filter.atBot (𝓝 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.exp x) Filter.atBot (𝓝 0) := Real.tendsto_exp_atBot
  have h2 : Filter.Tendsto (fun t : ℝ => a * t) Filter.atBot Filter.atBot := tendsto_mul_const_atBot a ha
  have h3 := h1.comp h2
  convert h3 using 1
  funext t
  rfl

theorem tendsto_pairSum_exp_atBot (l : List (ℝ × ℝ)) (g : ℝ × ℝ → ℝ)
    (h : ∀ p ∈ l, 0 < p.1) :
    Filter.Tendsto (fun t => pairSum l fun p => g p * Real.exp (p.1 * t)) Filter.atBot (𝓝 0) := by
  induction l with
  | nil => simpa using (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atBot (𝓝 0))
  | cons p rest ih =>
      have h1 : Filter.Tendsto (fun t => g p * Real.exp (p.1 * t)) Filter.atBot (𝓝 0) := by
        convert (tendsto_exp_mul_atBot p.1 (h p (by simp))).const_mul (g p) using 1 <;> simp
      have h2 : Filter.Tendsto (fun t => pairSum rest fun q => g q * Real.exp (q.1 * t)) Filter.atBot (𝓝 0) :=
        ih fun q hq => h q (by simp [hq])
      simpa [pairSum] using h1.add h2

theorem tendsto_expSum_atBot (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, 0 < p.1) :
    Filter.Tendsto (fun t => expSum l t) Filter.atBot (𝓝 0) :=
  tendsto_pairSum_exp_atBot l (fun p => p.2) h

theorem tendsto_expSum_scaled (p : ℝ × ℝ) (rest : List (ℝ × ℝ))
    (hrest : ∀ q ∈ rest, p.1 < q.1) :
    Filter.Tendsto (fun t => expSum (p :: rest) t * Real.exp (-(p.1 * t))) Filter.atBot (𝓝 p.2) := by
  have hkey : ∀ t, expSum (p :: rest) t * Real.exp (-(p.1 * t))
      = p.2 + expSum (shiftDown rest p.1) t := by
    intro t
    have h := expSum_mul_exp_neg (p :: rest) p.1 t
    have h3 : expSum (shiftDown (p :: rest) p.1) t
        = (p.1 - p.1, p.2).2 * Real.exp ((p.1 - p.1, p.2).1 * t)
          + expSum (shiftDown rest p.1) t := rfl
    have h4 : (p.1 - p.1, p.2).1 = 0 := by simp
    have h5 : (p.1 - p.1, p.2).2 = p.2 := rfl
    rw [h3, h4, h5, zero_mul, Real.exp_zero, mul_one] at h
    linarith [h]
  rw [show (fun t => expSum (p :: rest) t * Real.exp (-(p.1 * t)))
      = fun t => p.2 + expSum (shiftDown rest p.1) t from funext hkey]
  have h1 : Filter.Tendsto (fun t => expSum (shiftDown rest p.1) t) Filter.atBot (𝓝 0) :=
    tendsto_expSum_atBot _ fun q hq => by
      simp only [shiftDown, List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact sub_pos.mpr (by linarith [hrest r hr])
  convert h1.const_add p.2 using 1 <;> simp

/-- If `f t → L` as `t → -∞` with `L ≠ 0`, then `f t` has the sign of `L` for all sufficiently
negative `t`. -/
theorem exists_lt_of_tendsto_sign {f : ℝ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (h : Filter.Tendsto f Filter.atBot (𝓝 L)) : ∃ T, ∀ t < T, SignType.sign (f t) = SignType.sign L := by
  have h1 : ∀ᶠ t in Filter.atBot, dist (f t) L < |L| := by
    have hε : |L| > 0 := abs_pos.mpr hL
    filter_upwards [Metric.tendsto_nhds.1 h |L| hε] with t ht
    exact ht
  obtain ⟨T, hT⟩ : ∃ T, ∀ t < T, dist (f t) L < |L| := by
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 h1
    refine ⟨a, fun t ht => ha t (le_of_lt ht)⟩
  refine ⟨T, fun t ht => ?_⟩
  rcases lt_trichotomy L 0 with hLneg | hLzero | hLpos
  · have h2 : f t < 0 := by
      have h3 := abs_lt.mp (hT t ht)
      linarith [abs_of_neg hLneg]
    rw [sign_neg h2, sign_neg hLneg]
  · exact absurd hLzero hL
  · have h2 : 0 < f t := by
      have h3 := abs_lt.mp (hT t ht)
      linarith [abs_of_pos hLpos]
    rw [sign_pos h2, sign_pos hLpos]

/-- The next element of a finite set of reals above `x`, if there is one. -/
noncomputable def nextOf (Z : Finset ℝ) (x : ℝ) : ℝ :=
  if h : (Z.filter (x < ·)).Nonempty then (Z.filter (x < ·)).min' h else x


/-! ### The generalized Descartes rule -/

/-- The sign sequence of a list of (exponent, coefficient) pairs: the signs of the nonzero
coefficients, in order. -/
noncomputable def signsOfPairs (l : List (ℝ × ℝ)) : List SignType :=
  (l.map fun p => SignType.sign (Prod.snd p)).filter (· ≠ 0)

/-- Remove the pairs with zero coefficient. -/
noncomputable def dropZeroCoeffs : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | p :: rest => if p.2 = 0 then dropZeroCoeffs rest else p :: dropZeroCoeffs rest

theorem signsOfPairs_dropZeroCoeffs (l : List (ℝ × ℝ)) :
    signsOfPairs (dropZeroCoeffs l) = signsOfPairs l := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      have ih' : ((dropZeroCoeffs rest).map (fun q => SignType.sign (Prod.snd q))).filter (· ≠ 0)
          = (rest.map (fun q => SignType.sign (Prod.snd q))).filter (· ≠ 0) := by
        simpa [signsOfPairs] using ih
      by_cases h : p.2 = 0
      · rw [dropZeroCoeffs, ite_eq_left h, ih]
        simp only [signsOfPairs, List.map_cons, List.filter_cons]
        have hp : Prod.snd p = p.2 := rfl
        rw [hp]
        simp [h]
      · rw [dropZeroCoeffs, ite_eq_right h]
        simp only [signsOfPairs, List.map_cons, List.filter_cons]
        rw [ih']

theorem listSignVariations_eq_signsOfPairs (l : List (ℝ × ℝ)) :
    listSignVariations (l.map Prod.snd) = ((signsOfPairs l).destutter (· ≠ ·)).length - 1 := by
  have h1 : (l.map Prod.snd).map SignType.sign = l.map fun p => SignType.sign (Prod.snd p) := by
    simp [List.map_map, Function.comp_def]
  unfold listSignVariations List.signVariations signsOfPairs
  rw [h1]

theorem listSignVariations_dropZeroCoeffs (l : List (ℝ × ℝ)) :
    listSignVariations ((dropZeroCoeffs l).map Prod.snd) = listSignVariations (l.map Prod.snd) := by
  rw [listSignVariations_eq_signsOfPairs, listSignVariations_eq_signsOfPairs]
  rw [signsOfPairs_dropZeroCoeffs l]

theorem expSum_dropZeroCoeffs (l : List (ℝ × ℝ)) (t : ℝ) :
    expSum (dropZeroCoeffs l) t = expSum l t := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      have hsplit : expSum (p :: rest) t = p.2 * Real.exp (p.1 * t) + expSum rest t := rfl
      by_cases h : p.2 = 0
      · rw [dropZeroCoeffs, ite_eq_left h, hsplit, ih]
        simp [h]
      · have hsplit' : expSum (p :: dropZeroCoeffs rest) t
            = p.2 * Real.exp (p.1 * t) + expSum (dropZeroCoeffs rest) t := rfl
        rw [dropZeroCoeffs, ite_eq_right h, hsplit', ih, hsplit]

theorem dropZeroCoeffs_ne_nil (l : List (ℝ × ℝ)) : (∃ p ∈ l, p.2 ≠ 0) → dropZeroCoeffs l ≠ [] := by
  induction l with
  | nil => intro hl; simp at hl
  | cons q rest ih =>
      intro hl
      rw [dropZeroCoeffs]
      by_cases hq : q.2 = 0
      · rw [ite_eq_left hq]
        apply ih
        rcases hl with ⟨p, hp, hp2⟩
        rcases List.mem_cons.mp hp with h1 | h2
        · rw [h1] at hp2
          exact absurd hq hp2
        · exact ⟨p, h2, hp2⟩
      · rw [ite_eq_right hq]
        simp

theorem dropZeroCoeffs_sublist (l : List (ℝ × ℝ)) : List.Sublist (dropZeroCoeffs l) l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons p rest ih =>
      rw [dropZeroCoeffs]
      by_cases h : p.2 = 0
      · rw [ite_eq_left h]
        exact List.Sublist.cons p ih
      · rw [ite_eq_right h]
        exact List.Sublist.cons_cons p ih

theorem dropZeroCoeffs_pairwise {l : List (ℝ × ℝ)} (hl : l.Pairwise (fun p q => p.1 < q.1)) :
    (dropZeroCoeffs l).Pairwise (fun p q => p.1 < q.1) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
      rw [dropZeroCoeffs]
      by_cases h : p.2 = 0
      · rw [ite_eq_left h]
        exact ih (hl.tail)
      · rw [ite_eq_right h]
        refine List.Pairwise.cons (fun a ha => ?_) (ih (hl.tail))
        exact (List.pairwise_cons.mp hl).1 a (List.Sublist.mem ha (dropZeroCoeffs_sublist rest))

/-- The next element of a finite set of reals above `x` is at most any larger element of the
set. -/
theorem nextOf_le (Z : Finset ℝ) (x y : ℝ) (hy : y ∈ Z) (hxy : x < y) :
    nextOf Z x ≤ y := by
  by_cases h : (Z.filter (x < ·)).Nonempty
  · rw [nextOf, dite_eq_left h]
    exact Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hxy⟩)
  · exfalso
    exact h ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩

/-- **Rolle's theorem between consecutive zeros.**  If `g` is differentiable with derivative `g'`
and `Z` is a finite set of zeros of `g`, then there is a finite set `T` of zeros of `g'` with one
element in each gap between consecutive zeros of `g`, and no element below the least zero of `g`. -/
theorem rolle_points {g' : ℝ → ℝ} {Z : Finset ℝ} (hZne : Z.Nonempty)
    (hRolle : ∀ x ∈ Z, x < Z.max' hZne → ∃ w, x < w ∧ w < nextOf Z x ∧ g' w = 0) :
    ∃ T : Finset ℝ, (∀ t ∈ T, g' t = 0) ∧ (∀ t ∈ T, Z.min' hZne < t) ∧
      T.card = (Z.erase (Z.max' hZne)).card ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x < y → (∀ z ∈ Z, z ∉ Set.Ioo x y) → ∃ w ∈ T, x < w ∧ w < y) := by
  set Zmax := Z.max' hZne with hZmax
  have hmin_next : ∀ x ∈ Z, x < Zmax → ∀ y ∈ Z, x < y → (∀ z ∈ Z, z ∉ Set.Ioo x y) →
      nextOf Z x = y := by
    intro x hx hlt y hy hxy hconc
    have hne : (Z.filter (x < ·)).Nonempty :=
      ⟨Zmax, Finset.mem_filter.mpr ⟨Finset.max'_mem _ hZne, hlt⟩⟩
    have hmin : nextOf Z x = (Z.filter (x < ·)).min' hne := by simp [nextOf, hne]
    rw [hmin]
    have hyf : y ∈ Z.filter (x < ·) := Finset.mem_filter.mpr ⟨hy, hxy⟩
    have hle : (Z.filter (x < ·)).min' hne ≤ y := Finset.min'_le _ y hyf
    have hmem : (Z.filter (x < ·)).min' hne ∈ Z :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
    have hlt' : x < (Z.filter (x < ·)).min' hne :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    by_contra hcon
    have hlt2 : (Z.filter (x < ·)).min' hne < y := lt_of_le_of_ne hle hcon
    exact hconc _ hmem ⟨hlt', hlt2⟩
  have htotal : ∀ x : ℝ, ∃ w, x ∈ Z.erase Zmax → x < w ∧ w < nextOf Z x ∧ g' w = 0 := by
    intro x
    by_cases hx : x ∈ Z.erase Zmax
    · obtain ⟨w, h1, h2, h3⟩ := hRolle x (Finset.mem_erase.mp hx).2
        (lt_of_le_of_ne (Finset.le_max' _ x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1)
      exact ⟨w, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨x, fun h => absurd h hx⟩
  let r : ℝ → ℝ := fun x => Classical.choose (htotal x)
  set T : Finset ℝ := (Z.erase Zmax).image r with hT
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact ((Classical.choose_spec (htotal x) hx).2.2)
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hxl : Z.min' hZne ≤ x := Finset.min'_le _ x (Finset.mem_erase.mp hx).2
    have hwx : x < Classical.choose (htotal x) := (Classical.choose_spec (htotal x) hx).1
    exact lt_of_le_of_lt hxl hwx
  · -- the Rolle points are pairwise distinct: one for each gap
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h2 : r x < nextOf Z x := (Classical.choose_spec (htotal x) hx).2.1
      have h3 : y < r y := (Classical.choose_spec (htotal y) hy).1
      have hn : nextOf Z x ≤ y :=
        nextOf_le Z x y (Finset.mem_erase.mp hy).2 hlt
      have hlt' : r x < r y := lt_of_lt_of_le h2 (le_of_lt (lt_of_le_of_lt hn h3))
      rw [hxy] at hlt'
      exact lt_irrefl _ hlt'
    · have h2 : r y < nextOf Z y := (Classical.choose_spec (htotal y) hy).2.1
      have h3 : x < r x := (Classical.choose_spec (htotal x) hx).1
      have hn : nextOf Z y ≤ x :=
        nextOf_le Z y x (Finset.mem_erase.mp hx).2 hlt
      have hlt' : r y < r x := lt_of_lt_of_le h2 (le_of_lt (lt_of_le_of_lt hn h3))
      rw [hxy] at hlt'
      exact lt_irrefl _ hlt'
  · intro x hx y hy hxy hconc
    have hxne : x ≠ Zmax := by
      intro h
      subst h
      exact absurd (hxy.trans_le (Finset.le_max' _ y hy)) (lt_irrefl _)
    have hx1 : x ∈ Z.erase Zmax := Finset.mem_erase.mpr ⟨hxne, hx⟩
    have hnext : nextOf Z x = y :=
      hmin_next x hx (lt_of_le_of_ne (Finset.le_max' _ x hx) hxne) y hy hxy hconc
    have hw' := Classical.choose_spec (htotal x) hx1
    have hmem : r x ∈ T :=
      Finset.mem_image.mpr ⟨x, hx1, rfl⟩
    refine ⟨r x, hmem, hw'.1, ?_⟩
    exact hnext ▸ hw'.2.1

/-- The next element of a finite set of reals above `x` belongs to the set. -/
theorem nextOf_mem (Z : Finset ℝ) (x : ℝ) (hx : x ∈ Z) : nextOf Z x ∈ Z := by
  by_cases h : (Z.filter (x < ·)).Nonempty
  · rw [nextOf, dite_eq_left h]
    exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1
  · rw [nextOf, dite_eq_right h]
    exact hx




theorem pairwise_shiftDown {l : List (ℝ × ℝ)} {a : ℝ} (hl : l.Pairwise (fun p q => p.1 < q.1)) :
    (shiftDown l a).Pairwise (fun p q => p.1 < q.1) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
      have hcons := List.pairwise_cons.mp hl
      rw [shiftDown, List.map_cons]
      refine List.Pairwise.cons (fun x hx => ?_) (ih hcons.2)
      simp only [List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      linarith [hcons.1 r (by simp [hr])]

theorem pairwise_shiftDownDeriv {l : List (ℝ × ℝ)} {a : ℝ} (hl : l.Pairwise (fun p q => p.1 < q.1)) :
    (shiftDownDeriv l a).Pairwise (fun p q => p.1 < q.1) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
      have hcons := List.pairwise_cons.mp hl
      rw [shiftDownDeriv, List.map_cons]
      refine List.Pairwise.cons (fun x hx => ?_) (ih hcons.2)
      simp only [List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      linarith [hcons.1 r (by simp [hr])]

/-- The intermediate value theorem: if `f` is continuous on `[a, b]` and `0` lies between
`f a` and `f b`, then `f` vanishes at some point of `[a, b]`. -/
theorem exists_eq_zero_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (h0 : min (f a) (f b) ≤ 0 ∧ 0 ≤ max (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = 0 := by
  rcases le_total (f a) (f b) with h | h
  · have hmin : min (f a) (f b) = f a := min_eq_left h
    have hmax : max (f a) (f b) = f b := max_eq_right h
    rw [hmin, hmax] at h0
    obtain ⟨c, hc, hcf⟩ := intermediate_value_Icc hab hcont ⟨h0.1, h0.2⟩
    exact ⟨c, hc, hcf⟩
  · have hmin : min (f a) (f b) = f b := min_eq_right h
    have hmax : max (f a) (f b) = f a := max_eq_left h
    rw [hmin, hmax] at h0
    obtain ⟨c, hc, hcf⟩ := intermediate_value_Icc' hab hcont ⟨h0.1, h0.2⟩
    exact ⟨c, hc, hcf⟩

/-- **The main induction for the generalized Descartes rule.**  The number of distinct real zeros
of `Φ t = ∑_k c_k e^{w_k t}` is at most the number of sign variations of the coefficients. -/
theorem card_zeros_expSum_le_aux : ∀ (n : ℕ) (l : List (ℝ × ℝ)), l.length = n →
    l.Pairwise (fun p q => p.1 < q.1) → (∀ p ∈ l, p.2 ≠ 0) → l ≠ [] →
    ∀ (Z : Finset ℝ), (∀ t ∈ Z, expSum l t = 0) → Z.card ≤ listSignVariations (l.map Prod.snd) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro l hlen hl hall hlne Z hZ
      cases l with
      | nil => exact absurd hlne (by simp)
      | cons p rest =>
          have hrestlen : rest.length + 1 = n := by simp at hlen; omega
          have hhallrest : ∀ r ∈ rest, r.2 ≠ 0 := fun r hr => hall r (by simp [hr])
          have hlrest : rest.Pairwise (fun a b => a.1 < b.1) := hl.tail
          by_cases hrestnil : rest = []
          · -- a single exponential has no zeros
            have hc1 : p.2 ≠ 0 := hall p (by simp)
            have hexp : ∀ t, expSum (p :: rest) t = p.2 * Real.exp (p.1 * t) := by
              intro t; rw [hrestnil]; simp [expSum, pairSum]
            have hzero : ∀ t ∈ Z, p.2 * Real.exp (p.1 * t) = 0 := by
              intro t ht
              have h0 := hZ t ht
              rw [hexp] at h0
              exact h0
            have hZnil : Z = ∅ := by
              ext t
              constructor
              · intro ht
                have h0 := hzero t ht
                have hne : Real.exp (p.1 * t) ≠ 0 := Real.exp_ne_zero _
                have : p.2 = 0 := by
                  rw [mul_eq_zero] at h0
                  exact h0.resolve_right hne
                exact (hc1 this).elim
              · intro ht; exact absurd ht (by simp)
            have hcard : Z.card = 0 := Finset.card_eq_zero.mpr hZnil
            have hsv : listSignVariations ((p :: rest).map Prod.snd) = 0 := by
              rw [hrestnil]; simp [listSignVariations]
            omega
          · -- the main case: `l = p :: q :: rest'`
            cases rest with
            | nil => exact (hrestnil rfl).elim
            | cons q rest' =>
                have hcons := List.pairwise_cons.mp hl
                have hlam : p.1 < q.1 := hcons.1 q (by simp)
                have htail : (q :: rest').Pairwise (fun a b => a.1 < b.1) := hcons.2
                have hc1 : p.2 ≠ 0 := hall p (by simp)
                have hc2 : q.2 ≠ 0 := hall q (by simp)
                have hhall' : ∀ r ∈ rest', r.2 ≠ 0 := fun r hr => hall r (by simp [hr])
                have hcons2 := List.pairwise_cons.mp htail
                have hq' : ∀ r ∈ rest', q.1 < r.1 :=
                  fun r hr => hcons2.1 r (by simp [hr])
                -- the shifted list (the derivative)
                have hl3len : (shiftDownDeriv (q :: rest') p.1).length = n - 1 := by
                  simp only [shiftDownDeriv, List.length_map]
                  simp at hlen
                  omega
                have hl3pair : (shiftDownDeriv (q :: rest') p.1).Pairwise (fun a b => a.1 < b.1) :=
                  pairwise_shiftDownDeriv htail
                have hl3coeff : ∀ r ∈ shiftDownDeriv (q :: rest') p.1, r.2 ≠ 0 := by
                  intro r hr
                  simp only [shiftDownDeriv, List.mem_map] at hr
                  obtain ⟨s, hs, rfl⟩ := hr
                  have hsp : p.1 < s.1 := by
                    rcases List.mem_cons.mp hs with rfl | hrest
                    · exact hlam
                    · exact lt_trans hlam (hq' s hrest)
                  exact mul_ne_zero (hall s (by simp [hs])) (ne_of_gt (sub_pos.mpr hsp))
                have hl3ne : shiftDownDeriv (q :: rest') p.1 ≠ [] := by
                  intro h
                  have hmem : (q.1 - p.1, q.2 * (q.1 - p.1)) ∈ shiftDownDeriv (q :: rest') p.1 := by
                    simp [shiftDownDeriv]
                  rw [h] at hmem
                  simp at hmem
                -- the function `g` and its derivative
                have hderiv : ∀ t, HasDerivAt (fun s => p.2 + expSum (shiftDown (q :: rest') p.1) s)
                    (expSum (shiftDownDeriv (q :: rest') p.1) t) t := by
                  intro t
                  exact (hasDerivAt_expSum_shiftDown (q :: rest') p.1 t).const_add p.2
                have hcont : Continuous (fun s => p.2 + expSum (shiftDown (q :: rest') p.1) s) :=
                  continuous_const.add (continuous_expSum _)
                have hcont' : Continuous (fun s => expSum (shiftDownDeriv (q :: rest') p.1) s) :=
                  continuous_expSum _
                have hzero : ∀ t ∈ Z, p.2 + expSum (shiftDown (q :: rest') p.1) t = 0 := by
                  intro t ht
                  have h := hZ t ht
                  rw [expSum_cons_shiftDown] at h
                  rcases mul_eq_zero.mp h with h1 | h2
                  · exact absurd h1 (Real.exp_ne_zero _)
                  · exact h2
                -- the sign variations
                have hsvmain : listSignVariations ((p :: q :: rest').map Prod.snd)
                    = listSignVariations ((q :: rest').map Prod.snd)
                      + (if oppositeSigns p.2 q.2 then 1 else 0) := by
                  have h1 : (p :: q :: rest').map Prod.snd = p.2 :: q.2 :: (rest'.map Prod.snd) := rfl
                  have h2 : (q :: rest').map Prod.snd = q.2 :: (rest'.map Prod.snd) := rfl
                  rw [h1, h2]
                  exact listSignVariations_cons_cons p.2 q.2 _ hc1 hc2
                have hsvderiv : listSignVariations ((shiftDownDeriv (q :: rest') p.1).map Prod.snd)
                    = listSignVariations ((q :: rest').map Prod.snd) := by
                  rw [listSignVariations_eq_signsOfPairs, listSignVariations_eq_signsOfPairs]
                  congr 1
                  unfold signsOfPairs
                  have hkey : (shiftDownDeriv (q :: rest') p.1).map (fun p => SignType.sign (Prod.snd p))
                      = (q :: rest').map (fun r => SignType.sign (Prod.snd r)) := by
                    have h1 : shiftDownDeriv (q :: rest') p.1
                        = List.map (fun r => (r.1 - p.1, r.2 * (r.1 - p.1))) (q :: rest') := rfl
                    rw [h1, List.map_map]
                    apply List.map_congr_left
                    intro r hr
                    simp only [Function.comp_apply]
                    have hpos : 0 < r.1 - p.1 := by linarith [hcons.1 r hr]
                    rw [sign_mul]
                    have h2 : sign (r.1 - p.1) = 1 := sign_pos hpos
                    rw [h2, mul_one]
                  rw [hkey]
                -- the counting
                by_cases hZne : Z.Nonempty
                · have hRolle : ∀ x ∈ Z, x < Z.max' hZne → ∃ w, x < w ∧ w < nextOf Z x
                        ∧ expSum (shiftDownDeriv (q :: rest') p.1) w = 0 := by
                    intro x hx hlt
                    have hnx : nextOf Z x ∈ Z := nextOf_mem Z x hx
                    have hgz : p.2 + expSum (shiftDown (q :: rest') p.1) (nextOf Z x) = 0 :=
                      hzero _ hnx
                    have hff' : ∀ t ∈ Set.Ioo x (nextOf Z x),
                        HasDerivAt (fun s => p.2 + expSum (shiftDown (q :: rest') p.1) s)
                          (expSum (shiftDownDeriv (q :: rest') p.1) t) t := fun t ht => hderiv t
                    have hnext : x < nextOf Z x := by
                      by_cases h : (Z.filter (x < ·)).Nonempty
                      · rw [nextOf, dite_eq_left h]
                        exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
                      · exfalso
                        exact h ⟨Finset.max' _ hZne,
                          Finset.mem_filter.mpr ⟨Finset.max'_mem _ hZne, hlt⟩⟩
                    obtain ⟨w, hw1, hw2⟩ := exists_hasDerivAt_eq_zero
                      (f := fun s => p.2 + expSum (shiftDown (q :: rest') p.1) s)
                      (f' := fun t => expSum (shiftDownDeriv (q :: rest') p.1) t)
                      (a := x) (b := nextOf Z x)
                      (hab := hnext) (hfc := hcont.continuousOn)
                      (hfI := (hzero x hx).trans hgz.symm) hff'
                    exact ⟨w, hw1.1, hw1.2, hw2⟩
                  obtain ⟨T, hTzero, hTlow, hTcard, hTinter⟩ := rolle_points
                    (g' := fun t => expSum (shiftDownDeriv (q :: rest') p.1) t) hZne hRolle
                  have hcard : Z.card ≤ T.card + 1 := Finset.card_le_of_interleaved hTinter
                  have hTbound : T.card ≤ listSignVariations ((shiftDownDeriv (q :: rest') p.1).map Prod.snd) :=
                    ih (n - 1) (by omega) (shiftDownDeriv (q :: rest') p.1) hl3len hl3pair hl3coeff hl3ne T hTzero
                  by_cases hopp : oppositeSigns p.2 q.2
                  · -- the two leading coefficients have opposite signs: Rolle suffices
                    have : Z.card ≤ listSignVariations ((p :: q :: rest').map Prod.snd) := by
                      calc Z.card ≤ T.card + 1 := hcard
                        _ ≤ listSignVariations ((shiftDownDeriv (q :: rest') p.1).map Prod.snd) + 1 := by omega
                        _ = listSignVariations ((q :: rest').map Prod.snd) + 1 := by rw [hsvderiv]
                        _ = listSignVariations ((p :: q :: rest').map Prod.snd) := by
                          rw [hsvmain]
                          simp [hopp]
                    exact this
                  · -- the two leading coefficients have the same sign: an extra zero of the
                    -- derivative below the least zero is needed
                    have hsign : SignType.sign p.2 = SignType.sign q.2 := by
                      by_contra hcon
                      exact hopp ((oppositeSigns_iff hc1 hc2).mpr
                        ((sign_eq_sign_or_eq_neg hc1 hc2).resolve_left hcon))
                    -- the limit of `g` at `-∞`
                    have hlimg : Filter.Tendsto (fun t => p.2 + expSum (shiftDown (q :: rest') p.1) t)
                        Filter.atBot (𝓝 p.2) := by
                      have h1 : Filter.Tendsto (fun t => expSum (shiftDown (q :: rest') p.1) t)
                          Filter.atBot (𝓝 0) := by
                        apply tendsto_expSum_atBot
                        intro q' hq'
                        simp only [shiftDown, List.mem_map] at hq'
                        obtain ⟨r, hr, rfl⟩ := hq'
                        exact sub_pos.mpr (by linarith [hcons.1 r (by simp [hr])])
                      convert h1.const_add p.2 using 1 <;> simp
                    -- the limit of the scaled derivative at `-∞`
                    have hlimg' : Filter.Tendsto (fun t => expSum (shiftDownDeriv (q :: rest') p.1) t
                          * Real.exp (-((q.1 - p.1) * t))) Filter.atBot (𝓝 (q.2 * (q.1 - p.1))) := by
                      have hhead : shiftDownDeriv (q :: rest') p.1
                          = (q.1 - p.1, q.2 * (q.1 - p.1)) :: shiftDownDeriv rest' p.1 := rfl
                      rw [hhead]
                      apply tendsto_expSum_scaled
                      intro r' hr'
                      simp only [shiftDownDeriv, List.mem_map] at hr'
                      obtain ⟨r, hr, rfl⟩ := hr'
                      exact by linarith [hq' r hr]
                    obtain ⟨T1, hT1⟩ := exists_lt_of_tendsto_sign hc1 hlimg
                    obtain ⟨T2, hT2⟩ := exists_lt_of_tendsto_sign
                      (mul_ne_zero hc2 (ne_of_gt (sub_pos.mpr hlam))) hlimg'
                    have hsg' : ∀ t < T2, SignType.sign (expSum (shiftDownDeriv (q :: rest') p.1) t)
                        = SignType.sign q.2 := by
                      intro t ht
                      have h := hT2 t ht
                      have hexppos : 0 < Real.exp (-((q.1 - p.1) * t)) := Real.exp_pos _
                      have he1 : sign (Real.exp (-((q.1 - p.1) * t))) = 1 := sign_pos hexppos
                      rw [sign_mul, he1, mul_one] at h
                      have hpos : 0 < q.1 - p.1 := by linarith
                      have he2 : sign (q.1 - p.1) = 1 := sign_pos hpos
                      rw [sign_mul, he2, mul_one] at h
                      exact h
                    -- the least zero of `Z`
                    set zmin := Z.min' hZne with hzmin
                    obtain ⟨a, ha1, ha2, ha3⟩ : ∃ a, a < zmin ∧ a < T1 ∧ a < T2 := by
                      refine ⟨min zmin (min T1 T2) - 1, ?_, ?_, ?_⟩
                      · have h1 : min zmin (min T1 T2) ≤ zmin := min_le_left _ _
                        linarith
                      · have h1 : min zmin (min T1 T2) ≤ min T1 T2 := min_le_right _ _
                        have h2 : min T1 T2 ≤ T1 := min_le_left _ _
                        linarith
                      · have h1 : min zmin (min T1 T2) ≤ min T1 T2 := min_le_right _ _
                        have h2 : min T1 T2 ≤ T2 := min_le_right _ _
                        linarith
                    have hga : SignType.sign (p.2 + expSum (shiftDown (q :: rest') p.1) a)
                        = SignType.sign p.2 := hT1 a ha2
                    have hga' : SignType.sign (expSum (shiftDownDeriv (q :: rest') p.1) a)
                        = SignType.sign q.2 := hsg' a ha3
                    -- the mean value theorem on `[a, zmin]`
                    have hff'2 : ∀ t ∈ Set.Ioo a zmin,
                        HasDerivAt (fun s => p.2 + expSum (shiftDown (q :: rest') p.1) s)
                          (expSum (shiftDownDeriv (q :: rest') p.1) t) t := fun t ht => hderiv t
                    obtain ⟨s, hs, hsderiv⟩ := exists_hasDerivAt_eq_slope
                      (f := fun t => p.2 + expSum (shiftDown (q :: rest') p.1) t)
                      (f' := fun t => expSum (shiftDownDeriv (q :: rest') p.1) t)
                      (a := a) (b := zmin)
                      (by linarith) (hcont.continuousOn) hff'2
                    have hgz : p.2 + expSum (shiftDown (q :: rest') p.1) zmin = 0 :=
                      hzero _ (Finset.min'_mem _ hZne)
                    have hsderiv' : expSum (shiftDownDeriv (q :: rest') p.1) s
                        = (0 - (p.2 + expSum (shiftDown (q :: rest') p.1) a)) / (zmin - a) := by
                      rw [hsderiv, hgz]
                    -- the signs at `a` and at `s`
                    have hmain : (0 < p.2 + expSum (shiftDown (q :: rest') p.1) a ∧
                              0 < expSum (shiftDownDeriv (q :: rest') p.1) a ∧
                              expSum (shiftDownDeriv (q :: rest') p.1) s < 0) ∨
                              (p.2 + expSum (shiftDown (q :: rest') p.1) a < 0 ∧
                              expSum (shiftDownDeriv (q :: rest') p.1) a < 0 ∧
                              0 < expSum (shiftDownDeriv (q :: rest') p.1) s) := by
                      by_cases hq2pos : 0 < q.2
                      · left
                        have hsgq : SignType.sign q.2 = 1 := sign_eq_one_iff.mpr hq2pos
                        have hsgp : SignType.sign p.2 = 1 := hsign.trans hsgq
                        have hsg1 : SignType.sign (p.2 + expSum (shiftDown (q :: rest') p.1) a) = 1 :=
                          hga.trans hsgp
                        have hsg2 : SignType.sign (expSum (shiftDownDeriv (q :: rest') p.1) a) = 1 :=
                          hga'.trans hsgq
                        have hga_pos : 0 < p.2 + expSum (shiftDown (q :: rest') p.1) a :=
                          sign_eq_one_iff.mp hsg1
                        have hga'_pos : 0 < expSum (shiftDownDeriv (q :: rest') p.1) a :=
                          sign_eq_one_iff.mp hsg2
                        refine ⟨hga_pos, hga'_pos, ?_⟩
                        rw [hsderiv']
                        have h1 : 0 - (p.2 + expSum (shiftDown (q :: rest') p.1) a) < 0 := by linarith
                        have h2 : 0 < zmin - a := by linarith
                        exact (div_neg_iff).2 (Or.inr ⟨h1, h2⟩)
                      · right
                        have hsgq : SignType.sign q.2 = -1 := by
                          refine sign_eq_neg_one_iff.mpr ?_
                          rcases lt_trichotomy q.2 0 with h | h | h
                          · exact h
                          · exact absurd h hc2
                          · exact absurd h hq2pos
                        have hsgp : SignType.sign p.2 = -1 := hsign.trans hsgq
                        have hsg1 : SignType.sign (p.2 + expSum (shiftDown (q :: rest') p.1) a) = -1 :=
                          hga.trans hsgp
                        have hsg2 : SignType.sign (expSum (shiftDownDeriv (q :: rest') p.1) a) = -1 :=
                          hga'.trans hsgq
                        have hga_neg : p.2 + expSum (shiftDown (q :: rest') p.1) a < 0 :=
                          sign_eq_neg_one_iff.mp hsg1
                        have hga'_neg : expSum (shiftDownDeriv (q :: rest') p.1) a < 0 :=
                          sign_eq_neg_one_iff.mp hsg2
                        refine ⟨hga_neg, hga'_neg, ?_⟩
                        rw [hsderiv']
                        have h1 : 0 < 0 - (p.2 + expSum (shiftDown (q :: rest') p.1) a) := by linarith
                        have h2 : 0 < zmin - a := by linarith
                        exact (div_pos_iff).2 (Or.inl ⟨h1, h2⟩)
                    -- the intermediate value theorem gives an extra zero of the derivative
                    have h0 : min (expSum (shiftDownDeriv (q :: rest') p.1) a)
                        (expSum (shiftDownDeriv (q :: rest') p.1) s) ≤ 0 ∧
                        0 ≤ max (expSum (shiftDownDeriv (q :: rest') p.1) a)
                          (expSum (shiftDownDeriv (q :: rest') p.1) s) := by
                      rcases hmain with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
                      · rw [min_eq_right (le_of_lt (lt_of_lt_of_le h3 h2.le)),
                          max_eq_left (le_of_lt (lt_of_lt_of_le h3 h2.le))]
                        exact ⟨le_of_lt h3, le_of_lt h2⟩
                      · rw [min_eq_left (le_of_lt (lt_of_lt_of_le h2 h3.le)),
                          max_eq_right (le_of_lt (lt_of_lt_of_le h2 h3.le))]
                        exact ⟨le_of_lt h2, le_of_lt h3⟩
                    obtain ⟨w, hwmem, hw0⟩ := exists_eq_zero_of_continuousOn (by linarith [hs.1])
                      hcont'.continuousOn h0
                    have hwzero : expSum (shiftDownDeriv (q :: rest') p.1) w = 0 := hw0
                    have hwin : w < zmin := by
                      have hw1 : a ≤ w := hwmem.1
                      have hw2 : w ≤ s := hwmem.2
                      have hslt : s < zmin := hs.2
                      linarith
                    -- the counting with the extra zero: the Rolle points together with `w`
                    -- give as many zeros of the derivative as there are zeros of `g`
                    have hwnotT : w ∉ T := by
                      intro hwT
                      have : zmin < w := hTlow w hwT
                      exact (not_lt_of_ge (le_of_lt hwin)) this
                    have hZcard : Z.card = (Z.erase (Z.max' hZne)).card + 1 := by
                      rw [Finset.card_erase_of_mem (Finset.max'_mem _ hZne)]
                      symm
                      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hZne))
                    have hT'card : (insert w T).card = Z.card := by
                      rw [Finset.card_insert_of_notMem hwnotT, hTcard, hZcard]
                    have hT'zero : ∀ t ∈ insert w T, expSum (shiftDownDeriv (q :: rest') p.1) t = 0 := by
                      intro t ht
                      rcases Finset.mem_insert.mp ht with rfl | ht
                      · exact hwzero
                      · exact hTzero t ht
                    have hTbound' : (insert w T).card
                        ≤ listSignVariations ((shiftDownDeriv (q :: rest') p.1).map Prod.snd) :=
                      ih (n - 1) (by omega) (shiftDownDeriv (q :: rest') p.1) hl3len hl3pair hl3coeff hl3ne
                        (insert w T) hT'zero
                    have : Z.card ≤ listSignVariations ((p :: q :: rest').map Prod.snd) := by
                      calc Z.card = (insert w T).card := hT'card.symm
                        _ ≤ listSignVariations ((shiftDownDeriv (q :: rest') p.1).map Prod.snd) := hTbound'
                        _ = listSignVariations ((q :: rest').map Prod.snd) := hsvderiv
                        _ = listSignVariations ((p :: q :: rest').map Prod.snd) := by
                          rw [hsvmain]
                          simp [hopp]
                    exact this
                · -- no zeros at all
                  have hZempty : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZne
                  have hcard : Z.card = 0 := Finset.card_eq_zero.mpr hZempty
                  have : Z.card ≤ listSignVariations ((p :: q :: rest').map Prod.snd) := by
                    rw [hsvmain]
                    simp [hZempty]
                  exact this



/-! ### The generalized Descartes rule for exponential sums -/

theorem pairSum_eq_sum_map (l : List (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    pairSum l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      rw [pairSum_cons, List.map_cons, List.sum_cons, ih]

theorem sum_fin_eq_list_sum (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∑ k, f k) = ((List.finRange (n + 1)).map f).sum := by
  rw [← List.sum_toFinset (f := f) (l := List.finRange (n + 1)) (List.nodup_finRange _)]
  congr 1
  ext k
  simp

theorem fin_succ_lt_succ {n : ℕ} {a b : Fin n} (h : a < b) : Fin.succ a < Fin.succ b := by
  rw [Fin.lt_def] at h ⊢
  simp only [Fin.val_succ] at *
  omega

theorem fin_zero_lt_succ {n : ℕ} (b : Fin n) : (0 : Fin (n + 1)) < Fin.succ b := by
  rw [Fin.lt_def]
  have h1 : ((0 : Fin (n + 1)) : ℕ) = 0 := by rw [← Fin.zero_eta]
  rw [h1]
  simp only [Fin.val_succ]
  omega

theorem pairwise_finRange_lt {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : StrictMono w) :
    (List.finRange (n + 1)).Pairwise (fun i j : Fin (n + 1) => w i < w j) := by
  induction n with
  | zero =>
      rw [List.finRange_succ]
      simp only [List.finRange_zero, List.map_nil]
      exact List.Pairwise.cons (fun a ha => absurd ha (by simp)) List.Pairwise.nil
  | succ n ih =>
      rw [List.finRange_succ]
      refine List.Pairwise.cons (fun a ha => ?_) ?_
      · rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
        exact hw (fin_zero_lt_succ b)
      · rw [List.pairwise_map]
        exact ih (fun k => w k.succ) (fun a b hab => hw (fin_succ_lt_succ hab))

theorem dropZeroCoeffs_coeff_ne_zero (l : List (ℝ × ℝ)) : ∀ p ∈ dropZeroCoeffs l, p.2 ≠ 0 := by
  induction l with
  | nil => intro p hp; rw [dropZeroCoeffs] at hp; simp at hp
  | cons q rest ih =>
      rw [dropZeroCoeffs]
      by_cases h : q.2 = 0
      · rw [ite_eq_left h]
        exact ih
      · rw [ite_eq_right h]
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact h
        · exact ih p hp

/-- **Generalized Descartes rule (list form).**  The number of distinct real zeros of the
exponential sum `∑ c_k e^{λ_k t}` (with `λ_0 < λ_1 < ⋯` and `c_k` the coefficients) is at most the
number of sign variations of the coefficient list. -/
theorem card_zeros_expSum_le (l : List (ℝ × ℝ)) (hl : l.Pairwise fun p q => p.1 < q.1)
    (hn : ∃ p ∈ l, p.2 ≠ 0) (Z : Finset ℝ) (hZ : ∀ t ∈ Z, expSum l t = 0) :
    Z.card ≤ listSignVariations (l.map Prod.snd) := by
  have hl'ne : dropZeroCoeffs l ≠ [] := dropZeroCoeffs_ne_nil l hn
  have hl'pair : (dropZeroCoeffs l).Pairwise (fun p q => p.1 < q.1) := dropZeroCoeffs_pairwise hl
  have hl'coeff : ∀ p ∈ dropZeroCoeffs l, p.2 ≠ 0 := dropZeroCoeffs_coeff_ne_zero l
  have hZ' : ∀ t ∈ Z, expSum (dropZeroCoeffs l) t = 0 := by
    intro t ht
    rw [expSum_dropZeroCoeffs l t]
    exact hZ t ht
  have hres := card_zeros_expSum_le_aux (dropZeroCoeffs l).length (dropZeroCoeffs l) rfl hl'pair hl'coeff
    hl'ne Z hZ'
  rw [listSignVariations_dropZeroCoeffs l] at hres
  exact hres

/-- The exponential sum of the list of pairs attached to a `Fin`-indexed family. -/
theorem expSum_finRange_map (n : ℕ) (w : Fin (n + 1) → ℝ) (c : Fin (n + 1) → ℝ) (t : ℝ) :
    expSum ((List.finRange (n + 1)).map (fun k => (w k, c k))) t = ∑ k, c k * Real.exp (w k * t) := by
  rw [expSum, pairSum_eq_sum_map]
  simp only [List.map_map, Function.comp_def]
  have h2 : (List.finRange (n + 1)).map (fun k => (w k, c k).2 * Real.exp ((w k, c k).1 * t))
      = (List.finRange (n + 1)).map (fun k => c k * Real.exp (w k * t)) := by
    apply List.map_congr_left
    intro k hk
    simp
  rw [h2]
  rw [← List.sum_toFinset (f := fun k => c k * Real.exp (w k * t)) (l := List.finRange (n + 1))
    (List.nodup_finRange _)]
  rw [sum_fin_eq_list_sum]
  rw [List.sum_toFinset (f := fun k => c k * Real.exp (w k * t)) (l := List.finRange (n + 1))
    (List.nodup_finRange _)]

/-- **Generalized Descartes rule for exponential sums.**  Let `w_0 < w_1 < ⋯ < w_n` be real
exponents and `c_0, …, c_n` real coefficients, not all zero.  Then the number of *distinct* real
zeros of `Φ t = ∑_k c_k e^{w_k t}` is at most the number of sign variations of
`(c_0, …, c_n)`.

This is Descartes' rule of signs for exponential sums (equivalently, for generalized polynomials
`g(y) = ∑_k c_k y^{w_k}`, since `Φ t = g(e^t)`). -/
theorem card_zeros_exp_sum_le {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : StrictMono w)
    (c : Fin (n + 1) → ℝ) (hc : ∃ k, c k ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, ∑ k, c k * Real.exp (w k * t) = 0) :
    Z.card ≤ signVariations c := by
  have hlpair : ((List.finRange (n + 1)).map (fun k => (w k, c k))).Pairwise
      (fun p q => p.1 < q.1) := by
    rw [List.pairwise_map]
    exact pairwise_finRange_lt w hw
  have hlnon : ∃ p ∈ (List.finRange (n + 1)).map (fun k => (w k, c k)), p.2 ≠ 0 := by
    rcases hc with ⟨k, hk⟩
    refine ⟨(w k, c k), ?_, hk⟩
    simp only [List.mem_map]
    exact ⟨k, Finset.mem_univ k, rfl⟩
  have hZ' : ∀ t ∈ Z, expSum ((List.finRange (n + 1)).map (fun k => (w k, c k))) t = 0 := by
    intro t ht
    rw [expSum_finRange_map]
    exact hZ t ht
  have hres := card_zeros_expSum_le ((List.finRange (n + 1)).map (fun k => (w k, c k))) hlpair hlnon Z hZ'
  have hsv : listSignVariations
      (((List.finRange (n + 1)).map (fun k => (w k, c k))).map Prod.snd) = signVariations c := by
    simp only [List.map_map]
    rfl
  rw [hsv] at hres
  exact hres

/-- **Descartes' rule of signs for generalized polynomials.**  The number of positive roots of
`g(y) = ∑_k c_k y^{w_k}` (with real exponents `w_0 < w_1 < ⋯ < w_n`) is at most the number of
sign variations of the coefficients `(c_k)`. -/
theorem card_pos_roots_exp_le_signVariations {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : StrictMono w)
    (c : Fin (n + 1) → ℝ) (hc : ∃ k, c k ≠ 0) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, 0 < y ∧ ∑ k, c k * y ^ w k = 0) :
    Y.card ≤ signVariations c := by
  set T : Finset ℝ := Y.image Real.log with hT
  have hcard : Y.card = T.card := by
    rw [hT]
    symm
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    exact Real.log_injOn_pos (hY x hx).1 (hY y hy).1 hxy
  have hzero : ∀ t ∈ T, ∑ k, c k * Real.exp (w k * t) = 0 := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    have hy0 : 0 < y := (hY y hy).1
    have h2 := (hY y hy).2
    simp only [Real.rpow_def_of_pos hy0] at h2
    simpa [mul_comm] using h2
  have hres := card_zeros_exp_sum_le w hw c hc T hzero
  rw [← hcard] at hres
  exact hres

end CircuitDescartes
end CRNT

/-! ### The sign-variation refinement of Bihan's bound for circuits -/

namespace CRNT
namespace Circuit

open Polynomial Finset Set

/-- **Descartes' rule of signs (polynomial form).**  The number of *distinct* positive roots of a
real polynomial `P` is at most the number of sign variations of its coefficients. -/
theorem card_le_signVariations_roots {P : Polynomial ℝ} {R : Finset ℝ}
    (hR : ∀ r ∈ R, r ∈ P.roots) (hr : ∀ r ∈ R, 0 < r) :
    R.card ≤ P.signVariations := by
  have hsub : R ⊆ (P.roots.filter (0 < ·)).toFinset := by
    intro r hrR
    simp only [Multiset.mem_toFinset]
    exact Multiset.mem_filter.mpr ⟨hR r hrR, hr r hrR⟩
  have hcard : R.card ≤ (P.roots.filter (0 < ·)).toFinset.card := Finset.card_le_card hsub
  calc R.card ≤ (P.roots.filter (0 < ·)).toFinset.card := hcard
    _ ≤ (P.roots.filter (0 < ·)).card := Multiset.toFinset_card_le _
    _ = P.roots.countP (0 < ·) := (Multiset.countP_eq_card_filter (0 < ·) (P.roots)).symm
    _ ≤ P.signVariations := Polynomial.roots_countP_pos_le_signVariations P

/-- **The sign-variation refinement of the `n + 1` bound.**  The number of zeros of the log-affine
function `φ` of a circuit is at most the number of sign variations of the coefficients of the
numerator polynomial `circuitPoly`, plus one.  (The plain `n + 1` bound is
`card_log_affine_zeros_le`.) -/
theorem card_log_affine_zeros_le_signVariations (p q μ : Fin n → ℝ) (hP : circuitPoly p q μ ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, t ∈ admissible p q ∧ phi p q μ t = 0) :
    Z.card ≤ Polynomial.signVariations (circuitPoly p q μ) + 1 := by
  set T : Finset ℝ := (circuitPoly p q μ).roots.filter (0 < ·) |>.toFinset with hT
  have hinter : ∀ x ∈ Z, ∀ y ∈ Z, x < y → (∀ z ∈ Z, z ∉ Set.Ioo x y) → ∃ z ∈ T, x < z ∧ z < y := by
    intro x hx y hy hxy hconc
    have hxI := (hZ x hx).1
    have hyI := (hZ y hy).1
    have hseg : Icc x y ⊆ admissible p q :=
      (convex_admissible p q).segment_subset hxI hyI |>.trans' (by
        rw [segment_eq_Icc hxy.le])
    have hcont : ContinuousOn (phi p q μ) (Icc x y) := fun t ht =>
      (hasDerivAt_phi p q μ (hseg ht)).continuousAt.continuousWithinAt
    have heq : phi p q μ x = phi p q μ y := by rw [(hZ x hx).2, (hZ y hy).2]
    obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hxy hcont heq
    have hcI : c ∈ admissible p q := hseg (Ioo_subset_Icc_self hc)
    have hd := (hasDerivAt_phi p q μ hcI).deriv
    rw [hdc] at hd
    refine ⟨c, ?_, hc.1, hc.2⟩
    rw [hT]
    simp only [Multiset.mem_toFinset]
    exact Multiset.mem_filter.mpr ⟨by
      rw [mem_roots hP, IsRoot]
      exact circuitPoly_eval_eq_zero p q μ hcI hd.symm, hcI.1⟩
  have hcard : Z.card ≤ T.card + 1 := Finset.card_le_of_interleaved hinter
  have hTcard : T.card ≤ Polynomial.signVariations (circuitPoly p q μ) := by
    rw [hT]
    refine card_le_signVariations_roots (P := circuitPoly p q μ) ?_ ?_
    · intro r hr
      have h1 := Multiset.mem_toFinset.mp hr
      have h2 := Multiset.mem_filter.mp h1
      exact h2.1
    · intro r hr
      have h1 := Multiset.mem_toFinset.mp hr
      have h2 := Multiset.mem_filter.mp h1
      exact h2.2
  omega

/-- **The sign-variation refinement of Bihan's bound for circuit systems.**  The number of positive
solutions of a circuit system `C y + c₀ + y^μ c₁ = 0` (in the normal form of
`card_circuit_solutions_le`) is at most the number of sign variations of the coefficients of the
numerator polynomial `circuitPoly`, plus one.  In particular it is at most `n + 1`, and it is
strictly smaller when the numerator polynomial has few sign variations. -/
theorem card_circuit_solutions_le_signVariations (Cm : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit Cm.det)
    (c₀ c₁ μ : Fin n → ℝ)
    (hP : circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ ≠ 0)
    (Y : Finset (Fin n → ℝ))
    (hY : ∀ y ∈ Y, (∀ k, 0 < y k) ∧ Cm.mulVec y + c₀ + rmono μ y • c₁ = 0) :
    Y.card ≤ Polynomial.signVariations (circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ) + 1 := by
  classical
  set p : Fin n → ℝ := -(Cm⁻¹.mulVec c₀) with hp
  set q : Fin n → ℝ := -(Cm⁻¹.mulVec c₁) with hq
  have hsol : ∀ y ∈ Y, y = p + rmono μ y • q := by
    intro y hy
    have h := (hY y hy).2
    have hy' : Cm.mulVec y = -(c₀ + rmono μ y • c₁) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact h
    have hinv : Cm⁻¹ * Cm = 1 := Matrix.nonsing_inv_mul Cm hC
    calc y = (Cm⁻¹ * Cm).mulVec y := by rw [hinv, Matrix.one_mulVec]
      _ = Cm⁻¹.mulVec (Cm.mulVec y) := by rw [Matrix.mulVec_mulVec]
      _ = p + rmono μ y • q := by
        rw [hy', Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_smul, hp, hq]
        simp only [neg_add, smul_neg]
  have hpos : ∀ y ∈ Y, 0 < rmono μ y := fun y hy =>
    Finset.prod_pos fun k _ => Real.rpow_pos_of_pos ((hY y hy).1 k) _
  have hcoord : ∀ y ∈ Y, ∀ k, y k = p k + rmono μ y * q k := by
    intro y hy k
    have := congrFun (hsol y hy) k
    simpa using this
  have hinj : Set.InjOn (rmono μ) Y := by
    intro y hy y' hy' h
    rw [hsol y hy, hsol y' hy', h]
  have hZ : ∀ t ∈ Y.image (rmono μ), t ∈ admissible p q ∧ phi p q μ t = 0 := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨⟨hpos y hy, fun k => ?_⟩, ?_⟩
    · rw [← hcoord y hy k]; exact (hY y hy).1 k
    · unfold phi
      have hlog : Real.log (rmono μ y) = ∑ k, μ k * Real.log (y k) := by
        unfold rmono
        rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos ((hY y hy).1 k) _).ne']
        exact Finset.sum_congr rfl fun k _ => by
          rw [Real.log_rpow ((hY y hy).1 k)]
      rw [hlog]
      have : ∀ k, Real.log (p k + rmono μ y * q k) = Real.log (y k) := fun k => by
        rw [← hcoord y hy k]
      simp only [this, sub_self]
  have h := card_log_affine_zeros_le_signVariations p q μ hP (Y.image (rmono μ)) hZ
  rwa [Finset.card_image_of_injOn hinj] at h

end Circuit
end CRNT


/-! ### Examples: the sign-variation bound for generalized polynomials -/

namespace CRNT
namespace CircuitDescartes
namespace Example

/-- The coefficients `1, -1, 1` (in the order of the exponents `0 < 1 < 2`). -/
def coeffsAlt : Fin 3 → ℝ := fun | 0 => 1 | 1 => -1 | 2 => 1

/-- The coefficients `1, 1, -1`. -/
def coeffsPos : Fin 3 → ℝ := fun | 0 => 1 | 1 => 1 | 2 => -1

/-- The exponents `0 < 1 < 2`. -/
def exps : Fin 3 → ℝ := fun | 0 => 0 | 1 => 1 | 2 => 2

theorem strictMono_exps : StrictMono exps := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [exps, Fin.lt_def]

/-- The coefficients `1, -1, 1` have **two** sign variations. -/
theorem signVariations_coeffsAlt : signVariations coeffsAlt = 2 := by
  unfold signVariations
  rw [show (List.finRange (2 + 1)).map coeffsAlt = [1, -1, 1] by rfl]
  rw [listSignVariations_cons_cons 1 (-1) [1] (by norm_num) (by norm_num)]
  rw [listSignVariations_cons_cons (-1) 1 [] (by norm_num) (by norm_num)]
  norm_num [oppositeSigns, listSignVariations_singleton]

/-- The coefficients `1, 1, -1` have **one** sign variation. -/
theorem signVariations_coeffsPos : signVariations coeffsPos = 1 := by
  unfold signVariations
  rw [show (List.finRange (2 + 1)).map coeffsPos = [1, 1, -1] by rfl]
  rw [listSignVariations_cons_cons 1 1 [-1] (by norm_num) (by norm_num)]
  rw [listSignVariations_cons_cons 1 (-1) [] (by norm_num) (by norm_num)]
  norm_num [oppositeSigns, listSignVariations_singleton]

/-- The generalized polynomial with coefficients `1, -1, 1` is `g(y) = 1 - y + y²`. -/
theorem gAlt_eq : ∀ y : ℝ, (∑ k, coeffsAlt k * y ^ exps k) = 1 - y + y ^ 2 := by
  intro y
  rw [Fin.sum_univ_three]
  simp only [coeffsAlt, exps]
  rw [Real.rpow_zero, Real.rpow_one, Real.rpow_two, one_mul]
  ring

/-- The generalized polynomial with coefficients `1, 1, -1` is `h(y) = 1 + y - y²`. -/
theorem gPos_eq : ∀ y : ℝ, (∑ k, coeffsPos k * y ^ exps k) = 1 + y - y ^ 2 := by
  intro y
  rw [Fin.sum_univ_three]
  simp only [coeffsPos, exps]
  rw [Real.rpow_zero, Real.rpow_one, Real.rpow_two, one_mul]
  ring

/-- **The generalized polynomial `1 - y + y²` has no positive root** (its discriminant is
negative), consistently with the two sign variations of its coefficients. -/
theorem no_pos_root : ∀ y : ℝ, 0 < y → 1 - y + y ^ 2 ≠ 0 := by
  intro y hy h0
  have h1 : 0 < 1 - y + y ^ 2 := by
    nlinarith [sq_nonneg (y - 1 / 2)]
  linarith

/-- **The generalized polynomial `1 + y - y²` has the positive root `(1 + √5)/2`**, so the bound
"one sign variation ⇒ at most one positive root" is attained. -/
theorem one_pos_root :
    0 < (1 + Real.sqrt 5) / 2 ∧ 1 + (1 + Real.sqrt 5) / 2 - ((1 + Real.sqrt 5) / 2) ^ 2 = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor
  · have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · have h6 : ((1 + Real.sqrt 5) / 2) ^ 2 = 1 + (1 + Real.sqrt 5) / 2 := by
      field_simp
      nlinarith [h5]
    rw [h6]
    ring

/-- **Descartes' rule for `1 - y + y²`.**  At most two positive roots. -/
theorem descartes_alt : ∀ (Y : Finset ℝ), (∀ y ∈ Y, 0 < y ∧ ∑ k, coeffsAlt k * y ^ exps k = 0) →
    Y.card ≤ 2 := by
  intro Y hY
  have h := card_pos_roots_exp_le_signVariations exps strictMono_exps coeffsAlt
    ⟨0, by simp [coeffsAlt]⟩ Y hY
  rw [signVariations_coeffsAlt] at h
  exact h

/-- **Descartes' rule for `1 + y - y²`.**  At most one positive root. -/
theorem descartes_pos : ∀ (Y : Finset ℝ), (∀ y ∈ Y, 0 < y ∧ ∑ k, coeffsPos k * y ^ exps k = 0) →
    Y.card ≤ 1 := by
  intro Y hY
  have h := card_pos_roots_exp_le_signVariations exps strictMono_exps coeffsPos
    ⟨0, by simp [coeffsPos]⟩ Y hY
  rw [signVariations_coeffsPos] at h
  exact h

/-- The bound of `descartes_pos` is attained: the singleton `{(1 + √5)/2}` is a set of positive
roots of `1 + y - y²`. -/
theorem descartes_pos_attained :
    ({(1 + Real.sqrt 5) / 2} : Finset ℝ).card = 1 ∧
      ∀ y ∈ ({(1 + Real.sqrt 5) / 2} : Finset ℝ),
        0 < y ∧ ∑ k, coeffsPos k * y ^ exps k = 0 := by
  constructor
  · simp
  · intro y hy
    simp only [Finset.mem_singleton] at hy
    subst hy
    refine ⟨one_pos_root.1, ?_⟩
    rw [gPos_eq]
    exact one_pos_root.2

end Example
end CircuitDescartes
end CRNT
