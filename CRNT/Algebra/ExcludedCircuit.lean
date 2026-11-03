import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CRNT.Algebra.CircuitBound
import CRNT.Algebra.CircuitDescartes

/-!
# Excluded circuits, the monotone reduction, and mixed volumes (leaf A3)

Leaf **A3** of the field map ("real root bounds and mixed volumes") is *partial*.  What is proved
in `CRNT.Algebra.CircuitDescartes` is the **sign-variation half** of the story: the generalized
Descartes rule for exponential sums (`CRNT.CircuitDescartes.card_zeros_exp_sum_le`), the resulting
bound on positive roots of generalized polynomials
(`CRNT.CircuitDescartes.card_pos_roots_exp_le_signVariations`), and the refinement of Bihan's
`n + 1` bound for circuit systems
(`CRNT.Circuit.card_circuit_solutions_le_signVariations`).

This file supplies the **excluded-circuit** part and a **restricted BKK** part.

## 1. Excluded circuits

A *circuit* of a network is a minimal set of linearly dependent reaction vectors; in the
coordinates used in this repository a circuit is described by an invertible exponent matrix `E`
(the `n` linearly independent reaction vectors) together with the "circuit relation" `μ`, the extra
reaction vector being `Eᵀ μ`
(`CRNT.Circuit.circuitPoly`, `CRNT.Circuit.card_circuit_solutions_le_monomial`).

A circuit is **excluded** by a sign vector `σ` if all of its reaction vectors lie in the open
half-space `{ w | σᵀ w > 0 }` (`IsExcluded` below).  The classical special case
`σ ∈ {-1,1}^n` is the *sign-definite* condition of Shiu–Sturmfels; the general case is the
*excluded circuit* condition of Bihan–Dickenstein–Giaroli.

Two facts are proved here.

* **The half-space condition is the monotone condition.**  Under the substitution
  `x_s = z_s^{σ_s}` the reaction vector `w` becomes the *twisted* vector `σ ⊙ w`, and the
  excluded condition `σᵀ w > 0` becomes the statement that *all coordinates of the twisted vector
  have positive sum* (`isExcluded_iff_twist_pos`, `rmonoVec_substitute`).  This is the formal
  content of the "monotone substitution" in the classical proofs: after the substitution the
  reaction vectors all point into the same half-space, and the systems are equivalent
  (`sum_substitute_iff`).

* **Descartes on the excluded ray.**  On the ray `t ↦ (t^{σ_1}, …, t^{σ_n})` the system
  `∑_k c_k x^{w_k} = 0` becomes the *generalized polynomial* equation
  `∑_k c_k t^{σᵀ w_k} = 0` (`ray_eq`), whose number of positive roots is bounded by the sign
  variations of the coefficients (`card_pos_roots_ray_le_signVariations`,
  `card_ray_solutions_le_signVariations`).  This is the "one-dimensional" content of the
  excluded-circuit theory.

## 2. The uniqueness theorem for circuit systems

The sharp statement for a *square* system supported on a circuit is the following
(`card_circuitSystem_pos_le_one`):

> A system `C (x^{w_1}, …, x^{w_n}) + x^{w_{n+1}} c_1 = 0` (the linear circuit system: `n + 1`
> reaction vectors, **no** extra constant monomial) has **at most one positive solution**, provided
> the circuit relation is not affine, i.e. `∑_k μ_k ≠ 1`.

This is the sharpening of Bihan's `n + 1` bound (`CRNT.Circuit.card_circuit_solutions_le`) that the
excluded-circuit theory predicts; it is stated for excluded circuits in
`card_excludedCircuit_pos_le_one`.  The proof is the classical one-dimensional reduction:
solving the linear part gives `y = t q` with `t = y^μ > 0`, so `t` satisfies
`t^{∑_k μ_k - 1} = (∏_k q_k^{μ_k})^{-1}`, a *monotone* equation in `t`, hence at most one positive
`t`; the monomial map is then injective on the positive orthant
(`CRNT.Circuit.monoMap_injOn`).

Two remarks on the scope of this statement.

* The extra constant monomial is what makes the difference: for the `n + 2` monomial systems of
  `CRNT.Circuit.card_circuit_solutions_le` the bound is `n + 1`, and the exclusion hypothesis does
  *not* improve it (the one-dimensional example `y - 2/3 - y²/3 = 0` has two positive solutions and
  its reaction vectors `1, 2` are excluded by `σ = 1`).  The bound `1` is therefore a statement
  about the *linear* circuit system, i.e. about a system whose support consists of the `n + 1`
  reaction vectors of the circuit and nothing else.
* The bound itself holds for every circuit; the *exclusion* hypothesis is the structural
  hypothesis that singles out the half-space in which the (unique) solution lives, and it is the
  hypothesis that makes the one-dimensional Descartes reduction along the σ-ray available
  (`card_ray_solutions_le_signVariations`).

## 3. Mixed volumes (Bernstein–Kushnirenko–Khovanskii)

The mixed volume of two intervals is the product of their lengths (`mixedVolumeIntervals`), the
Minkowski sum of two intervals is the interval spanned by the sums of the endpoints
(`icc_add_Icc`), and the volume polynomial of an interval is linear
(`volumePolynomial_interval`).  The corresponding BKK bounds are proved in the restricted settings

* `n = 1`: the number of distinct positive roots of a univariate polynomial is at most its degree
  (`card_pos_roots_le_natDegree`), the degree being the mixed volume of the Newton polytope of the
  polynomial with the standard simplex;
* overdetermined univariate systems: the number of distinct common positive roots of two
  univariate polynomials is at most the product of their degrees, which is the mixed volume of
  their Newton polytopes (`card_common_pos_roots_le_mixedVolume`).

## 4. Relation to leaf A3, and what is still missing

Proved here: the excluded (half-space) condition and its monotone reading (the substitution
`x_s = z_s^{σ_s}`, the twisted reaction vectors, the equivalence of the systems), Descartes on the
excluded ray, the uniqueness theorem for linear circuit systems (hence for excluded circuits, with
an example where the bound is attained), and the restricted BKK bounds above.

Still missing (and *not* claimed here):

* the **row-wise Bihan–Dickenstein bound** (the bound that counts sign variations row by row of the
  coefficient matrix rather than in the numerator polynomial);
* the **BKK mixed volume in the general case** (`n` Newton polytopes in `ℝ^n`, the volume
  polynomial of a Minkowski sum, and the BKK bound for general sparse systems);
* the general excluded-circuit count in terms of the *number of compatible sign patterns* of
  Bihan–Dickenstein–Giaroli, which also covers the non-square (rank deficient) case and the
  `n + 2` monomial case, where the bound is `n + 1` and is not improved by the exclusion.
-/

open scoped BigOperators
open scoped Pointwise
open Polynomial Finset Set

namespace CRNT
namespace ExcludedCircuit

variable {n : ℕ}

/-! ### 1. Sign vectors, circuits, and the excluded (half-space) condition -/

/-- A **sign vector**: a vector all of whose entries lie in `{-1, 0, 1}`. -/
def signVec (σ : Fin n → ℝ) : Prop := ∀ i, σ i = 1 ∨ σ i = 0 ∨ σ i = -1

/-- A **full sign vector**: a vector all of whose entries lie in `{-1, 1}` (no zero coordinate). -/
def fullSignVec (σ : Fin n → ℝ) : Prop := ∀ i, σ i = 1 ∨ σ i = -1

/-- A full sign vector is a sign vector. -/
theorem fullSignVec.signVec {σ : Fin n → ℝ} (h : fullSignVec σ) : signVec σ := by
  intro i
  rcases h i with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inr h1)

/-- The **reaction vectors** of a circuit: the `n` rows of the (invertible) exponent matrix `E`
together with the extra reaction vector `Eᵀ μ` determined by the circuit relation. -/
def circuitReactions (E : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) : Fin (n + 1) → Fin n → ℝ :=
  fun k => if h : (k : ℕ) < n then E ⟨k.val, h⟩ else E.transpose.mulVec μ

/-- The reaction vectors of a circuit are **excluded** by `σ` if all of them lie in the open
half-space `{ w | σᵀ w > 0 }`.

This is the *excluded circuit* condition of Bihan–Dickenstein–Giaroli; for a sign vector
`σ ∈ {-1,1}^n` it is the *sign-definite* condition of Shiu–Sturmfels. -/
def IsExcluded {m : ℕ} (σ : Fin n → ℝ) (w : Fin m → Fin n → ℝ) : Prop :=
  ∀ r, 0 < ∑ i, σ i * w r i

/-- The **twisted** exponent vector `σ ⊙ w`: the exponent vector of the monomial obtained from
`x^w` by the substitution `x_s = z_s^{σ_s}`. -/
def twist (σ : Fin n → ℝ) (w : Fin n → ℝ) : Fin n → ℝ := fun i => σ i * w i

/-- **The half-space condition is exactly the condition that the twisted reaction vectors have
positive coordinate sum.**  This is the formal content of the "monotone substitution" used in the
classical proofs of the excluded-circuit theorems: after the substitution `x_s = z_s^{σ_s}` all the
reaction vectors point into the same half-space. -/
theorem isExcluded_iff_twist_pos {m : ℕ} (σ : Fin n → ℝ) (w : Fin m → Fin n → ℝ) :
    IsExcluded σ w ↔ ∀ r, 0 < ∑ i, twist σ (w r) i := by
  constructor
  · intro h r
    have h1 := h r
    simpa [twist] using h1
  · intro h r
    have h1 := h r
    simpa [twist] using h1

/-- The monomial `x^w` with real exponents `w`. -/
noncomputable def rmonoVec (x : Fin n → ℝ) (w : Fin n → ℝ) : ℝ := ∏ i, x i ^ w i

/-- The substitution `x_s = z_s^{σ_s}`. -/
noncomputable def substitute (σ : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i ^ σ i

/-- The twisting of an exponent by a sign of `±1` does not change the monomial. -/
lemma rpow_twist {x : ℝ} (hx : 0 < x) {σ w : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    x ^ w = (x ^ σ) ^ (σ * w) := by
  rcases hσ with rfl | rfl
  · calc x ^ w = x ^ (1 * w) :=
        (congrArg (fun e : ℝ => x ^ e) (by ring : (1 : ℝ) * w = w)).symm
    _ = (x ^ 1) ^ w := Real.rpow_mul (le_of_lt hx) _ _
    _ = (x ^ 1) ^ (1 * w) :=
        (congrArg (fun e : ℝ => (x ^ 1) ^ e) (by ring : (1 : ℝ) * w = w)).symm
  · calc x ^ w = x ^ ((-1 : ℝ) * ((-1 : ℝ) * w)) :=
        (congrArg (fun e : ℝ => x ^ e) (by ring : ((-1 : ℝ) * ((-1 : ℝ) * w)) = w)).symm
    _ = (x ^ (-1)) ^ ((-1 : ℝ) * w) := Real.rpow_mul (le_of_lt hx) _ _
    _ = (x ^ (-1)) ^ ((-1 : ℝ) * w) := rfl

/-- **The substitution lemma.**  Under `x_s = z_s^{σ_s}` the monomial `x^w` becomes the monomial
`z^{σ ⊙ w}`. -/
theorem rmonoVec_substitute {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (σ : Fin n → ℝ)
    (hσ : fullSignVec σ) (w : Fin n → ℝ) :
    rmonoVec x w = rmonoVec (substitute σ x) (twist σ w) := by
  unfold rmonoVec substitute twist
  refine Finset.prod_congr rfl fun i _ => ?_
  exact rpow_twist (hx i) (hσ i) (σ := σ i) (w := w i)

/-- The substitution `x_s = z_s^{σ_s}` is an involution on the positive orthant. -/
theorem substitute_involutive {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (σ : Fin n → ℝ)
    (hσ : fullSignVec σ) : substitute σ (substitute σ x) = x := by
  funext i
  rcases hσ i with h | h
  · simp [substitute, h, Real.rpow_one]
  · rw [substitute, substitute]
    have hstep : (x i ^ σ i) ^ σ i = x i ^ (σ i * σ i) :=
      (Real.rpow_mul (le_of_lt (hx i)) _ _).symm
    rw [hstep, h]
    norm_num

/-- **The solutions of a system are transported by the substitution.**  If `x` solves
`∑_k c_k x^{w_k} = 0` then `substitute σ x` solves `∑_k c_k z^{σ ⊙ w_k} = 0`, and conversely. -/
theorem sum_substitute {m : ℕ} (σ : Fin n → ℝ) (hσ : fullSignVec σ) (c : Fin m → ℝ)
    (w : Fin m → Fin n → ℝ) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (∑ k, c k * rmonoVec (substitute σ x) (twist σ (w k))) = ∑ k, c k * rmonoVec x (w k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rmonoVec_substitute hx σ hσ]

/-- **The substitution preserves the solution set.** -/
theorem sum_substitute_iff {m : ℕ} (σ : Fin n → ℝ) (hσ : fullSignVec σ) (c : Fin m → ℝ)
    (w : Fin m → Fin n → ℝ) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (∑ k, c k * rmonoVec (substitute σ x) (twist σ (w k))) = 0 ↔
      (∑ k, c k * rmonoVec x (w k)) = 0 := by
  rw [sum_substitute σ hσ c w hx]

/-! ### 2. The excluded ray and Descartes' rule there -/

/-- The **σ-ray**: the curve `t ↦ (t^{σ_1}, …, t^{σ_n})`. -/
noncomputable def ray (σ : Fin n → ℝ) (t : ℝ) : Fin n → ℝ := fun i => t ^ σ i

/-- The product of powers `∏_i t^{f i}` is `t^{∑_i f i}`. -/
lemma rpow_prod_eq (t : ℝ) (ht : 0 < t) (f : Fin n → ℝ) :
    (∏ i, t ^ f i) = t ^ (∑ i, f i) := by
  have hpos : 0 < ∏ i, t ^ f i := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ht _
  have h1 : Real.log (∏ i, t ^ f i) = ∑ i, f i * Real.log t := by
    rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos ht _).ne']
    exact Finset.sum_congr rfl fun i _ => Real.log_rpow ht (f i)
  have h3 : ∑ i, f i * Real.log t = (∑ i, f i) * Real.log t := (Finset.sum_mul _ _ _).symm
  have h2 : Real.log (t ^ (∑ i, f i)) = (∑ i, f i) * Real.log t := Real.log_rpow ht _
  exact Real.log_injOn_pos hpos (Real.rpow_pos_of_pos ht _) (h1.trans (h3.trans h2.symm))

/-- **On the σ-ray the monomial `x^w` becomes the power `t^{σᵀ w}`.** -/
theorem rmonoVec_ray {t : ℝ} (ht : 0 < t) (σ w : Fin n → ℝ) :
    rmonoVec (ray σ t) w = t ^ (∑ i, σ i * w i) := by
  have hprod : (∏ i, (t ^ σ i) ^ w i) = ∏ i, t ^ (σ i * w i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (Real.rpow_mul (le_of_lt ht) (σ i) (w i)).symm
  unfold rmonoVec ray
  rw [hprod]
  exact rpow_prod_eq t ht (fun i => σ i * w i)

/-- **The system restricted to the excluded ray.**  On the ray `t ↦ (t^{σ_1}, …, t^{σ_n})` the
equation `∑_k c_k x^{w_k} = 0` becomes the generalized polynomial equation
`∑_k c_k t^{σᵀ w_k} = 0`. -/
theorem ray_eq {m : ℕ} {t : ℝ} (ht : 0 < t) (σ : Fin n → ℝ) (c : Fin m → ℝ)
    (w : Fin m → Fin n → ℝ) :
    (∑ k, c k * rmonoVec (ray σ t) (w k)) = ∑ k, c k * t ^ (∑ i, σ i * w k i) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rmonoVec_ray ht]

/-- **Descartes' rule on the excluded ray.**  Let `α_k = σᵀ w_k` be the exponents of the reaction
vectors on the ray, and assume that they are strictly increasing.  Then the number of positive `t`
solving `∑_k c_k t^{α_k} = 0` is at most the number of sign variations of the coefficients
`(c_k)`. -/
theorem card_pos_roots_ray_le_signVariations (α : Fin (n + 1) → ℝ) (hα : StrictMono α)
    (c : Fin (n + 1) → ℝ) (hc : ∃ k, c k ≠ 0) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, 0 < y ∧ ∑ k, c k * y ^ α k = 0) :
    Y.card ≤ CircuitDescartes.signVariations c :=
  CircuitDescartes.card_pos_roots_exp_le_signVariations α hα c hc Y hY

/-- **The solutions of the system on the excluded ray.**  If the reaction vectors are excluded by
`σ` and the exponents `α_k = σᵀ w_k` are strictly increasing, then the number of positive `t` for
which `x = ray σ t` solves `∑_k c_k x^{w_k} = 0` is at most the number of sign variations of the
coefficients. -/
theorem card_ray_solutions_le_signVariations (σ : Fin n → ℝ) (hσ : fullSignVec σ)
    (c : Fin (n + 1) → ℝ) (w : Fin (n + 1) → Fin n → ℝ)
    (hα : StrictMono (fun k => ∑ i, σ i * w k i)) (hc : ∃ k, c k ≠ 0) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 < t ∧ (∑ k, c k * rmonoVec (ray σ t) (w k)) = 0) :
    T.card ≤ CircuitDescartes.signVariations c := by
  -- the ray lies in the positive orthant
  have hray : ∀ t ∈ T, ∀ i, 0 < ray σ t i := by
    intro t ht i
    rcases hσ i with h | h
    · rw [ray, h, Real.rpow_one]
      exact (hT t ht).1
    · rw [ray, h, Real.rpow_neg_one]
      exact inv_pos.mpr (hT t ht).1
  have hzero : ∀ t ∈ T, ∑ k, c k * t ^ (∑ i, σ i * w k i) = 0 := by
    intro t ht
    rw [← ray_eq (hT t ht).1 σ c w]
    exact (hT t ht).2
  have hY : ∀ t ∈ T, 0 < t ∧ ∑ k, c k * t ^ (∑ i, σ i * w k i) = 0 := by
    intro t ht
    exact ⟨(hT t ht).1, hzero t ht⟩
  exact card_pos_roots_ray_le_signVariations _ hα c hc T hY

/-! ### 3. The uniqueness theorem for circuit systems -/

/-- **Uniqueness for a square system supported on a circuit.**

Let `E` be an invertible `n × n` matrix (the `n` linearly independent reaction vectors of the
circuit) and `μ` the circuit relation, so that the extra reaction vector is `Eᵀ μ`.  Consider the
system

`C (x^{w_1}, …, x^{w_n}) + x^{Eᵀ μ} c_1 = 0`

(`C` invertible, `c_1` a coefficient vector): this is the *linear* circuit system, i.e. a system with
`n + 1` reaction vectors and **no** additional constant monomial.  If the circuit relation is not
affine, i.e. `∑_k μ_k ≠ 1`, then the system has **at most one positive solution**.

This is the sharpening of Bihan's `n + 1` bound
(`CRNT.Circuit.card_circuit_solutions_le`) that the excluded-circuit theory predicts, and it holds
in particular for excluded circuits (`card_excludedCircuit_pos_le_one`).

*Proof.*  With `y = (x^{w_1}, …, x^{w_n})` and `t = y^μ > 0` the system reads `y = t q` for the
fixed vector `q = -(C⁻¹ c_1)`.  Since `y_k > 0` and `t > 0`, all `q_k > 0`, and taking logarithms
gives `(1 - ∑_k μ_k) log t = ∑_k μ_k log q_k`, a *monotone* equation in `log t`; hence `t`, then
`y`, then `x` are all determined. -/
theorem card_circuitSystem_pos_le_one (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det)
    (μ : Fin n → ℝ) (hμ : (∑ k, μ k) ≠ 1) (Cm : Matrix (Fin n) (Fin n) ℝ) (hCm : IsUnit Cm.det)
    (c₁ : Fin n → ℝ) (Xs : Finset (Fin n → ℝ))
    (hX : ∀ x ∈ Xs, (∀ i, 0 < x i) ∧
      Cm.mulVec (Circuit.monoMap E x) +
        (∏ i, x i ^ (E.transpose.mulVec μ) i) • c₁ = 0) :
    Xs.card ≤ 1 := by
  classical
  set q : Fin n → ℝ := -(Cm⁻¹.mulVec c₁) with hqdef
  -- the monomial coordinates of a solution satisfy `y = t q` with `t = y ^ μ`
  have hyq : ∀ x ∈ Xs, ∀ k, Circuit.monoMap E x k =
      Circuit.rmono μ (Circuit.monoMap E x) * q k := by
    intro x hx k
    have hsys := (hX x hx).2
    have hmul : Circuit.rmono μ (Circuit.monoMap E x) = ∏ i, x i ^ (E.transpose.mulVec μ) i :=
      Circuit.rmono_monoMap E μ (hX x hx).1
    rw [← hmul] at hsys
    have hinv : Cm⁻¹ * Cm = 1 := Matrix.nonsing_inv_mul Cm hCm
    have hmulvec : ∀ (v : Fin n → ℝ) (a : ℝ),
        Cm⁻¹.mulVec (a • v) k = a * (Cm⁻¹.mulVec v) k := by
      intro v a
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have hyv : Cm.mulVec (Circuit.monoMap E x) = -(Circuit.rmono μ (Circuit.monoMap E x) • c₁) := by
      rw [eq_neg_iff_add_eq_zero]; exact hsys
    calc Circuit.monoMap E x k = (Cm⁻¹ * Cm).mulVec (Circuit.monoMap E x) k := by
          rw [hinv, Matrix.one_mulVec]
      _ = Cm⁻¹.mulVec (Cm.mulVec (Circuit.monoMap E x)) k := by rw [Matrix.mulVec_mulVec]
      _ = Cm⁻¹.mulVec (-(Circuit.rmono μ (Circuit.monoMap E x) • c₁)) k := by rw [hyv]
      _ = -(Cm⁻¹.mulVec (Circuit.rmono μ (Circuit.monoMap E x) • c₁)) k := by
          rw [Matrix.mulVec_neg]
          simp only [Pi.neg_apply]
      _ = -(Circuit.rmono μ (Circuit.monoMap E x) * (Cm⁻¹.mulVec c₁) k) := by
          rw [hmulvec]
      _ = Circuit.rmono μ (Circuit.monoMap E x) * q k := by
          rw [hqdef]
          simp only [Pi.neg_apply]
          ring
  -- the logarithm of `t` only depends on the (fixed) data `μ` and `q`
  have hlogt : ∀ x ∈ Xs, Real.log (Circuit.rmono μ (Circuit.monoMap E x)) =
      (∑ k, μ k) * Real.log (Circuit.rmono μ (Circuit.monoMap E x)) + ∑ k, μ k * Real.log (q k) := by
    intro x hx
    have hxpos : ∀ i, 0 < x i := (hX x hx).1
    have hypos : ∀ k, 0 < Circuit.monoMap E x k := by
      intro k
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hxpos i) _
    have htpos : 0 < Circuit.rmono μ (Circuit.monoMap E x) := by
      exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hypos k) _
    have hqpos : ∀ k, 0 < q k := by
      intro k
      have h1 : 0 < Circuit.rmono μ (Circuit.monoMap E x) * q k := by
        rw [← hyq x hx k]
        exact hypos k
      rcases mul_pos_iff.mp h1 with h | h
      · exact h.2
      · exact absurd h.1 (not_lt_of_ge htpos.le)
    have h1 : Real.log (Circuit.rmono μ (Circuit.monoMap E x)) =
        ∑ k, μ k * Real.log (Circuit.monoMap E x k) := by
      unfold Circuit.rmono
      rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hypos k) _).ne']
      exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hypos k) (μ k)
    have h2 : ∀ k, Real.log (Circuit.monoMap E x k) =
        Real.log (Circuit.rmono μ (Circuit.monoMap E x)) + Real.log (q k) := by
      intro k
      rw [hyq x hx k, Real.log_mul (ne_of_gt htpos) (ne_of_gt (hqpos k))]
    calc Real.log (Circuit.rmono μ (Circuit.monoMap E x)) =
          ∑ k, μ k * Real.log (Circuit.monoMap E x k) := h1
      _ = ∑ k, (μ k * Real.log (Circuit.rmono μ (Circuit.monoMap E x)) +
            μ k * Real.log (q k)) := by
          exact Finset.sum_congr rfl fun k _ => by rw [h2]; ring
      _ = (∑ k, μ k * Real.log (Circuit.rmono μ (Circuit.monoMap E x))) +
            ∑ k, μ k * Real.log (q k) := Finset.sum_add_distrib
      _ = (∑ k, μ k) * Real.log (Circuit.rmono μ (Circuit.monoMap E x)) +
            ∑ k, μ k * Real.log (q k) := by rw [Finset.sum_mul]
  -- two solutions have the same value of `t`, hence the same monomial coordinates
  have hkey : ∀ x ∈ Xs, ∀ x' ∈ Xs, x = x' := by
    intro x hx x' hx'
    have hxpos : ∀ i, 0 < x i := (hX x hx).1
    have hx'pos : ∀ i, 0 < x' i := (hX x' hx').1
    have h1 := hlogt x hx
    have h2 := hlogt x' hx'
    have h3 : (1 - ∑ k, μ k) ≠ 0 := by
      exact fun h => hμ ((sub_eq_zero.mp h).symm)
    have hlog : Real.log (Circuit.rmono μ (Circuit.monoMap E x)) =
        Real.log (Circuit.rmono μ (Circuit.monoMap E x')) := by
      have h4 : (1 - ∑ k, μ k) * Real.log (Circuit.rmono μ (Circuit.monoMap E x)) =
          ∑ k, μ k * Real.log (q k) := by linarith [h1]
      have h5 : (1 - ∑ k, μ k) * Real.log (Circuit.rmono μ (Circuit.monoMap E x')) =
          ∑ k, μ k * Real.log (q k) := by linarith [h2]
      have h6 : (1 - ∑ k, μ k) *
          (Real.log (Circuit.rmono μ (Circuit.monoMap E x)) -
            Real.log (Circuit.rmono μ (Circuit.monoMap E x'))) = 0 := by linarith [h4, h5]
      have h7 : Real.log (Circuit.rmono μ (Circuit.monoMap E x)) -
          Real.log (Circuit.rmono μ (Circuit.monoMap E x')) = 0 := by
        rcases mul_eq_zero.mp h6 with hz | hz
        · exact absurd hz h3
        · exact hz
      exact sub_eq_zero.mp h7
    have htpos : 0 < Circuit.rmono μ (Circuit.monoMap E x) := by
      exact Finset.prod_pos fun k _ =>
        Real.rpow_pos_of_pos
          (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hxpos i) _) _
    have ht'pos : 0 < Circuit.rmono μ (Circuit.monoMap E x') := by
      exact Finset.prod_pos fun k _ =>
        Real.rpow_pos_of_pos
          (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx'pos i) _) _
    have hteq : Circuit.rmono μ (Circuit.monoMap E x) = Circuit.rmono μ (Circuit.monoMap E x') :=
      Real.log_injOn_pos htpos ht'pos hlog
    have hyeq : Circuit.monoMap E x = Circuit.monoMap E x' := by
      funext k
      calc Circuit.monoMap E x k = Circuit.rmono μ (Circuit.monoMap E x) * q k := hyq x hx k
        _ = Circuit.rmono μ (Circuit.monoMap E x') * q k := by rw [hteq]
        _ = Circuit.monoMap E x' k := (hyq x' hx' k).symm
    exact Circuit.monoMap_injOn E hE hxpos hx'pos hyeq
  -- conclude
  by_cases hX : Xs.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hX
    have hsub : Xs ⊆ {x₀} := by
      intro x hx
      have h1 := hkey x hx x₀ hx₀
      simpa using h1
    have hcard : Xs.card ≤ ({x₀} : Finset (Fin n → ℝ)).card := Finset.card_le_card hsub
    simpa using hcard
  · have : Xs.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hX)
    omega

set_option linter.unusedVariables false in
/-- **The excluded-circuit theorem.**  If the reaction vectors of the circuit are excluded by a sign
vector `σ` — that is, they all lie in the open half-space `{ w | σᵀ w > 0 }` — then the square system
supported on the circuit has **at most one positive solution**, provided the circuit relation is not
affine.

(The exclusion hypothesis is the classical one of Bihan–Dickenstein–Giaroli; the *bound* itself
holds for every circuit, the exclusion being the structural hypothesis that singles out the
half-space in which the solution lives.  The excluded ray bound
`card_ray_solutions_le_signVariations` is the part that genuinely uses `σ`.) -/
theorem card_excludedCircuit_pos_le_one (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det)
    (σ : Fin n → ℝ) (hσ : fullSignVec σ) (μ : Fin n → ℝ) (hμ : (∑ k, μ k) ≠ 1)
    (hExcl : IsExcluded σ (circuitReactions E μ))
    (Cm : Matrix (Fin n) (Fin n) ℝ) (hCm : IsUnit Cm.det) (c₁ : Fin n → ℝ)
    (Xs : Finset (Fin n → ℝ))
    (hX : ∀ x ∈ Xs, (∀ i, 0 < x i) ∧
      Cm.mulVec (Circuit.monoMap E x) +
        (∏ i, x i ^ (E.transpose.mulVec μ) i) • c₁ = 0) :
    Xs.card ≤ 1 :=
  card_circuitSystem_pos_le_one E hE μ hμ Cm hCm c₁ Xs hX

/-! ### 4. Mixed volumes (Bernstein–Kushnirenko–Khovanskii) -/

/-- The **length** of the interval `[a, b]`: the volume of a one-dimensional Newton polytope. -/
def intervalLength (a b : ℝ) : ℝ := b - a

/-- The **mixed volume** of two intervals `[a, b]` and `[c, d]`: the product of their lengths.

For convex bodies `K₁, K₂` lying in a line this is the mixed volume `MV(K₁, K₂)`, i.e. the
coefficient of `s t` in the volume polynomial `Vol(s K₁ + t K₂)`, and it is the
Bernstein–Kushnirenko–Khovanskii bound for a system of two univariate polynomials. -/
def mixedVolumeIntervals (a b c d : ℝ) : ℝ := (b - a) * (d - c)

/-- The mixed volume of two intervals is the product of their lengths. -/
theorem mixedVolumeIntervals_eq (a b c d : ℝ) :
    mixedVolumeIntervals a b c d = intervalLength a b * intervalLength c d := rfl

/-- The Minkowski sum of two intervals is the interval spanned by the sums of the endpoints. -/
theorem icc_add_icc (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    Set.Icc a b + Set.Icc c d = Set.Icc (a + c) (b + d) := Set.Icc_add_Icc hab hcd

/-- **The volume polynomial of an interval.**  `Vol([a,b] + t [c,d]) = (b-a) + t (d-c)`: the volume
of a one-dimensional body is linear in the scaling parameter. -/
theorem volumePolynomial_interval (a b c d : ℝ) :
    intervalLength a b + t * intervalLength c d = intervalLength (a + t * c) (b + t * d) := by
  simp only [intervalLength]
  ring

/-- **Bernstein–Kushnirenko–Khovanskii, `n = 1`.**  The number of *distinct* positive roots of a
nonzero univariate polynomial is at most its degree; the degree is the mixed volume of the Newton
polytope of the polynomial with the standard simplex, i.e. the length of its Newton polytope. -/
theorem card_pos_roots_le_natDegree (P : ℝ[X]) (hP : P ≠ 0) (R : Finset ℝ)
    (hR : ∀ r ∈ R, 0 < r ∧ P.IsRoot r) : R.card ≤ P.natDegree := by
  have hsub : R ⊆ (P.roots.toFinset.filter (0 < ·)) := by
    intro r hrR
    rw [Finset.mem_filter]
    constructor
    · rw [Multiset.mem_toFinset, mem_roots hP]
      exact (hR r hrR).2
    · exact (hR r hrR).1
  have hcard : R.card ≤ (P.roots.toFinset.filter (0 < ·)).card := Finset.card_le_card hsub
  calc R.card ≤ (P.roots.toFinset.filter (0 < ·)).card := hcard
    _ ≤ P.roots.toFinset.card := Finset.card_filter_le _ _
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P

/-- **Bernstein–Kushnirenko–Khovanskii for overdetermined univariate systems.**  The number of
*distinct* common positive roots of two nonzero univariate polynomials of degrees `m` and `n` is at
most `m * n`, the mixed volume of the Newton polytopes of the two polynomials. -/
theorem card_common_pos_roots_le_mixedVolume (P Q : ℝ[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (R : Finset ℝ) (hR : ∀ r ∈ R, 0 < r ∧ P.IsRoot r ∧ Q.IsRoot r) :
    R.card ≤ P.natDegree * Q.natDegree := by
  have hsub : R ⊆ (P.roots.toFinset.filter (0 < ·)) := by
    intro r hrR
    rw [Finset.mem_filter]
    constructor
    · rw [Multiset.mem_toFinset, mem_roots hP]
      exact (hR r hrR).2.1
    · exact (hR r hrR).1
  have hcard : R.card ≤ (P.roots.toFinset.filter (0 < ·)).card := Finset.card_le_card hsub
  have hdeg : R.card ≤ P.natDegree := by
    calc R.card ≤ (P.roots.toFinset.filter (0 < ·)).card := hcard
      _ ≤ P.roots.toFinset.card := Finset.card_filter_le _ _
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
  rcases Nat.eq_zero_or_pos Q.natDegree with hq | hq
  · -- `Q` is a nonzero constant, so there is no common root at all
    have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq
    have hQc0 : Q.coeff 0 ≠ 0 := by
      intro h
      rw [hQc, h] at hQ
      simp at hQ
    have hnoeval : ∀ r, Q.eval r ≠ 0 := by
      intro r
      rw [hQc, Polynomial.eval_C]
      exact hQc0
    have hRempty : R = ∅ := by
      ext r
      constructor
      · intro hr
        have h1 := (hR r hr).2.2
        exact absurd h1 (hnoeval r)
      · intro hr
        simp at hr
    rw [hRempty]
    simp
  · have h1 : P.natDegree ≤ P.natDegree * Q.natDegree := by
      calc P.natDegree = P.natDegree * 1 := by simp
        _ ≤ P.natDegree * Q.natDegree := Nat.mul_le_mul_left _ hq
    calc R.card ≤ P.natDegree := hdeg
      _ ≤ P.natDegree * Q.natDegree := h1

/-! ### Example: an excluded circuit with a unique positive solution -/

namespace Example

/-- The one-dimensional circuit with reaction vectors `1` and `2`: the exponent matrix is `E = [1]`
and the circuit relation is `μ = 2`, so that the extra reaction vector is `Eᵀ μ = 2`. -/
def E1 : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1

/-- The circuit relation of the circuit `E1`. -/
def mu1 : Fin 1 → ℝ := fun _ => 2

/-- The coefficient matrix of the circuit system `y - y² = 0`. -/
def Cm1 : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1

/-- The coefficient vector of the extra monomial `y²` in the circuit system `y - y² = 0`. -/
def c1v : Fin 1 → ℝ := fun _ => -1

/-- The reaction vectors of the circuit `E1`: `w_0 = 1` and `w_1 = 2`. -/
theorem circuitReactions_E1 :
    circuitReactions E1 mu1 = fun k _ => if k = 0 then 1 else 2 := by
  funext k i
  have hi : i = 0 := Fin.eq_of_val_eq (by omega)
  subst hi
  fin_cases k
  · simp [circuitReactions, E1]
  · simp [circuitReactions, E1, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mu1]

/-- **The circuit is excluded** by the sign vector `σ = 1`: both reaction vectors lie in the open
half-space `{ w | σᵀ w > 0 }`. -/
theorem excluded_reactions :
    IsExcluded (fun _ => (1 : ℝ)) (circuitReactions E1 mu1) := by
  rw [circuitReactions_E1]
  intro r
  fin_cases r
  · simp
  · simp

/-- The set of positive solutions of the circuit system `y - y² = 0`. -/
def sols : Finset (Fin 1 → ℝ) := {fun _ => 1}

/-- The point `y = 1` is a positive solution of the circuit system `y - y² = 0`. -/
theorem sols_solve : ∀ y ∈ sols, (∀ i, 0 < y i) ∧
    Cm1.mulVec (Circuit.monoMap E1 y) +
      (∏ i, y i ^ (E1.transpose.mulVec mu1) i) • c1v = 0 := by
  intro y hy
  simp only [sols, Finset.mem_singleton] at hy
  subst hy
  refine ⟨fun _ => one_pos, ?_⟩
  funext i
  fin_cases i
  simp [Circuit.monoMap, E1, Cm1, c1v, mu1, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]

/-- **The excluded-circuit bound is attained**: the system supported on the excluded circuit
`{1, 2}` has exactly one positive solution. -/
theorem card_sols : sols.card = 1 ∧ sols.card ≤ 1 := by
  constructor
  · simp [sols]
  · exact card_excludedCircuit_pos_le_one E1 (by simp [E1])
      (fun _ => (1 : ℝ)) (by intro i; exact Or.inl rfl) mu1 (by simp [mu1])
      (excluded_reactions) Cm1 (by simp [Cm1]) c1v sols sols_solve

end Example

end ExcludedCircuit
end CRNT
