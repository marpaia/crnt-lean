import CRNT.Algebra.MixedVolume
import CRNT.Algebra.VolumePolynomial
import CRNT.Algebra.CircuitBound
import CRNT.Algebra.CircuitDescartes
import CRNT.Algebra.ExcludedCircuit

/-!
# The BKK bound for a circuit, and the mixed volume of the Newton polytopes (leaf A3)

Leaf **A3** of the field map ("real root bounds and mixed volumes") is concerned with the
**mixed volume** of convex bodies and with the **Bernstein–Kushnirenko–Khovanskii (BKK) bound**
on the number of solutions of a sparse polynomial system.  The campaign has delivered, so far,

* `CRNT.Algebra.MixedVolume`: the mixed volume of **zonotopes** (`CRNT.MixedVolume.mixedVolume`,
  the classical determinant formula of Shephard), with its two defining properties
  (**Minkowski additivity** `mixedVolume_add` and **homogeneity** `mixedVolume_smul`), the Newton
  polytope of a univariate polynomial, the sharp univariate BKK bound
  `card_pos_roots_le_mixedVolume`, the Bézout bound `card_common_pos_roots_le_mixedVolume` and the
  BKK bound for systems in separated variables `card_solutions_le_mixedVolume`;
* `CRNT.Algebra.VolumePolynomial`: the **volume polynomial** of a zonotope
  (`zonotopeVolumePolynomial`), its multilinearity and its degree-`n` homogeneity, and the link
  between its coefficients and the repository's `mixedVolume`
  (`zonotopeVolumePolynomial_coeff_eq_mixedVolume`);
* `CRNT.Algebra.CircuitBound`: the **circuit polynomial** `circuitPoly`, its degree bound
  `natDegree_circuitPoly_le` and Bihan's `n + 1` bound `card_circuit_solutions_le` for a system
  supported on a circuit;
* `CRNT.Algebra.CircuitDescartes`: the **generalized Descartes rule** for real exponents and the
  resulting sign-variation refinement of Bihan's bound
  (`card_circuit_solutions_le_signVariations`);
* `CRNT.Algebra.ExcludedCircuit`: the **excluded-circuit** theory and the uniqueness theorem for
  linear circuit systems (`card_circuitSystem_pos_le_one`, `card_excludedCircuit_pos_le_one`),
  together with the one-dimensional mixed volume of intervals (`mixedVolumeIntervals`).

## 1. The theory

The **Bernstein–Kushnirenko–Khovanskii theorem** (BKK 1981) says:

> If `f₁, …, fₙ` are `n` polynomials in `n` variables with Newton polytopes `K₁, …, Kₙ`, then the
> number of isolated solutions of `f₁ = ⋯ = fₙ = 0` in `(ℂ*)ⁿ`, counted with multiplicity, is at
> most `MV(K₁, …, Kₙ)`, the **mixed volume** of the Newton polytopes, normalized so that
> `MV(K, …, K) = n! Vol K`.

For a *circuit* — a minimally dependent set of `n + 2` monomials `1, x^{w₁}, …, x^{wₙ},
x^{w_{n+1}}` — the Newton polytope of an equation is the polytope `conv(0, w₁, …, wₙ, w_{n+1})`
and the mixed volume of the Newton polytopes of the system is `n!` times its volume.  See
Bihan–Dickenstein–Giaroli 2020, *The Bernstein–Kushnirenko–Khovanskii bound for positive solutions
of a sparse system*, for the modern formulation of the bound and its relation to the circuit
theory.

## 2. What this module adds

* **The mixed volume of the Newton polytopes of a circuit** (`mixedVolume_circuit`): for a circuit
  with exponent differences `w₁, …, wₙ` (the rows of an invertible exponent matrix `E`) the mixed
  volume is `|det E|`, the **normalized volume** of the circuit simplex `conv(0, w₁, …, wₙ)`
  (i.e. `n!` times its Euclidean volume).  This is the quantity the BKK bound uses, and it is
  computed by the repository's `mixedVolume` as the mixed volume of the `n` singleton zonotopes
  spanned by the exponent vectors.  `zonotopeVolumePolynomial_circuit` identifies the same number
  with the volume of the parallelepiped spanned by the reaction vectors, i.e. with the volume
  polynomial of the zonotope at `t = 1`.
* **The BKK bound for a system supported on a circuit, in the mixed-volume form**
  (`card_circuit_solutions_le_mixedVolume`): for a circuit with **integral** exponent vectors and
  a system supported on the `n + 1` monomials `1, x^{w₁}, …, x^{wₙ}` — whose Newton polytope is
  the *circuit simplex* — the number of positive solutions is at most the mixed volume of the
  Newton polytopes, i.e. at most `|det E|`.
* **Bihan's bound and the mixed volume of a circuit, side by side**
  (`card_circuit_solutions_le_n_plus_one`): for the `n + 2` monomial circuit system of the
  repository the number of positive solutions is at most `n + 1`, while the mixed volume of the
  circuit simplex is `|det E|`; § 4 below explains why the two bounds do not imply each other.
* **The multivariate Bézout bound** (`card_common_positive_roots_le_mul_degrees`): the number of
  common positive roots of `n` univariate polynomials in `n` separated variables of degrees
  `d₁, …, dₙ` is at most `d₁ ⋯ dₙ`; and for **dense** equations, whose Newton polytopes are
  simplices (the `dᵢ`-fold Minkowski sum of the standard simplex), the mixed volume of the Newton
  polytopes is *exactly* the product of the degrees
  (`mixedVolume_newtonPolytope_eq_natDegree_of_dense`, `card_solutions_le_mixedVolume_of_dense`).
* **A worked instance** (`CRNT.MixedVolume.Example`): the two-species bimolecular system
  `1 + x + y - 3xy = 0`, `5 + 2x + y - 8xy = 0`, whose Newton polytope is the unit square — the
  zonotope spanned by `e₁, e₂` — of mixed volume `2`, and which has exactly **two** positive
  solutions, `(1, 1)` and `(2, 3/5)`: the mixed-volume bound is attained.

## 3. What is *not* formalized

* the **mixed volume of arbitrary convex bodies**: the definition of the repository is restricted to
  **zonotopes**, where the classical determinant formula of Shephard *is* the definition (see
  `CRNT.Algebra.MixedVolume`, § 2);
* the **volume polynomial theorem for arbitrary convex bodies** (the Brunn–Minkowski theory), and
  hence the mixed volume of a general polytope given by its vertices;
* the **general BKK bound** for `n` Newton polytopes in `ℝⁿ` and general sparse systems: the
  volume of a *non-zonotopal* Newton polytope (such as `conv(0, w₁, …, wₙ, w_{n+1})`, which is
  not a zonotope in general) is not computable with the machinery of this repository, so the
  general bound is *not* claimed here;
* the **multivariate Bézout bound** `deg P · deg Q` for two polynomials in several variables: this
  is a consequence of the general BKK bound and is out of reach with Mathlib's univariate
  polynomial toolkit.

## 4. A remark on the scope of the bound proved here

The literal reading of the BKK bound for a circuit, namely that the number of positive solutions
of a system supported on the `n + 2` monomials `1, x^{w₁}, …, x^{wₙ}, x^{w_{n+1}}` is at most the
mixed volume `|det E|` of the *circuit simplex*, is **false**: for the circuit `1, x, y, xy` (the
exponent vectors `e₁, e₂, e₁ + e₂`, so `|det E| = 1`) the system

```
1 + x + y - 3xy = 0,      5 + 2x + y - 8xy = 0
```

has the two positive solutions `(1, 1)` and `(2, 3/5)`; the refutation is machine-checked
(`CRNT.MixedVolume.Example.not_le_mixedVolume_circuit`).  The reason is that the Newton polytope
of such an equation is `conv(0, w₁, …, wₙ, w_{n+1})`, which is *not* the circuit simplex
`conv(0, w₁, …, wₙ)` but a larger polytope (for `1, x, y, xy` it is the unit square, of normalized
volume `2`), and the mixed volume of the Newton polytopes of the system is `n!` times the volume of
*that* polytope.  Bihan's `n + 1` bound (`CRNT.Circuit.card_circuit_solutions_le_monomial`) and the
BKK bound are genuinely different quantities and neither implies the other.

What *is* proved here (`card_circuit_solutions_le_mixedVolume`) is the BKK bound in the case in
which the Newton polytopes of the system are simplices: the support `1, x^{w₁}, …, x^{wₙ}` of a
circuit, whose Newton polytope is the circuit simplex `conv(0, w₁, …, wₙ)` and whose mixed volume
is `|det E|`, the normalized volume of that simplex.
-/

open scoped BigOperators
open Polynomial

set_option maxHeartbeats 800000

namespace CRNT
namespace MixedVolume

variable {n : ℕ}

/-! ### 1. The circuit simplex -/

/-- The exponent matrix of a circuit, cast to the reals: its rows are the reaction vectors
`w₁, …, wₙ` of the circuit, viewed as elements of `ℝⁿ`. -/
def EReal (E : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ := E.map (fun x => (x : ℝ))

/-- The determinant of the cast exponent matrix is the cast of the determinant. -/
theorem EReal_det (E : Matrix (Fin n) (Fin n) ℤ) : (EReal E).det = (E.det : ℝ) := by
  rw [EReal, Int.cast_det]

/-- The **Newton polytope of a circuit equation**: the simplex `conv(0, w₁, …, wₙ)`, where
`w₁, …, wₙ` are the reaction vectors of the circuit, i.e. the rows of the exponent matrix `E`.

It is the convex hull of the origin and of the reaction vectors, i.e. the smallest convex body
containing them (`convexHull_min`). -/
noncomputable def circuitNewtonPolytope (E : Matrix (Fin n) (Fin n) ℝ) : ConvexBody (Fin n → ℝ) :=
  { carrier := convexHull ℝ ({0} ∪ Set.range (fun k => E k))
    convex' := convex_convexHull ℝ _
    isCompact' := Set.Finite.isCompact_convexHull ℝ ((Set.finite_range _).insert 0)
    nonempty' := ⟨0, subset_convexHull ℝ _ (by simp)⟩ }

/-- The origin belongs to the Newton polytope of a circuit equation. -/
theorem zero_mem_circuitNewtonPolytope (E : Matrix (Fin n) (Fin n) ℝ) :
    (0 : Fin n → ℝ) ∈ circuitNewtonPolytope E := by
  refine subset_convexHull ℝ _ ?_
  exact Or.inl rfl

/-- A reaction vector of the circuit belongs to the Newton polytope of a circuit equation. -/
theorem mem_circuitNewtonPolytope (E : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    E k ∈ circuitNewtonPolytope E := by
  refine subset_convexHull ℝ _ ?_
  exact Or.inr ⟨k, rfl⟩

/-! ### 2. The mixed volume of the Newton polytopes of a circuit -/

/-- The absolute determinant of the list of the reaction vectors of a circuit. -/
theorem absDet_ofFn (E : Matrix (Fin n) (Fin n) ℝ) : absDet (List.ofFn (fun k => E k)) = |E.det| := by
  unfold absDet
  rw [ite_eq_left (by simp)]
  congr 1
  have hcol : columnMatrix (List.ofFn (fun k => E k)) = E.transpose := by
    ext i j
    have hj : j.val < n := j.isLt
    have hget : (List.ofFn (fun k => E k)).getD j.val 0 = fun i => E ⟨j.val, hj⟩ i := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [columnMatrix, hget]
    rfl
  rw [hcol, Matrix.det_transpose]

/-- **The mixed volume of the Newton polytopes of a circuit.**

For a circuit with exponent differences `w₁, …, wₙ` (the rows of the exponent matrix `E`, which
are linearly independent), the Newton polytope of an equation supported on the monomials
`1, x^{w₁}, …, x^{wₙ}` is the **circuit simplex** `conv(0, w₁, …, wₙ)`.  The mixed volume of `n`
copies of that simplex is `n!` times its Euclidean volume, i.e. its **normalized volume**, and it
is the absolute value of the determinant `det E` of the exponent matrix — the quantity the BKK
bound uses.

The repository computes mixed volumes of zonotopes; the value above is the mixed volume of the `n`
*singleton* zonotopes `[0, w₁], …, [0, wₙ]`, which by the classical Shephard formula is
`|det (w₁ … wₙ)| = |det E|`, i.e. exactly the normalized volume of the circuit simplex. -/
theorem mixedVolume_circuit (E : Matrix (Fin n) (Fin n) ℝ) :
    mixedVolume (fun k : Fin n => (⟨[E k]⟩ : Zonotope n)) = |E.det| := by
  have h1 : mixedVolume (fun k : Fin n => (⟨[E k]⟩ : Zonotope n))
      = absDet (List.ofFn (fun k => E k)) := by
    have h : List.ofFn (fun k : Fin n => (⟨[E k]⟩ : Zonotope n))
        = List.map (fun v : Fin n → ℝ => (⟨[v]⟩ : Zonotope n)) (List.ofFn (fun k => E k)) :=
      List.ofFn_comp' (fun k : Fin n => E k) (fun v : Fin n → ℝ => (⟨[v]⟩ : Zonotope n))
    rw [mixedVolume, h, mixedVolumeList_singleton]
  rw [h1, absDet_ofFn]

/-- The column matrix of the list of the reaction vectors of a circuit is the transpose of the
exponent matrix. -/
theorem columnMatrix_finRange_map (E : Matrix (Fin n) (Fin n) ℝ) :
    columnMatrix ((List.finRange n).map (fun k => E k)) = E.transpose := by
  ext i j
  have hj : j.val < n := j.isLt
  have hget : ((List.finRange n).map (fun k => E k)).getD j.val 0 = fun i => E ⟨j.val, hj⟩ i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
    simp
  simp only [columnMatrix, hget]
  rfl

/-- **The volume polynomial of a circuit.**  The zonotope spanned by the reaction vectors
`w₁, …, wₙ` of a circuit is the parallelepiped `∑_k [0, w_k]`; its volume — the volume polynomial
evaluated at `t = 1` — is `|det E|`, the normalized volume of the circuit simplex.

This is the link with `CRNT.Algebra.VolumePolynomial`: the mixed volume of the Newton polytopes of
the circuit is the value of the volume polynomial of the zonotope spanned by its reaction vectors.
-/
theorem zonotopeVolumePolynomial_circuit (E : Matrix (Fin n) (Fin n) ℝ) :
    zonotopeVolumePolynomial (fun k => E k) (fun _ => 1) = |E.det| := by
  classical
  have hone : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using (Finset.powersetCard_self (Finset.univ : Finset (Fin n)))
  have hsort : finsetSorted (Finset.univ : Finset (Fin n)) = List.finRange n := by
    rw [finsetSorted, Fin.sort_univ]
  have habs : absDet ((List.finRange n).map (fun k => E k)) = |E.det| := by
    unfold absDet
    rw [ite_eq_left (by simp)]
    congr 1
    rw [columnMatrix_finRange_map E, Matrix.det_transpose]
  simp only [zonotopeVolumePolynomial, hone, Finset.sum_singleton]
  rw [Finset.prod_const, one_pow, one_mul]
  rw [absDetFinset, hsort, habs]

/-- **The mixed volume of the Newton polytopes of a circuit is the volume of the parallelepiped
spanned by its reaction vectors.** -/
theorem mixedVolume_circuit_eq_volumePolynomial (E : Matrix (Fin n) (Fin n) ℝ) :
    mixedVolume (fun k : Fin n => (⟨[E k]⟩ : Zonotope n))
      = zonotopeVolumePolynomial (fun k => E k) (fun _ => 1) := by
  rw [mixedVolume_circuit, zonotopeVolumePolynomial_circuit]

/-- A nonzero integer has absolute value at least one.  This is the arithmetic input of the BKK
bound: the normalized volume of an integral simplex is a positive integer. -/
theorem one_le_abs_cast_of_ne_zero {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have h1 : (1 : ℤ) ≤ |z| := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  rw [← Int.cast_abs]
  exact_mod_cast h1

/-! ### 3. The BKK bound for a system supported on a circuit -/

/-- **Bihan's bound and the mixed volume of a circuit, side by side.**

For a circuit system supported on the `n + 2` monomials `1, x^{w₁}, …, x^{wₙ}, x^{w_{n+1}}` the
number of positive solutions is at most `n + 1` (Bihan's bound,
`CRNT.Circuit.card_circuit_solutions_le_monomial`), while the mixed volume of the *circuit
simplex* `conv(0, w₁, …, wₙ)` is `|det E|` (`mixedVolume_circuit`).  The two bounds are different
quantities and neither implies the other: the Newton polytope of an equation of the system is the
larger polytope `conv(0, w₁, …, wₙ, w_{n+1})`, whose mixed volume is `n!` times its volume (see
`CRNT.MixedVolume.Example.not_le_mixedVolume_circuit` for a machine-checked counterexample to the
naive reading). -/
theorem card_circuit_solutions_le_n_plus_one (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det)
    (Cm : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit Cm.det) (c₀ c₁ μ : Fin n → ℝ)
    (hP : Circuit.circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ ≠ 0)
    (Xs : Finset (Fin n → ℝ))
    (hX : ∀ x ∈ Xs, (∀ i, 0 < x i) ∧
      Cm.mulVec (Circuit.monoMap E x) + c₀ + (∏ i, x i ^ (E.transpose.mulVec μ) i) • c₁ = 0) :
    Xs.card ≤ n + 1 ∧
      mixedVolume (fun k : Fin n => (⟨[E k]⟩ : Zonotope n)) = |E.det| := by
  constructor
  · exact Circuit.card_circuit_solutions_le_monomial E hE Cm hC c₀ c₁ μ hP Xs hX
  · exact mixedVolume_circuit E

/-- **The BKK bound for a system supported on a circuit, in the mixed-volume form.**

Let `E` be an **integral** exponent matrix with `E.det ≠ 0` — its rows `w₁, …, wₙ` are the
linearly independent reaction vectors of a circuit — and let `B` be an invertible real matrix and
`a` a real vector.  The system

```
∑_k B j k x^{w_k} + a j = 0        (j = 1, …, n)
```

is supported on the `n + 1` monomials `1, x^{w₁}, …, x^{wₙ}` of the circuit; the Newton polytope of
each of its equations is the **circuit simplex** `conv(0, w₁, …, wₙ)`, whose mixed volume (the
mixed volume of `n` copies of it) is the normalized volume `|det E|`.  The number of positive
solutions of the system is at most that mixed volume.

*Proof.* The monomial coordinates `x^{w_k}` of a solution are determined by the (invertible) linear
part, and the monomial map `x ↦ (x^{w₁}, …, x^{wₙ})` is injective on the positive orthant
(`CRNT.Circuit.monoMap_injOn`), so the system has at most one positive solution; and the
normalized volume of an integral simplex is a positive integer, so the mixed volume is at least
one. -/
theorem card_circuit_solutions_le_mixedVolume
    (E : Matrix (Fin n) (Fin n) ℤ) (hE : E.det ≠ 0)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B.det) (a : Fin n → ℝ)
    (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧
      ∀ j, (B.mulVec (Circuit.monoMap (EReal E) x) j) + a j = 0) :
    (S.card : ℝ) ≤ mixedVolume (fun k : Fin n => (⟨[EReal E k]⟩ : Zonotope n)) := by
  have hEreal : IsUnit (EReal E).det := by
    have hne : (EReal E).det ≠ 0 := by
      rw [EReal_det E]
      exact_mod_cast hE
    exact isUnit_iff_ne_zero.mpr hne
  have hmul : ∀ x ∈ S, B.mulVec (Circuit.monoMap (EReal E) x) = fun j => -a j := by
    intro x hx
    funext j
    have h := (hS x hx).2 j
    linarith
  have hkey : ∀ x ∈ S, ∀ x' ∈ S, x = x' := by
    intro x hx x' hx'
    have h1 : Circuit.monoMap (EReal E) x = Circuit.monoMap (EReal E) x' := by
      have hthis : B.mulVec (Circuit.monoMap (EReal E) x)
          = B.mulVec (Circuit.monoMap (EReal E) x') := by
        rw [hmul x hx, hmul x' hx']
      have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
      calc Circuit.monoMap (EReal E) x
          = (B⁻¹ * B).mulVec (Circuit.monoMap (EReal E) x) := by
              rw [hinv, Matrix.one_mulVec]
        _ = B⁻¹.mulVec (B.mulVec (Circuit.monoMap (EReal E) x)) := by
              rw [Matrix.mulVec_mulVec]
        _ = B⁻¹.mulVec (B.mulVec (Circuit.monoMap (EReal E) x')) := by rw [hthis]
        _ = (B⁻¹ * B).mulVec (Circuit.monoMap (EReal E) x') := by
              rw [Matrix.mulVec_mulVec]
        _ = Circuit.monoMap (EReal E) x' := by rw [hinv, Matrix.one_mulVec]
    exact Circuit.monoMap_injOn (EReal E) hEreal (hS x hx).1 (hS x' hx').1 h1
  have hcard : S.card ≤ 1 := by
    by_cases hne : S.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hsub : S ⊆ {x₀} := by
        intro x hx
        rw [hkey x hx x₀ hx₀]
        exact Finset.mem_singleton_self x₀
      have h2 := Finset.card_le_card hsub
      have h3 : ({x₀} : Finset (Fin n → ℝ)).card = 1 := Finset.card_singleton x₀
      omega
    · have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      omega
  have hmv : mixedVolume (fun k : Fin n => (⟨[EReal E k]⟩ : Zonotope n)) = |(E.det : ℝ)| := by
    rw [mixedVolume_circuit, EReal_det E]
  have h1 : (1 : ℝ) ≤ |(E.det : ℝ)| := one_le_abs_cast_of_ne_zero hE
  have h2 : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  calc (S.card : ℝ) ≤ 1 := h2
    _ ≤ |(E.det : ℝ)| := h1
    _ = mixedVolume (fun k : Fin n => (⟨[EReal E k]⟩ : Zonotope n)) := hmv.symm

/-! ### 4. The multivariate Bézout bound -/

/-- **The multivariate Bézout bound for separated variables.**  The number of common positive roots
of `n` univariate polynomials in `n` separated variables, of degrees `d₁, …, dₙ`, is at most
`d₁ ⋯ dₙ`.

This is the classical Bézout bound; in the mixed-volume language of this repository it is the
product of the mixed volumes of the Newton polytopes of the equations. -/
theorem card_common_positive_roots_le_mul_degrees {n : ℕ} (p : Fin n → ℝ[X]) (hp : ∀ i, p i ≠ 0)
    (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧ (∀ i, (p i).eval (x i) = 0)) :
    S.card ≤ ∏ i, (p i).natDegree := by
  have h1 : (S.card : ℝ) ≤ ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := by
    simpa using (card_solutions_le_mixedVolume p hp S hS)
  have h3 : ∀ i, newtonLength (p i) ≤ (p i).natDegree := by
    intro i
    have h := newtonLength_eq (p i) (hp i)
    rw [h]
    omega
  have h4 : (∏ i, newtonLength (p i)) ≤ ∏ i, (p i).natDegree := by
    refine Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => newtonLength (p i)) (g := fun i => (p i).natDegree) ?_
    intro i _
    exact h3 i
  have h5 : (∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)))
      = ∏ i, (newtonLength (p i) : ℝ) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact mixedVolume_newtonPolytope (p i)
  have h6 : (S.card : ℝ) ≤ ∏ i, ((p i).natDegree : ℝ) := by
    calc (S.card : ℝ) ≤ ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := h1
      _ = ∏ i, (newtonLength (p i) : ℝ) := h5
      _ ≤ ∏ i, ((p i).natDegree : ℝ) := by exact_mod_cast h4
  exact_mod_cast h6

/-- **The Newton polytope of a dense polynomial is a simplex, and its mixed volume is its
degree.**  If `p` has degree `d` and all its coefficients `p₀, …, p_d` are nonzero, then the
Newton polytope of `p` is the segment `[0, d]`, the `d`-fold Minkowski sum of the standard simplex
`Δ₁ = [0, 1]`, and its mixed volume is `d`. -/
theorem mixedVolume_newtonPolytope_eq_natDegree_of_dense (p : ℝ[X]) (hp : p ≠ 0)
    (hdense : ∀ i ≤ p.natDegree, p.coeff i ≠ 0) :
    mixedVolume (fun _ : Fin 1 => newtonPolytope p) = (p.natDegree : ℝ) := by
  rw [mixedVolume_newtonPolytope, newtonLength_eq_natDegree_of_dense p hp hdense]

/-- **The BKK bound for separated variables whose Newton polytopes are simplices.**  If every
equation is dense, the Newton polytope of `p i` is the simplex `[0, deg p i]` and its mixed volume
is exactly `deg p i`; hence the mixed volume of the Newton polytopes of the system is the product
of the degrees, and the number of positive solutions is at most that product. -/
theorem card_solutions_le_mixedVolume_of_dense {n : ℕ} (p : Fin n → ℝ[X]) (hp : ∀ i, p i ≠ 0)
    (hdense : ∀ i, ∀ j ≤ (p i).natDegree, (p i).coeff j ≠ 0)
    (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧ (∀ i, (p i).eval (x i) = 0)) :
    (S.card : ℝ) ≤ ∏ i, ((p i).natDegree : ℝ) ∧
      (∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i))) = ∏ i, ((p i).natDegree : ℝ) := by
  constructor
  · have h1 : (S.card : ℝ) ≤ ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := by
      simpa using (card_solutions_le_mixedVolume p hp S hS)
    have h2 : (∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)))
        = ∏ i, ((p i).natDegree : ℝ) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mixedVolume_newtonPolytope_eq_natDegree_of_dense (p i) (hp i) (hdense i)]
    exact h1.trans h2.le
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [mixedVolume_newtonPolytope_eq_natDegree_of_dense (p i) (hp i) (hdense i)]

/-- **The product of the degrees is the mixed volume of the Newton polytopes, for dense
equations.** -/
theorem mixedVolume_prod_eq_mul_degrees_of_dense {n : ℕ} (p : Fin n → ℝ[X]) (hp : ∀ i, p i ≠ 0)
    (hdense : ∀ i, ∀ j ≤ (p i).natDegree, (p i).coeff j ≠ 0) :
    (∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i))) = ∏ i, ((p i).natDegree : ℝ) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [mixedVolume_newtonPolytope_eq_natDegree_of_dense (p i) (hp i) (hdense i)]

/-! ### 5. A worked instance -/

namespace Example

open scoped BigOperators
open Polynomial

/-- The first equation of the two-species bimolecular system. -/
def f1 (x y : ℝ) : ℝ := 1 + x + y - 3 * x * y

/-- The second equation of the two-species bimolecular system. -/
def f2 (x y : ℝ) : ℝ := 5 + 2 * x + y - 8 * x * y

/-- The first equation, evaluated at a point of `ℝ²`. -/
def F1 (v : Fin 2 → ℝ) : ℝ := f1 (v 0) (v 1)

/-- The second equation, evaluated at a point of `ℝ²`. -/
def F2 (v : Fin 2 → ℝ) : ℝ := f2 (v 0) (v 1)

/-- The first positive solution, `(1, 1)`. -/
def sol1 : Fin 2 → ℝ := fun _ => 1

/-- The second positive solution, `(2, 3/5)`. -/
noncomputable def sol2 : Fin 2 → ℝ := fun i => if i = 0 then 2 else 3 / 5

/-- The two positive solutions of the two-species system. -/
noncomputable def sols : Finset (Fin 2 → ℝ) := {sol1, sol2}

/-- The two displayed points are solutions of the two-species system. -/
theorem sols_solve : ∀ v ∈ sols, F1 v = 0 ∧ F2 v = 0 := by
  intro v hv
  simp only [sols, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · refine ⟨?_, ?_⟩
    · simp [F1, f1, sol1]
      norm_num
    · simp [F2, f2, sol1]
      norm_num
  · refine ⟨?_, ?_⟩
    · simp [F1, f1, sol2]
      norm_num
    · simp [F2, f2, sol2]
      norm_num

/-- The two-species system has exactly two positive solutions. -/
theorem card_sols : sols.card = 2 := by
  rw [sols, Finset.card_pair]
  intro h
  have h1 := congrFun h 0
  simp [sol1, sol2] at h1

/-- **The two-species system has at most two positive solutions.**  Eliminating `y` from the two
equations gives the quadratic `2(x² - 3x + 2) = 0`, i.e. `x = 1` or `x = 2`; the value of `y` is
then forced by the linear combination `7 - 2x - 5y = 0` of the two equations. -/
theorem card_le_two (S : Finset (Fin 2 → ℝ)) (hS : ∀ v ∈ S, F1 v = 0 ∧ F2 v = 0) : S.card ≤ 2 := by
  have hsub : ∀ v ∈ S, v = sol1 ∨ v = sol2 := by
    intro v hv
    have h1' : 1 + (v 0) + (v 1) - 3 * (v 0) * (v 1) = 0 := (hS v hv).1
    have h2' : 5 + 2 * (v 0) + (v 1) - 8 * (v 0) * (v 1) = 0 := (hS v hv).2
    have h3 : 7 - 2 * (v 0) - 5 * (v 1) = 0 := by linarith [h1', h2']
    have h5 : 4 + (v 0) - 5 * (v 0) * (v 1) = 0 := by linarith [h1', h3]
    have h6 : 2 * ((v 0) ^ 2 - 3 * (v 0) + 2) = 0 := by nlinarith [h3, h5]
    have h7 : (v 0 - 1) * (v 0 - 2) = 0 := by nlinarith [h6]
    rcases mul_eq_zero.mp h7 with h | h
    · have hv0 : v 0 = 1 := by linarith [h]
      have hy : v 1 = 1 := by linarith [h3]
      left
      funext i
      fin_cases i
      · simp [hv0, sol1]
      · simp [hy, sol1]
    · have hv0 : v 0 = 2 := by linarith [h]
      have hy : v 1 = 3 / 5 := by linarith [h3]
      right
      funext i
      fin_cases i
      · simp [hv0, sol2]
      · simp [hy, sol2]
  have hsub' : S ⊆ {sol1, sol2} := by
    intro v hv
    rcases hsub v hv with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hcard := Finset.card_le_card hsub'
  have h2 : ({sol1, sol2} : Finset (Fin 2 → ℝ)).card = 2 := by
    rw [Finset.card_pair]
    intro h
    have h1 := congrFun h 0
    simp [sol1, sol2] at h1
  omega

/-- **The Newton polytope of each equation of the two-species system**: the unit square
`conv(0, e₁, e₂, e₁ + e₂)`, which is the zonotope spanned by `e₁` and `e₂`.

The support `1, x, y, xy` is the circuit of the exponent vectors `e₁, e₂, e₁ + e₂`; the bimolecular
reaction is the monomial `xy`. -/
def squareZonotope : Zonotope 2 :=
  ⟨[fun i => if i = 0 then 1 else 0, fun i => if i = 1 then 1 else 0]⟩

/-- **The mixed volume of the Newton polytopes of the two-species system is `2`:** the Newton
polytope of each equation is the unit square, the zonotope spanned by `e₁` and `e₂`, and the mixed
volume of two copies of it is `2!` times its area, i.e. `2`. -/
theorem mixedVolume_square : mixedVolume (fun _ : Fin 2 => squareZonotope) = 2 := by
  have h1 : List.ofFn (fun _ : Fin 2 => squareZonotope) = [squareZonotope, squareZonotope] := by
    simp
  rw [mixedVolume, h1]
  simp only [mixedVolumeList, mvSum]
  simp [squareZonotope, absDet, columnMatrix, Matrix.det_fin_two]
  norm_num

/-- **The mixed-volume bound is attained for the two-species system:** the mixed volume of the
Newton polytopes is `2` and the system has exactly two positive solutions. -/
theorem mixedVolume_bound_attained :
    mixedVolume (fun _ : Fin 2 => squareZonotope) = 2 ∧ sols.card = 2 ∧
      ∀ v ∈ sols, F1 v = 0 ∧ F2 v = 0 :=
  ⟨mixedVolume_square, card_sols, sols_solve⟩

/-- The exponent vector `e₁` of the circuit `1, x, y, xy`. -/
def e1 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- The exponent vector `e₂` of the circuit `1, x, y, xy`. -/
def e2 : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0

/-- The singleton zonotope `[0, e₁]`. -/
def Z1 : Zonotope 2 := ⟨[e1]⟩

/-- The singleton zonotope `[0, e₂]`. -/
def Z2 : Zonotope 2 := ⟨[e2]⟩

/-- **The mixed volume of the circuit simplex of the circuit `1, x, y, xy` is `1`**: it is the
mixed volume of the two singleton zonotopes `[0, e₁]` and `[0, e₂]`, i.e. `|det (e₁ e₂)| = 1`,
the normalized volume of the simplex `conv(0, e₁, e₂)`. -/
theorem mixedVolume_circuit_simplex_twoSpecies :
    mixedVolume (Fin.cons Z1 (fun _ : Fin 1 => Z2)) = 1 := by
  have h1 : List.ofFn (Fin.cons Z1 (fun _ : Fin 1 => Z2)) = [Z1, Z2] := by
    rw [List.ofFn_cons]
    simp
  rw [mixedVolume, h1]
  simp only [mixedVolumeList, mvSum]
  simp [Z1, Z2, e1, e2, absDet, columnMatrix, Matrix.det_fin_two]

/-- **The naive reading of the BKK bound for a circuit is false.**

The mixed volume of the *circuit simplex* of the circuit `1, x, y, xy` is `1`
(`mixedVolume_circuit_simplex_twoSpecies`), but the two-species system of this example has **two**
positive solutions.  The reason is that the Newton polytope of an equation of that system is the
unit square `conv(0, e₁, e₂, e₁ + e₂)`, *not* the circuit simplex `conv(0, e₁, e₂)`: the BKK
bound uses the former, whose mixed volume is `2` (`mixedVolume_square`). -/
theorem not_le_mixedVolume_circuit :
    ¬ ((sols.card : ℝ) ≤ mixedVolume (Fin.cons Z1 (fun _ : Fin 1 => Z2))) := by
  rw [mixedVolume_circuit_simplex_twoSpecies]
  simp [card_sols]

end Example

/-! ### 6. Audit -/

#print axioms EReal_det
#print axioms absDet_ofFn
#print axioms mixedVolume_circuit
#print axioms columnMatrix_finRange_map
#print axioms zonotopeVolumePolynomial_circuit
#print axioms mixedVolume_circuit_eq_volumePolynomial
#print axioms one_le_abs_cast_of_ne_zero
#print axioms card_circuit_solutions_le_n_plus_one
#print axioms card_circuit_solutions_le_mixedVolume
#print axioms card_common_positive_roots_le_mul_degrees
#print axioms mixedVolume_newtonPolytope_eq_natDegree_of_dense
#print axioms card_solutions_le_mixedVolume_of_dense
#print axioms mixedVolume_prod_eq_mul_degrees_of_dense
#print axioms Example.card_le_two
#print axioms Example.mixedVolume_square
#print axioms Example.mixedVolume_bound_attained
#print axioms Example.mixedVolume_circuit_simplex_twoSpecies
#print axioms Example.not_le_mixedVolume_circuit

end MixedVolume
end CRNT
