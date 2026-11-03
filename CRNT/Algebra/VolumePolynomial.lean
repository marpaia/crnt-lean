import CRNT.Algebra.MixedVolume
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange

/-!
# An algebraic determinant polynomial for zonotope generators

A polynomial is constructed from absolute determinants of generator subsets.
The module proves its parameter linearity, homogeneity, coefficient identities,
and applications to separated-variable root bounds. These are algebraic
identities. A general equality with Lebesgue volume of a Minkowski sum and the
full convex-body volume-polynomial/BKK theorems remain separate obligations.
-/

open scoped BigOperators
open Polynomial

set_option maxHeartbeats 800000

namespace CRNT
namespace MixedVolume

variable {n m : ℕ}

/-! ### 1. The volume polynomial of a zonotope -/

/-- The elements of the finite set `S`, in increasing order. -/
def finsetSorted (S : Finset (Fin m)) : List (Fin m) := S.sort

/-- The **absolute determinant** of the `n × n` matrix whose columns are the generators `z j`,
`j ∈ S` (in increasing order of the indices).  It is `0` unless `S` has exactly `n` elements.

This is one algebraic determinant term. Its use below does not require a general
Lebesgue-volume identity. -/
def absDetFinset (z : Fin m → Fin n → ℝ) (S : Finset (Fin m)) : ℝ :=
  absDet ((finsetSorted S).map z)

/-- The `k`-th generator of `S` (in increasing order of the indices), or the zero vector if `S`
has fewer than `k + 1` elements. -/
def sortedGenerator (z : Fin m → Fin n → ℝ) (S : Finset (Fin m)) (k : Fin n) : Fin n → ℝ :=
  ((finsetSorted S).map z).getD k.val 0

/-- **The volume polynomial of a zonotope.**

Let `z 0, …, z (m-1) ∈ ℝⁿ` be the generators of a zonotope and `t 0, …, t (m-1) ∈ ℝ` the
scaling parameters of its segments.  The volume polynomial is

```
V(t) = ∑_{|S| = n} (∏_{j ∈ S} t j) · |det (z j₁, …, z jₙ)|
```

where the sum runs over the `n`-element subsets `S` of `{0, …, m-1}` and `j₁ < ⋯ < jₙ` are the
elements of `S`. The expression is defined algebraically; identifying it with
Lebesgue volume remains separate. It is a homogeneous polynomial of degree `n` in `t`,
linear in each `t j` separately, and the coefficient of the monomial `∏_{j ∈ S} t j` is the mixed
volume of the `n` singleton zonotopes spanned by the generators indexed by `S`
(`zonotopeVolumePolynomial_coeff_eq_mixedVolume`). -/
def zonotopeVolumePolynomial (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n, (∏ j ∈ S, t j) * absDetFinset z S

/-! ### 2. Multilinearity -/

/-- **Splitting off a factor.**  If `i ∈ S`, the product over `S` of the function
`fun j => if j = i then c else t j` is `c` times the product of `t` over `S.erase i`. -/
lemma prod_split (S : Finset (Fin m)) (i : Fin m) (c : ℝ) (t : Fin m → ℝ) (hi : i ∈ S) :
    (∏ j ∈ S, (if j = i then c else t j)) = c * ∏ j ∈ S.erase i, t j := by
  have hmul : (if i = i then c else t i) * ∏ j ∈ S.erase i, (if j = i then c else t j)
      = ∏ j ∈ S, (if j = i then c else t j) :=
    Finset.mul_prod_erase S (fun j => if j = i then c else t j) hi
  rw [← hmul, ite_eq_left rfl]
  rw [Finset.prod_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj))]

/-- **A parameter which does not occur.**  If `i ∉ S`, the product over `S` of the function
`fun j => if j = i then c else t j` is the product of `t` over `S`. -/
lemma prod_no_occ (S : Finset (Fin m)) (i : Fin m) (c : ℝ) (t : Fin m → ℝ) (hi : i ∉ S) :
    (∏ j ∈ S, (if j = i then c else t j)) = ∏ j ∈ S, t j := by
  refine Finset.prod_congr rfl (fun j hj => ?_)
  by_cases h : j = i
  · subst h
    exact absurd (hi hj) (by simp)
  · rw [ite_eq_right h]

/-- **The volume polynomial is linear in each scaling parameter.**

This is the multilinearity of the volume polynomial: with the other scaling parameters fixed,
the volume of the scaled zonotope is an affine function of the `i`-th one.  Equivalently, the
coefficient of the monomials containing `t i` is proportional to `t i`, and the coefficient of the
monomials which do not contain `t i` does not depend on `t i` at all. -/
theorem zonotopeVolumePolynomial_linear (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (i : Fin m)
    (c : ℝ) :
    zonotopeVolumePolynomial z (fun j => if j = i then c else t j)
      = zonotopeVolumePolynomial z (fun j => if j = i then 0 else t j)
        + c * (zonotopeVolumePolynomial z (fun j => if j = i then 1 else t j)
          - zonotopeVolumePolynomial z (fun j => if j = i then 0 else t j)) := by
  classical
  have key : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ((∏ j ∈ S, (if j = i then c else t j)) * absDetFinset z S)
        = ((∏ j ∈ S, (if j = i then 0 else t j)) * absDetFinset z S)
          + c * (((∏ j ∈ S, (if j = i then 1 else t j)) * absDetFinset z S)
            - ((∏ j ∈ S, (if j = i then 0 else t j)) * absDetFinset z S)) := by
    intro S hS
    by_cases hi : i ∈ S
    · have h1 : (∏ j ∈ S, (if j = i then c else t j)) = c * ∏ j ∈ S.erase i, t j :=
        prod_split S i c t hi
      have h0 : (∏ j ∈ S, (if j = i then 0 else t j)) = 0 * ∏ j ∈ S.erase i, t j :=
        prod_split S i 0 t hi
      have h1' : (∏ j ∈ S, (if j = i then 1 else t j)) = 1 * ∏ j ∈ S.erase i, t j :=
        prod_split S i 1 t hi
      rw [h1, h0, h1']
      ring
    · have h1 : (∏ j ∈ S, (if j = i then c else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i c t hi
      have h0 : (∏ j ∈ S, (if j = i then 0 else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i 0 t hi
      have h1' : (∏ j ∈ S, (if j = i then 1 else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i 1 t hi
      rw [h1, h0, h1']
      ring
  simp only [zonotopeVolumePolynomial]
  rw [Finset.sum_congr rfl (fun S hS => key S hS)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- **Additivity of the volume polynomial, with the zero convention.**

The volume polynomial is additive in the `i`-th scaling parameter, up to the term at `t = 0`
(the monomials of `V` which do not involve `t i` are unaffected by the value of `t i`):

```
V(t|_{i = μ + ν}) = V(t|_{i = μ}) + V(t|_{i = ν}) − V(t|_{i = 0}).
```

The statement without the last term is false in general: for `n = 1`, `m = 2`, generators
`z 0 = z 1 = 1` and `t = (t, s)` with `s ≠ 0` the two sides read `2 + s` and `2 + 2s`. -/
theorem zonotopeVolumePolynomial_add (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (i : Fin m)
    (μ ν : ℝ) :
    zonotopeVolumePolynomial z (fun j => if j = i then μ + ν else t j)
      = zonotopeVolumePolynomial z (fun j => if j = i then μ else t j)
        + zonotopeVolumePolynomial z (fun j => if j = i then ν else t j)
        - zonotopeVolumePolynomial z (fun j => if j = i then 0 else t j) := by
  classical
  have key : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ((∏ j ∈ S, (if j = i then μ + ν else t j)) * absDetFinset z S)
        = ((∏ j ∈ S, (if j = i then μ else t j)) * absDetFinset z S)
          + (((∏ j ∈ S, (if j = i then ν else t j)) * absDetFinset z S)
            - ((∏ j ∈ S, (if j = i then 0 else t j)) * absDetFinset z S)) := by
    intro S hS
    by_cases hi : i ∈ S
    · have h1 : (∏ j ∈ S, (if j = i then μ + ν else t j)) = (μ + ν) * ∏ j ∈ S.erase i, t j :=
        prod_split S i (μ + ν) t hi
      have hμ : (∏ j ∈ S, (if j = i then μ else t j)) = μ * ∏ j ∈ S.erase i, t j :=
        prod_split S i μ t hi
      have hν : (∏ j ∈ S, (if j = i then ν else t j)) = ν * ∏ j ∈ S.erase i, t j :=
        prod_split S i ν t hi
      have h0 : (∏ j ∈ S, (if j = i then 0 else t j)) = 0 * ∏ j ∈ S.erase i, t j :=
        prod_split S i 0 t hi
      rw [h1, hμ, hν, h0]
      ring
    · have h1 : (∏ j ∈ S, (if j = i then μ + ν else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i (μ + ν) t hi
      have hμ : (∏ j ∈ S, (if j = i then μ else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i μ t hi
      have hν : (∏ j ∈ S, (if j = i then ν else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i ν t hi
      have h0 : (∏ j ∈ S, (if j = i then 0 else t j)) = ∏ j ∈ S, t j :=
        prod_no_occ S i 0 t hi
      rw [h1, hμ, hν, h0]
      ring
  simp only [zonotopeVolumePolynomial]
  rw [Finset.sum_congr rfl (fun S hS => key S hS)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **Homogeneity of degree `n`.**  Scaling all the segments by `c` scales the volume of the
zonotope by `cⁿ`, the volume polynomial being a homogeneous polynomial of degree `n`. -/
theorem zonotopeVolumePolynomial_smul (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (c : ℝ) :
    zonotopeVolumePolynomial z (fun j => c * t j) = c ^ n * zonotopeVolumePolynomial z t := by
  classical
  have key : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ((∏ j ∈ S, (c * t j)) * absDetFinset z S)
        = c ^ n * ((∏ j ∈ S, t j) * absDetFinset z S) := by
    intro S hS
    have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
    have hprod : (∏ j ∈ S, (c * t j)) = c ^ S.card * ∏ j ∈ S, t j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [hprod, hcard]
    ring
  simp only [zonotopeVolumePolynomial]
  rw [Finset.sum_congr rfl (fun S hS => key S hS)]
  rw [← Finset.mul_sum]

/-! ### 3. The coefficients are mixed volumes -/

/-- Two lists of `n` vectors which agree elementwise have the same absolute determinant. -/
lemma absDet_congr {vs vs' : List (Fin n → ℝ)} (hlen : vs.length = n) (hlen' : vs'.length = n)
    (h : ∀ j : Fin n, vs.getD j.val 0 = vs'.getD j.val 0) : absDet vs = absDet vs' := by
  unfold absDet
  rw [ite_eq_left hlen, ite_eq_left hlen']
  have hmat : columnMatrix vs = columnMatrix vs' := by
    funext i j
    show (vs.getD j.val 0) i = (vs'.getD j.val 0) i
    rw [h j]
  rw [hmat]

/-- **The mixed volume of singleton zonotopes.**  The mixed volume of a list of singleton
zonotopes `[0, w]` is the absolute determinant of the list of their generators. -/
lemma mvSum_singleton : ∀ (vs l : List (Fin n → ℝ)),
    mvSum vs (List.map (fun w => (⟨[w]⟩ : Zonotope n)) l) = absDet (vs ++ l) := by
  intro vs l
  induction l generalizing vs with
  | nil => simp [mvSum, List.append_nil]
  | cons w l ih =>
      rw [List.map_cons]
      have h1 : mvSum vs ((⟨[w]⟩ : Zonotope n) :: List.map (fun w => (⟨[w]⟩ : Zonotope n)) l)
          = mvSum (vs ++ [w]) (List.map (fun w => (⟨[w]⟩ : Zonotope n)) l) := by
        simp [mvSum]
      rw [h1, ih]
      simp

/-- **The mixed volume of singleton zonotopes.**  The mixed volume of a list of singleton
zonotopes `[0, w]` is the absolute determinant of the list of their generators. -/
lemma mixedVolumeList_singleton (l : List (Fin n → ℝ)) :
    mixedVolumeList (List.map (fun w => (⟨[w]⟩ : Zonotope n)) l) = absDet l := by
  have h := mvSum_singleton [] l
  simpa [mixedVolumeList] using h

/-- **The coefficient of the monomial `∏_{j ∈ S} t j` is the mixed volume of the `n` singleton
zonotopes spanned by the generators indexed by `S`.**

This is the link with `CRNT.MixedVolume.mixedVolume`: the classical determinant formula of
Shephard, `MV([0, z j₁], …, [0, z jₙ]) = |det (z j₁ … z jₙ)|`, is exactly the coefficient of the
monomial `t j₁ ⋯ t jₙ` in the volume polynomial. -/
theorem zonotopeVolumePolynomial_coeff_eq_mixedVolume (z : Fin m → Fin n → ℝ) (S : Finset (Fin m))
    (hS : S.card = n) :
    absDetFinset z S
      = mixedVolume (fun k : Fin n => (⟨[sortedGenerator z S k]⟩ : Zonotope n)) := by
  classical
  have hlen : (finsetSorted S).length = n := by
    rw [finsetSorted, Finset.length_sort (fun a b => a ≤ b), hS]
  -- the mixed volume is the absolute determinant of the list of the singleton generators
  have hmv : mixedVolume (fun k : Fin n => (⟨[sortedGenerator z S k]⟩ : Zonotope n))
      = absDet (List.ofFn (fun k : Fin n => sortedGenerator z S k)) := by
    rw [mixedVolume]
    have hon : (fun k : Fin n => (⟨[sortedGenerator z S k]⟩ : Zonotope n))
        = ((fun w : Fin n → ℝ => (⟨[w]⟩ : Zonotope n)) ∘ sortedGenerator z S) := by
      funext k; rfl
    rw [hon]
    simp only [List.ofFn_eq_map]
    rw [← List.map_map]
    exact mixedVolumeList_singleton _
  -- the two lists of vectors agree
  have habs : absDet (List.ofFn (fun k : Fin n => sortedGenerator z S k))
      = absDet ((finsetSorted S).map z) := by
    refine absDet_congr (by simp) (by simp [hlen]) ?_
    intro j
    have hlen' : j.val < ((finsetSorted S).map z).length := by simp [hlen]
    have h1 : (List.ofFn (fun k : Fin n => sortedGenerator z S k)).getD j.val 0
        = sortedGenerator z S ⟨j.val, by omega⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn (by simp)]
    have h2 : ((finsetSorted S).map z).getD j.val 0 = ((finsetSorted S).map z)[j.val]'hlen' := by
      exact List.getD_eq_get _ _ ⟨j.val, hlen'⟩
    rw [h1, h2]
    have h3 : sortedGenerator z S ⟨j.val, by omega⟩ = ((finsetSorted S).map z).getD j.val 0 := rfl
    rw [h3]
    exact h2
  rw [hmv, habs]
  rfl

/-- **The expansion of the volume polynomial in the mixed volumes.**  The volume polynomial is
the sum of the mixed volumes `MV(S)` of the `n` singleton zonotopes spanned by the generators,
multiplied by the corresponding monomial `∏_{j ∈ S} t j`. -/
theorem zonotopeVolumePolynomial_eq_sum (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) :
    zonotopeVolumePolynomial z t
      = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
          mixedVolume (fun k : Fin n => (⟨[sortedGenerator z S k]⟩ : Zonotope n)) * ∏ j ∈ S, t j := by
  classical
  simp only [zonotopeVolumePolynomial]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
  rw [zonotopeVolumePolynomial_coeff_eq_mixedVolume z S hcard]
  ring

/-- **The volume of the zonotope is the sum of its mixed volumes.**  At the point `t = 1` of the
volume polynomial — the zonotope itself — the volume is the sum of the mixed volumes of the
`n`-element subsets of the generators. -/
theorem zonotopeVolumePolynomial_at_one (z : Fin m → Fin n → ℝ) :
    zonotopeVolumePolynomial z (fun _ => 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
          mixedVolume (fun k : Fin n => (⟨[sortedGenerator z S k]⟩ : Zonotope n)) := by
  have h := zonotopeVolumePolynomial_eq_sum z (fun _ => 1)
  rw [h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.prod_const, one_pow, mul_one]

/-! ### 4. The volume polynomial as a polynomial in one scaling parameter -/

/-- **The volume polynomial, seen as a univariate polynomial in the `i`-th scaling parameter.**
For a fixed choice of the other scaling parameters the volume polynomial is an affine function of
the `i`-th one; this is the polynomial form of the multilinearity proved above. -/
noncomputable def zonotopeVolumePolynomialIn (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ)
    (i : Fin m) : ℝ[X] :=
  Polynomial.C (zonotopeVolumePolynomial z (fun j => if j = i then 0 else t j))
    + Polynomial.C (zonotopeVolumePolynomial z (fun j => if j = i then 1 else t j)
      - zonotopeVolumePolynomial z (fun j => if j = i then 0 else t j)) * Polynomial.X

/-- **The volume polynomial, evaluated at a scaling parameter.**  The polynomial
`zonotopeVolumePolynomialIn z t i` is the affine function of the `i`-th scaling parameter whose
value at `c` is the volume polynomial at the scaling parameters `t` with the `i`-th one replaced
by `c`. -/
theorem zonotopeVolumePolynomialIn_eval (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (i : Fin m)
    (c : ℝ) :
    (zonotopeVolumePolynomialIn z t i).eval c
      = zonotopeVolumePolynomial z (fun j => if j = i then c else t j) := by
  have h := zonotopeVolumePolynomial_linear z t i c
  rw [zonotopeVolumePolynomialIn, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, h]
  ring

/-- **The volume polynomial, evaluated at its own scaling parameters.** -/
theorem zonotopeVolumePolynomialIn_eval_at (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (i : Fin m) :
    (zonotopeVolumePolynomialIn z t i).eval (t i) = zonotopeVolumePolynomial z t := by
  have h : zonotopeVolumePolynomial z (fun j => if j = i then t i else t j)
      = zonotopeVolumePolynomial z t := by
    apply congrArg (zonotopeVolumePolynomial z)
    funext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  rw [zonotopeVolumePolynomialIn_eval, h]

/-- **The volume polynomial has degree at most one in each scaling parameter.** -/
theorem zonotopeVolumePolynomialIn_deg_le_one (z : Fin m → Fin n → ℝ) (t : Fin m → ℝ) (i : Fin m) :
    (zonotopeVolumePolynomialIn z t i).degree ≤ 1 := by
  rw [zonotopeVolumePolynomialIn]
  refine Polynomial.degree_add_le_of_degree_le (Polynomial.degree_C_le.trans (by simp))
    (Polynomial.degree_C_mul_X_le _)

/-! ### 5. The BKK bound for systems in separated variables, in the volume-polynomial form -/

/-- The generators of the zonotope spanned by the Newton polytopes of a system in separated
variables: the `i`-th Newton polytope is the segment `[0, len pᵢ eᵢ]`, whose generator is the
vector `len pᵢ eᵢ`. -/
def newtonAxisGenerators {n : ℕ} (p : Fin n → ℝ[X]) : Fin n → Fin n → ℝ :=
  fun i j => if j = i then (newtonLength (p i) : ℝ) else 0

/-- **The volume polynomial of the zonotope spanned by the Newton polytopes.**  The zonotope
spanned by the Newton polytopes of a system in separated variables is the box
`∏ᵢ [0, len pᵢ]`, and its volume polynomial, evaluated at `t = 1`, is the product of the Newton
polytope lengths — the classical Bernstein–Kushnirenko–Khovanskii bound for such systems. -/
theorem zonotopeVolumePolynomial_newtonAxis (p : Fin n → ℝ[X]) :
    zonotopeVolumePolynomial (newtonAxisGenerators p) (fun _ => 1) = ∏ i, (newtonLength (p i) : ℝ) := by
  classical
  have hone : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using (Finset.powersetCard_self (Finset.univ : Finset (Fin n)))
  have hsort : finsetSorted (Finset.univ : Finset (Fin n)) = List.finRange n := by
    rw [finsetSorted, Fin.sort_univ]
  have hcol : columnMatrix ((List.finRange n).map (newtonAxisGenerators p))
      = Matrix.diagonal (fun i => (newtonLength (p i) : ℝ)) := by
    funext i j
    have hget : ((List.finRange n).map (newtonAxisGenerators p)).getD j.val 0
        = newtonAxisGenerators p ⟨j.val, by omega⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
      simp
    simp only [columnMatrix, Matrix.diagonal, hget]
    by_cases hij : i = j
    · have hEq : (⟨j.val, by omega⟩ : Fin n) = i := Fin.ext (by simp [hij])
      simp [newtonAxisGenerators, hEq, hij]
    · simp [newtonAxisGenerators, hij]
  have habs : absDet ((List.finRange n).map (newtonAxisGenerators p))
      = ∏ i, (newtonLength (p i) : ℝ) := by
    have h1 : absDet ((List.finRange n).map (newtonAxisGenerators p))
        = |(Matrix.diagonal (fun i => (newtonLength (p i) : ℝ))).det| := by
      unfold absDet
      rw [ite_eq_left (by simp), hcol]
    rw [h1, Matrix.det_diagonal, Finset.abs_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [abs_of_nonneg]
    exact_mod_cast (Nat.zero_le _)
  simp only [zonotopeVolumePolynomial, hone, Finset.sum_singleton]
  rw [Finset.prod_const, one_pow, one_mul]
  rw [absDetFinset, hsort, habs]

/-- **Bernstein–Kushnirenko–Khovanskii, in the volume-polynomial form.**  The number of positive
solutions of a system of `n` univariate polynomials in separated variables is at most the volume
polynomial, evaluated at `t = 1`, of the zonotope spanned by the Newton polytopes of the
equations; this is the product of the Newton polytope lengths. -/
theorem card_solutions_le_volumePolynomial {n : ℕ} (p : Fin n → ℝ[X]) (hp : ∀ i, p i ≠ 0)
    (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧ (∀ i, (p i).eval (x i) = 0)) :
    (S.card : ℝ) ≤ zonotopeVolumePolynomial (newtonAxisGenerators p) (fun _ => 1) := by
  have h1 := card_solutions_le_mixedVolume p hp S hS
  have h2 : (S.card : ℝ) ≤ ∏ i, (newtonLength (p i) : ℝ) := by
    calc (S.card : ℝ) ≤ ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := h1
      _ = ∏ i, (newtonLength (p i) : ℝ) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        exact mixedVolume_newtonPolytope (p i)
  rw [zonotopeVolumePolynomial_newtonAxis p]
  exact h2

/-! ### 6. Audit -/

#print axioms zonotopeVolumePolynomial_linear
#print axioms zonotopeVolumePolynomial_add
#print axioms zonotopeVolumePolynomial_smul
#print axioms zonotopeVolumePolynomial_coeff_eq_mixedVolume
#print axioms zonotopeVolumePolynomial_eq_sum
#print axioms zonotopeVolumePolynomial_at_one
#print axioms zonotopeVolumePolynomialIn_eval
#print axioms zonotopeVolumePolynomialIn_deg_le_one
#print axioms zonotopeVolumePolynomial_newtonAxis
#print axioms card_solutions_le_volumePolynomial

end MixedVolume
end CRNT
