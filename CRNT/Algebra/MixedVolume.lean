import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-!
# Determinant mixed-volume expressions and restricted root bounds

`mixedVolume` is defined algebraically from lists of zonotope generators as a
sum of absolute determinants. Additivity and homogeneity follow for this
expression. A general identification with Lebesgue volume of the represented
zonotope body is not established here.

The polynomial root bounds count distinct positive roots in one variable or
solutions of separated-variable systems, with the displayed support assumptions.
They do not prove the general sparse BKK theorem with multiplicities.
-/

open scoped BigOperators
open scoped Pointwise

open Polynomial

set_option maxHeartbeats 800000

namespace CRNT
namespace MixedVolume

variable {n : ℕ}

/-! ### 1. Convex bodies: the Minkowski structure -/

/-- The **Minkowski sum** of two convex bodies `K` and `L` of `ℝⁿ`:
`K + L = {x + y | x ∈ K, y ∈ L}`. -/
def minkowskiSum (K L : ConvexBody (Fin n → ℝ)) : ConvexBody (Fin n → ℝ) := K + L

@[simp] theorem coe_minkowskiSum (K L : ConvexBody (Fin n → ℝ)) :
    ((minkowskiSum K L : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      (K : Set (Fin n → ℝ)) + (L : Set (Fin n → ℝ)) :=
  ConvexBody.coe_add K L

/-- The **dilation** of a convex body `K` by the scalar `c`, i.e. the image of `K` under
`x ↦ c x`. -/
def dilation (c : ℝ) (K : ConvexBody (Fin n → ℝ)) : ConvexBody (Fin n → ℝ) := c • K

@[simp] theorem coe_dilation (c : ℝ) (K : ConvexBody (Fin n → ℝ)) :
    ((dilation c K : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) = c • (K : Set (Fin n → ℝ)) :=
  ConvexBody.coe_smul c K

/-- The **volume** of a convex body: its Lebesgue measure. -/
noncomputable def convexVolume (K : ConvexBody (Fin n → ℝ)) : ℝ :=
  (MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (K : Set (Fin n → ℝ))).real
    (K : Set (Fin n → ℝ))

/-! ### 2. Zonotopes -/

/-- A **zonotope** of `ℝⁿ`: a Minkowski sum of finitely many segments `[0, v]`.  The list `gens` is
the list of **generators** of the zonotope; the zonotope itself is the Minkowski sum `∑ᵢ [0, gensᵢ]`.

Zonotopes are the class on which the mixed volume is computed explicitly in this file. -/
structure Zonotope (n : ℕ) where
  /-- The **generators** of the zonotope. -/
  gens : List (Fin n → ℝ)

namespace Zonotope

/-- The **Minkowski sum** of two zonotopes: the generators are concatenated. -/
def add (Z W : Zonotope n) : Zonotope n := ⟨Z.gens ++ W.gens⟩

instance : Add (Zonotope n) := ⟨Zonotope.add⟩

@[simp] theorem gens_add (Z W : Zonotope n) : (Z + W).gens = Z.gens ++ W.gens := rfl

/-- The **dilation** of a zonotope by `c`: every generator is multiplied by `c`. -/
def smul (c : ℝ) (Z : Zonotope n) : Zonotope n := ⟨Z.gens.map fun v => c • v⟩

instance : SMul ℝ (Zonotope n) := ⟨Zonotope.smul⟩

@[simp] theorem gens_smul (c : ℝ) (Z : Zonotope n) :
    (c • Z).gens = Z.gens.map fun v => c • v := rfl

/-- The **segment** `[0, v]` as a convex body of `ℝⁿ`. -/
noncomputable def segmentBody (v : Fin n → ℝ) : ConvexBody (Fin n → ℝ) :=
  { carrier := convexHull ℝ ({0, v} : Set (Fin n → ℝ))
    convex' := convex_convexHull ℝ _
    isCompact' := Set.Finite.isCompact_convexHull ℝ
      ((Set.finite_singleton v).insert 0 : ({0, v} : Set (Fin n → ℝ)).Finite)
    nonempty' := ⟨0, subset_convexHull ℝ _ (by simp : 0 ∈ ({0, v} : Set (Fin n → ℝ)))⟩ }

/-- The **convex body** of a zonotope: the Minkowski sum of the segments `[0, v]`. -/
noncomputable def toConvexBody (Z : Zonotope n) : ConvexBody (Fin n → ℝ) :=
  Z.gens.foldr (fun v K => segmentBody v + K) 0

end Zonotope

/-! ### 3. Determinants of lists of vectors -/

/-- The matrix whose columns are the vectors of the list `vs` (the zero vector is used for the
missing entries). -/
def columnMatrix (vs : List (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (vs.getD j.val 0) i

/-- The absolute value of the determinant of the vectors of the list `vs`, viewed as the columns of
an `n × n` matrix.  This is `0` if `vs` does not have exactly `n` entries. -/
def absDet (vs : List (Fin n → ℝ)) : ℝ :=
  if vs.length = n then |(columnMatrix vs).det| else 0

/-- Scaling a list of vectors by `c` scales its `j`-th entry by `c`. -/
lemma getD_smul (c : ℝ) : ∀ (vs : List (Fin n → ℝ)) (j : ℕ),
    (vs.map fun v => c • v).getD j 0 = (c • vs.getD j 0 : Fin n → ℝ) := by
  intro vs
  induction vs with
  | nil => intro j; simp [List.getD]
  | cons v vs ih =>
      intro j
      cases j with
      | zero =>
          simp only [List.map_cons, List.getD_cons_zero]
      | succ j =>
          simp only [List.map_cons, List.getD_cons_succ]
          exact ih j

/-- Scaling all the vectors of a list scales the matrix of its columns by the same scalar. -/
lemma columnMatrix_smul (c : ℝ) (vs : List (Fin n → ℝ)) :
    columnMatrix (vs.map fun v => c • v) = (c • columnMatrix vs : Matrix (Fin n) (Fin n) ℝ) := by
  funext i j
  rw [show columnMatrix (vs.map fun v => c • v) i j = (vs.map fun v => c • v).getD j.val 0 i from rfl]
  rw [getD_smul]
  simp [columnMatrix]

/-- **Scaling all the vectors of a list scales its determinant**:
`|det (c v₀ … c v_{n-1})| = |c|ⁿ |det (v₀ … v_{n-1})|`. -/
lemma absDet_smul (c : ℝ) (vs : List (Fin n → ℝ)) :
    absDet (vs.map fun v => c • v) = |c| ^ n * absDet vs := by
  by_cases h : vs.length = n
  · have h1 : (vs.map fun v => c • v).length = n := by simp [h]
    rw [absDet, ite_eq_left h1, absDet, ite_eq_left h, columnMatrix_smul, Matrix.det_smul,
      abs_mul, abs_pow, Fintype.card_fin]
  · have h1 : (vs.map fun v => c • v).length ≠ n := by simp [h]
    rw [absDet, ite_eq_right h1, absDet, ite_eq_right h]
    simp

/-- Scaling all the vectors of a list scales its determinant by `|c|` to the power of the *length
of the list* (which is the number of columns of the determinant). -/
lemma absDet_smul_len (c : ℝ) (vs : List (Fin n → ℝ)) :
    absDet (vs.map fun v => c • v) = |c| ^ vs.length * absDet vs := by
  by_cases h : vs.length = n
  · rw [absDet_smul, h]
  · have h1 : (vs.map fun v => c • v).length ≠ n := by simp [h]
    rw [absDet, ite_eq_right h1, absDet, ite_eq_right h]
    simp

/-- The absolute determinant of a single vector of `ℝ¹` is its length. -/
lemma absDet_singleton (v : Fin 1 → ℝ) : absDet [v] = |v 0| := by
  have h1 : ([v] : List (Fin 1 → ℝ)).length = 1 := by simp
  rw [absDet, ite_eq_left h1, Matrix.det_fin_one]
  rfl

/-! ### 4. The mixed volume of zonotopes -/

/-- `mvSum vs zs` is the sum of `|det|` over all choices of one generator from each of the zonotopes
of the list `zs`, the chosen vectors being appended to the list `vs` of already chosen vectors.

For `vs = []` and `zs` a list of `n` zonotopes of `ℝⁿ`, this is the mixed volume of the zonotopes
in the Bernstein–Kushnirenko–Khovanskii normalization. -/
def mvSum : List (Fin n → ℝ) → List (Zonotope n) → ℝ
  | vs, [] => absDet vs
  | vs, Z :: zs => (Z.gens.map fun v => mvSum (vs ++ [v]) zs).sum

/-- The **mixed volume** of a list of zonotopes of `ℝⁿ`, in the
Bernstein–Kushnirenko–Khovanskii normalization: `MV(Z₀, …, Z_{n-1}) = ∑ |det (v₀ … v_{n-1})|`,
the sum running over all choices of one generator `vᵢ` from each zonotope.

This defines the determinant expression. A general bridge to the Lebesgue volume
of the represented zonotope body is not proved here. -/
def mixedVolumeList (Z : List (Zonotope n)) : ℝ :=
  mvSum [] Z

/-- The **mixed volume** of `n` zonotopes `Z₀, …, Z_{n-1}` of `ℝⁿ`. -/
def mixedVolume (Z : Fin n → Zonotope n) : ℝ := mixedVolumeList (List.ofFn Z)

/-- The **mixed volume** of two zonotopes `K` and `L` of `ℝⁿ`: the mixed volume of the `n`-tuple
`(K, L, K, …, K)` (`n-2` copies of `K` and one copy of `L`).  In the classical normalization this is
`n! V(K[n-2], L[1])`. -/
def mixedVolume2 (K L : Zonotope n) : ℝ :=
  mixedVolumeList (K :: L :: List.replicate (n - 2) K)

/-! ### 5. Minkowski additivity and homogeneity -/

/-- **Minkowski additivity.**  The mixed volume is additive in an argument that occurs *once*:
`MV(Z₁ + Z₂, rest) = MV(Z₁, rest) + MV(Z₂, rest)`.  This is the classical additivity of the
mixed volume, and one of the two defining properties of the mixed volume (the other being
homogeneity). -/
theorem mvSum_add (Z₁ Z₂ : Zonotope n) (zs : List (Zonotope n)) :
    mvSum [] ((Z₁ + Z₂) :: zs) = mvSum [] (Z₁ :: zs) + mvSum [] (Z₂ :: zs) := by
  have hgens : (Z₁ + Z₂).gens = Z₁.gens ++ Z₂.gens := by simp
  simp only [mvSum, hgens, List.map_append, List.sum_append]

/-- **Minkowski additivity of the mixed volume.**  The mixed volume is additive in an argument
that occurs *once*. -/
theorem mixedVolumeList_add (Z₁ Z₂ : Zonotope n) (rest : List (Zonotope n)) :
    mixedVolumeList ((Z₁ + Z₂) :: rest) = mixedVolumeList (Z₁ :: rest) + mixedVolumeList (Z₂ :: rest) := by
  exact mvSum_add Z₁ Z₂ rest

/-- **Minkowski additivity of the mixed volume.**  The mixed volume of `m + 1` zonotopes of `ℝᵐ⁺¹`
is additive in its first argument:
`MV(Z₁ + Z₂, Z, …, Z) = MV(Z₁, Z, …, Z) + MV(Z₂, Z, …, Z)`. -/
theorem mixedVolume_add {m : ℕ} (Z : Fin m → Zonotope (m + 1)) (Z₁ Z₂ : Zonotope (m + 1)) :
    mixedVolume (Fin.cons (Z₁ + Z₂) Z)
      = mixedVolume (Fin.cons Z₁ Z) + mixedVolume (Fin.cons Z₂ Z) := by
  simp only [mixedVolume, List.ofFn_cons]
  exact mixedVolumeList_add Z₁ Z₂ (List.ofFn Z)

/-- A list of scaled vectors appended with a scaled vector is the scaling of the concatenation. -/
lemma map_append_singleton (c : ℝ) (vs : List (Fin n → ℝ)) (v : Fin n → ℝ) :
    (vs.map fun v => c • v) ++ [c • v] = (vs ++ [v]).map fun v => c • v := by
  simp only [List.map_append, List.map_cons, List.map_nil]

/-- A constant factor can be pulled out of a sum over a list. -/
lemma sum_mul_const (k : ℝ) (l : List α) (f : α → ℝ) :
    (l.map fun x => k * f x).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

/-- **Scaling lemma.**  Scaling all the vectors of the accumulator *and* all the generators of the
zonotopes by `c` scales the mixed volume by `|c|` to the power of the total number of vectors. -/
theorem mvSum_smul (c : ℝ) (vs : List (Fin n → ℝ)) (zs : List (Zonotope n)) :
    mvSum (vs.map fun v => c • v) (zs.map fun z => c • z)
      = |c| ^ (vs.length + zs.length) * mvSum vs zs := by
  induction zs generalizing vs with
  | nil =>
      simp only [List.map_nil, mvSum, absDet_smul_len, List.length_nil, Nat.add_zero]
  | cons Z zs ih =>
      have hgens : (c • Z).gens = Z.gens.map fun v => c • v := Zonotope.gens_smul c Z
      simp only [List.map_cons, mvSum, hgens]
      rw [List.map_map, Function.comp_def]
      simp only [map_append_singleton]
      simp_rw [ih]
      have hk : ∀ v : Fin n → ℝ, (vs ++ [v]).length + zs.length = vs.length + 1 + zs.length := by
        intro v
        simp only [List.length_append, List.length_singleton]
      simp_rw [hk]
      have hfact : (Z.gens.map fun v => |c| ^ (vs.length + 1 + zs.length) * mvSum (vs ++ [v]) zs).sum
          = |c| ^ (vs.length + 1 + zs.length) * (Z.gens.map fun v => mvSum (vs ++ [v]) zs).sum := by
        exact sum_mul_const _ _ _
      rw [hfact]
      have hexp : vs.length + 1 + zs.length = vs.length + (Z :: zs).length := by
        simp only [List.length_cons]
        omega
      rw [hexp]

/-- **Homogeneity of the mixed volume.**  Scaling all the zonotopes by `c` scales the mixed volume
by `|c|ⁿ`, the `n` being the number of zonotopes (equivalently, the dimension of the ambient
space). -/
theorem mixedVolumeList_smul (c : ℝ) (Z : List (Zonotope n)) :
    mixedVolumeList (Z.map fun z => c • z) = |c| ^ Z.length * mixedVolumeList Z := by
  have h := mvSum_smul c [] Z
  simpa [mixedVolumeList] using h

/-- **Homogeneity of the mixed volume.**  `MV(c Z₀, …, c Z_{n-1}) = cⁿ MV(Z₀, …, Z_{n-1})`. -/
theorem mixedVolume_smul (c : ℝ) (Z : Fin n → Zonotope n) :
    mixedVolume (fun i => c • Z i) = |c| ^ n * mixedVolume Z := by
  have h : List.ofFn (fun i => c • Z i) = List.map (fun z => c • z) (List.ofFn Z) := by
    exact List.ofFn_comp' Z (c • ·)
  simp only [mixedVolume, h, mixedVolumeList_smul, List.length_ofFn]

/-! ### 6. Newton polytopes -/

/-- The **minimal degree** of a nonzero polynomial: the least exponent with a nonzero
coefficient. -/
def minDegree (p : ℝ[X]) (hp : p ≠ 0) : ℕ := p.support.min' (Polynomial.support_nonempty.mpr hp)

/-- The **length of the Newton polytope** of `p`: the difference between the largest and the
smallest exponent with a nonzero coefficient.  The Newton polytope of the zero polynomial is empty;
its length is `0`. -/
def newtonLength (p : ℝ[X]) : ℕ :=
  if h : p.support.Nonempty then p.natDegree - p.support.min' h else 0

/-- The length of the Newton polytope of a nonzero polynomial is its degree minus its minimal
degree. -/
theorem newtonLength_eq (p : ℝ[X]) (hp : p ≠ 0) :
    newtonLength p = p.natDegree - minDegree p hp := by
  have h : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  simp [newtonLength, h, minDegree]

/-- The **Newton polytope** of a univariate polynomial `p`, as a segment of `ℝ¹` anchored at the
origin: the segment `[0, newtonLength p]`.  (The Newton polytope itself is the translate of this
segment by `minDegree p`; the mixed volume is translation invariant, so the anchored
representative computes the same mixed volume.) -/
def newtonPolytope (p : ℝ[X]) : Zonotope 1 := ⟨[fun _ => (newtonLength p : ℝ)]⟩

/-- The **Newton polytope** of a univariate polynomial `p`, regarded as a segment of `ℝⁿ` lying on
the `i`-th coordinate axis: the segment `[0, newtonLength p · eᵢ]`. -/
def newtonPolytopeAxis (i : Fin n) (p : ℝ[X]) : Zonotope n :=
  ⟨[fun j => if j = i then (newtonLength p : ℝ) else 0]⟩

/-- **The mixed volume of a Newton polytope.**  In dimension one the mixed volume of a single body
is its length; hence the mixed volume of the Newton polytope of `p` is the length of that
polytope. -/
theorem mixedVolume_newtonPolytope (p : ℝ[X]) :
    mixedVolume (fun _ : Fin 1 => newtonPolytope p) = (newtonLength p : ℝ) := by
  have h1 : List.ofFn (fun _ : Fin 1 => newtonPolytope p) = [newtonPolytope p] := by
    simp
  have h2 : mixedVolumeList [newtonPolytope p] = (newtonLength p : ℝ) := by
    simp only [mixedVolumeList, mvSum, newtonPolytope, List.map_singleton, List.sum_singleton,
      List.nil_append]
    rw [absDet_singleton]
    simp
  rw [mixedVolume, h1, h2]

/-! ### 7. The univariate BKK bound -/

/-- The **positive roots** of a polynomial: the set of its positive roots. -/
noncomputable def positiveRoots (p : ℝ[X]) : Finset ℝ := p.roots.toFinset.filter (0 < ·)

/-- The number of distinct positive roots of a polynomial is at most its degree. -/
theorem card_positiveRoots_le_natDegree (p : ℝ[X]) :
    (positiveRoots p).card ≤ p.natDegree := by
  have h1 : (positiveRoots p).card ≤ p.roots.toFinset.card := Finset.card_filter_le _ _
  have h2 : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
  have h3 : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  omega

/-- The **minimal degree** of a nonzero polynomial is the multiplicity of `0` as a root: the
polynomial is divisible by `X ^ minDegree p`. -/
theorem minDegree_dvd (p : ℝ[X]) (hp : p ≠ 0) : Polynomial.X ^ minDegree p hp ∣ p := by
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  have hmin : ∀ d, d < minDegree p hp → p.coeff d = 0 := by
    intro d hd
    have hdn : d ∉ p.support := by
      intro hd'
      exact (Nat.not_lt.mpr ((Finset.isLeast_min' p.support hne).2 hd')) hd
    by_contra hcon
    exact hdn (Polynomial.mem_support_iff.mpr hcon)
  rw [Polynomial.X_pow_dvd_iff]
  exact hmin

/-- **Bernstein–Kushnirenko–Khovanskii, `n = 1`.**  The number of *distinct* positive roots of a
nonzero univariate polynomial `p` is at most the mixed volume of its Newton polytope, i.e. at most
the **length** of the Newton polytope of `p`.

This is the sharp one-dimensional BKK bound: it improves the degree bound
(`card_positiveRoots_le_natDegree`) by the multiplicity of the root `0`. -/
theorem card_pos_roots_le_mixedVolume (p : ℝ[X]) (hp : p ≠ 0) (R : Finset ℝ)
    (hR : ∀ r ∈ R, 0 < r ∧ p.IsRoot r) :
    R.card ≤ mixedVolume (fun _ : Fin 1 => newtonPolytope p) := by
  -- Step 1: factor out the highest power of `X` dividing `p`.
  obtain ⟨q, hq⟩ := minDegree_dvd p hp
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    exact hp hq
  set m : ℕ := minDegree p hp with hm
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  have hminIn : m ∈ p.support := by
    rw [hm]
    exact Finset.min'_mem _ hne
  have hcoeffMin : p.coeff m ≠ 0 :=
    (Polynomial.mem_support_iff).mp hminIn
  -- the constant coefficient of `q` is the coefficient of `p` of degree `m`
  have hcoeff0 : q.coeff 0 ≠ 0 := by
    have h2 : p.coeff m = q.coeff 0 := by
      rw [hq, Polynomial.coeff_X_pow_mul']
      simp
    rw [← h2]
    exact hcoeffMin
  -- Step 2: the degree of `q` is the degree of `p` minus the minimal degree.
  have hdeg : q.natDegree = p.natDegree - m := by
    have hlc : ((Polynomial.X : ℝ[X]) ^ m).leadingCoeff * q.leadingCoeff ≠ 0 := by
      rw [Polynomial.leadingCoeff_X_pow]
      simp [hq0]
    have h3 : p.natDegree = ((Polynomial.X : ℝ[X]) ^ m).natDegree + q.natDegree := by
      rw [hq]
      exact Polynomial.natDegree_mul' hlc
    have h4 : ((Polynomial.X : ℝ[X]) ^ m).natDegree = m := by
      simp
    omega
  -- Step 3: the positive roots of `p` are the positive roots of `q`.
  have hroots : ∀ r : ℝ, 0 < r → (p.IsRoot r ↔ q.IsRoot r) := by
    intro r hr
    rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def]
    constructor
    · intro he
      have hne' : ((Polynomial.X : ℝ[X]) ^ m).eval r ≠ 0 := by
        simp [ne_of_gt hr]
      have hthis := congrArg (fun f : ℝ[X] => f.eval r) hq
      rw [Polynomial.eval_mul, he] at hthis
      exact (mul_eq_zero.mp hthis.symm).resolve_left hne'
    · intro he
      have hthis := congrArg (fun f : ℝ[X] => f.eval r) hq
      rw [Polynomial.eval_mul, he, mul_zero] at hthis
      exact hthis
  -- Step 4: counting.
  have hsub : R ⊆ positiveRoots q := by
    intro r hrR
    rw [positiveRoots, Finset.mem_filter]
    constructor
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
      exact (hroots r ((hR r hrR).1)).1 ((hR r hrR).2)
    · exact (hR r hrR).1
  have hcard : R.card ≤ (positiveRoots q).card := Finset.card_le_card hsub
  have hcard' : (positiveRoots q).card ≤ q.natDegree := card_positiveRoots_le_natDegree q
  have hlen : q.natDegree = newtonLength p := by
    rw [newtonLength_eq p hp, hdeg, hm]
  have hmv : mixedVolume (fun _ : Fin 1 => newtonPolytope p) = (newtonLength p : ℝ) :=
    mixedVolume_newtonPolytope p
  have hbound : R.card ≤ newtonLength p := hcard.trans (hcard'.trans hlen.le)
  rw [hmv]
  exact_mod_cast hbound

/-- **Bernstein–Kushnirenko–Khovanskii, `n = 1`, in the degree normalization.**  The number of
distinct positive roots of a nonzero univariate polynomial is at most its degree. -/
theorem card_pos_roots_le_natDegree (p : ℝ[X]) (hp : p ≠ 0) (R : Finset ℝ)
    (hR : ∀ r ∈ R, 0 < r ∧ p.IsRoot r) : R.card ≤ p.natDegree := by
  have h1 := card_pos_roots_le_mixedVolume p hp R hR
  rw [mixedVolume_newtonPolytope] at h1
  have h2 : (newtonLength p : ℝ) ≤ (p.natDegree : ℝ) := by
    rw [newtonLength_eq p hp]
    exact_mod_cast Nat.sub_le _ _
  have h3 : (R.card : ℝ) ≤ (p.natDegree : ℝ) :=
    (show (R.card : ℝ) ≤ (newtonLength p : ℝ) from h1).trans h2
  exact_mod_cast h3

/-! ### 8. The Bézout bound for two univariate polynomials -/

/-- The **one-dimensional mixed volume** of two segments of `ℝ¹`: the product of their lengths.
This is the one-dimensional analogue of the mixed volume (the coefficient of `s t` in the volume
polynomial of `s K₁ + t K₂` is the product of the lengths, as the volume in dimension one is
linear in the scaling parameters); it is the BKK bound for two univariate polynomials. -/
def mixedVolumeSegments (l₁ l₂ : ℝ) : ℝ := l₁ * l₂

/-- **The Bézout bound.**  The number of *distinct* common positive roots of two nonzero univariate
polynomials of degrees `m` and `n` is at most `m * n`, the mixed volume of the Newton polytopes of
the two polynomials in the one-dimensional (product of lengths) convention. -/
theorem card_common_pos_roots_le_mixedVolume (P Q : ℝ[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (R : Finset ℝ) (hR : ∀ r ∈ R, 0 < r ∧ P.IsRoot r ∧ Q.IsRoot r) :
    R.card ≤ mixedVolumeSegments P.natDegree Q.natDegree := by
  have h1 : (R.card : ℝ) ≤ (P.natDegree : ℝ) := by
    exact_mod_cast card_pos_roots_le_natDegree P hP R fun r hr => ⟨(hR r hr).1, (hR r hr).2.1⟩
  rcases Nat.eq_zero_or_pos Q.natDegree with hq | hq
  · -- `Q` is a nonzero constant, so there is no common root at all
    have hQc : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq
    have hQc0 : Q.coeff 0 ≠ 0 := by
      intro h
      rw [hQc, h] at hQ
      simp at hQ
    have hnoeval : ∀ r : ℝ, Q.eval r ≠ 0 := by
      intro r
      rw [hQc, Polynomial.eval_C]
      exact hQc0
    have hRempty : R = ∅ := by
      ext r
      constructor
      · intro hr
        exact absurd ((hR r hr).2.2) (hnoeval r)
      · intro hr
        simp at hr
    rw [hRempty]
    simp only [Finset.card_empty, mixedVolumeSegments]
    rw [← Nat.cast_mul]
    exact Nat.cast_le (α := ℝ).mpr (Nat.zero_le _)
  · have h3 : (P.natDegree : ℝ) ≤ (P.natDegree : ℝ) * (Q.natDegree : ℝ) := by
      have hq1 : (1 : ℕ) ≤ Q.natDegree := Nat.succ_le_of_lt hq
      have hmul : P.natDegree * 1 ≤ P.natDegree * Q.natDegree :=
        Nat.mul_le_mul_left _ hq1
      have hmul' : ((P.natDegree * 1 : ℕ) : ℝ) ≤ ((P.natDegree * Q.natDegree : ℕ) : ℝ) :=
        Nat.cast_le (α := ℝ).mpr hmul
      simpa using hmul'
    exact h1.trans h3

/-- **The Bézout bound, sharpened by the Newton polytopes.**  The number of distinct common
positive roots of two nonzero univariate polynomials is at most the *smaller* of the two Newton
polytope lengths. -/
theorem card_common_pos_roots_le_newtonLength (P Q : ℝ[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (R : Finset ℝ) (hR : ∀ r ∈ R, 0 < r ∧ P.IsRoot r ∧ Q.IsRoot r) :
    R.card ≤ min (newtonLength P) (newtonLength Q) := by
  have h1 : R.card ≤ newtonLength P := by
    have h := card_pos_roots_le_mixedVolume P hP R fun r hr => ⟨(hR r hr).1, (hR r hr).2.1⟩
    rw [mixedVolume_newtonPolytope] at h
    exact_mod_cast h
  have h2 : R.card ≤ newtonLength Q := by
    have h := card_pos_roots_le_mixedVolume Q hQ R fun r hr => ⟨(hR r hr).1, (hR r hr).2.2⟩
    rw [mixedVolume_newtonPolytope] at h
    exact_mod_cast h
  omega

/-! ### 9. The simplex -/
/-- The **standard simplex** `Δ₁ = [0, 1]` of `ℝ¹`, as a zonotope.  It is the Newton polytope of
the polynomial `1 + X`. -/
def stdSimplex1 : Zonotope 1 := ⟨[fun _ => 1]⟩

/-- The mixed volume of the standard simplex of `ℝ¹` is `1`, its length. -/
theorem mixedVolume_stdSimplex1 : mixedVolume (fun _ : Fin 1 => stdSimplex1) = 1 := by
  have h1 : List.ofFn (fun _ : Fin 1 => stdSimplex1) = [stdSimplex1] := by
    simp
  have h2 : mixedVolumeList [stdSimplex1] = 1 := by
    simp only [mixedVolumeList, mvSum, stdSimplex1, List.map_singleton, List.sum_singleton,
      List.nil_append]
    rw [absDet_singleton]
    simp
  rw [mixedVolume, h1, h2]

/-- The `k`-fold Minkowski sum of the standard simplex `Δ₁ = [0, 1]` of `ℝ¹` is the segment
`[0, k]`, whose mixed volume is `k`. -/
def simplexPow (k : ℕ) : Zonotope 1 := ⟨[fun _ => (k : ℝ)]⟩

/-- The mixed volume of the `k`-fold Minkowski sum of the standard simplex is `k`. -/
theorem mixedVolume_simplex_pow (k : ℕ) :
    mixedVolume (fun _ : Fin 1 => simplexPow k) = (k : ℝ) := by
  have h1 : List.ofFn (fun _ : Fin 1 => simplexPow k) = [simplexPow k] := by
    simp
  have h2 : mixedVolumeList [simplexPow k] = (k : ℝ) := by
    simp only [mixedVolumeList, mvSum, simplexPow, List.map_singleton, List.sum_singleton,
      List.nil_append]
    rw [absDet_singleton]
    simp
  rw [mixedVolume, h1, h2]

/-- **The Newton polytope of a dense polynomial is a multiple of the simplex.**  If `p` has degree
`d` and all its coefficients `p₀, …, p_d` are nonzero, then the Newton polytope of `p` is the
segment `[0, d]`, i.e. the `d`-fold Minkowski sum of the standard simplex `Δ₁`, and its mixed
volume is `d`. -/
theorem newtonLength_eq_natDegree_of_dense (p : ℝ[X]) (hp : p ≠ 0)
    (hdense : ∀ i ≤ p.natDegree, p.coeff i ≠ 0) : newtonLength p = p.natDegree := by
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  have hmin : minDegree p hp = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    have h0 : (0 : ℕ) ∈ p.support := by
      rw [Polynomial.mem_support_iff]
      exact hdense 0 (Nat.zero_le p.natDegree)
    rw [minDegree]
    exact (Finset.isLeast_min' p.support hne).2 h0
  rw [newtonLength_eq p hp, hmin]
  omega

/-! ### 10. The BKK bound for systems in separated variables -/

/-- **Counting lemma.**  If every coordinate of every element of `S` lies in `R i`, then
`S.card ≤ ∏ i, (R i).card`: the solution set injects into the product of the coordinate sets. -/
theorem card_le_prod_card {n : ℕ} (R : Fin n → Finset ℝ) (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, ∀ i, x i ∈ R i) : S.card ≤ ∏ i, (R i).card := by
  have hsub : S ⊆ Fintype.piFinset R := by
    intro x hx
    rw [Fintype.mem_piFinset]
    exact hS x hx
  have h1 : S.card ≤ (Fintype.piFinset R).card := Finset.card_le_card hsub
  have h2 : (Fintype.piFinset R).card = ∏ i, (R i).card := by
    rw [Fintype.piFinset, Finset.card_map, Finset.card_pi]
  omega

/-- **Bernstein–Kushnirenko–Khovanskii for systems in separated variables.**  Let `p₁, …, pₙ` be
nonzero univariate polynomials and let `S` be a finite set of positive solutions of the system
`p₁(x₁) = 0, …, pₙ(xₙ) = 0`.  Then the number of solutions is at most the product of the mixed
volumes of the Newton polytopes of the equations, that is, the product of the Newton polytope
lengths.

For a system in separated variables the Newton polytope of `pᵢ` is the segment `[0, len pᵢ]` lying
on the `i`-th coordinate axis, and the mixed volume of these `n` segments is the product of their
lengths; the bound proved here is the classical BKK bound for such systems. -/
theorem card_solutions_le_mixedVolume {n : ℕ} (p : Fin n → ℝ[X]) (hp : ∀ i, p i ≠ 0)
    (S : Finset (Fin n → ℝ))
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧ (∀ i, (p i).eval (x i) = 0)) :
    S.card ≤ ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := by
  -- Step 1: every coordinate of a solution is a positive root of the corresponding polynomial.
  have hcoord : ∀ x ∈ S, ∀ i, x i ∈ positiveRoots (p i) := by
    intro x hx i
    rw [positiveRoots, Finset.mem_filter]
    constructor
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp i), Polynomial.IsRoot.def]
      exact (hS x hx).2 i
    · exact (hS x hx).1 i
  -- Step 2: the solutions inject into the product of the sets of positive roots.
  have h1 : S.card ≤ ∏ i, (positiveRoots (p i)).card := card_le_prod_card _ S hcoord
  -- Step 3: the Newton polytope lengths are the mixed volumes of the Newton polytopes.
  have h3 : ∀ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) = (newtonLength (p i) : ℝ) :=
    fun i => mixedVolume_newtonPolytope (p i)
  -- Step 4: each set of positive roots has at most `len pᵢ` elements.
  have h2 : ∀ i, (positiveRoots (p i)).card ≤ (newtonLength (p i) : ℝ) := by
    intro i
    have h := card_pos_roots_le_mixedVolume (p i) (hp i) (positiveRoots (p i)) (by
      intro r hr
      rw [positiveRoots, Finset.mem_filter] at hr
      exact ⟨hr.2, (Polynomial.mem_roots (hp i)).mp (Multiset.mem_toFinset.mp hr.1)⟩)
    rw [h3 i] at h
    exact_mod_cast h
  -- Step 5: the product.
  have h4' : (∏ i, (positiveRoots (p i)).card) ≤ ∏ i, (newtonLength (p i)) := by
    refine Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (positiveRoots (p i)).card)
      (g := fun i => (newtonLength (p i))) ?_
    intro i _
    exact_mod_cast h2 i
  have h4 : (∏ i, ((positiveRoots (p i)).card : ℝ)) ≤ ∏ i, (newtonLength (p i) : ℝ) := by
    exact_mod_cast h4'
  have h6 : (S.card : ℝ) ≤ (∏ i, ((positiveRoots (p i)).card : ℝ)) := by
    exact_mod_cast h1
  calc (S.card : ℝ) ≤ (∏ i, ((positiveRoots (p i)).card : ℝ)) := h6
    _ ≤ ∏ i, (newtonLength (p i) : ℝ) := h4
    _ = ∏ i, mixedVolume (fun _ : Fin 1 => newtonPolytope (p i)) := by simp only [h3]

end MixedVolume
end CRNT
