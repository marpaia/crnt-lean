import CRNT.Multistationarity.TotalDegreeGeneral
import CRNT.Multistationarity.ParityGeneral
import CRNT.Multistationarity.MMatrixDeterminant

/-!
# The total-degree sign for fully open affine fields

For a fully open network, this module proves the classical total-degree sign in the affine-field
case.  If the affine field has an invertible linear part and its unique zero lies in the
nonnegative orthant, the reduced field on every class has Brouwer degree `(-1)^{card S}`.

The proof starts with the stoichiometric structure of the linear part `M`: the constant source is
strictly positive, the off-diagonal entries of `M` are nonnegative, and the nonnegative affine zero
is strictly positive with `M x* = -source`.  Thus `-M` has positive diagonal, nonpositive
off-diagonal, and maps `x* > 0` to the strictly positive source.  The existing nonsingular M-matrix
determinant criterion then gives `det(-M) > 0`.  This fixes the determinant sign and yields the
stated degree.

This is a genuine affine-field result.  It does **not** prove the general nonlinear total-degree
claim for arbitrary polynomial mass-action fields, whose degree at infinity depends on their
higher-degree leading part.  In particular, it does not establish a mixed-volume/Bernstein count
for quadratic or higher-degree fields.

The affine degree theorem used as the starting point is
`CRNT.Multistationarity.TotalDegreeGeneral.fullyOpen_classDegree_of_affineLinear`; this module
discharges its determinant-sign ambiguity for fully open affine mass-action fields.
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The mass-action monomial at the origin and at a basis vector -/

/-- **A complex is supported at a species** when it vanishes away from it: the source complex of
a reaction whose source consists of `m` molecules of the species `t` and nothing else. -/
def Complex.SupportedAt (t : S) (y : Complex S) : Prop := ∀ s, s ≠ t → y s = 0

/-- **The `t`-th basis vector of the species space.** -/
def Concentration.basisVec (t : S) : Concentration S := Pi.single t (1 : ℝ)

omit [DecidableEq S] in
/-- **The monomial of the empty complex** is `1`, at every concentration. -/
theorem massActionMonomial_zero_cone (x : Concentration S) :
    (0 : Complex S).massActionMonomial x = 1 := by
  have hz : (0 : Complex S) = Complex.zero := rfl
  rw [hz]
  exact Complex.massActionMonomial_zero x

omit [DecidableEq S] in
/-- **The mass-action monomial of a complex at the zero concentration** is `1` if the complex is
empty and `0` otherwise: a nonempty complex has a positive coefficient somewhere, and the
corresponding factor of the product is `0`. -/
theorem massActionMonomial_at_zero (y : Complex S) :
    y.massActionMonomial 0 = if y = 0 then 1 else 0 := by
  by_cases hy : y = 0
  · simp [hy, massActionMonomial_zero_cone]
  · obtain ⟨s, hs⟩ : ∃ s, y s ≠ 0 := by
      by_contra hcon
      refine hy (funext fun s => ?_)
      by_contra hs
      exact hcon ⟨s, hs⟩
    rw [Complex.massActionMonomial]
    simp only [hy]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    simp only [Pi.zero_apply, mul_zero]

/-- **The mass-action monomial of a complex at a basis vector** is `1` if the complex is supported
at the corresponding species and `0` otherwise. -/
theorem massActionMonomial_at_single (t : S) (y : Complex S) :
    y.massActionMonomial (Concentration.basisVec t) = if Complex.SupportedAt t y then 1 else 0 := by
  by_cases hy : Complex.SupportedAt t y
  · have hprod : (∏ s : S, (Concentration.basisVec t s) ^ (y s)) = 1 := by
      refine Finset.prod_eq_one fun s _ => ?_
      by_cases hst : s = t
      · subst hst
        simp [Concentration.basisVec]
      · have hys : y s = 0 := hy s hst
        simp [Concentration.basisVec, hys, hst]
    have hmono : y.massActionMonomial (Concentration.basisVec t) = 1 := by
      rw [Complex.massActionMonomial]
      exact hprod
    rw [hmono]
    simp [hy]
  · obtain ⟨s, hs, hne⟩ : ∃ s, y s ≠ 0 ∧ s ≠ t := by
      by_contra hcon
      refine hy fun s hst => ?_
      by_contra h2
      exact hcon ⟨s, h2, hst⟩
    rw [Complex.massActionMonomial]
    simp only [hy]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ, Concentration.basisVec, Pi.single_apply, ite_eq_right hne]
    simp only [mul_zero]

/-- **The difference of the monomials of a complex at a basis vector and at the origin** is `1`
exactly when the complex is nonempty and supported at that species: such a complex is the source
of a reaction with a one-molecule source complex, and it is the only kind of complex whose
monomial varies linearly in the concentration. -/
theorem massActionMonomial_sub_at_single_at_zero (t : S) (y : Complex S) :
    y.massActionMonomial (Concentration.basisVec t) - y.massActionMonomial 0
      = if y ≠ 0 ∧ Complex.SupportedAt t y then 1 else 0 := by
  by_cases hy0 : y = 0
  · simp [hy0, massActionMonomial_zero_cone]
  · by_cases hsup : Complex.SupportedAt t y
    · have h1 : y.massActionMonomial (Concentration.basisVec t) = 1 := by
        rw [massActionMonomial_at_single]
        simp [hsup]
      have h2 : y.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero]
        simp [hy0]
      rw [h1, h2]
      simp [hsup, hy0]
    · have h1 : y.massActionMonomial (Concentration.basisVec t) = 0 := by
        rw [massActionMonomial_at_single]
        simp [hsup]
      have h2 : y.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero]
        simp [hy0]
      rw [h1, h2]
      simp [hsup]

/-! ## The matrix of the linear part at infinity -/

/-- **The matrix of the linear part at infinity of a field in general affine form**, in the
standard basis of the species space: its `(s,t)` entry is the coefficient of `x_t` in the
`s`-th component of the field. -/
noncomputable def affineFieldMatrix {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) : Matrix S S ℝ :=
  LinearMap.toMatrix' h.M.toLinearMap

/-- **The entries of the matrix of the linear part at infinity.** -/
theorem affineFieldMatrix_apply {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) (s t : S) :
    affineFieldMatrix h s t = h.M.toLinearMap (Concentration.basisVec t) s := by
  rw [affineFieldMatrix, LinearMap.toMatrix'_apply]
  rfl

/-- **The determinant of the linear part at infinity** is the determinant of its matrix. -/
theorem det_affineFieldMatrix {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) :
    LinearMap.det h.M.toLinearMap = (affineFieldMatrix h).det := by
  rw [← LinearMap.det_toMatrix', affineFieldMatrix]

/-- **The product of the matrix of the linear part at infinity with a vector** is the linear part
applied to that vector. -/
theorem affineFieldMatrix_mulVec {N : Network S} {κ : N.RateConstants}
    (h : AffineFieldGeneral N κ) (x : Concentration S) :
    (affineFieldMatrix h).mulVec x = h.M.toLinearMap x := by
  rw [affineFieldMatrix, LinearMap.toMatrix'_mulVec]

/-! ## The source of a fully open field is strictly positive -/

/-- **The constant part of the field of a fully open network is strictly positive.**  The inflow
pseudo-reaction `0 → s` contributes the strictly positive rate constant `κ^{in}_s` to the
constant part, and every reaction with an empty source complex contributes a nonnegative constant
(a reaction with a nonempty source complex has a vanishing monomial at the origin, and a reaction
with an empty source complex has a nonnegative reaction vector). -/
theorem fullyOpen_affineFieldGeneral_source_pos {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ) (s : S) : 0 < h.source s := by
  have h1 : h.source s = N.fullyOpen.massActionVectorField κ 0 s := by
    rw [h.eq_field]
    simp
  rw [h1, fullyOpen_massActionVectorField_eq]
  have hsum : 0 ≤ (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial 0 *
      N.reactionVector r s) := by
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases hs0 : (N.reaction r).source = 0
    · have hmono : (N.reaction r).source.massActionMonomial 0 = 1 := by
        rw [hs0]
        exact massActionMonomial_zero_cone 0
      have hvec : N.reactionVector r s = ((N.reaction r).target s : ℝ) := by
        rw [reactionVector_apply]
        have hz : ((N.reaction r).source s : ℝ) = 0 := by
          rw [hs0]
          simp
        rw [hz, sub_zero]
      have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, hvec, mul_one]
      exact mul_nonneg hk.le (Nat.cast_nonneg _)
    · have hmono : (N.reaction r).source.massActionMonomial 0 = 0 := by
        rw [massActionMonomial_at_zero, ite_eq_right hs0]
      rw [hmono, mul_zero, zero_mul]
  have hin : 0 < κ.k (Sum.inr (Sum.inl s)) := κ.positive _
  simp only [Pi.zero_apply]
  linarith

/-! ## The off-diagonal entries of the linear part at infinity are nonnegative -/

/-- **The off-diagonal entries of the linear part at infinity of a fully open field are
nonnegative.**  A reaction with a one-molecule source complex `e_t` contributes
`κ_r (y'_r)_s` to the `(s,t)` entry of the linear part, and `(y'_r)_s ≥ 0`; the outflow
pseudo-reaction `t → 0` contributes only to the `(t,t)` entry. -/
theorem fullyOpen_affineFieldGeneral_offdiag_nonneg {N : Network S}
    {κ : N.fullyOpen.RateConstants} (h : AffineFieldGeneral N.fullyOpen κ) {s t : S}
    (hst : s ≠ t) : 0 ≤ h.M.toLinearMap (Concentration.basisVec t) s := by
  -- the linear part is the difference of the field at a basis vector and at the origin
  have hdiff : h.M.toLinearMap (Concentration.basisVec t) s
      = N.fullyOpen.massActionVectorField κ (Concentration.basisVec t) s
        - N.fullyOpen.massActionVectorField κ 0 s := by
    rw [h.eq_field, h.eq_field]
    simp
  rw [hdiff, fullyOpen_massActionVectorField_eq, fullyOpen_massActionVectorField_eq]
  -- the outflow term vanishes, because `s ≠ t`
  have hout : κ.k (Sum.inr (Sum.inr s)) * (Concentration.basisVec t s) = 0 := by
    rw [Concentration.basisVec, Pi.single_apply, ite_eq_right hst]
    simp
  rw [hout]
  simp only [Pi.zero_apply, sub_zero]
  -- the difference of the two sums is the sum of the differences
  have hsplit : (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial
        (Concentration.basisVec t) * N.reactionVector r s)
      - (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial 0
        * N.reactionVector r s)
      = ∑ r : N.R, κ.k (Sum.inl r) *
          ((N.reaction r).source.massActionMonomial (Concentration.basisVec t)
            - (N.reaction r).source.massActionMonomial 0) * N.reactionVector r s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  -- every summand is nonnegative
  have hsum : 0 ≤ (∑ r : N.R, κ.k (Sum.inl r) *
      ((N.reaction r).source.massActionMonomial (Concentration.basisVec t)
        - (N.reaction r).source.massActionMonomial 0) * N.reactionVector r s) := by
    refine Finset.sum_nonneg fun r _ => ?_
    have hmono := massActionMonomial_sub_at_single_at_zero t (N.reaction r).source
    by_cases hkey : (N.reaction r).source ≠ 0 ∧ Complex.SupportedAt t (N.reaction r).source
    · have hz : (N.reaction r).source s = 0 := by
        by_contra hz
        exact absurd (hkey.2 s hst) hz
      have hvec : N.reactionVector r s = ((N.reaction r).target s : ℝ) := by
        rw [reactionVector_apply]
        have hz' : ((N.reaction r).source s : ℝ) = 0 := by
          rw [hz]
          simp
        rw [hz', sub_zero]
      have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, ite_eq_left hkey, hvec, mul_one]
      exact mul_nonneg hk.le (Nat.cast_nonneg _)
    · have hk : 0 < κ.k (Sum.inl r) := κ.positive _
      rw [hmono, ite_eq_right hkey, mul_zero, zero_mul]
  linarith

/-! ## The zero of a fully open field is strictly positive -/

/-- **The zero of the field of a fully open network in general affine form is strictly positive**
as soon as it is nonnegative.  Indeed `M x* = −source` with `source` strictly positive and `x*`
nonnegative, and the off-diagonal entries of `M` are nonnegative, so no coordinate of `x*` can
vanish. -/
theorem fullyOpen_affineFieldGeneral_zero_pos {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    Concentration.Positive (affineFieldZeroGeneral h) := by
  intro s
  have hspec := affineFieldZeroGeneral_spec h
  -- `M x* = -source`
  have hmul : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) = -h.source := by
    rw [affineFieldMatrix_mulVec h]
    exact hspec
  have hsneg : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s = -h.source s := by
    rw [hmul]
    rfl
  -- the `s`-component splits into the diagonal term and the nonnegative off-diagonal terms
  have hsplit : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s
      = (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s
        + ∑ t ∈ (Finset.univ : Finset S).erase s,
            (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t := by
    simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply]
    have h := Finset.sum_erase_add (Finset.univ : Finset S)
      (fun t => (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t)
      (Finset.mem_univ s)
    rw [← h]
    ring
  have hsum : 0 ≤ (∑ t ∈ (Finset.univ : Finset S).erase s,
      (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t) := by
    refine Finset.sum_nonneg fun t ht => ?_
    have h1 : 0 ≤ (affineFieldMatrix h) s t := by
      rw [affineFieldMatrix_apply]
      exact fullyOpen_affineFieldGeneral_offdiag_nonneg h (Ne.symm (Finset.mem_erase.mp ht).1)
    exact mul_nonneg h1 (hz t)
  have hsrc : 0 < h.source s := fullyOpen_affineFieldGeneral_source_pos h s
  have hxs : 0 ≤ (affineFieldZeroGeneral h) s := hz s
  rw [hsplit] at hsneg
  have hdiag : (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s < 0 := by linarith
  by_contra hcon
  have hz' : (affineFieldZeroGeneral h) s = 0 := le_antisymm (le_of_not_gt hcon) hxs
  rw [hz'] at hdiag
  linarith

/-! ## The diagonal entries of the linear part at infinity are strictly negative -/

/-- **The diagonal entries of the linear part at infinity of a fully open field are strictly
negative**, provided the zero of the field is nonnegative: the `s`-th component of
`M x* = −source` is negative, its off-diagonal summands are nonnegative, and `x*_s > 0`. -/
theorem fullyOpen_affineFieldGeneral_diag_neg {N : Network S} {κ : N.fullyOpen.RateConstants}
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) (s : S) :
    h.M.toLinearMap (Concentration.basisVec s) s < 0 := by
  have hpos := fullyOpen_affineFieldGeneral_zero_pos h hz
  have hspec := affineFieldZeroGeneral_spec h
  have hmul : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) = -h.source := by
    rw [affineFieldMatrix_mulVec h]
    exact hspec
  have hsneg : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s = -h.source s := by
    rw [hmul]
    rfl
  have hsplit : (affineFieldMatrix h).mulVec (affineFieldZeroGeneral h) s
      = (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s
        + ∑ t ∈ (Finset.univ : Finset S).erase s,
            (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t := by
    simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply]
    have h := Finset.sum_erase_add (Finset.univ : Finset S)
      (fun t => (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t)
      (Finset.mem_univ s)
    rw [← h]
    ring
  have hsum : 0 ≤ (∑ t ∈ (Finset.univ : Finset S).erase s,
      (affineFieldMatrix h) s t * (affineFieldZeroGeneral h) t) := by
    refine Finset.sum_nonneg fun t ht => ?_
    have h1 : 0 ≤ (affineFieldMatrix h) s t := by
      rw [affineFieldMatrix_apply]
      exact fullyOpen_affineFieldGeneral_offdiag_nonneg h (Ne.symm (Finset.mem_erase.mp ht).1)
    exact mul_nonneg h1 (hz t)
  have hsrc : 0 < h.source s := fullyOpen_affineFieldGeneral_source_pos h s
  have hxs : 0 < (affineFieldZeroGeneral h) s := hpos s
  rw [hsplit] at hsneg
  have hdiag : (affineFieldMatrix h) s s * (affineFieldZeroGeneral h) s < 0 := by linarith
  have hmain : (affineFieldMatrix h) s s < 0 := by nlinarith
  show h.M.toLinearMap (Concentration.basisVec s) s < 0
  rw [← affineFieldMatrix_apply]
  exact hmain

/-! ## The determinant sign for a fully open affine mass-action field -/

/-- The negative of the linear part at infinity of a fully open affine mass-action field has
positive determinant whenever its zero lies in the nonnegative orthant.  Its off-diagonal entries
are nonpositive, its diagonal entries are positive, and it maps the positive zero to the positive
inflow vector. -/
theorem fullyOpen_affineFieldGeneral_neg_det_pos {N : Network S}
    {κ : N.fullyOpen.RateConstants} (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    0 < (-affineFieldMatrix h).det := by
  let A : Matrix S S ℝ := -affineFieldMatrix h
  let x : S → ℝ := affineFieldZeroGeneral h
  have hx : ∀ i, 0 < x i := fullyOpen_affineFieldGeneral_zero_pos h hz
  have hoff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    change -(affineFieldMatrix h i j) ≤ 0
    have hM := fullyOpen_affineFieldGeneral_offdiag_nonneg h hij
    rw [affineFieldMatrix_apply]
    linarith
  have hdiag : ∀ i, 0 < A i i := by
    intro i
    change 0 < -(affineFieldMatrix h i i)
    rw [affineFieldMatrix_apply]
    exact neg_pos.mpr (fullyOpen_affineFieldGeneral_diag_neg h hz i)
  have hmul : (affineFieldMatrix h).mulVec x = -h.source := by
    rw [affineFieldMatrix_mulVec]
    exact affineFieldZeroGeneral_spec h
  have hAx : ∀ i, 0 < A.mulVec x i := by
    intro i
    have hrow : A.mulVec x = h.source := by
      simp only [A, Matrix.neg_mulVec]
      rw [hmul]
      simp
    rw [hrow]
    exact fullyOpen_affineFieldGeneral_source_pos h i
  have hpos := det_pos_of_negZMatrix_of_pos_mulVec A x hdiag hoff hx hAx
  simpa [A] using hpos

/-- **The classical sign of the total degree for a fully open affine mass-action field.**
If its affine zero is nonnegative, the linear part at infinity has determinant sign
`(-1)^{card S}`; consequently the reduced field has that same class degree.  This closes the
fully-open affine case of the total-degree sign claim without assuming a sign for the determinant. -/
theorem fullyOpen_classDegree_of_affineLinear_eq_negOne_pow
    (N : Network S) (κ : N.fullyOpen.RateConstants) (c : Concentration S)
    (h : AffineFieldGeneral N.fullyOpen κ)
    (hz : Concentration.Nonnegative (affineFieldZeroGeneral h)) :
    N.fullyOpen.nonnegativeClassDegree κ c
      (fullyOpen_hfin_affineGeneral N κ c h hz) = (-1 : ℤ) ^ Fintype.card S := by
  have hfin := fullyOpen_hfin_affineGeneral N κ c h hz
  have hneg := fullyOpen_affineFieldGeneral_neg_det_pos h hz
  rw [Matrix.det_neg] at hneg
  by_cases heven : Even (Fintype.card S)
  · have hpow : (-1 : ℝ) ^ Fintype.card S = 1 :=
      (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).2 heven
    have hdet : 0 < (affineFieldMatrix h).det := by nlinarith
    rw [fullyOpen_classDegree_of_affineLinear N κ c h hz hfin,
      det_affineFieldMatrix, sign_pos hdet]
    have hpowInt : (-1 : ℤ) ^ Fintype.card S = 1 :=
      (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).2 heven
    simp [hpowInt]
  · have hodd : Odd (Fintype.card S) := Nat.not_even_iff_odd.mp heven
    have hpow : (-1 : ℝ) ^ Fintype.card S = -1 :=
      (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)).2 hodd
    have hdet : (affineFieldMatrix h).det < 0 := by nlinarith
    rw [fullyOpen_classDegree_of_affineLinear N κ c h hz hfin,
      det_affineFieldMatrix, sign_neg hdet]
    have hpowInt : (-1 : ℤ) ^ Fintype.card S = -1 :=
      (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).2 hodd
    simp [hpowInt]

/-! ## The axioms used by the principal declarations -/

#print axioms fullyOpen_affineFieldGeneral_source_pos
#print axioms fullyOpen_affineFieldGeneral_offdiag_nonneg
#print axioms fullyOpen_affineFieldGeneral_zero_pos
#print axioms fullyOpen_affineFieldGeneral_diag_neg
#print axioms fullyOpen_affineFieldGeneral_neg_det_pos
#print axioms fullyOpen_classDegree_of_affineLinear_eq_negOne_pow

end Network

end CRNT
