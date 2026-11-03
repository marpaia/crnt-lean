import CRNT.Multistationarity.PMatrix
import CRNT.Dynamics.RouthHurwitz
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Matrix predicates for modern structural Hopf/oscillation criteria

This file mirrors the linear-algebra vocabulary used in Vassena's 2025 mass-action oscillation
criteria more closely than the initial checkpoint did.

* `P^-`: all `k`-principal minors have strict sign `(-1)^k`;
* `P^-_0`: all nonzero `k`-principal minors have sign `(-1)^k`, equivalently the corresponding
  principal minors of `-M` are nonnegative;
* Fisher--Fuller `P^-_{FF}`: a `P^-_0` matrix admitting a nested nonsingular principal-submatrix
  chain of every order;
* right `D`-stability: `M * D` is Hurwitz for every positive diagonal `D`, matching the factorization
  `J = B(v) * diag(1/x)` used for mass-action Jacobians.

`CriterionI` and `CriterionII` package only the matrix side of Corollary 5.3 of Vassena (2025):
respectively a stable matrix which is not `P^-_0`, and an unstable Fisher--Fuller `P^-_{FF}` matrix.
The steady-state-flux/Jacobian realization and global-Hopf bridge are separate theorem frontiers; no
periodic-orbit conclusion is smuggled into these definitions.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Determinant of the principal submatrix indexed by `s`. -/
def principalDet (M : Matrix n n ℝ) (s : Finset n) : ℝ :=
  (M.submatrix (fun i : s => (i : n)) (fun i : s => (i : n))).det

/-- A `P^-` matrix: negating it gives a strict P-matrix. -/
def IsPMinusMatrix (M : Matrix n n ℝ) : Prop :=
  (-M).IsPMatrix

/-- A `P_0` matrix has all principal minors nonnegative. -/
def IsPZeroMatrix (M : Matrix n n ℝ) : Prop :=
  ∀ s : Finset n, 0 ≤ principalDet M s

/-- A `P^-_0` matrix: all nonzero `k`-principal minors have sign `(-1)^k`.  Equivalently,
all principal minors of `-M` are nonnegative. -/
def IsPMinusZeroMatrix (M : Matrix n n ℝ) : Prop :=
  (-M).IsPZeroMatrix

namespace IsPMinusMatrix

/-- The defining equivalence with the strict P-matrix predicate. -/
theorem iff_neg_isPMatrix {M : Matrix n n ℝ} :
    M.IsPMinusMatrix ↔ (-M).IsPMatrix := Iff.rfl

/-- Every diagonal entry of a strict `P^-` matrix is strictly negative. -/
theorem diag_neg {M : Matrix n n ℝ} (h : M.IsPMinusMatrix) (i : n) : M i i < 0 := by
  change (-M).IsPMatrix at h
  have hneg : 0 < (-M) i i := Matrix.IsPMatrix.diag_pos h i
  simpa using hneg

/-- Principal submatrices of strict `P^-` matrices are again strict `P^-`. -/
theorem submatrix_isPMinusMatrix {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix n n ℝ} {e : m → n} (he : Function.Injective e)
    (h : M.IsPMinusMatrix) : (M.submatrix e e).IsPMinusMatrix := by
  change (-M).IsPMatrix at h
  show (-(M.submatrix e e)).IsPMatrix
  have hsub : -(M.submatrix e e) = (-M).submatrix e e := by
    ext i j
    simp
  rw [hsub]
  exact Matrix.IsPMatrix.submatrix_isPMatrix he h

/-- Every strict `P^-` matrix is `P^-_0`. -/
theorem isPMinusZeroMatrix {M : Matrix n n ℝ} (h : M.IsPMinusMatrix) :
    M.IsPMinusZeroMatrix := by
  change (-M).IsPMatrix at h
  change (-M).IsPZeroMatrix
  intro s
  exact (h s).le

end IsPMinusMatrix

/-- A real matrix is Hurwitz when the characteristic polynomial of its complexification has all
roots in the open left half-plane. -/
def IsHurwitzReal (M : Matrix n n ℝ) : Prop :=
  CRNT.IsHurwitz ((M.map (algebraMap ℝ ℂ)).charpoly)

/-- A real matrix has a genuinely unstable eigenvalue when its complexified characteristic
polynomial has a root in the open right half-plane. -/
def HasUnstableEigenvalue (M : Matrix n n ℝ) : Prop :=
  ∃ z : ℂ, z ∈ (M.map (algebraMap ℝ ℂ)).charpoly.roots ∧ 0 < z.re

/-- A matrix with a right-half-plane eigenvalue is not Hurwitz. -/
theorem not_isHurwitzReal_of_hasUnstableEigenvalue {M : Matrix n n ℝ}
    (h : M.HasUnstableEigenvalue) : ¬ M.IsHurwitzReal := by
  intro hhur
  obtain ⟨z, hz, hzpos⟩ := h
  have hzneg : z.re < 0 := hhur z hz
  linarith

/-- Right diagonal (`D`) stability: every positive right diagonal scaling remains Hurwitz.
This orientation matches the steady-state Jacobian factorization `B(v) * diag(1/x)`. -/
def IsDStable (M : Matrix n n ℝ) : Prop :=
  ∀ d : n → ℝ, (∀ i, 0 < d i) → IsHurwitzReal (M * Matrix.diagonal d)

namespace IsDStable

/-- A right `D`-stable matrix is itself Hurwitz, by choosing the identity diagonal scaling. -/
theorem isHurwitzReal {M : Matrix n n ℝ} (h : M.IsDStable) : M.IsHurwitzReal := by
  have h1 := h (fun _ : n => (1 : ℝ)) (fun _ => zero_lt_one)
  have hdiag : Matrix.diagonal (fun _ : n => (1 : ℝ)) = (1 : Matrix n n ℝ) := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [hdiag, mul_one] at h1
  exact h1

/-- A right `D`-stable matrix cannot already have a strict right-half-plane eigenvalue. -/
theorem not_hasUnstableEigenvalue {M : Matrix n n ℝ} (h : M.IsDStable) :
    ¬ M.HasUnstableEigenvalue := by
  intro hu
  exact (not_isHurwitzReal_of_hasUnstableEigenvalue hu) h.isHurwitzReal

end IsDStable

/-- Fisher--Fuller `P^-_{FF}` matrix.

A `P^-_0` matrix belongs to this class when there exists a nested sequence of nonsingular principal
submatrices of every order `1,...,n`, ending at the full matrix.  The function is unconstrained
outside that finite range; this keeps the definition independent of a chosen enumeration of `n`. -/
def IsFisherFullerPMinusMatrix (M : Matrix n n ℝ) : Prop :=
  M.IsPMinusZeroMatrix ∧ 0 < Fintype.card n ∧
    ∃ κ : ℕ → Finset n,
      (∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card n →
        (κ k).card = k ∧ principalDet M (κ k) ≠ 0) ∧
      (∀ k : ℕ, 1 ≤ k → k < Fintype.card n → κ k ⊆ κ (k + 1)) ∧
      κ (Fintype.card n) = Finset.univ


/-- Principal submatrix selected by a finite index set. -/
def principalSubmatrix (M : Matrix n n ℝ) (I : Finset n) :
    Matrix {i : n // i ∈ I} {i : n // i ∈ I} ℝ :=
  M.submatrix (fun i => i.1) (fun i => i.1)

/-- A matrix is a **minimal unstable core** when it has a strict right-half-plane eigenvalue and no
proper principal submatrix has one.  This is the matrix-level notion used by the child-selection
literature; CRN child selections below simply instantiate it with their stoichiometric matrix. -/
def IsUnstableCore (M : Matrix n n ℝ) : Prop :=
  M.HasUnstableEigenvalue ∧
    ∀ I : Finset n, I ⊂ Finset.univ →
      ¬ (M.principalSubmatrix I).HasUnstableEigenvalue

namespace IsUnstableCore

/-- Every unstable core is unstable by definition. -/
theorem unstable {M : Matrix n n ℝ} (h : M.IsUnstableCore) : M.HasUnstableEigenvalue :=
  h.1

/-- Every proper principal block of an unstable core lacks a strict right-half-plane eigenvalue. -/
theorem properPrincipal_not_unstable {M : Matrix n n ℝ} (h : M.IsUnstableCore)
    (I : Finset n) (hI : I ⊂ Finset.univ) :
    ¬ (M.principalSubmatrix I).HasUnstableEigenvalue :=
  h.2 I hI

end IsUnstableCore

/-- Determinant sign of an unstable negative feedback: the determinant has the Hurwitz-compatible
sign `(-1)^n`. -/
def HasNegativeFeedbackSign (M : Matrix n n ℝ) : Prop :=
  0 < ((-1 : ℝ) ^ Fintype.card n) * M.det

/-- Determinant sign of an unstable positive feedback: the determinant has the opposite sign
`(-1)^(n-1)`. -/
def HasPositiveFeedbackSign (M : Matrix n n ℝ) : Prop :=
  ((-1 : ℝ) ^ Fintype.card n) * M.det < 0

/-- Matrix-level unstable negative feedback. -/
def IsUnstableNegativeFeedback (M : Matrix n n ℝ) : Prop :=
  M.IsUnstableCore ∧ M.HasNegativeFeedbackSign

/-- Matrix-level unstable positive feedback. -/
def IsUnstablePositiveFeedback (M : Matrix n n ℝ) : Prop :=
  M.IsUnstableCore ∧ M.HasPositiveFeedbackSign

/-- A matrix contains an unstable-positive feedback as a proper principal submatrix. -/
def ContainsUnstablePositiveFeedback (M : Matrix n n ℝ) : Prop :=
  ∃ I : Finset n, I ⊂ Finset.univ ∧
    (M.principalSubmatrix I).IsUnstablePositiveFeedback

/-- The defining property of a class-I oscillatory core before minimalization: Hurwitz stability
plus an unstable-positive-feedback principal submatrix. -/
def HasClassIOscillatoryProperty (M : Matrix n n ℝ) : Prop :=
  M.IsHurwitzReal ∧ M.ContainsUnstablePositiveFeedback

/-- **Oscillatory core, class I** (Blokhuis--Stadler--Vassena): a matrix minimal, under proper
principal submatrices, with the property of being Hurwitz stable while containing an
unstable-positive feedback. -/
def IsOscillatoryCoreClassI (M : Matrix n n ℝ) : Prop :=
  M.HasClassIOscillatoryProperty ∧
    ∀ I : Finset n, I ⊂ Finset.univ →
      ¬ (M.principalSubmatrix I).HasClassIOscillatoryProperty

/-- A square matrix has a Hurwitz-stable principal submatrix of codimension one. -/
def HasStableCodimOnePrincipalSubmatrix (M : Matrix n n ℝ) : Prop :=
  ∃ I : Finset n, I.card + 1 = Fintype.card n ∧
    (M.principalSubmatrix I).IsHurwitzReal

/-- **Oscillatory core, class II** (Blokhuis--Stadler--Vassena): an unstable-negative feedback
which either is Fisher--Fuller `P^-_{FF}` or has a Hurwitz-stable codimension-one principal
submatrix. -/
def IsOscillatoryCoreClassII (M : Matrix n n ℝ) : Prop :=
  M.IsUnstableNegativeFeedback ∧
    (M.IsFisherFullerPMinusMatrix ∨ M.HasStableCodimOnePrincipalSubmatrix)

/-- Every class-I oscillatory core is Hurwitz stable. -/
theorem IsOscillatoryCoreClassI.stable {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassI) : M.IsHurwitzReal :=
  h.1.1

/-- Every class-I oscillatory core contains a proper unstable-positive-feedback principal block. -/
theorem IsOscillatoryCoreClassI.containsUnstablePositiveFeedback {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassI) : M.ContainsUnstablePositiveFeedback :=
  h.1.2

/-- Every class-II oscillatory core is an unstable-negative feedback. -/
theorem IsOscillatoryCoreClassII.unstableNegativeFeedback {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassII) : M.IsUnstableNegativeFeedback :=
  h.1

/-- In particular, every class-II oscillatory core has a strict right-half-plane eigenvalue. -/
theorem IsOscillatoryCoreClassII.unstable {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassII) : M.HasUnstableEigenvalue :=
  h.1.1.1

/-- A class-II core satisfies one of the two exact auxiliary alternatives used in its definition. -/
theorem IsOscillatoryCoreClassII.fisherFuller_or_stableCodimOne {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassII) :
    M.IsFisherFullerPMinusMatrix ∨ M.HasStableCodimOnePrincipalSubmatrix :=
  h.2

/-- Fisher--Fuller membership includes the `P^-_0` condition by definition. -/
theorem IsFisherFullerPMinusMatrix.isPMinusZero {M : Matrix n n ℝ}
    (h : M.IsFisherFullerPMinusMatrix) : M.IsPMinusZeroMatrix :=
  h.1

/-- Fisher--Fuller membership includes a nonsingular principal block of full order, hence the
whole matrix is nonsingular.  This is the full-size endpoint of the nested principal-minor chain. -/
theorem IsFisherFullerPMinusMatrix.det_ne_zero {M : Matrix n n ℝ}
    (h : M.IsFisherFullerPMinusMatrix) : M.det ≠ 0 := by
  obtain ⟨_hP0, hcard, κ, hminor, _hnested, hfull⟩ := h
  have hk := (hminor (Fintype.card n) (Nat.succ_le_iff.mpr hcard) le_rfl).2
  rw [hfull] at hk
  -- the order-`card n` principal minor is taken over all of `n`, so its submatrix is `M`
  -- itself up to the canonical bijection `↥univ ≃ n`.
  simp only [principalDet] at hk
  intro h0
  refine hk ?_
  -- the coercion `↥univ → n` *is* `Equiv.subtypeUnivEquiv`, but only up to unfolding
  have he : (fun i : {x // x ∈ (Finset.univ : Finset n)} => (i : n))
      = (Equiv.subtypeUnivEquiv (fun i => Finset.mem_univ i) : _ → n) := rfl
  rw [he, Matrix.det_submatrix_equiv_self]
  exact h0

/-- Matrix side of Vassena Criterion I: stable but not `P^-_0`. -/
structure CriterionI (M : Matrix n n ℝ) : Prop where
  stable : M.IsHurwitzReal
  notPMinusZero : ¬ M.IsPMinusZeroMatrix

/-- Matrix side of Vassena Criterion II: unstable Fisher--Fuller `P^-_{FF}`. -/
structure CriterionII (M : Matrix n n ℝ) : Prop where
  unstable : M.HasUnstableEigenvalue
  fisherFuller : M.IsFisherFullerPMinusMatrix

namespace CriterionII

/-- Criterion II is incompatible with Hurwitz stability. -/
theorem not_isHurwitzReal {M : Matrix n n ℝ} (h : CriterionII M) : ¬ M.IsHurwitzReal :=
  not_isHurwitzReal_of_hasUnstableEigenvalue h.unstable

end CriterionII

/-- Class-I and class-II oscillatory-core predicates are mutually exclusive: class I is Hurwitz
stable, whereas class II carries a strict right-half-plane eigenvalue. -/
theorem IsOscillatoryCoreClassI.not_classII {M : Matrix n n ℝ}
    (hI : M.IsOscillatoryCoreClassI) : ¬ M.IsOscillatoryCoreClassII := by
  intro hII
  exact (not_isHurwitzReal_of_hasUnstableEigenvalue hII.unstable) hI.stable

/-- Symmetric form of class-I/class-II exclusivity. -/
theorem IsOscillatoryCoreClassII.not_classI {M : Matrix n n ℝ}
    (hII : M.IsOscillatoryCoreClassII) : ¬ M.IsOscillatoryCoreClassI := by
  intro hI
  exact hI.not_classII hII

/-- Backwards-compatible descriptive alias for Criterion I. -/
abbrev StableNotPMinusZero (M : Matrix n n ℝ) := CriterionI M

/-- Backwards-compatible descriptive alias for Criterion II. -/
abbrev UnstableFisherFullerPMinus (M : Matrix n n ℝ) := CriterionII M

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace IsHurwitzReal

/-- A Hurwitz matrix is nonsingular: otherwise zero is a characteristic root, contradicting the
strict left-half-plane root condition. -/
theorem det_ne_zero {M : Matrix n n ℝ} (h : M.IsHurwitzReal) : M.det ≠ 0 := by
  intro hdet
  let MC : Matrix n n ℂ := M.map (algebraMap ℝ ℂ)
  have hdetC : MC.det = 0 := by
    -- `RingHom.map_det` is stated for `RingHom.mapMatrix`, which is `Matrix.map` definitionally
    show ((algebraMap ℝ ℂ).mapMatrix M).det = 0
    rw [← RingHom.map_det, hdet, map_zero]
  -- the characteristic polynomial is monic, hence nonzero
  have hpoly : MC.charpoly ≠ 0 := (Matrix.charpoly_monic MC).ne_zero
  have heval : Polynomial.eval (0 : ℂ) MC.charpoly = 0 := by
    rw [Matrix.eval_charpoly]
    -- `eval 0` of the characteristic polynomial is `det (-MC)`, and `det` is homogeneous.
    -- `Matrix.eval_charpoly` phrases the entries via `Complex.ofReal` rather than
    -- `algebraMap ℝ ℂ`, so restate the vanishing determinant in that form.
    have hdet' : (M.map Complex.ofReal).det = 0 := by
      show (Complex.ofRealHom.mapMatrix M).det = 0
      rw [← RingHom.map_det, hdet, map_zero]
    simp [Matrix.det_neg, hdet']
    exact hdetC
  have hroot : (0 : ℂ) ∈ MC.charpoly.roots := by
    rw [Polynomial.mem_roots hpoly]
    exact heval
  have hleft := h (0 : ℂ) hroot
  norm_num at hleft

end IsHurwitzReal

/-- Negative-feedback determinant sign is in particular a nonsingularity certificate. -/
theorem HasNegativeFeedbackSign.det_ne_zero {M : Matrix n n ℝ}
    (h : M.HasNegativeFeedbackSign) : M.det ≠ 0 := by
  intro hzero
  rw [Matrix.HasNegativeFeedbackSign, hzero, mul_zero] at h
  linarith

/-- Positive-feedback determinant sign is likewise nonsingular. -/
theorem HasPositiveFeedbackSign.det_ne_zero {M : Matrix n n ℝ}
    (h : M.HasPositiveFeedbackSign) : M.det ≠ 0 := by
  intro hzero
  rw [Matrix.HasPositiveFeedbackSign, hzero, mul_zero] at h
  linarith

end Matrix
