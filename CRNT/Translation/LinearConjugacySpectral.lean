import CRNT.Translation.LinearConjugacy
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Spectral invariants of positive diagonal conjugacy

The Jacobians of linearly conjugate reaction systems are similar through a positive
diagonal matrix.  Hence every invariant of matrix similarity--characteristic polynomial,
determinant, trace, spectrum and algebraic multiplicities--is transported exactly.
This module records those consequences separately from the dynamical definition.
-/

namespace CRNT
namespace Network

open Polynomial

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The diagonal matrices of a positive coordinate change are mutual inverses. -/
theorem PositiveDiagonalChange.matrix_mul_invMatrix
    (D : PositiveDiagonalChange S) :
    D.matrix * D.invMatrix = (1 : Matrix S S ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [PositiveDiagonalChange.matrix, PositiveDiagonalChange.invMatrix,
      (D.positive i).ne']
  · simp [PositiveDiagonalChange.matrix, PositiveDiagonalChange.invMatrix, hij]

/-- Reverse inverse identity. -/
theorem PositiveDiagonalChange.invMatrix_mul_matrix
    (D : PositiveDiagonalChange S) :
    D.invMatrix * D.matrix = (1 : Matrix S S ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [PositiveDiagonalChange.matrix, PositiveDiagonalChange.invMatrix,
      (D.positive i).ne']
  · simp [PositiveDiagonalChange.matrix, PositiveDiagonalChange.invMatrix, hij]

/-- Similar Jacobians have the same characteristic polynomial. -/
theorem jacobian_charpoly_eq_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    Matrix.charpoly (M.massActionJacobian κM (D.map x)) =
      Matrix.charpoly (N.massActionJacobian κN x) := by
  rw [jacobian_similarity_of_linearConjugacy h x]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, D.invMatrix_mul_matrix,
    Matrix.one_mul]

/-- Determinant is invariant under positive diagonal linear conjugacy. -/
theorem jacobian_det_eq_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    Matrix.det (M.massActionJacobian κM (D.map x)) =
      Matrix.det (N.massActionJacobian κN x) := by
  rw [jacobian_similarity_of_linearConjugacy h x]
  have hdet : Matrix.det D.matrix * Matrix.det D.invMatrix = 1 := by
    calc
      Matrix.det D.matrix * Matrix.det D.invMatrix =
          Matrix.det (D.matrix * D.invMatrix) := (Matrix.det_mul _ _).symm
      _ = Matrix.det (1 : Matrix S S ℝ) := congrArg Matrix.det D.matrix_mul_invMatrix
      _ = 1 := Matrix.det_one
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det D.matrix * Matrix.det (N.massActionJacobian κN x) * Matrix.det D.invMatrix =
        Matrix.det (N.massActionJacobian κN x) *
          (Matrix.det D.matrix * Matrix.det D.invMatrix) := by ring
    _ = Matrix.det (N.massActionJacobian κN x) := by rw [hdet, mul_one]

/-- Trace is invariant under positive diagonal linear conjugacy. -/
theorem jacobian_trace_eq_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    Matrix.trace (M.massActionJacobian κM (D.map x)) =
      Matrix.trace (N.massActionJacobian κN x) := by
  rw [jacobian_similarity_of_linearConjugacy h x]
  rw [Matrix.trace_mul_cycle, D.invMatrix_mul_matrix, Matrix.one_mul]

/-- Singularity/nondegeneracy of the full Jacobian is invariant under linear conjugacy. -/
theorem jacobian_nonsingular_iff_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    Matrix.det (N.massActionJacobian κN x) ≠ 0 ↔
      Matrix.det (M.massActionJacobian κM (D.map x)) ≠ 0 := by
  rw [jacobian_det_eq_of_linearConjugacy h x]

/-- Every eigenvalue is preserved by the Jacobian similarity relation. -/
theorem jacobian_eigenvalue_iff_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) (lam : ℂ) :
    IsRoot ((Matrix.charpoly (N.massActionJacobian κN x)).map (algebraMap ℝ ℂ)) lam ↔
      IsRoot ((Matrix.charpoly (M.massActionJacobian κM (D.map x))).map (algebraMap ℝ ℂ)) lam := by
  rw [jacobian_charpoly_eq_of_linearConjugacy h x]

/-- Therefore any local stability criterion depending only on the Jacobian spectrum is
invariant under positive diagonal realization conjugacy. -/
def SpectralLocalProperty (P : Multiset ℂ → Prop) (A : Matrix S S ℝ) : Prop :=
  P ((A.charpoly.map (algebraMap ℝ ℂ)).roots)

end Network
end CRNT
