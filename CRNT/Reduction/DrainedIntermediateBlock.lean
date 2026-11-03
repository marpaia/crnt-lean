import CRNT.Reduction.IntermediateSchurComplement
import CRNT.Reduction.LinearElimination

/-!
# Drainage makes the intermediate block invertible

`CRNT.IntermediateLinearBlock` performs Schur-complement elimination of intermediates under the
hypothesis that the intermediate block `A` is invertible. This module derives that hypothesis
from the structural drainage condition of `CRNT.Elimination` and shows that the eliminated
intermediate concentrations are then nonnegative (positive for positive inflows).

Main results:
* `CRNT.Elimination.opMatrix_mulVec`, `CRNT.Elimination.isUnit_det_opMatrix`.
* `CRNT.Elimination.drainedBlock`: an `IntermediateLinearBlock` with `A = -L`.
* `CRNT.Elimination.drainedBlock_eliminated_nonneg`,
  `CRNT.Elimination.drainedBlock_eliminated_pos`.
-/

namespace CRNT

namespace Elimination

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The matrix of the intermediate operator `L`. -/
def opMatrix (a : ι → ι → ℝ) (e : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then ∑ k, a k i + e i else 0) - a i j

theorem opMatrix_mulVec (a : ι → ι → ℝ) (e : ι → ℝ) (u : ι → ℝ) :
    (opMatrix a e).mulVec u = op a e u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, opMatrix, sub_mul, Finset.sum_sub_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, op]

/-- Under drainage the matrix of `L` is invertible. -/
theorem isUnit_det_opMatrix {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j)
    (he : ∀ i, 0 ≤ e i) (hdr : Drained a e) : IsUnit (opMatrix a e).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  apply op_injective ha he hdr
  show op a e u = op a e v
  rw [← opMatrix_mulVec, ← opMatrix_mulVec]
  exact huv

/-- The Schur-complement elimination block of a drained intermediate system: `A = -L`, so
`0 = A h + b` is `L h = b`. -/
noncomputable def drainedBlock {Core : Type} [Fintype Core] [DecidableEq Core]
    {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j) (he : ∀ i, 0 ≤ e i)
    (hdr : Drained a e) (input : (Core → ℝ) → (ι → ℝ)) (coreField : (Core → ℝ) → (Core → ℝ))
    (coupling : (ι → ℝ) →ₗ[ℝ] (Core → ℝ)) : IntermediateLinearBlock Core ι where
  A := -(opMatrix a e)
  input := input
  coreField := coreField
  coupling := coupling
  invertible := by
    rw [Matrix.det_neg]
    exact ((isUnit_neg_one (α := ℝ)).pow _).mul (isUnit_det_opMatrix ha he hdr)

/-- The eliminated intermediate solves `L h = input x`. -/
theorem drainedBlock_op_eliminated {Core : Type} [Fintype Core] [DecidableEq Core]
    {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j) (he : ∀ i, 0 ≤ e i)
    (hdr : Drained a e) (input : (Core → ℝ) → (ι → ℝ)) (coreField : (Core → ℝ) → (Core → ℝ))
    (coupling : (ι → ℝ) →ₗ[ℝ] (Core → ℝ)) (x : Core → ℝ) :
    op a e ((drainedBlock ha he hdr input coreField coupling).eliminatedIntermediate x) =
      input x := by
  set B := drainedBlock ha he hdr input coreField coupling
  have h := B.eliminatedIntermediate_solves x
  rw [← opMatrix_mulVec]
  have hA : B.A = -(opMatrix a e) := rfl
  rw [hA, Matrix.neg_mulVec] at h
  have hin : B.input x = input x := rfl
  rw [hin] at h
  exact neg_add_eq_zero.mp h

/-- Nonnegative inflows give nonnegative eliminated intermediates. -/
theorem drainedBlock_eliminated_nonneg {Core : Type} [Fintype Core] [DecidableEq Core]
    {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j) (he : ∀ i, 0 ≤ e i)
    (hdr : Drained a e) (input : (Core → ℝ) → (ι → ℝ)) (coreField : (Core → ℝ) → (Core → ℝ))
    (coupling : (ι → ℝ) →ₗ[ℝ] (Core → ℝ)) {x : Core → ℝ} (hx : ∀ i, 0 ≤ input x i) :
    ∀ i, 0 ≤ (drainedBlock ha he hdr input coreField coupling).eliminatedIntermediate x i :=
  nonneg_of_nonneg ha he hdr (fun i => by
    rw [drainedBlock_op_eliminated]; exact hx i)

/-- Positive inflows give positive eliminated intermediates. -/
theorem drainedBlock_eliminated_pos {Core : Type} [Fintype Core] [DecidableEq Core]
    {a : ι → ι → ℝ} {e : ι → ℝ} (ha : ∀ i j, 0 ≤ a i j) (he : ∀ i, 0 ≤ e i)
    (hdr : Drained a e) (input : (Core → ℝ) → (ι → ℝ)) (coreField : (Core → ℝ) → (Core → ℝ))
    (coupling : (ι → ℝ) →ₗ[ℝ] (Core → ℝ)) {x : Core → ℝ} (hx : ∀ i, 0 < input x i) :
    ∀ i, 0 < (drainedBlock ha he hdr input coreField coupling).eliminatedIntermediate x i :=
  pos_of_pos ha he hdr (drainedBlock_op_eliminated ha he hdr input coreField coupling x) hx

end Elimination

end CRNT
