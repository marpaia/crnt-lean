import CRNT.Multistationarity.PMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur complements of P-matrices

The Schur complement of a P-matrix is a P-matrix. This is the key linear-algebraic step in the
inductive proof of the Gale–Nikaido global-injectivity theorem (a map with everywhere-P-matrix
Jacobian is injective), reducing the `n+1`-dimensional statement to the `n`-dimensional one.

The development is built generically: for any index `ω`, `schurAt M ω` is the Schur complement of
`M` with respect to the `ω`-th diagonal entry, a matrix indexed by `{i // i ≠ ω}`. The determinant
identity `det_schurAt` (`det M = M ω ω * det (schurAt M ω)`, valid when `M ω ω ≠ 0`) comes from the
block-expansion `Matrix.det_fromBlocks₁₁` after splitting the index along `Equiv.sumCompl (· = ω)`.
Applying it to principal submatrices shows `IsPMatrix.schurAt`: every principal minor of the Schur
complement is, up to the positive factor `M ω ω`, a principal minor of `M`, hence positive.

The `Fin (n+1)` specialization `schurLast`/`IsPMatrix.schurLast` (Schur complement at the last
coordinate, reindexed to `Fin n`) is the form the dimension induction consumes.

Depends on: `CRNT.Multistationarity.PMatrix`,
`Mathlib.LinearAlgebra.Matrix.SchurComplement`.
-/

set_option linter.unusedSectionVars false

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The **Schur complement of `M` at the index `ω`**: the matrix indexed by `{i // i ≠ ω}` with
entries `M i j - M i ω * (M ω ω)⁻¹ * M ω j`. -/
def schurAt (M : Matrix ι ι R) (ω : ι) : Matrix {i // i ≠ ω} {i // i ≠ ω} R :=
  fun i j => M i j - M i ω * (M ω ω)⁻¹ * M ω j

/-- The singleton subtype `{a // a = ω}` is a one-element type. -/
instance instUniqueEq (ω : ι) : Unique {a : ι // a = ω} where
  default := ⟨ω, rfl⟩
  uniq := fun x => Subtype.ext x.2

/-- **Schur determinant identity at `ω`.** When the `ω`-th diagonal entry is nonzero, the
determinant of `M` factors as that entry times the determinant of the Schur complement. -/
theorem det_schurAt (M : Matrix ι ι R) (ω : ι) (hd : M ω ω ≠ 0) :
    M.det = M ω ω * (schurAt M ω).det := by
  classical
  -- Split the index set into the singleton `{a = ω}` and its complement `{a ≠ ω}`.
  set e : {a : ι // a = ω} ⊕ {a : ι // a ≠ ω} ≃ ι := Equiv.sumCompl (· = ω) with he
  set A : Matrix {a : ι // a = ω} {a : ι // a = ω} R := fun u u' => M ↑u ↑u' with hA
  set B : Matrix {a : ι // a = ω} {a : ι // a ≠ ω} R := fun u v => M ↑u ↑v with hB
  set C : Matrix {a : ι // a ≠ ω} {a : ι // a = ω} R := fun v u => M ↑v ↑u with hC
  set D : Matrix {a : ι // a ≠ ω} {a : ι // a ≠ ω} R := fun v v' => M ↑v ↑v' with hD
  have hcoeD : (↑(default : {a : ι // a = ω}) : ι) = ω := rfl
  have hblock : M.submatrix e e = fromBlocks A B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.submatrix_apply, he, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, Matrix.fromBlocks, hA, hB, hC, hD]
  -- `A` is the `1×1` block `[M ω ω]`: every entry equals `M ω ω`.
  have hAconst : ∀ x y : {a : ι // a = ω}, A x y = M ω ω := by
    intro x y; rw [hA]; simp only; rw [x.2, y.2]
  -- It is invertible since `M ω ω ≠ 0`; name the explicit inverse so `⅟A` computes.
  letI invA : Invertible A :=
    { invOf := fun _ _ => (M ω ω)⁻¹
      invOf_mul_self := by
        ext u u'
        change (∑ v : {a : ι // a = ω}, (M ω ω)⁻¹ * A v u') =
          if u = u' then 1 else 0
        rw [Fintype.sum_unique]
        simp only [hAconst, Matrix.one_apply, Subsingleton.elim u u', if_pos]
        exact inv_mul_cancel₀ hd
      mul_invOf_self := by
        ext u u'
        change (∑ v : {a : ι // a = ω}, A u v * (M ω ω)⁻¹) =
          if u = u' then 1 else 0
        rw [Fintype.sum_unique]
        simp only [hAconst, Matrix.one_apply, Subsingleton.elim u u', if_pos]
        exact mul_inv_cancel₀ hd }
  have hinv : (⅟A : Matrix {a : ι // a = ω} {a : ι // a = ω} R) = fun _ _ => (M ω ω)⁻¹ := rfl
  have hdetA : A.det = M ω ω := by rw [det_unique]; exact hAconst _ _
  -- The Schur complement is the bottom-right block minus the rank-one correction.
  have hschur : D - C * ⅟A * B = schurAt M ω := by
    ext v v'
    change D v v' - (C * ⅟A * B) v v' =
      M (v : ι) (v' : ι) - M (v : ι) ω * (M ω ω)⁻¹ * M ω (v' : ι)
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    simp [Fintype.sum_unique, hinv, hC, hB, hD, hcoeD]
  -- Assemble via the block determinant expansion.
  rw [← det_submatrix_equiv_self e M, hblock, det_fromBlocks₁₁, hschur, hdetA]

/-- **The Schur complement of a P-matrix is a P-matrix.** Each principal minor of `schurAt M ω` is,
via the Schur determinant identity applied to a principal submatrix of `M` containing `ω`, the
positive factor `M ω ω` dividing a positive principal minor of `M`, hence positive. -/
theorem IsPMatrix.schurAt {M : Matrix ι ι R} (h : M.IsPMatrix) (ω : ι) :
    (Matrix.schurAt M ω).IsPMatrix := by
  classical
  intro s
  -- Lift `s` to a principal index set `t` of `M` containing `ω`.
  set t : Finset ι := insert ω (s.image Subtype.val) with ht
  have hωt : ω ∈ t := Finset.mem_insert_self _ _
  have hval_mem : ∀ a : {i // i ≠ ω}, a ∈ s → (↑a : ι) ∈ t :=
    fun a ha => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
  set P : Matrix ↥t ↥t R := M.submatrix Subtype.val Subtype.val with hP
  have hPp : P.IsPMatrix := h.submatrix_isPMatrix Subtype.coe_injective
  set ωt : ↥t := ⟨ω, hωt⟩ with hωtdef
  have hPωt : P ωt ωt = M ω ω := rfl
  have hωpos : 0 < M ω ω := h.diag_pos ω
  have hne : P ωt ωt ≠ 0 := by rw [hPωt]; exact hωpos.ne'
  -- The equivalence between `s` and the off-`ω` indices of `t`.
  let φ : ↥s ≃ {x : ↥t // x ≠ ωt} :=
    { toFun := fun a =>
        ⟨⟨(↑a : ι), hval_mem a a.2⟩, fun hcontra => a.1.2 (congrArg Subtype.val hcontra)⟩
      invFun := fun x =>
        ⟨⟨(↑x : ι), fun hcontra => x.2 (Subtype.ext hcontra)⟩, by
          have hx : (↑x : ι) ∈ t := x.1.2
          rcases Finset.mem_insert.mp hx with hω | himg
          · exact absurd (Subtype.ext hω) x.2
          · obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp himg
            have heq : a = (⟨(↑x : ι), fun hc => x.2 (Subtype.ext hc)⟩ : {i // i ≠ ω}) :=
              Subtype.ext hav
            exact heq ▸ ha⟩
      left_inv := fun a => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl }
  -- The reindexed Schur complement of `P` at `ωt` is the principal submatrix of `schurAt M ω`.
  have hmat : (Matrix.schurAt P ωt).submatrix φ φ
      = (Matrix.schurAt M ω).submatrix Subtype.val Subtype.val := by
    ext a b; rfl
  -- The minor is positive: `det P = (M ω ω) * det (schurAt P ωt)` with both factors positive.
  have hdetpos : 0 < (Matrix.schurAt P ωt).det := by
    have hP0 : 0 < P.det := hPp.det_pos
    rw [det_schurAt P ωt hne, hPωt] at hP0
    have key : 0 < (M ω ω)⁻¹ * (M ω ω * (Matrix.schurAt P ωt).det) :=
      mul_pos (inv_pos.mpr hωpos) hP0
    rwa [inv_mul_cancel_left₀ hωpos.ne'] at key
  calc 0 < (Matrix.schurAt P ωt).det := hdetpos
    _ = ((Matrix.schurAt P ωt).submatrix φ φ).det := (det_submatrix_equiv_self φ _).symm
    _ = ((Matrix.schurAt M ω).submatrix Subtype.val Subtype.val).det := by rw [hmat]

/-! ### Specialization to the last `Fin (n+1)` coordinate -/

variable {n : ℕ}

/-- The order-embedding `Fin n ≃ {i : Fin (n+1) // i ≠ Fin.last n}` via `Fin.castSucc`. -/
def eLast (n : ℕ) : Fin n ≃ {i : Fin (n + 1) // i ≠ Fin.last n} where
  toFun i := ⟨i.castSucc, (Fin.castSucc_lt_last i).ne⟩
  invFun x := x.1.castPred x.2
  left_inv i := by simp [Fin.castPred_castSucc]
  right_inv x := by apply Subtype.ext; simp [Fin.castSucc_castPred]

/-- The **Schur complement at the last coordinate**, reindexed to `Fin n`: the Schur complement of
`M` with respect to `M (Fin.last n) (Fin.last n)`. -/
def schurLast (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => M i.castSucc j.castSucc
    - M i.castSucc (Fin.last n) * (M (Fin.last n) (Fin.last n))⁻¹ * M (Fin.last n) j.castSucc

/-- `schurLast` is `schurAt` at the last coordinate, reindexed by `eLast`. -/
theorem schurLast_eq (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    schurLast M = (schurAt M (Fin.last n)).submatrix (eLast n) (eLast n) := by
  ext i j; rfl

/-- **Schur determinant identity at the last coordinate.** -/
theorem det_schurLast (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hd : M (Fin.last n) (Fin.last n) ≠ 0) :
    M.det = M (Fin.last n) (Fin.last n) * (schurLast M).det := by
  rw [det_schurAt M (Fin.last n) hd, schurLast_eq, det_submatrix_equiv_self]

/-- **The Schur complement at the last coordinate of a P-matrix is a P-matrix** — the dimension-drop
step for the inductive Gale–Nikaido theorem. -/
theorem IsPMatrix.schurLast {M : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (h : M.IsPMatrix) :
    (Matrix.schurLast M).IsPMatrix := by
  rw [schurLast_eq]
  exact (h.schurAt (Fin.last n)).submatrix_isPMatrix (eLast n).injective

end Matrix
