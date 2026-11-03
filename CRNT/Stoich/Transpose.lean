import CRNT.Deficiency.KernelDimension
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Transpose of the stoichiometric map

For a finite CRN the stoichiometric map

`S : (reactions → ℝ) →ₗ[ℝ] (species → ℝ)`

has the usual transpose

`Sᵀ : (species → ℝ) →ₗ[ℝ] (reactions → ℝ)`.

The image of `Sᵀ` is exactly the orthogonal complement of `ker S`.  This is the
finite-dimensional fundamental theorem of linear algebra in the coordinates used by CRNT.
It is the key bridge behind the converse direction of the Wegscheider theorem: an affinity
vector annihilates every stoichiometric cycle iff it is a stoichiometric potential gradient.

This module is structural linear algebra only; it contains no kinetics or solver machinery.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The real stoichiometric matrix with rows indexed by species and columns by reactions. -/
noncomputable def reactionStoichMatrix (N : Network S) : Matrix S N.R ℝ :=
  fun s r => N.reactionVector r s

/-- The matrix representation of the stoichiometric map. -/
theorem reactionStoichMatrix_mulVecLin (N : Network S) :
    N.reactionStoichMatrix.mulVecLin = N.stoichMap := by
  apply LinearMap.ext
  intro v
  funext s
  rw [Matrix.mulVecLin_apply, N.stoichMap_apply]
  simp only [Matrix.mulVec, dotProduct, reactionStoichMatrix]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The transpose stoichiometric map.  Its `r` coordinate is the pairing of the
reaction vector of `r` with the species potential `μ`. -/
noncomputable def stoichTransposeMap (N : Network S) :
    (S → ℝ) →ₗ[ℝ] (N.R → ℝ) :=
  N.reactionStoichMatrixᵀ.mulVecLin

@[simp] theorem stoichTransposeMap_apply (N : Network S) (μ : S → ℝ) (r : N.R) :
    N.stoichTransposeMap μ r = ∑ s : S, N.reactionVector r s * μ s := by
  rw [stoichTransposeMap, Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, reactionStoichMatrix]

/-- The transpose has the same rank as the stoichiometric map. -/
theorem finrank_range_stoichTransposeMap (N : Network S) :
    Module.finrank ℝ (LinearMap.range N.stoichTransposeMap) = N.stoichRank := by
  calc
    Module.finrank ℝ (LinearMap.range N.stoichTransposeMap)
        = N.reactionStoichMatrixᵀ.rank := rfl
    _ = N.reactionStoichMatrix.rank := Matrix.rank_transpose N.reactionStoichMatrix
    _ = Module.finrank ℝ (LinearMap.range N.reactionStoichMatrix.mulVecLin) := rfl
    _ = Module.finrank ℝ (LinearMap.range N.stoichMap) := by
      rw [N.reactionStoichMatrix_mulVecLin]
    _ = N.stoichRank := (N.stoichRank_eq_finrank_range).symm

/-- Every stoichiometric potential gradient annihilates every stoichiometric cycle. -/
theorem range_stoichTransposeMap_le_orthSum_ker (N : Network S) :
    LinearMap.range N.stoichTransposeMap ≤ orthSum (LinearMap.ker N.stoichMap) := by
  rintro w ⟨μ, rfl⟩
  rw [mem_orthSum]
  intro z hz
  have hz0 : N.stoichMap z = 0 := hz
  calc
    (∑ r : N.R, N.stoichTransposeMap μ r * z r)
        = ∑ r : N.R, ∑ s : S, (N.reactionVector r s * μ s) * z r := by
          apply Finset.sum_congr rfl
          intro r _
          rw [N.stoichTransposeMap_apply, Finset.sum_mul]
    _ = ∑ s : S, ∑ r : N.R, (N.reactionVector r s * μ s) * z r := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, μ s * (∑ r : N.R, z r * N.reactionVector r s) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      have hs := congrFun hz0 s
      rw [N.stoichMap_apply, Pi.zero_apply] at hs
      rw [hs, mul_zero]

/-- **Fundamental stoichiometric orthogonality theorem.**

The row space / transpose image of the stoichiometric matrix is exactly the orthogonal
complement of its cycle space:

`range Sᵀ = (ker S)ᗮ`.

The reverse inclusion follows from finite-dimensional rank-nullity: both subspaces have
rank `stoichRank N`. -/
theorem range_stoichTransposeMap_eq_orthSum_ker (N : Network S) :
    LinearMap.range N.stoichTransposeMap = orthSum (LinearMap.ker N.stoichMap) := by
  refine Submodule.eq_of_le_of_finrank_eq
    (N.range_stoichTransposeMap_le_orthSum_ker) ?_
  rw [N.finrank_range_stoichTransposeMap, finrank_orthSum]
  have hranknull := LinearMap.finrank_range_add_finrank_ker N.stoichMap
  have hrange := N.stoichRank_eq_finrank_range
  have hdim : Module.finrank ℝ (N.R → ℝ) = Fintype.card N.R :=
    Module.finrank_pi ℝ
  rw [hdim] at hranknull
  omega

/-- Cycle-annihilation is equivalent to representability by a species potential. -/
theorem mem_orthSum_ker_iff_exists_stoichPotential (N : Network S) (a : N.R → ℝ) :
    a ∈ orthSum (LinearMap.ker N.stoichMap) ↔
      ∃ μ : S → ℝ, ∀ r : N.R,
        a r = ∑ s : S, N.reactionVector r s * μ s := by
  rw [← N.range_stoichTransposeMap_eq_orthSum_ker]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    intro r
    have := congrFun hμ r
    simpa using this.symm
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    funext r
    rw [N.stoichTransposeMap_apply]
    exact (hμ r).symm

end Network
end CRNT
