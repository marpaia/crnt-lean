import CRNT.Equilibria.TreeConstants
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Deficiency.PerClassKernel
import CRNT.Deficiency.Confluence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Linkage-class kinetic cofactor definitions

Low-level definitions used by the finite directed Matrix--Tree proof.  The theorem itself lives
above `DirectedMatrixTreeProof` so the dependency graph remains acyclic.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Matrix representation of the full kinetic Laplacian. -/
noncomputable def kineticMatrix (N : Network S) (κ : N.RateConstants) :
    Matrix N.ComplexIdx N.ComplexIdx ℝ :=
  fun c d => ∑ r : N.R,
    if N.sourceIdx r = d then
      κ.k r * ((if N.targetIdx r = c then 1 else 0) - (if d = c then 1 else 0))
    else 0

/-- Matrix and linear-map versions of the kinetic Laplacian agree. -/
theorem kineticMatrix_mulVec (N : Network S) (κ : N.RateConstants)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMatrix κ *ᵥ v = N.kineticMap κ v := by
  funext c
  simp only [kineticMatrix, Matrix.mulVec, dotProduct, N.kineticMap_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single (N.sourceIdx r)]
  · simp
    ring
  · intro d _ hd
    simp [if_neg (Ne.symm hd)]
  · simp

/-- Complexes in the linkage class of `root`. -/
abbrev LinkageComplex (N : Network S) (root : N.ComplexIdx) :=
  {c : N.ComplexIdx // N.SameLinkage root c}

/-- The root as an element of its own linkage-class subtype. -/
def linkageRoot (N : Network S) (root : N.ComplexIdx) : N.LinkageComplex root :=
  ⟨root, by exact Linked.refl N root.1⟩

/-- Kinetic Laplacian block of one linkage class.  Linkage classes are reaction-graph
components, so no reaction connects this block to a different block. -/
noncomputable def linkageKineticMatrix (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) :
    Matrix (N.LinkageComplex root) (N.LinkageComplex root) ℝ :=
  fun i j => N.kineticMatrix κ i.1 j.1

/-- Complexes of the root linkage class other than the root. -/
abbrev WithoutLinkageRoot (N : Network S) (root : N.ComplexIdx) :=
  {c : N.LinkageComplex root // c ≠ N.linkageRoot root}

/-- `WithoutLinkageRoot` is a subtype of a finite type, but deciding `c ≠ linkageRoot`
needs classical choice, so the `Fintype` instance is `noncomputable`. -/
noncomputable instance instFintypeWithoutLinkageRoot (N : Network S)
    (root : N.ComplexIdx) : Fintype (N.WithoutLinkageRoot root) := by
  classical
  exact Subtype.fintype _

/-- Reduced linkage-class kinetic matrix obtained by deleting the root row and column. -/
noncomputable def linkageReducedKineticMatrix
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    Matrix (N.WithoutLinkageRoot root) (N.WithoutLinkageRoot root) ℝ :=
  fun i j => N.linkageKineticMatrix κ root i.1 j.1

/-- The reduced **outflow Laplacian** on the linkage class of `root`.

`kineticMatrix` represents the CRNT kinetic generator `A_κ = inflow - outflow`, so its
diagonal entries are nonpositive.  The directed Matrix--Tree theorem with positive tree
weights applies to `-A_κ`.  Keeping this sign change explicit prevents the odd-dimensional
sign error that arises from taking a raw principal minor of `A_κ`. -/
noncomputable def linkageReducedOutflowLaplacian
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    Matrix (N.WithoutLinkageRoot root) (N.WithoutLinkageRoot root) ℝ :=
  -N.linkageReducedKineticMatrix κ root

/-- Correct positive CRNT kinetic cofactor: the principal cofactor of `-A_κ` **inside the
root linkage class**. -/
noncomputable def kineticCofactor (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) : ℝ :=
  Matrix.det (N.linkageReducedOutflowLaplacian κ root)


end Network
end CRNT
