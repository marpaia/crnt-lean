import CRNT.Equilibria.DirectedMatrixTreeProof

/-!
# Linkage-class cofactor form of the directed Matrix--Tree theorem

The low-level cofactor definitions are in `MatrixTreeCofactorDefs`; the finite determinant proof is
in `DirectedMatrixTreeProof`.  This module exposes the public cofactor theorem and its consequences.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Directed Matrix--Tree theorem, linkage-class cofactor form.** -/
theorem kineticCofactor_eq_treeConstant (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) :
    N.kineticCofactor κ root = N.treeConstant κ root :=
  N.kineticCofactor_eq_treeConstant_combinatorial κ root

/-- Weak reversibility makes every linkage-class principal cofactor positive. -/
theorem kineticCofactor_pos_of_weaklyReversible (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) (root : N.ComplexIdx) :
    0 < N.kineticCofactor κ root := by
  rw [N.kineticCofactor_eq_treeConstant]
  exact N.treeConstant_pos_of_weaklyReversible κ hwr root

/-- Tree constants may equivalently be defined as linkage-class kinetic cofactors. -/
theorem treeConstantVector_eq_cofactorVector (N : Network S)
    (κ : N.RateConstants) :
    N.treeConstantVector κ = fun c => N.kineticCofactor κ c := by
  funext c
  exact (N.kineticCofactor_eq_treeConstant κ c).symm

/-- The linkage-cofactor vector lies in the full kinetic kernel. -/
theorem cofactorVector_kineticKernel (N : Network S) (κ : N.RateConstants) :
    N.kineticMap κ (fun c => N.kineticCofactor κ c) = 0 := by
  rw [← N.treeConstantVector_eq_cofactorVector κ]
  exact N.treeConstant_kineticKernel κ

/-- The tree-constant kinetic-kernel theorem follows from the corrected cofactor theorem. -/
theorem treeConstant_kineticKernel_via_cofactor (N : Network S)
    (κ : N.RateConstants) :
    N.kineticMap κ (N.treeConstantVector κ) = 0 := by
  rw [N.treeConstantVector_eq_cofactorVector κ]
  exact N.cofactorVector_kineticKernel κ

/-- Full-matrix principal minor, retained because it is useful for stating why the
linkage restriction matters. -/
abbrev WithoutComplex (N : Network S) (root : N.ComplexIdx) :=
  {c : N.ComplexIdx // c ≠ root}

noncomputable def globalReducedKineticMatrix (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) :
    Matrix (N.WithoutComplex root) (N.WithoutComplex root) ℝ :=
  fun i j => N.kineticMatrix κ i.1 j.1

/-- The full reduced outflow Laplacian `-A_κ` after deleting `root`. -/
noncomputable def globalReducedOutflowLaplacian
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    Matrix (N.WithoutComplex root) (N.WithoutComplex root) ℝ :=
  -N.globalReducedKineticMatrix κ root

/-- Full-matrix principal cofactor with the same positive `-A_κ` sign convention. -/
noncomputable def globalKineticCofactor (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) : ℝ :=
  Matrix.det (N.globalReducedOutflowLaplacian κ root)

/-- Single-linkage-class hypothesis. -/
def HasSingleLinkageClass (N : Network S) : Prop :=
  ∀ c d : N.ComplexIdx, N.Linked c.1 d.1

/-- In a single linkage class the global and linkage-restricted cofactors coincide. -/
theorem globalKineticCofactor_eq_kineticCofactor_of_singleLinkage
    (N : Network S) (κ : N.RateConstants)
    (h₁ : N.HasSingleLinkageClass) (root : N.ComplexIdx) :
    N.globalKineticCofactor κ root = N.kineticCofactor κ root := by
  classical
  let e : N.WithoutComplex root ≃ N.WithoutLinkageRoot root :=
    { toFun := fun c =>
        ⟨⟨c.1, h₁ root c.1⟩, by
          intro h
          apply c.2
          exact congrArg (fun x : N.LinkageComplex root => x.1) h⟩
      invFun := fun c =>
        ⟨c.1.1, by
          intro h
          apply c.2
          apply Subtype.ext
          exact h⟩
      left_inv := by intro c; apply Subtype.ext; rfl
      right_inv := by intro c; apply Subtype.ext; apply Subtype.ext; rfl }
  have hmat : Matrix.reindex e e (N.globalReducedOutflowLaplacian κ root) =
      N.linkageReducedOutflowLaplacian κ root := by
    ext i j
    rfl
  unfold globalKineticCofactor kineticCofactor
  rw [← hmat]
  exact (Matrix.det_reindex_self e (N.globalReducedOutflowLaplacian κ root)).symm

/-- Classical full-cofactor Matrix--Tree statement in the single-linkage-class case. -/
theorem globalKineticCofactor_eq_treeConstant_of_singleLinkage
    (N : Network S) (κ : N.RateConstants)
    (h₁ : N.HasSingleLinkageClass) (root : N.ComplexIdx) :
    N.globalKineticCofactor κ root = N.treeConstant κ root := by
  rw [N.globalKineticCofactor_eq_kineticCofactor_of_singleLinkage κ h₁ root,
    N.kineticCofactor_eq_treeConstant]

/-- With at least two linkage classes, deleting one row/column leaves another entire
Laplacian block singular, so the **global** cofactor vanishes. -/
theorem globalKineticCofactor_eq_zero_of_otherLinkageClass
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx)
    (hother : ∃ c : N.ComplexIdx, ¬ N.Linked root.1 c.1) :
    N.globalKineticCofactor κ root = 0 := by
  classical
  rcases hother with ⟨c, hc⟩
  let θ : Quotient N.linkedSetoid := N.classOf c
  obtain ⟨b, hbnn, hb0, hbsupp, hbker⟩ :=
    N.exists_nonneg_kernelVector_on_class κ θ
  have hroot : N.classOf root ≠ θ := by
    intro h
    apply hc
    apply classOf_eq_iff_linked.mp
    simpa [θ] using h
  have hbroot : b root = 0 := hbsupp root hroot
  obtain ⟨d, hd⟩ := Function.ne_iff.mp hb0
  have hdroot : d ≠ root := by
    intro h
    subst d
    exact hd hbroot
  let v : N.WithoutComplex root → ℝ := fun i => b i.1
  have hv0 : v ≠ 0 := by
    intro hv
    apply hd
    have := congrFun hv ⟨d, hdroot⟩
    simpa [v] using this
  have hmul : N.globalReducedKineticMatrix κ root *ᵥ v = 0 := by
    funext i
    have hfull := congrFun (N.kineticMatrix_mulVec κ b) i.1
    rw [hbker] at hfull
    change (∑ j : N.WithoutComplex root,
      N.kineticMatrix κ i.1 j.1 * b j.1) = 0
    have hsub : (∑ j : N.WithoutComplex root,
        N.kineticMatrix κ i.1 j.1 * b j.1) =
        ∑ j ∈ (Finset.univ.erase root), N.kineticMatrix κ i.1 j * b j := by
      symm
      exact Finset.sum_subtype (Finset.univ.erase root)
        (fun j => by simp) (fun j => N.kineticMatrix κ i.1 j * b j)
    rw [hsub]
    have hterm : N.kineticMatrix κ i.1 root * b root = 0 := by
      rw [hbroot, mul_zero]
    have herase :
        (∑ j ∈ (Finset.univ.erase root), N.kineticMatrix κ i.1 j * b j) =
          ∑ j ∈ (Finset.univ : Finset N.ComplexIdx), N.kineticMatrix κ i.1 j * b j :=
      Finset.sum_erase (Finset.univ : Finset N.ComplexIdx)
        (f := fun j => N.kineticMatrix κ i.1 j * b j) hterm
    rw [herase]
    simpa [Matrix.mulVec, dotProduct] using hfull
  have hout : N.globalReducedOutflowLaplacian κ root *ᵥ v = 0 := by
    funext i
    have hi := congrFun hmul i
    change (∑ j, (-N.globalReducedKineticMatrix κ root i j) * v j) = 0
    calc
      (∑ j, (-N.globalReducedKineticMatrix κ root i j) * v j) =
          -(∑ j, N.globalReducedKineticMatrix κ root i j * v j) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by
        have hi' : (∑ j, N.globalReducedKineticMatrix κ root i j * v j) = 0 := by
          simpa [Matrix.mulVec, dotProduct] using hi
        rw [hi', neg_zero]
  unfold globalKineticCofactor
  by_contra hdet
  have hunitDet : IsUnit (N.globalReducedOutflowLaplacian κ root).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunitMat : IsUnit (N.globalReducedOutflowLaplacian κ root) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hunitDet
  have hinj : Function.Injective (fun w => N.globalReducedOutflowLaplacian κ root *ᵥ w) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunitMat
  apply hv0
  apply hinj
  change N.globalReducedOutflowLaplacian κ root *ᵥ v =
    N.globalReducedOutflowLaplacian κ root *ᵥ (0 : N.WithoutComplex root → ℝ)
  rw [hout]
  simp

end Network
end CRNT
