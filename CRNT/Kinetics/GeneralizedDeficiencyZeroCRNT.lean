import CRNT.Equilibria.GeneralizedComplexBalanceToric
import CRNT.Kinetics.GeneralizedBirchExistence
import CRNT.Kinetics.GeneralizedCycleExactSequence
import CRNT.LinearAlgebra.OrientedMatroidNondegeneracy
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Generalized deficiency-zero theorem interface

For a weakly reversible generalized mass-action network with ordinary deficiency zero and
kinetic-order deficiency zero, the graph tree constants determine a compatible affine system in
log-concentration.  This is the generalized deficiency-zero mechanism.  Stoichiometric-class
existence and uniqueness then reduce to the oriented-matroid closure/face/nondegeneracy and
uniqueness conditions for the pair of stoichiometric and kinetic-order subspaces.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

open scoped Matrix BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Structural generalized deficiency-zero hypothesis. -/
def IsGeneralizedDeficiencyZero
    (G : N.GeneralizedMassActionData) : Prop :=
  N.WeaklyReversible ∧ N.deficiency = 0 ∧ G.kineticDeficiency = 0

/-- Kinetic deficiency zero makes the kinetic-order complex map injective on the incidence image.
This is the linear-algebraic core that makes arbitrary positive tree constants lift to a
log-concentration potential. -/
theorem kineticComplexMap_injective_on_incidence_of_kineticDeficiency_zero
    (G : N.GeneralizedMassActionData) (hδ : G.kineticDeficiency = 0) :
    ∀ z ∈ LinearMap.range N.incidenceMap,
      G.kineticComplexMap z = 0 → z = 0 := by
  intro z hzrange hmap
  have hzdef : z ∈ G.kineticDeficiencySubspace := by
    exact ⟨hmap, hzrange⟩
  have hfin : Module.finrank ℝ G.kineticDeficiencySubspace = 0 := by
    rw [← G.kineticDeficiency_eq_finrank_subspace]
    exact hδ
  have hbot : G.kineticDeficiencySubspace = ⊥ :=
    Submodule.finrank_eq_zero.mp hfin
  rw [hbot] at hzdef
  simpa using hzdef

/-- The transpose kinetic-order row space has dimension equal to the kinetic-order rank. -/
theorem finrank_range_kineticOrderTranspose (G : N.GeneralizedMassActionData) :
    Module.finrank ℝ (LinearMap.range G.kineticOrderMatrixᵀ.mulVecLin) =
      G.kineticOrderRank := by
  calc
    Module.finrank ℝ (LinearMap.range G.kineticOrderMatrixᵀ.mulVecLin) =
        G.kineticOrderMatrixᵀ.rank := rfl
    _ = G.kineticOrderMatrix.rank := Matrix.rank_transpose _
    _ = Module.finrank ℝ (LinearMap.range G.kineticOrderMatrix.mulVecLin) := rfl
    _ = Module.finrank ℝ (LinearMap.range G.kineticOrderMap) := by
      rw [G.kineticOrderMatrix_mulVecLin]
    _ = G.kineticOrderRank := rfl

/-- The kinetic-order row space is contained in the incidence row space. -/
theorem range_kineticOrderTranspose_le_incidenceTranspose
    (G : N.GeneralizedMassActionData) :
    LinearMap.range G.kineticOrderMatrixᵀ.mulVecLin ≤
      LinearMap.range N.incidenceMatrixᵀ.mulVecLin := by
  have hT : G.kineticOrderMatrixᵀ =
      N.incidenceMatrixᵀ * G.kineticComplexMatrixᵀ := by
    rw [kineticOrderMatrix, Matrix.transpose_mul]
  rw [hT, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- Kinetic deficiency zero collapses the kinetic-order and incidence row spaces. -/
theorem range_kineticOrderTranspose_eq_incidenceTranspose_of_zero
    (G : N.GeneralizedMassActionData) (hδ : G.kineticDeficiency = 0) :
    LinearMap.range G.kineticOrderMatrixᵀ.mulVecLin =
      LinearMap.range N.incidenceMatrixᵀ.mulVecLin := by
  refine Submodule.eq_of_le_of_finrank_eq
    G.range_kineticOrderTranspose_le_incidenceTranspose ?_
  rw [G.finrank_range_kineticOrderTranspose]
  calc
    G.kineticOrderRank = N.incidenceRank := by
      have h := G.incidenceRank_eq_kineticOrderRank_add_kineticDeficiency
      omega
    _ = Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin) := by
      symm
      calc
        Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin) =
            N.incidenceMatrixᵀ.rank := rfl
        _ = N.incidenceMatrix.rank := Matrix.rank_transpose _
        _ = N.incidenceRank := (N.incidenceRank_eq_matrixRank).symm

/-- Under kinetic deficiency zero and weak reversibility, the log tree-constant equations are
consistent for every choice of positive rate constants. -/
theorem exists_logTreeSolution_of_kineticDeficiency_zero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδk : G.kineticDeficiency = 0) :
    ∃ z : S → ℝ,
      ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
        ∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * z s =
          Real.log (N.treeConstant κ j) - Real.log (N.treeConstant κ i) := by
  have hβrange : (fun r : N.R =>
      Real.log (N.treeConstant κ (N.targetIdx r)) -
        Real.log (N.treeConstant κ (N.sourceIdx r))) ∈
      LinearMap.range N.incidenceMatrixᵀ.mulVecLin := by
    refine ⟨fun c => Real.log (N.treeConstant κ c), ?_⟩
    funext r
    rw [N.incidenceTranspose_apply]
  rw [← G.range_kineticOrderTranspose_eq_incidenceTranspose_of_zero hδk] at hβrange
  obtain ⟨z, hz⟩ := hβrange
  have hedge : ∀ r : N.R,
      (∑ s : S, (G.kineticComplex (N.targetIdx r) s -
        G.kineticComplex (N.sourceIdx r) s) * z s) =
      Real.log (N.treeConstant κ (N.targetIdx r)) -
        Real.log (N.treeConstant κ (N.sourceIdx r)) := by
    intro r
    have hr := congrFun hz r
    rw [G.kineticOrderTranspose_apply] at hr
    exact hr
  refine ⟨z, ?_⟩
  intro i j hij
  have hreach : N.Reaches i.1 j.1 := hwr.reaches_of_linked hij
  obtain ⟨k, hk⟩ := (N.reaches_iff_exists_reachesWithin i.1 j.1).1 hreach
  clear hij hreach
  have hres :
      (∑ s : S, G.kineticComplex i s * z s) - Real.log (N.treeConstant κ i) =
      (∑ s : S, G.kineticComplex j s * z s) - Real.log (N.treeConstant κ j) := by
    revert i
    induction k with
    | zero =>
        intro i hk
        have hij' : i = j := Subtype.ext hk
        simpa [hij']
    | succ k ih =>
        intro i hk
        rcases hk with hij' | ⟨r, hsrc, hrest⟩
        · have hij'' : i = j := Subtype.ext hij'
          simpa [hij'']
        · have hsi : N.sourceIdx r = i := by
            apply Subtype.ext
            simpa [Network.sourceIdx] using hsrc
          have he := hedge r
          have hsumEdge :
              (∑ s : S, (G.kineticComplex (N.targetIdx r) s -
                G.kineticComplex (N.sourceIdx r) s) * z s) =
              (∑ s : S, G.kineticComplex (N.targetIdx r) s * z s) -
                (∑ s : S, G.kineticComplex (N.sourceIdx r) s * z s) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro s _
            ring
          rw [hsumEdge] at he
          have hedgeResidual :
              (∑ s : S, G.kineticComplex (N.sourceIdx r) s * z s) -
                  Real.log (N.treeConstant κ (N.sourceIdx r)) =
              (∑ s : S, G.kineticComplex (N.targetIdx r) s * z s) -
                  Real.log (N.treeConstant κ (N.targetIdx r)) := by
            linarith
          calc
            (∑ s : S, G.kineticComplex i s * z s) - Real.log (N.treeConstant κ i) =
                (∑ s : S, G.kineticComplex (N.sourceIdx r) s * z s) -
                  Real.log (N.treeConstant κ (N.sourceIdx r)) := by rw [hsi]
            _ = (∑ s : S, G.kineticComplex (N.targetIdx r) s * z s) -
                  Real.log (N.treeConstant κ (N.targetIdx r)) := hedgeResidual
            _ = (∑ s : S, G.kineticComplex j s * z s) -
                  Real.log (N.treeConstant κ j) := ih (N.targetIdx r) hrest
  have hsumFinal :
      (∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * z s) =
        (∑ s : S, G.kineticComplex j s * z s) -
          (∑ s : S, G.kineticComplex i s * z s) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsumFinal]
  linarith

/-- Exponentiating a solution of the log tree equations gives a positive generalized CBE. -/
theorem exists_positive_complexBalanced_of_logTreeSolution
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    (hz : ∃ z : S → ℝ,
      ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
        ∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * z s =
          Real.log (N.treeConstant κ j) - Real.log (N.treeConstant κ i)) :
    ∃ x : Concentration S, x.Positive ∧ G.IsComplexBalanced κ x := by
  obtain ⟨z, hz⟩ := hz
  let x : Concentration S := fun s => Real.exp (z s)
  have hx : x.Positive := fun s => Real.exp_pos _
  refine ⟨x, hx, ?_⟩
  apply (G.complexBalanced_iff_logTreeEquations κ hwr hx).2
  intro i j hij
  simpa [x, Real.log_exp] using hz i j hij

/-- **Generalized deficiency-zero existence theorem.**  Weak reversibility and kinetic-order
deficiency zero guarantee at least one positive generalized complex-balanced equilibrium for every
positive rate vector.  Ordinary deficiency zero is retained in the bundled CRNT hypothesis because
it is the standard two-deficiency formulation and controls the stoichiometric realization. -/
theorem exists_positive_complexBalanced_of_generalizedDeficiencyZero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (h : G.IsGeneralizedDeficiencyZero) :
    ∃ x : Concentration S, x.Positive ∧ G.IsComplexBalanced κ x := by
  exact G.exists_positive_complexBalanced_of_logTreeSolution κ h.1
    (G.exists_logTreeSolution_of_kineticDeficiency_zero κ h.1 h.2.2)

/-- Oriented-matroid data specialized to a generalized CRN.

The closure/face conditions are stated in the same orientation as generalized Birch
existence (`S` versus the kinetic-order space `T`).  The earlier kernel-space alias
reversed these implications and was too weak for the theorem below. -/
structure CRNOrientedMatroidConditions
    (G : N.GeneralizedMassActionData) : Prop where
  closure : GeneralizedClosureCondition N.stoichSubspace G.kineticOrderSubspace
  uniqueness : GeneralizedUniquenessCondition N.stoichSubspace G.kineticOrderSubspace
  face : GeneralizedFaceCondition N.stoichSubspace G.kineticOrderSubspace

/-- Generalized deficiency zero plus the uniqueness sign condition gives at most one generalized
CBE in every positive stoichiometric class. -/
theorem atMostOne_complexBalanced_in_class_of_generalizedDeficiencyZero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hδ : G.IsGeneralizedDeficiencyZero)
    (huniq : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hcx : G.IsComplexBalanced κ x) (hcy : G.IsComplexBalanced κ y)
    (hclass : N.SameStoichClass x y) : x = y :=
  G.complexBalanced_unique_in_stoichClass_of_signCompatible κ hδ.1 huniq
    hx hy hcx hcy hclass

/-- Full robust generalized-CBE theorem interface: structural deficiency-zero hypotheses supply the
toric CBE set; the oriented-matroid conditions supply proper intersection with positive
stoichiometric classes. -/
theorem existsUnique_complexBalanced_in_every_positiveClass
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hδ : G.IsGeneralizedDeficiencyZero)
    (hom : G.CRNOrientedMatroidConditions) :
    ∀ c : Concentration S, c.Positive →
      ∃! x : Concentration S,
        x.Positive ∧ N.SameStoichClass x c ∧ G.IsComplexBalanced κ x := by
  intro c hc
  obtain ⟨xstar, hxs, hcbs⟩ :=
    G.exists_positive_complexBalanced_of_generalizedDeficiencyZero κ hδ
  obtain ⟨x, hx, hclass, htoric⟩ :=
    generalized_birch_existence_of_conditions
      N.stoichSubspace G.kineticOrderSubspace
      hom.closure xstar c hxs hc
  have hcbx : G.IsComplexBalanced κ x := by
    apply G.complexBalanced_of_toricLeaf κ hδ.1 hxs hcbs
    exact ⟨hx, by simpa [logRatio] using htoric⟩
  refine ⟨x, ⟨hx, hclass, hcbx⟩, ?_⟩
  intro y hy
  have hsign : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace) := by
    simpa [GeneralizedUniquenessCondition] using hom.uniqueness
  have hyx : N.SameStoichClass y x := by
    change y - x ∈ N.stoichSubspace
    have heq : y - x = (y - c) - (x - c) := by
      ext s
      simp [Pi.sub_apply]
    rw [heq]
    exact N.stoichSubspace.sub_mem hy.2.1 hclass
  exact G.complexBalanced_unique_in_stoichClass_of_signCompatible κ hδ.1 hsign
    hy.1 hx hy.2.2 hcbx hyx

end GeneralizedMassActionData
end Network
end CRNT
