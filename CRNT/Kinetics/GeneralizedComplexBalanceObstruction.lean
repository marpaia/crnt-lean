import CRNT.Equilibria.ComplexBalanceObstruction
import CRNT.Kinetics.GeneralizedCycleExactSequence
import CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT
import CRNT.Equilibria.GeneralizedTreeConstantCriterion
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Kinetic deficiency as generalized complex-balance obstruction

The generalized mass-action analogue replaces the stoichiometric row space by the
kinetic-order row space. The quotient of the incidence row space by the kinetic-order
row space has dimension `δ~`; it contains the tree-affinity obstruction whose vanishing
is equivalent to solvability of the generalized tree-constant equations.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

open scoped Matrix BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Kinetic-order row space in reaction coordinates. -/
noncomputable def kineticOrderRowSpace (G : N.GeneralizedMassActionData) :
    Submodule ℝ (N.R → ℝ) :=
  LinearMap.range G.kineticOrderMatrixᵀ.mulVecLin

/-- The kinetic-order row space lies inside the incidence row space. -/
theorem kineticOrderRowSpace_le_incidenceRowSpace
    (G : N.GeneralizedMassActionData) :
    G.kineticOrderRowSpace ≤ N.incidenceRowSpace := by
  exact G.range_kineticOrderTranspose_le_incidenceTranspose

/-- Generalized complex-balance obstruction quotient. -/
abbrev generalizedComplexBalanceObstructionSpace
    (G : N.GeneralizedMassActionData) :=
  ↥N.incidenceRowSpace ⧸ G.kineticOrderRowSpace.comap N.incidenceRowSpace.subtype

/-- Its dimension is the kinetic deficiency. -/
theorem finrank_generalizedComplexBalanceObstructionSpace
    (G : N.GeneralizedMassActionData) :
    Module.finrank ℝ G.generalizedComplexBalanceObstructionSpace =
      G.kineticDeficiency := by
  let K : Submodule ℝ N.incidenceRowSpace :=
    G.kineticOrderRowSpace.comap N.incidenceRowSpace.subtype
  have hmap : K.map N.incidenceRowSpace.subtype = G.kineticOrderRowSpace := by
    dsimp [K]
    rw [Submodule.map_comap_subtype,
      inf_of_le_right G.kineticOrderRowSpace_le_incidenceRowSpace]
  have hK : Module.finrank ℝ K = G.kineticOrderRank := by
    rw [← Submodule.finrank_map_subtype_eq N.incidenceRowSpace K, hmap]
    exact G.finrank_range_kineticOrderTranspose
  have hI : Module.finrank ℝ N.incidenceRowSpace = N.incidenceRank :=
    N.finrank_range_incidenceTranspose
  have hq := K.finrank_quotient_add_finrank
  change Module.finrank ℝ G.generalizedComplexBalanceObstructionSpace +
      Module.finrank ℝ K = Module.finrank ℝ N.incidenceRowSpace at hq
  rw [hK, hI, G.incidenceRank_eq_kineticOrderRank_add_kineticDeficiency] at hq
  omega

/-- The tree affinity defines a generalized obstruction class as well. -/
noncomputable def generalizedComplexBalanceObstruction
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) :
    G.generalizedComplexBalanceObstructionSpace :=
  Submodule.Quotient.mk ⟨N.treeAffinity κ,
    N.treeAffinity_mem_incidenceRowSpace κ hwr⟩

/-- Vanishing generalized obstruction iff the tree-affinity vector is realizable by a
kinetic-order species potential. -/
theorem generalizedObstruction_eq_zero_iff
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) :
    G.generalizedComplexBalanceObstruction κ hwr = 0 ↔
      N.treeAffinity κ ∈ G.kineticOrderRowSpace := by
  change Submodule.Quotient.mk
      (⟨N.treeAffinity κ, N.treeAffinity_mem_incidenceRowSpace κ hwr⟩ :
        N.incidenceRowSpace) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- On a weakly reversible generalized network, solvability of the generalized
complex-balance equations is equivalent to vanishing of the kinetic-deficiency
obstruction.  The face hypothesis is retained for compatibility with the broader
oriented-matroid existence API, but is not needed for this rate-specific equivalence. -/
theorem exists_generalizedComplexBalanced_iff_obstruction_zero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    (hface : GeneralizedFaceCondition N.stoichSubspace G.kineticOrderSubspace) :
    (∃ x : Concentration S, x.Positive ∧ G.IsComplexBalanced κ x) ↔
      G.generalizedComplexBalanceObstruction κ hwr = 0 := by
  constructor
  · rintro ⟨x, hx, hcb⟩
    rw [G.generalizedObstruction_eq_zero_iff κ hwr]
    refine ⟨fun s => Real.log (x s), ?_⟩
    funext r
    rw [G.kineticOrderTranspose_apply]
    exact (G.complexBalanced_iff_logTreeEquations κ hwr hx).1 hcb
      (N.sourceIdx r) (N.targetIdx r) (N.linked_of_reaction r)
  · intro hzero
    rw [G.generalizedObstruction_eq_zero_iff κ hwr] at hzero
    obtain ⟨z, hz⟩ := hzero
    have hedge : ∀ r : N.R,
        (∑ s : S, (G.kineticComplex (N.targetIdx r) s -
          G.kineticComplex (N.sourceIdx r) s) * z s) =
        Real.log (N.treeConstant κ (N.targetIdx r)) -
          Real.log (N.treeConstant κ (N.sourceIdx r)) := by
      intro r
      have hr := congrFun hz r
      rw [G.kineticOrderTranspose_apply] at hr
      exact hr
    have hlog : ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
        ∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * z s =
          Real.log (N.treeConstant κ j) - Real.log (N.treeConstant κ i) := by
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
    exact G.exists_positive_complexBalanced_of_logTreeSolution κ hwr ⟨z, hlog⟩

/-- Kinetic deficiency zero makes the generalized obstruction space trivial. -/
theorem generalizedObstructionSpace_trivial_of_kineticDeficiencyZero
    (G : N.GeneralizedMassActionData) (hδ : G.kineticDeficiency = 0) :
    Subsingleton G.generalizedComplexBalanceObstructionSpace := by
  apply (Module.finrank_zero_iff (R := ℝ)).mp
  rw [G.finrank_generalizedComplexBalanceObstructionSpace, hδ]

end GeneralizedMassActionData
end Network
end CRNT
