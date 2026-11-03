import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Equilibria.TreeConstantCriterion
import CRNT.Equilibria.TreePotentialIntegration
import CRNT.Equilibria.MatrixTreeCofactor
import CRNT.Deficiency.ExactSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Deficiency as the obstruction space for complex balance

For a weakly reversible network, positive tree constants define a logarithmic edge
vector

`β_κ(r) = log K_{target(r)} - log K_{source(r)}`.

This always lies in the incidence row space. A positive complex-balanced equilibrium
exists exactly when `β_κ` lies in the smaller stoichiometric row space. The quotient

`row(∂) / row(S)`

is therefore the natural space of independent complex-balance obstructions, and its
dimension is the deficiency.
-/

namespace CRNT
namespace Network

open scoped Matrix BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Incidence row space in reaction coordinates. -/
noncomputable def incidenceRowSpace (N : Network S) : Submodule ℝ (N.R → ℝ) :=
  LinearMap.range N.incidenceMatrixᵀ.mulVecLin

/-- Stoichiometric row space in reaction coordinates. -/
noncomputable def stoichRowSpace (N : Network S) : Submodule ℝ (N.R → ℝ) :=
  LinearMap.range N.stoichMatrixᵀ.mulVecLin

/-- Stoichiometric row space is contained in the incidence row space. -/
theorem stoichRowSpace_le_incidenceRowSpace (N : Network S) :
    N.stoichRowSpace ≤ N.incidenceRowSpace :=
  N.range_stoichTranspose_le

/-- Quotient obstruction space for complex-balance realization. -/
abbrev complexBalanceObstructionSpace (N : Network S) :=
  ↥N.incidenceRowSpace ⧸ N.stoichRowSpace.comap N.incidenceRowSpace.subtype

/-- The obstruction-space dimension is exactly the deficiency. -/
theorem finrank_complexBalanceObstructionSpace (N : Network S) :
    Module.finrank ℝ N.complexBalanceObstructionSpace = N.deficiency := by
  let K : Submodule ℝ N.incidenceRowSpace :=
    N.stoichRowSpace.comap N.incidenceRowSpace.subtype
  have hmap : K.map N.incidenceRowSpace.subtype = N.stoichRowSpace := by
    dsimp [K]
    rw [Submodule.map_comap_subtype, inf_of_le_right N.stoichRowSpace_le_incidenceRowSpace]
  have hK : Module.finrank ℝ K = N.stoichRank := by
    rw [← Submodule.finrank_map_subtype_eq N.incidenceRowSpace K, hmap]
    exact N.finrank_range_stoichTranspose
  have hI : Module.finrank ℝ N.incidenceRowSpace = N.incidenceRank :=
    N.finrank_range_incidenceTranspose
  have hq := K.finrank_quotient_add_finrank
  change Module.finrank ℝ N.complexBalanceObstructionSpace +
      Module.finrank ℝ K = Module.finrank ℝ N.incidenceRowSpace at hq
  rw [hK, hI, N.incidenceRank_eq_stoichRank_add] at hq
  change Module.finrank ℝ N.complexBalanceObstructionSpace =
    Module.finrank ℝ N.deficiencySubspace
  omega

/-- Tree-constant log edge vector. -/
noncomputable def treeAffinity (N : Network S) (κ : N.RateConstants) : N.R → ℝ :=
  fun r => Real.log (N.treeConstant κ (N.targetIdx r)) -
    Real.log (N.treeConstant κ (N.sourceIdx r))

/-- Under weak reversibility, the tree affinity lies in the incidence row space. -/
theorem treeAffinity_mem_incidenceRowSpace (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    N.treeAffinity κ ∈ N.incidenceRowSpace := by
  refine ⟨fun c => Real.log (N.treeConstant κ c), ?_⟩
  funext r
  rw [N.incidenceTranspose_apply]
  rfl

/-- The class of the tree affinity in the deficiency obstruction quotient. -/
noncomputable def complexBalanceObstruction (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    N.complexBalanceObstructionSpace :=
  Submodule.Quotient.mk ⟨N.treeAffinity κ,
    N.treeAffinity_mem_incidenceRowSpace κ hwr⟩

/-- Vanishing obstruction is equivalent to species-potential realizability of the tree
log ratios. -/
theorem complexBalanceObstruction_eq_zero_iff_treeAffinity_mem_stoichRow
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    N.complexBalanceObstruction κ hwr = 0 ↔
      N.treeAffinity κ ∈ N.stoichRowSpace := by
  change Submodule.Quotient.mk
      (⟨N.treeAffinity κ, N.treeAffinity_mem_incidenceRowSpace κ hwr⟩ : N.incidenceRowSpace) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- **Rate-parameter obstruction theorem.** On a weakly reversible network, positive
complex balance exists iff the tree-affinity obstruction vanishes. -/
theorem exists_positive_complexBalanced_iff_obstruction_zero
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    (∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x) ↔
      N.complexBalanceObstruction κ hwr = 0 := by
  constructor
  · rintro ⟨x, hx, hcb⟩
    have hbin := N.satisfiesTreeConstantBinomials_of_complexBalanced κ hwr hx hcb
    rw [N.complexBalanceObstruction_eq_zero_iff_treeAffinity_mem_stoichRow κ hwr]
    refine ⟨fun s => Real.log (x s), ?_⟩
    funext r
    rw [N.stoichTranspose_apply, N.complexTranspose_apply, N.complexTranspose_apply]
    have hb := hbin (N.sourceIdx r) (N.targetIdx r) (N.linked_of_reaction r)
    have hKt : 0 < N.treeConstant κ (N.targetIdx r) :=
      N.treeConstant_pos_of_weaklyReversible κ hwr _
    have hKs : 0 < N.treeConstant κ (N.sourceIdx r) :=
      N.treeConstant_pos_of_weaklyReversible κ hwr _
    have hms : 0 < N.complexMonomial x (N.sourceIdx r) :=
      Complex.massActionMonomial_pos hx _
    have hmt : 0 < N.complexMonomial x (N.targetIdx r) :=
      Complex.massActionMonomial_pos hx _
    have hlog := congrArg Real.log hb
    rw [Real.log_mul hKt.ne' hms.ne', Real.log_mul hKs.ne' hmt.ne'] at hlog
    have hlog_s : Real.log (N.complexMonomial x (N.sourceIdx r)) =
        ∑ s : S, ((N.sourceIdx r).val s : ℝ) * Real.log (x s) := by
      simpa [complexMonomial, complexMonomialVector_apply] using
        N.log_complexMonomialVector hx (N.sourceIdx r)
    have hlog_t : Real.log (N.complexMonomial x (N.targetIdx r)) =
        ∑ s : S, ((N.targetIdx r).val s : ℝ) * Real.log (x s) := by
      simpa [complexMonomial, complexMonomialVector_apply] using
        N.log_complexMonomialVector hx (N.targetIdx r)
    rw [hlog_s, hlog_t] at hlog
    unfold treeAffinity
    linarith
  · intro hzero
    rw [N.complexBalanceObstruction_eq_zero_iff_treeAffinity_mem_stoichRow κ hwr] at hzero
    rcases hzero with ⟨p, hp⟩
    have hedge : ∀ r : N.R,
        ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r := by
      intro r
      have hr := congrFun hp r
      rw [N.stoichTranspose_apply, N.complexTranspose_apply, N.complexTranspose_apply] at hr
      simp only [Network.reactionVector_apply, treeLogDifference, treeAffinity,
        Network.sourceIdx, Network.targetIdx, sub_mul] at hr ⊢
      rw [Finset.sum_sub_distrib]
      exact hr
    let x : Concentration S := fun s => Real.exp (p s)
    have hx : x.Positive := fun s => Real.exp_pos _
    refine ⟨x, hx, ?_⟩
    apply N.complexBalanced_of_treeConstantBinomials κ hwr hx
    simpa [x] using N.exp_treePotential_satisfies_treeBinomials_from_edges κ hwr p hedge

/-- Deficiency zero annihilates the obstruction space, explaining why every positive
rate vector on a weakly reversible deficiency-zero network admits complex balance. -/
theorem complexBalanceObstruction_trivial_of_deficiencyZero (N : Network S)
    (hδ : N.deficiency = 0) :
    Subsingleton N.complexBalanceObstructionSpace := by
  apply (Module.finrank_zero_iff (R := ℝ)).mp
  rw [N.finrank_complexBalanceObstructionSpace, hδ]

/-- Positive deficiency counts the maximum number of independent logarithmic rate
constraints required for complex balance. -/
theorem number_independent_complexBalance_constraints (N : Network S) :
    Module.finrank ℝ N.complexBalanceObstructionSpace = N.deficiency :=
  N.finrank_complexBalanceObstructionSpace

end Network
end CRNT
