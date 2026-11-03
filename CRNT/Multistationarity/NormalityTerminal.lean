import CRNT.Multistationarity.Normality
import CRNT.Deficiency.TerminalKernelDimension
import CRNT.Deficiency.DeficiencyOne

/-!
# Terminal-SLC obstruction to normality

A classical necessary condition for normality is

`t - ℓ - δ ≤ 0`,

where `t` is the number of terminal strong-linkage classes, `ℓ` the number of linkage
classes, and `δ` the deficiency.  Equivalently, `t ≤ ℓ + δ`.

The dimension interpretation is transparent in the current library: `t` is the dimension
of the kinetic-Laplacian kernel, while `ℓ+δ` is the incidence-kernel contribution plus the
deficiency excess available to the stoichiometric map.  Too many terminal SCC modes force
the normality operator to be singular on the stoichiometric subspace.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]


private lemma complexMap_kineticMap_eq_sum_rv
    (N : Network S) (κ : N.RateConstants) (v : N.ComplexIdx → ℝ) :
    N.complexMap (N.kineticMap κ v) =
      ∑ r : N.R, (κ.k r * v (N.sourceIdx r)) • N.reactionVector r := by
  funext s
  rw [N.complexMap_apply]
  simp only [N.kineticMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  have hexpand : ∀ c : N.ComplexIdx,
      κ.k r * v (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0)) * (c.val s : ℝ)
        = κ.k r * v (N.sourceIdx r) *
            ((if N.targetIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ) -
              (if N.sourceIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)) := by
    intro c
    ring
  simp only [hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    N.sum_ite_complexMap, N.sum_ite_complexMap]
  rw [N.reactionVector_apply]
  rfl

/-- **Normality terminal-component bound:** `t ≤ ℓ + δ`. -/
theorem numTerminalSLC_le_linkage_add_deficiency_of_normal
    (N : Network S) (hn : N.Normal) :
    N.numTerminalSLC ≤ N.numLinkageClasses + N.deficiency := by
  rcases hn with ⟨W⟩
  let κ : N.RateConstants :=
    { k := W.reactionWeights.weight
      positive := W.reactionWeights.positive }
  let B0 : (S → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) :=
    { toFun := fun σ c => weightedComplexPairing W.speciesWeights c.val σ
      map_add' := by
        intro σ τ
        funext c
        simp [weightedComplexPairing, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a σ
        funext c
        simp [weightedComplexPairing, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring }
  let B : N.stoichSubspace →ₗ[ℝ] (N.ComplexIdx → ℝ) :=
    B0.domRestrict N.stoichSubspace
  let KB : N.stoichSubspace →ₗ[ℝ] (N.ComplexIdx → ℝ) :=
    (N.kineticMap κ).comp B
  let F : N.stoichSubspace →ₗ[ℝ] LinearMap.range (N.kineticMap κ) :=
    KB.codRestrict (LinearMap.range (N.kineticMap κ)) (by
      intro σ
      exact ⟨B σ, rfl⟩)
  have hfactor : ∀ σ : N.stoichSubspace,
      N.complexMap (N.kineticMap κ (B σ)) =
        N.normalityOperator W.speciesWeights W.reactionWeights σ.1 := by
    intro σ
    rw [complexMap_kineticMap_eq_sum_rv]
    rfl
  have hFinj : Function.Injective F := by
    intro σ τ hst
    apply W.nonsingular
    apply Subtype.ext
    have hv : (F σ : N.ComplexIdx → ℝ) = F τ := congrArg Subtype.val hst
    change N.kineticMap κ (B σ) = N.kineticMap κ (B τ) at hv
    have hc := congrArg N.complexMap hv
    rw [hfactor σ, hfactor τ] at hc
    exact hc
  have hrank : N.stoichRank ≤
      Module.finrank ℝ (LinearMap.range (N.kineticMap κ)) := by
    change Module.finrank ℝ N.stoichSubspace ≤ _
    exact LinearMap.finrank_le_finrank_of_injective hFinj
  have hnull := (N.kineticMap κ).finrank_range_add_finrank_ker
  rw [N.finrank_ker_kineticMap_eq_numTerminalSLC κ] at hnull
  have hncomp : Module.finrank ℝ (N.ComplexIdx → ℝ) = N.numComplexes := by
    rw [Module.finrank_pi]
    simpa [Network.numComplexes, ComplexIdx] using (Fintype.card_coe N.complexes)
  rw [hncomp] at hnull
  have hstruct := N.numComplexes_eq_add
  omega

/-- Integer form of the same necessary condition. -/
theorem terminal_excess_nonpos_of_normal (N : Network S) (hn : N.Normal) :
    (N.numTerminalSLC : ℤ) - (N.numLinkageClasses : ℤ) - (N.deficiency : ℤ) ≤ 0 := by
  have h := N.numTerminalSLC_le_linkage_add_deficiency_of_normal hn
  omega

/-- If `t - ℓ - δ > 0`, the network cannot be normal. -/
theorem not_normal_of_linkage_deficiency_lt_terminal (N : Network S)
    (h : N.numLinkageClasses + N.deficiency < N.numTerminalSLC) :
    ¬ N.Normal := by
  intro hn
  exact (not_lt_of_ge (N.numTerminalSLC_le_linkage_add_deficiency_of_normal hn)) h

/-- At deficiency zero, a normal network has at most one terminal SLC per linkage class. -/
theorem numTerminalSLC_le_numLinkageClasses_of_normal_deficiencyZero
    (N : Network S) (hn : N.Normal) (hδ : N.deficiency = 0) :
    N.numTerminalSLC ≤ N.numLinkageClasses := by
  simpa [hδ] using N.numTerminalSLC_le_linkage_add_deficiency_of_normal hn

/-- A deficiency-zero normal network satisfying the universal graph inequality
`ℓ ≤ t` must have exactly one terminal strong-linkage class per linkage class. -/
theorem numTerminalSLC_eq_numLinkageClasses_of_normal_deficiencyZero
    (N : Network S) (hn : N.Normal) (hδ : N.deficiency = 0)
    (hlt : N.numLinkageClasses ≤ N.numTerminalSLC) :
    N.numTerminalSLC = N.numLinkageClasses := by
  exact Nat.le_antisymm
    (N.numTerminalSLC_le_numLinkageClasses_of_normal_deficiencyZero hn hδ) hlt

/-- Weak reversibility saturates the terminal-component bound at `t=ℓ`. -/
theorem terminal_bound_of_weaklyReversible (N : Network S) (hwr : N.WeaklyReversible) :
    N.numTerminalSLC ≤ N.numLinkageClasses + N.deficiency :=
  N.numTerminalSLC_le_linkage_add_deficiency_of_normal
    (N.normal_of_weaklyReversible hwr)

end Network
end CRNT
