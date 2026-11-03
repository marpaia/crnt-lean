import CRNT.Kinetics.GeneralizedCycleExactSequence
import CRNT.Deficiency.DeficiencyOne

/-!
# Comparing stoichiometric and kinetic-order deficiency

A generalized mass-action network carries two natural complex embeddings on the same
reaction graph:

* the stoichiometric complex map `Y`, of rank `s`, and
* the kinetic-order complex map `Y~`, of rank `s~`.

Consequently the two deficiency numbers differ only by the rank defect between these
two embeddings:

`δ - δ~ = s~ - s`.

It is usually safer in Lean to record this as the addition identity

`δ + s = δ~ + s~`,

which avoids truncated subtraction in `ℕ`.  This module also records the cycle-space
and deficiency-space forms of the same comparison.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Rank balance relating ordinary and kinetic-order deficiency. -/
theorem deficiency_add_stoichRank_eq_kineticDeficiency_add_kineticOrderRank
    (G : N.GeneralizedMassActionData) :
    N.deficiency + N.stoichRank = G.kineticDeficiency + G.kineticOrderRank := by
  have hS := N.incidenceRank_eq_stoichRank_add
  change N.incidenceRank = N.stoichRank + N.deficiency at hS
  have hK := G.incidenceRank_eq_kineticOrderRank_add_kineticDeficiency
  omega

/-- Integer difference form of the two-deficiency rank identity. -/
theorem deficiency_sub_kineticDeficiency_eq_rank_difference
    (G : N.GeneralizedMassActionData) :
    (N.deficiency : ℤ) - (G.kineticDeficiency : ℤ) =
      (G.kineticOrderRank : ℤ) - (N.stoichRank : ℤ) := by
  have h := G.deficiency_add_stoichRank_eq_kineticDeficiency_add_kineticOrderRank
  have hZ : (N.deficiency : ℤ) + (N.stoichRank : ℤ) =
      (G.kineticDeficiency : ℤ) + (G.kineticOrderRank : ℤ) := by
    exact_mod_cast h
  omega

/-- If the stoichiometric and kinetic-order subspaces have the same rank, then the two
 deficiency numbers agree. -/
theorem kineticDeficiency_eq_deficiency_of_rank_eq
    (G : N.GeneralizedMassActionData)
    (hrank : G.kineticOrderRank = N.stoichRank) :
    G.kineticDeficiency = N.deficiency := by
  have h := G.deficiency_add_stoichRank_eq_kineticDeficiency_add_kineticOrderRank
  omega

/-- Equality of the two subspaces is a sufficient condition for equality of the two
 deficiencies. -/
theorem kineticDeficiency_eq_deficiency_of_subspace_eq
    (G : N.GeneralizedMassActionData)
    (hsub : G.kineticOrderSubspace = N.stoichSubspace) :
    G.kineticDeficiency = N.deficiency := by
  apply G.kineticDeficiency_eq_deficiency_of_rank_eq
  unfold kineticOrderRank Network.stoichRank
  exact congrArg (fun W : Submodule ℝ (S → ℝ) => Module.finrank ℝ W) hsub

/-- If both deficiencies vanish, both complex embeddings are injective on the incidence
image.  This is the intrinsic form of the two-deficiency-zero hypothesis. -/
theorem bothDeficienciesZero_iff_incidence_injective
    (G : N.GeneralizedMassActionData) :
    G.BothDeficienciesZero ↔
      (∀ z ∈ LinearMap.range N.incidenceMap,
          N.complexMap z = 0 → z = 0) ∧
      (∀ z ∈ LinearMap.range N.incidenceMap,
          G.kineticComplexMap z = 0 → z = 0) := by
  constructor
  · rintro ⟨hδ, hδk⟩
    have hS := N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp
      (N.deficiencyZero_iff_deficiency_eq_zero.mpr hδ)
    have hK := G.kineticDeficiency_zero_iff_cycle_is_graphCycle.mp hδk
    constructor
    · intro z hz hY
      rcases hz with ⟨v, rfl⟩
      apply hS v
      rw [← N.complexMap_comp_incidenceMap]
      exact hY
    · intro z hz hY
      rcases hz with ⟨v, rfl⟩
      apply hK v
      change G.kineticComplexMap (N.incidenceMap v) = 0
      exact hY
  · rintro ⟨hS, hK⟩
    constructor
    · apply N.deficiencyZero_iff_deficiency_eq_zero.mp
      apply N.deficiencyZero_iff_stoichCycle_is_graphCycle.mpr
      intro v hv
      apply hS (N.incidenceMap v) ⟨v, rfl⟩
      have hfac := congrArg (fun f => f v) N.complexMap_comp_incidenceMap
      simpa [LinearMap.comp_apply, hv] using hfac
    · apply G.kineticDeficiency_zero_iff_cycle_is_graphCycle.mpr
      intro v hv
      apply hK (N.incidenceMap v) ⟨v, rfl⟩
      change G.kineticComplexMap (N.incidenceMap v) = 0
      exact hv

/-- Both deficiencies zero means that ordinary and kinetic-order reaction-cycle spaces
are exactly the graph-circulation space. -/
theorem bothDeficienciesZero_iff_cycle_spaces
    (G : N.GeneralizedMassActionData) :
    G.BothDeficienciesZero ↔
      N.stoichCycleSpace = N.graphCycleSpace ∧
      G.kineticCycleSpace = N.graphCycleSpace := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact (N.deficiencyZero_iff_stoichCycles_eq_graphCycles).mp
        (N.deficiencyZero_iff_deficiency_eq_zero.mpr h.1)
    · exact G.kineticDeficiency_zero_iff_cycles_eq_graphCycles.mp h.2
  · rintro ⟨hS, hK⟩
    exact ⟨N.deficiencyZero_iff_deficiency_eq_zero.mp
        ((N.deficiencyZero_iff_stoichCycles_eq_graphCycles).mpr hS),
      G.kineticDeficiency_zero_iff_cycles_eq_graphCycles.mpr hK⟩

/-- The dimension difference between the ordinary and kinetic deficiency spaces is
exactly the difference between the two complex-map ranks. -/
theorem deficiencySpace_dimension_balance
    (G : N.GeneralizedMassActionData) :
    Module.finrank ℝ N.deficiencySubspace + N.stoichRank =
      Module.finrank ℝ G.kineticDeficiencySubspace + G.kineticOrderRank := by
  have h := G.deficiency_add_stoichRank_eq_kineticDeficiency_add_kineticOrderRank
  change Module.finrank ℝ N.deficiencySubspace + N.stoichRank =
      G.kineticDeficiency + G.kineticOrderRank at h
  rw [G.kineticDeficiency_eq_finrank_subspace] at h
  exact h

/-- Classical mass action lies on the diagonal of the two-deficiency theory. -/
theorem classical_twoDeficiency_diagonal (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticDeficiency = N.deficiency ∧
    (GeneralizedMassActionData.classical N).kineticOrderRank = N.stoichRank := by
  constructor
  · exact classical_kineticDeficiency_eq_deficiency N
  · unfold kineticOrderRank Network.stoichRank
    exact congrArg (fun W : Submodule ℝ (S → ℝ) => Module.finrank ℝ W)
      (classical_kineticOrderSubspace_eq_stoichSubspace N)

end GeneralizedMassActionData
end Network
end CRNT
