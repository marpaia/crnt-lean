import CRNT.Graph.PositiveCirculation
import CRNT.Flux.Cone

/-!
# Deficiency-zero consistency is weak reversibility

At deficiency zero the stoichiometric and graph cycle spaces coincide.  Therefore a
strictly positive stationary flux (consistency) is automatically a strictly positive
graph circulation, which forces weak reversibility.

This gives the structural equivalence

`δ = 0  →  (consistent ↔ weakly reversible)`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A deficiency-zero consistent network is weakly reversible. -/
theorem weaklyReversible_of_deficiencyZero_of_consistent
    (N : Network S) (hδ : N.DeficiencyZero) (hcons : N.IsConsistent) :
    N.WeaklyReversible := by
  obtain ⟨α, hpos, hS⟩ := hcons
  have hinc : N.incidenceMap α = 0 :=
    (N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp hδ) α hS
  exact N.weaklyReversible_of_positiveGraphCirculation ⟨hpos, hinc⟩

/-- **Deficiency-zero structural equivalence.** -/
theorem deficiencyZero_consistent_iff_weaklyReversible
    (N : Network S) (hδ : N.DeficiencyZero) :
    N.IsConsistent ↔ N.WeaklyReversible := by
  constructor
  · exact N.weaklyReversible_of_deficiencyZero_of_consistent hδ
  · exact N.isConsistent_of_weaklyReversible

/-- For deficiency-zero networks, the following are equivalent: consistency, weak
reversibility, and existence of a strictly positive graph circulation. -/
theorem deficiencyZero_structural_trichotomy
    (N : Network S) (hδ : N.DeficiencyZero) :
    N.IsConsistent ↔
      N.WeaklyReversible ∧
        ∃ α : N.R → ℝ, N.IsPositiveGraphCirculation α := by
  rw [N.deficiencyZero_consistent_iff_weaklyReversible hδ]
  constructor
  · intro hwr
    exact ⟨hwr, N.exists_positiveGraphCirculation_of_weaklyReversible hwr⟩
  · exact fun h => h.1

end Network
end CRNT
