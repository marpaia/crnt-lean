import CRNT.Deficiency.CycleSplitting
import CRNT.Equilibria.Wegscheider
import CRNT.Equilibria.WegscheiderDeficiency

/-!
# Wegscheider conditions at deficiency one

The stoichiometric cycle space is the graph-cycle space plus one deficiency direction.
Therefore at deficiency one, detailed-balance compatibility consists of:

1. the usual graph-cycle Wegscheider identities, and
2. exactly one additional independent stoichiometric-cycle identity.

This gives an explicit thermodynamic interpretation of deficiency one.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every full Wegscheider system satisfies graph-cycle identities. -/
theorem graphWegscheider_of_Wegscheider (N : Network S)
    (ρ : N.ReversiblePairing) (κ : N.RateConstants)
    (hW : N.SatisfiesWegscheider ρ κ) :
    N.SatisfiesGraphWegscheider ρ κ := by
  exact N.satisfiesGraphWegscheider_of_satisfiesWegscheider ρ κ hW

/-- One excess-cycle identity. -/
def SatisfiesExcessCycleIdentity (N : Network S) (ρ : N.ReversiblePairing)
    (κ : N.RateConstants) (e : N.R → ℝ) : Prop :=
  ∑ r : N.R, N.logEquilibriumConstant ρ κ r * e r = 0

/-- At deficiency one, graph-cycle Wegscheider plus one excess-cycle identity is sufficient
for the full basis-free Wegscheider condition. -/
theorem Wegscheider_of_graph_and_excess
    (N : Network S) (ρ : N.ReversiblePairing) (κ : N.RateConstants)
    (hδ : N.DeficiencyOne)
    {e : N.R → ℝ}
    (heS : e ∈ N.stoichCycleSpace) (heG : e ∉ N.graphCycleSpace)
    (hspan : ∀ v : N.R → ℝ, v ∈ N.stoichCycleSpace →
      ∃ (g : N.R → ℝ) (a : ℝ),
        g ∈ N.graphCycleSpace ∧ v = g + a • e)
    (hgraph : N.SatisfiesGraphWegscheider ρ κ)
    (hexcess : N.SatisfiesExcessCycleIdentity ρ κ e) :
    N.SatisfiesWegscheider ρ κ := by
  rw [N.satisfiesWegscheider_iff ρ κ]
  intro v hv
  obtain ⟨g, a, hg, rfl⟩ := hspan v hv
  have hg0 : (∑ r : N.R,
      N.logEquilibriumConstant ρ κ r * g r) = 0 := by
    change N.cycleAffinity ρ κ g = 0
    exact (N.satisfiesGraphWegscheider_iff ρ κ).1 hgraph g hg
  have he0 := hexcess
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, mul_assoc]
  rw [Finset.sum_add_distrib]
  have hscale : (∑ r : N.R,
      N.logEquilibriumConstant ρ κ r * (a * e r)) = a *
        ∑ r : N.R, N.logEquilibriumConstant ρ κ r * e r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hscale, hg0, he0]
  ring

/-- **Deficiency-one thermodynamic reduction.** There exists a single excess cycle whose
identity, together with graph-cycle identities, is equivalent to all Wegscheider
conditions. -/
theorem exists_single_extra_Wegscheider_condition
    (N : Network S) (ρ : N.ReversiblePairing) (κ : N.RateConstants)
    (hδ : N.DeficiencyOne) :
    ∃ e : N.R → ℝ,
      e ∈ N.stoichCycleSpace ∧ e ∉ N.graphCycleSpace ∧
      (N.SatisfiesWegscheider ρ κ ↔
        N.SatisfiesGraphWegscheider ρ κ ∧
          N.SatisfiesExcessCycleIdentity ρ κ e) := by
  obtain ⟨e, heS, heG, hspan⟩ := N.exists_excessCycle_of_deficiencyOne hδ
  refine ⟨e, heS, heG, ?_⟩
  constructor
  · intro hW
    refine ⟨N.graphWegscheider_of_Wegscheider ρ κ hW, ?_⟩
    rw [N.satisfiesWegscheider_iff ρ κ] at hW
    exact hW e heS
  · rintro ⟨hg, he⟩
    exact N.Wegscheider_of_graph_and_excess ρ κ hδ heS heG hspan hg he

end Network
end CRNT
