import CRNT.Persistence.StronglyEndotacticConsequences
import CRNT.Persistence.TwoSpeciesEndotactic

/-!
# Flow forms of the endotactic persistence results

* `endotacticStd_structurallyPersistentStd_of_bounded`: endotactic networks (standard sense)
  whose positive trajectories are bounded are persistent along every genuine mass-action flow
  (any dimension; the weakly reversible hypothesis of
  `weaklyReversible_structurallyPersistentStd_of_bounded` is replaced by endotacticity).
* `twoSpecies_endotacticStd_structurallyPersistentStd`: two-species endotactic networks, with no
  boundedness hypothesis.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Endotactic networks with bounded positive trajectories are persistent** (flow form). -/
theorem endotacticStd_structurallyPersistentStd_of_bounded {N : Network S}
    (hend : N.EndotacticStd) (hbdd : N.StructurallyBoundedPositiveTrajectories) :
    N.StructurallyPersistentStd := by
  intro κ ϕ γ hflow x₀ hx₀ s
  obtain ⟨K, hKc, hK⟩ := hbdd κ ϕ γ hflow x₀ hx₀
  obtain ⟨hzero, hϕγ, hsol⟩ := hflow
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y ∈ K, ∀ s, y s ≤ M := by
    have hb : ∀ s : S, ∃ M : ℝ, ∀ y ∈ K, y s ≤ M := fun s => by
      obtain ⟨M, hM⟩ := hKc.bddAbove_image (continuous_apply s).continuousOn
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    choose Mf hMf using hb
    by_cases hS : Nonempty S
    · refine ⟨Finset.univ.sup' Finset.univ_nonempty Mf, fun y hy s => ?_⟩
      exact (hMf s y hy).trans (Finset.le_sup' Mf (Finset.mem_univ s))
    · exact ⟨0, fun y _ s => absurd ⟨s⟩ hS⟩
  have hγ0 : (γ x₀ 0).Positive := by rw [hzero]; exact hx₀
  have hbd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ M := fun t ht s => by
    have h1 := hK ⟨t, ht⟩
    rw [hϕγ x₀ ⟨t, ht⟩] at h1
    exact hM _ h1 s
  obtain ⟨η, hη, hfl⟩ := N.endotacticStd_forward_floor κ hend hγ0 (hsol x₀) hbd
  refine ⟨η, hη, fun t => ?_⟩
  rw [hϕγ x₀ t]
  exact hfl t t.2 s

/-- **Two-species endotactic networks are persistent along every genuine mass-action flow.** -/
theorem twoSpecies_endotacticStd_structurallyPersistentStd {N : Network S}
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) : N.StructurallyPersistentStd := by
  intro κ ϕ γ hflow x₀ hx₀ s
  obtain ⟨hzero, hϕγ, hsol⟩ := hflow
  obtain ⟨η, B, hη, h⟩ := N.twoSpecies_endotacticStd_confined hS κ hend hx₀
  refine ⟨η, hη, fun t => ?_⟩
  rw [hϕγ x₀ t]
  exact (h (γ x₀) (hzero x₀) (hsol x₀) t t.2 s).1

/-- **The Persistence Conjecture holds for two-species networks** (flow form). -/
theorem persistenceConjecture_of_card_two (N : Network S) (hS : Fintype.card S = 2) :
    N.PersistenceConjecture :=
  fun hwr => twoSpecies_endotacticStd_structurallyPersistentStd hS hwr.endotacticStd

/-- **The strong Persistence Conjecture holds for two-species networks** (compact confinement). -/
theorem persistenceConjectureStrong_of_card_two (N : Network S) (hS : Fintype.card S = 2) :
    N.PersistenceConjectureStrong :=
  fun hwr => N.twoSpecies_weaklyReversible_structurallyPersistent hS hwr

end Network
end CRNT
