import CRNT.Examples.ReversiblePair
import CRNT.Persistence.FacetRepulsion

set_option backward.isDefEq.respectTransparency false

/-!
# Facet repulsion for `A ⇌ B`

The point `z = (0, 2)` lies in the relative interior of the facet `{x_A = 0}` of the class of
`x₀ = (1, 1)`; all hypotheses of `facet_repelling_of_weaklyReversible` hold, so near `z` the
concentration of `A` does not decrease, for every choice of rate constants.  Non-vacuity instance.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.ReversiblePair

open CRNT CRNT.Network Species

/-- Near `(0, 2)`, `x_A` is nondecreasing along `A ⇌ B`. -/
theorem facet_repelling_pair (κ : N.RateConstants) :
    ∃ δ > 0, ∀ x : Concentration Species, x.Positive →
      dist x (fun s => match s with | A => 0 | B => 2) < δ →
      0 ≤ N.massActionVectorField κ x A := by
  obtain ⟨δ, hδ, h⟩ := N.facet_repelling_of_weaklyReversible κ weaklyReversible
    (W := {A}) ⟨A, Finset.mem_singleton_self _⟩ (x₀ := fun _ => 1)
    (z := fun s => match s with | A => 0 | B => 2) (fun _ => one_pos)
    (fun s => by cases s <;> simp)
    (by
      have : (fun s : Species => match s with | A => (0 : ℝ) | B => 2) - (fun _ => 1) =
          N.reactionVector .fwd := by
        rw [reactionVector_fwd]; funext s; cases s <;> norm_num
      rw [this]; exact N.reactionVector_mem_stoichSubspace _)
    ⟨fun _ => 1, fun r => ⟨N.reactionVector r A, fun i hi => by
      rw [Finset.mem_singleton] at hi; subst hi; simp⟩⟩
  exact ⟨δ, hδ, fun x hx hd => h x hx hd A (Finset.mem_singleton_self _)⟩

end CRNT.Examples.ReversiblePair
