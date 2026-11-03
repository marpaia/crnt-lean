import CRNT.Persistence.OrbitClosureSiphon

set_option backward.isDefEq.respectTransparency false

/-!
# A network without drainable siphons: `0 ⇌ A`

The inflow `0 → A` produces `A` from the empty complex, so `{A}` is not a siphon and the network
has no siphon at all; in particular `HasNoDrainableSiphon` holds and
`orbitClosure_positive_of_hasNoDrainableSiphon` applies to it.  This is a non-vacuity instance
for the hypothesis of that theorem.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.InflowNoDrainable

open CRNT CRNT.Network

/-- One species. -/
abbrev Species := Fin 1

/-- The empty complex and the complex `A`. -/
def c0 : Complex Species := fun _ => 0
def cA : Complex Species := fun _ => 1

/-- `r 0 : 0 → A`, `r 1 : A → 0`. -/
def rxn : Fin 2 → Reaction Species
  | 0 => { source := c0, target := cA }
  | 1 => { source := cA, target := c0 }

/-- The network `0 ⇌ A`. -/
def N : Network Species :=
  { R := Fin 2, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- `0 ⇌ A` has no drainable siphon (indeed no siphon). -/
theorem hasNoDrainableSiphon : N.HasNoDrainableSiphon := by
  rintro P ⟨⟨s, hs⟩, hsiph, -⟩
  obtain ⟨s', hs', hreact⟩ := hsiph (0 : Fin 2) ⟨s, hs, by
    simp [IsProduct, N, rxn, cA]⟩
  simp [IsReactant, N, rxn, c0] at hreact

end CRNT.Examples.InflowNoDrainable
