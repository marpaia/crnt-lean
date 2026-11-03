import CRNT.Graph.WeakReversibility

/-!
# Reversible reaction networks

A CRN is reversible when every reaction channel has at least one reaction channel with the
opposite source and target complexes.  This is stronger than weak reversibility and weaker
than choosing a distinguished involutive pairing of parallel forward/reverse channels.

The definition is intentionally existential: parallel reactions are allowed by `Network`, so
reversibility should not require a canonical matching of channels.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A network is reversible when every reaction has a reverse reaction channel. -/
def Reversible (N : Network S) : Prop :=
  ∀ r : N.R, ∃ r' : N.R,
    (N.reaction r').source = (N.reaction r).target ∧
    (N.reaction r').target = (N.reaction r).source

/-- Reversibility can equivalently be stated as symmetry of the one-step reaction relation. -/
theorem reversible_iff_directlyReacts_symm (N : Network S) :
    N.Reversible ↔ ∀ ⦃c d : Complex S⦄, N.DirectlyReacts c d → N.DirectlyReacts d c := by
  constructor
  · intro h c d hcd
    rcases hcd with ⟨r, hsrc, htgt⟩
    rcases h r with ⟨r', hsrc', htgt'⟩
    refine ⟨r', ?_, ?_⟩
    · simpa [htgt] using hsrc'
    · simpa [hsrc] using htgt'
  · intro h r
    have hforward : N.DirectlyReacts (N.reaction r).source (N.reaction r).target :=
      ⟨r, rfl, rfl⟩
    rcases h hforward with ⟨r', hsrc, htgt⟩
    exact ⟨r', hsrc, htgt⟩

/-- Every reversible network is weakly reversible.  The reverse edge gives a return path
of length one for each reaction. -/
theorem Reversible.weaklyReversible {N : Network S} (h : N.Reversible) :
    N.WeaklyReversible := by
  intro r
  rcases h r with ⟨r', hsrc, htgt⟩
  exact Network.Reaches.single ⟨r', hsrc, htgt⟩

/-- In a reversible network, direct reaction adjacency is symmetric. -/
theorem Reversible.directlyReacts_comm {N : Network S} (h : N.Reversible)
    {c d : Complex S} :
    N.DirectlyReacts c d ↔ N.DirectlyReacts d c := by
  constructor
  · intro hcd
    exact (N.reversible_iff_directlyReacts_symm.mp h) hcd
  · intro hdc
    exact (N.reversible_iff_directlyReacts_symm.mp h) hdc

end Network
end CRNT
