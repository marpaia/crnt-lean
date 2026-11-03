import CRNT.Multistationarity.TrueSRPathSegment

/-!
# Terminal segments of a path

The shortening step of the minimality argument cuts a chord at whichever vertex its interior
shares with the cycle.  If that vertex is a *reaction* vertex the initial segment is the shorter
chord (`initialSegment`); if it is a *species* vertex the **terminal** segment is, since a chord
must run species-to-reaction.  So both cuts are needed.

A terminal segment cut at an even position `m` has length `L - m`, automatically odd since `L`
is odd (`TrueSRPath.odd_length`) — no separate parity hypothesis is required.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L : ℕ}

/-- The terminal segment of a path, cut at an even position (hence at a species vertex). -/
def terminalSegment (P : N.TrueSRPath L) (m : ℕ) (hm : m < L) (heven : m % 2 = 0) :
    N.TrueSRPath (L - m) where
  length_pos := by omega
  edge := fun q => P.edge ⟨m + q.1, by have := q.isLt; omega⟩
  vertex := fun p => P.vertex ⟨m + p.1, by have := p.isLt; omega⟩
  connects := by
    intro q
    exact P.connects ⟨m + q.1, by have := q.isLt; omega⟩
  edge_simple := by
    intro i j hij
    have := P.edge_simple hij
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  vertex_simple := by
    intro p p' hpp'
    have := P.vertex_simple hpp'
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  starts_at_species := by
    obtain ⟨s, hs⟩ := (P.species_iff_even m (by omega)).mpr (Nat.even_iff.mpr heven)
    refine ⟨s, ?_⟩
    show P.vertex ⟨m + ((0 : Fin (L - m + 1))).1, _⟩ = Sum.inl s
    exact (congrArg P.vertex (Fin.ext (by show m + 0 = m; omega))).trans hs
  ends_at_reaction := by
    refine ⟨P.endReaction, ?_⟩
    show P.vertex ⟨m + (Fin.last (L - m)).1, _⟩ = Sum.inr P.endReaction
    exact (congrArg P.vertex (Fin.ext (by show m + (L - m) = L; omega))).trans P.vertex_last

@[simp] theorem terminalSegment_edge (P : N.TrueSRPath L) (m : ℕ) (hm : m < L)
    (heven : m % 2 = 0) (q : Fin (L - m)) :
    (P.terminalSegment m hm heven).edge q = P.edge ⟨m + q.1, by have := q.isLt; omega⟩ := rfl

@[simp] theorem terminalSegment_vertex (P : N.TrueSRPath L) (m : ℕ) (hm : m < L)
    (heven : m % 2 = 0) (p : Fin (L - m + 1)) :
    (P.terminalSegment m hm heven).vertex p
      = P.vertex ⟨m + p.1, by have := p.isLt; omega⟩ := rfl

/-- A terminal segment ends where the path does. -/
theorem terminalSegment_endReaction (P : N.TrueSRPath L) (m : ℕ) (hm : m < L)
    (heven : m % 2 = 0) :
    (P.terminalSegment m hm heven).endReaction = P.endReaction := by
  have h1 := (P.terminalSegment m hm heven).vertex_last
  rw [terminalSegment_vertex] at h1
  have h2 : P.vertex ⟨m + (Fin.last (L - m)).1, by omega⟩ = Sum.inr P.endReaction :=
    (congrArg P.vertex (Fin.ext (by show m + (L - m) = L; omega))).trans P.vertex_last
  rw [h2] at h1
  exact (Sum.inr.inj h1).symm

/-- A terminal cut at a positive position is strictly shorter. -/
theorem terminalSegment_length_lt {m : ℕ} (hm : 0 < m) (hmL : m < L) : L - m < L := by omega

end CRNT.Network.TrueSRPath
