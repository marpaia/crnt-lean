import CRNT.Multistationarity.TrueSRPathTerminalSegment

/-!
# Where the cuts land

The shortening step needs to know the *new* endpoint each cut produces, so that the segment can
be recognised as a chord again: an initial cut ends at the cut vertex's reaction, a terminal cut
starts at the cut vertex's species.  Both are proved here by pairing the segment's own
`vertex_last` / `vertex_zero` against the original path's accessor at the cut position.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L : ℕ}

/-- An initial cut ends at the reaction sitting at the cut position. -/
theorem initialSegment_endReaction (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L)
    (hodd : m % 2 = 1) :
    (P.initialSegment m hm hodd).endReaction
      = P.reactionAt ⟨m, by omega⟩ (by show m % 2 ≠ 0; omega) := by
  have h1 := (P.initialSegment m hm hodd).vertex_last
  rw [initialSegment_vertex] at h1
  have h2 : P.vertex ⟨(Fin.last m).1, by omega⟩
      = Sum.inr (P.reactionAt ⟨m, by omega⟩ (by show m % 2 ≠ 0; omega)) := by
    exact (congrArg P.vertex (Fin.ext (rfl : (Fin.last m).1 = m))).trans
      (P.vertex_eq_reactionAt ⟨m, by omega⟩ (by show m % 2 ≠ 0; omega))
  rw [h2] at h1
  exact (Sum.inr.inj h1).symm

/-- A terminal cut starts at the species sitting at the cut position. -/
theorem terminalSegment_startSpecies (P : N.TrueSRPath L) (m : ℕ) (hm : m < L)
    (heven : m % 2 = 0) :
    (P.terminalSegment m hm heven).startSpecies
      = P.speciesAt ⟨m, by omega⟩ heven := by
  have h1 := (P.terminalSegment m hm heven).vertex_zero
  rw [terminalSegment_vertex] at h1
  have h2 : P.vertex ⟨m + ((0 : Fin (L - m + 1))).1, by omega⟩
      = Sum.inl (P.speciesAt ⟨m, by omega⟩ heven) := by
    exact (congrArg P.vertex (Fin.ext (by show m + 0 = m; omega))).trans
      (P.vertex_eq_speciesAt ⟨m, by omega⟩ heven)
  rw [h2] at h1
  exact (Sum.inl.inj h1).symm

/-- Every edge of an initial segment is an edge of the path. -/
theorem initialSegment_edge_mem (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L)
    (hodd : m % 2 = 1) (q : Fin m) :
    ∃ p : Fin L, (P.initialSegment m hm hodd).edge q = P.edge p :=
  ⟨⟨q.1, by have := q.isLt; omega⟩, rfl⟩

/-- Every edge of a terminal segment is an edge of the path. -/
theorem terminalSegment_edge_mem (P : N.TrueSRPath L) (m : ℕ) (hm : m < L)
    (heven : m % 2 = 0) (q : Fin (L - m)) :
    ∃ p : Fin L, (P.terminalSegment m hm heven).edge q = P.edge p :=
  ⟨⟨m + q.1, by have := q.isLt; omega⟩, rfl⟩

end CRNT.Network.TrueSRPath
