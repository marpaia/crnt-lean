import CRNT.Multistationarity.TrueSRParityLemma

/-!
# Initial segments of a path

Banaji--Craciun's Lemma 10 assumes only that the chord is *edge*-disjoint from the cycle, while
`Gluable` demands interior *vertex*-disjointness.  The bridge is the standard minimality
argument: take a chord of least length; if its interior met the cycle at a vertex `v`, the
initial segment up to `v` would be a shorter chord.

That argument needs initial segments, built here.  A segment must still run species-to-reaction,
so its length must be odd — which by `TrueSRPath.species_iff_even` is exactly the condition that
the cut vertex is a reaction vertex.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L : ℕ}

/-- The initial segment of a path, cut at an odd position (hence at a reaction vertex). -/
def initialSegment (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L) (hodd : m % 2 = 1) :
    N.TrueSRPath m where
  length_pos := by omega
  edge := fun q => P.edge ⟨q.1, by have := q.isLt; omega⟩
  vertex := fun p => P.vertex ⟨p.1, by have := p.isLt; omega⟩
  connects := by
    intro q
    exact P.connects ⟨q.1, by have := q.isLt; omega⟩
  edge_simple := by
    intro i j hij
    have := P.edge_simple hij
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  vertex_simple := by
    intro p p' hpp'
    have := P.vertex_simple hpp'
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  starts_at_species := by
    obtain ⟨s, hs⟩ := P.starts_at_species
    refine ⟨s, ?_⟩
    show P.vertex ⟨((0 : Fin (m + 1))).1, _⟩ = Sum.inl s
    exact (congrArg P.vertex (Fin.ext (rfl : (0 : ℕ) = ((0 : Fin (L + 1))).1))).trans hs
  ends_at_reaction := by
    obtain ⟨ρ, hρ⟩ := P.exists_reaction_of_odd ⟨m, by omega⟩ (by show m % 2 ≠ 0; omega)
    exact ⟨ρ, hρ⟩

@[simp] theorem initialSegment_edge (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L)
    (hodd : m % 2 = 1) (q : Fin m) :
    (P.initialSegment m hm hodd).edge q = P.edge ⟨q.1, by have := q.isLt; omega⟩ := rfl

@[simp] theorem initialSegment_vertex (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L)
    (hodd : m % 2 = 1) (p : Fin (m + 1)) :
    (P.initialSegment m hm hodd).vertex p = P.vertex ⟨p.1, by have := p.isLt; omega⟩ := rfl

/-- A segment starts where the path does. -/
theorem initialSegment_startSpecies (P : N.TrueSRPath L) (m : ℕ) (hm : m ≤ L)
    (hodd : m % 2 = 1) :
    (P.initialSegment m hm hodd).startSpecies = P.startSpecies := by
  have h1 := (P.initialSegment m hm hodd).vertex_zero
  have h2 := P.vertex_zero
  rw [initialSegment_vertex] at h1
  have h3 : P.vertex ⟨((0 : Fin (m + 1))).1, by omega⟩ = P.vertex 0 :=
    congrArg P.vertex (Fin.ext (rfl : (0 : ℕ) = ((0 : Fin (L + 1))).1))
  rw [h3, h2] at h1
  exact Sum.inl.inj h1.symm

end CRNT.Network.TrueSRPath
