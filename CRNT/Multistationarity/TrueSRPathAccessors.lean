import CRNT.Multistationarity.TrueSRGlueInterface

/-!
# Reading species and reactions off a path, and edge incidence

`TrueSRCycle` stores `species : Fin n → S` and `reaction : Fin n → TrueReaction`, whereas a
`TrueSRPath` stores vertices in `S ⊕ InternalTrueReaction`.  The glue construction therefore
needs to read the underlying species and reaction out of a path's vertices, and needs to know
how each edge is incident to them.

By `TrueSRPath.species_iff_even` a position carries a species exactly when it is even, so both
accessors are total on their parity class.  The four incidence lemmas then say: an edge at an
even position runs from its position's species to the next position's reaction, and an edge at an
odd position runs from its position's reaction to the next position's species.  These are what
discharge the cycle's `left_species` / `left_reaction` / `right_species` / `right_reaction`
fields after gluing.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L : ℕ}

/-- Every odd position of a path carries a reaction vertex. -/
theorem exists_reaction_of_odd (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    ∃ ρ : N.InternalTrueReaction, P.vertex p = Sum.inr ρ := by
  have hns : ¬ ∃ s : S, P.vertex p = Sum.inl s := by
    intro hs
    have hev := (P.species_iff_even p.1 (by have := p.isLt; omega)).mp hs
    rw [Nat.even_iff] at hev
    omega
  cases hv : P.vertex p with
  | inl s => exact absurd ⟨s, hv⟩ hns
  | inr ρ => exact ⟨ρ, rfl⟩

/-- The species carried by an even position. -/
noncomputable def speciesAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : S :=
  ((P.species_iff_even p.1 (by have := p.isLt; omega)).mpr
    (Nat.even_iff.mpr hp)).choose

theorem vertex_eq_speciesAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) :
    P.vertex p = Sum.inl (P.speciesAt p hp) :=
  ((P.species_iff_even p.1 (by have := p.isLt; omega)).mpr
    (Nat.even_iff.mpr hp)).choose_spec

/-- The reaction carried by an odd position. -/
noncomputable def reactionAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    N.InternalTrueReaction :=
  (P.exists_reaction_of_odd p hp).choose

theorem vertex_eq_reactionAt (P : N.TrueSRPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    P.vertex p = Sum.inr (P.reactionAt p hp) :=
  (P.exists_reaction_of_odd p hp).choose_spec

/-! ### Edge incidence -/

/-- An edge at an even position starts at that position's species. -/
theorem edge_species_of_even (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 = 0) :
    (P.edge q).species = P.speciesAt (Fin.castSucc q) (by simpa using hq) := by
  have hv := P.vertex_eq_speciesAt (Fin.castSucc q) (by simpa using hq)
  rcases P.connects q with ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [hv] at hu
    exact (Sum.inl.inj hu).symm
  · rw [hv] at hu
    exact absurd hu (by simp)

/-- An edge at an even position ends at the next position's reaction. -/
theorem edge_reaction_of_even (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 = 0) :
    (P.edge q).reaction = (P.reactionAt q.succ (by
      have : (q.succ).1 = q.1 + 1 := rfl
      omega)).1 := by
  have hodd : (q.succ).1 % 2 ≠ 0 := by
    have : (q.succ).1 = q.1 + 1 := rfl
    omega
  have hv := P.vertex_eq_reactionAt q.succ hodd
  rcases P.connects q with ⟨_, hw⟩ | ⟨_, hw⟩
  · rw [hv] at hw
    exact congrArg Subtype.val (Sum.inr.inj hw).symm
  · rw [hv] at hw
    exact absurd hw (by simp)

/-- An edge at an odd position starts at that position's reaction. -/
theorem edge_reaction_of_odd (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) :
    (P.edge q).reaction = (P.reactionAt (Fin.castSucc q) (by simpa using hq)).1 := by
  have hv := P.vertex_eq_reactionAt (Fin.castSucc q) (by simpa using hq)
  rcases P.connects q with ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [hv] at hu
    exact absurd hu (by simp)
  · rw [hv] at hu
    exact congrArg Subtype.val (Sum.inr.inj hu).symm

/-- An edge at an odd position ends at the next position's species. -/
theorem edge_species_of_odd (P : N.TrueSRPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) :
    (P.edge q).species = P.speciesAt q.succ (by
      have : (q.succ).1 = q.1 + 1 := rfl
      omega) := by
  have heven : (q.succ).1 % 2 = 0 := by
    have : (q.succ).1 = q.1 + 1 := rfl
    omega
  have hv := P.vertex_eq_speciesAt q.succ heven
  rcases P.connects q with ⟨_, hw⟩ | ⟨_, hw⟩
  · rw [hv] at hw
    exact absurd hw (by simp)
  · rw [hv] at hw
    exact (Sum.inl.inj hw).symm

/-- The start species is the species at position `0`. -/
theorem startSpecies_eq (P : N.TrueSRPath L) :
    P.startSpecies = P.speciesAt 0 (by simp) := by
  have h1 := P.vertex_zero
  have h2 := P.vertex_eq_speciesAt 0 (by simp)
  rw [h1] at h2
  exact Sum.inl.inj h2

/-- The end reaction is the reaction at position `L`. -/
theorem endReaction_eq (P : N.TrueSRPath L) :
    P.endReaction = P.reactionAt (Fin.last L) (by
      have hl : (Fin.last L).1 = L := rfl
      have := P.odd_length
      rw [Nat.odd_iff] at this
      omega) := by
  have h1 := P.vertex_last
  have h2 := P.vertex_eq_reactionAt (Fin.last L) (by
    have hl : (Fin.last L).1 = L := rfl
    have := P.odd_length
    rw [Nat.odd_iff] at this
    omega)
  rw [h1] at h2
  exact Sum.inr.inj h2

end CRNT.Network.TrueSRPath
