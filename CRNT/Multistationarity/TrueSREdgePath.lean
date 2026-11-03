import CRNT.Multistationarity.TrueSRTwoWeightGain

/-!
# A single edge as a path

In the split of a causal closed walk at a repeated reaction vertex `ρ = ρ_i = ρ_j`, one of the
two glued halves is a *single edge*: the walk's right edge at position `i`, running from
`x_{i+1}` to `ρ`.  The other half is the forward segment `x_{i+1} → … → x_j → ρ`.  Both run
species-to-reaction and share both endpoints, so `glueCycle` assembles the split cycle directly —
no bespoke two-regime construction is needed.

This file supplies the single-edge path and its endpoints.
-/

namespace CRNT.Network.TrueSREdge

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- A single true-SR edge, read as a species-to-reaction path of length one. -/
def toPath (e : N.TrueSREdge) : N.TrueSRPath 1 where
  length_pos := Nat.one_pos
  edge := fun _ => e
  vertex := fun p => if p.1 = 0 then Sum.inl e.species else Sum.inr ⟨e.reaction, e.internal⟩
  connects := by
    intro q
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    exact Or.inl ⟨by simp, by simp⟩
  edge_simple := by
    intro i j _
    exact Subsingleton.elim _ _
  vertex_simple := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  starts_at_species := ⟨e.species, by simp⟩
  ends_at_reaction := ⟨⟨e.reaction, e.internal⟩, by simp⟩

@[simp] theorem toPath_edge (e : N.TrueSREdge) (q : Fin 1) : (toPath e).edge q = e := rfl

theorem toPath_startSpecies (e : N.TrueSREdge) : (toPath e).startSpecies = e.species := by
  have h := (toPath e).vertex_zero
  have h2 : (toPath e).vertex 0 = Sum.inl e.species := by simp [toPath]
  rw [h2] at h
  exact (Sum.inl.inj h).symm

theorem toPath_endReaction (e : N.TrueSREdge) :
    (toPath e).endReaction = ⟨e.reaction, e.internal⟩ := by
  have h := (toPath e).vertex_last
  have h2 : (toPath e).vertex (Fin.last 1) = Sum.inr ⟨e.reaction, e.internal⟩ := by
    simp [toPath]
  rw [h2] at h
  exact (Sum.inr.inj h).symm

/-- A single-edge path has no interior species. -/
theorem toPath_no_interior_species (e : N.TrueSREdge) (s : S) :
    ¬ (toPath e).InteriorSpecies s := by
  rintro ⟨p, hp0, hp⟩
  have hplt := p.isLt
  have hp1 : p.1 = 1 := by omega
  have : (toPath e).vertex p = Sum.inr ⟨e.reaction, e.internal⟩ := by
    simp only [toPath]
    rw [if_neg (by omega : ¬ p.1 = 0)]
  rw [this] at hp
  exact absurd hp (by simp)

/-- A single-edge path has no interior reactions. -/
theorem toPath_no_interior_reaction (e : N.TrueSREdge) (ρ : N.InternalTrueReaction) :
    ¬ (toPath e).InteriorReaction ρ := by
  rintro ⟨p, hpL, hp⟩
  have hplt := p.isLt
  have hp0 : p.1 = 0 := by omega
  have : (toPath e).vertex p = Sum.inl e.species := by
    simp only [toPath]
    rw [if_pos hp0]
  rw [this] at hp
  exact absurd hp (by simp)

end CRNT.Network.TrueSREdge
