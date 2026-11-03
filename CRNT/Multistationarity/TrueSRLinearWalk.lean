import CRNT.Multistationarity.TrueSREdgePath

/-!
# Linear alternating walks are paths

The forward half of a split causal walk is an alternating sequence
`x_{i+1}, ρ_{i+1}, x_{i+2}, …, x_j, ρ_j` — species and reactions with the walk's left and right
edges between them.  This file packages that shape and turns it into a `TrueSRPath`.

Parametrised by `k`, with `k+1` species and reactions and `k` right edges, giving a path of
length `2k+1` — chosen so no truncated subtraction appears.  All indices go through named
accessor lemmas rather than inline `ite`, as in `TrueSRArc.lean`.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {k : ℕ}

/-- A linear alternating walk: `k+1` species and reactions joined by left and right edges. -/
structure TrueSRLinearWalk (N : Network S) (k : ℕ) where
  species : Fin (k + 1) → S
  reaction : Fin (k + 1) → N.InternalTrueReaction
  leftEdge : Fin (k + 1) → N.TrueSREdge
  rightEdge : Fin k → N.TrueSREdge
  left_species : ∀ t, (leftEdge t).species = species t
  left_reaction : ∀ t, (leftEdge t).reaction = (reaction t).1
  right_reaction : ∀ t : Fin k, (rightEdge t).reaction = (reaction ⟨t.1, by omega⟩).1
  right_species : ∀ t : Fin k, (rightEdge t).species = species ⟨t.1 + 1, by omega⟩
  species_injective : Function.Injective species
  reaction_injective : Function.Injective reaction

namespace TrueSRLinearWalk

variable (W : N.TrueSRLinearWalk k)

private theorem hidx {q : ℕ} (hq : q < 2 * k + 2) : q / 2 < k + 1 := by omega

/-- Edges of the path: left edges at even positions, right edges at odd ones. -/
private noncomputable def pEdge (q : Fin (2 * k + 1)) : N.TrueSREdge :=
  if h : q.1 % 2 = 0 then W.leftEdge ⟨q.1 / 2, hidx (by have := q.isLt; omega)⟩
  else W.rightEdge ⟨q.1 / 2, by have := q.isLt; omega⟩

/-- Vertices of the path: species at even positions, reactions at odd ones. -/
private noncomputable def pVertex (p : Fin (2 * k + 2)) : N.TrueSRVertex :=
  if h : p.1 % 2 = 0 then Sum.inl (W.species ⟨p.1 / 2, hidx p.isLt⟩)
  else Sum.inr (W.reaction ⟨p.1 / 2, hidx p.isLt⟩)

private theorem pEdge_even {q : Fin (2 * k + 1)} (h : q.1 % 2 = 0) :
    W.pEdge q = W.leftEdge ⟨q.1 / 2, hidx (by have := q.isLt; omega)⟩ := dif_pos h

private theorem pEdge_odd {q : Fin (2 * k + 1)} (h : ¬ q.1 % 2 = 0) :
    W.pEdge q = W.rightEdge ⟨q.1 / 2, by have := q.isLt; omega⟩ := dif_neg h

private theorem pVertex_even {p : Fin (2 * k + 2)} (h : p.1 % 2 = 0) :
    W.pVertex p = Sum.inl (W.species ⟨p.1 / 2, hidx p.isLt⟩) := dif_pos h

private theorem pVertex_odd {p : Fin (2 * k + 2)} (h : ¬ p.1 % 2 = 0) :
    W.pVertex p = Sum.inr (W.reaction ⟨p.1 / 2, hidx p.isLt⟩) := dif_neg h

/-- **A linear alternating walk is a species-to-reaction path.** -/
noncomputable def toPath : N.TrueSRPath (2 * k + 1) where
  length_pos := by omega
  edge := W.pEdge
  vertex := W.pVertex
  connects := by
    intro q
    have hq := q.isLt
    have hcs : (Fin.castSucc q).1 = q.1 := rfl
    have hsu : (q.succ).1 = q.1 + 1 := rfl
    by_cases h : q.1 % 2 = 0
    · refine Or.inl ⟨?_, ?_⟩
      · rw [pVertex_even W (by rw [hcs]; exact h), pEdge_even W h]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (W.left_species _).symm
        exact congrArg W.species (Fin.ext (by show (Fin.castSucc q).1 / 2 = q.1 / 2; rfl))
      · rw [pVertex_odd W (by rw [hsu]; omega), pEdge_even W h]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (W.left_reaction _).symm
        exact congrArg (fun t => (W.reaction t).1) (Fin.ext (by
          show (q.succ).1 / 2 = q.1 / 2
          show (q.1 + 1) / 2 = q.1 / 2
          omega))
    · refine Or.inr ⟨?_, ?_⟩
      · rw [pVertex_odd W (by rw [hcs]; exact h), pEdge_odd W h]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (W.right_reaction _).symm
        exact congrArg (fun t => (W.reaction t).1) (Fin.ext (by
          show (Fin.castSucc q).1 / 2 = q.1 / 2
          rfl))
      · rw [pVertex_even W (by rw [hsu]; omega), pEdge_odd W h]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (W.right_species _).symm
        exact congrArg W.species (Fin.ext (by
          show (q.succ).1 / 2 = q.1 / 2 + 1
          show (q.1 + 1) / 2 = q.1 / 2 + 1
          omega))
  edge_simple := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    obtain ⟨hsp, hrx, -⟩ := hij
    by_cases h1 : i.1 % 2 = 0 <;> by_cases h2 : j.1 % 2 = 0
    · rw [pEdge_even W h1, pEdge_even W h2, W.left_species, W.left_species] at hsp
      have hv := congrArg Fin.val (W.species_injective hsp)
      exact Fin.ext (by simp only at hv; omega)
    · rw [pEdge_even W h1, pEdge_odd W h2, W.left_reaction, W.right_reaction] at hrx
      rw [pEdge_even W h1, pEdge_odd W h2, W.left_species, W.right_species] at hsp
      have hv := congrArg Fin.val (W.reaction_injective (Subtype.ext hrx))
      have hv2 := congrArg Fin.val (W.species_injective hsp)
      exfalso
      simp only at hv hv2
      omega
    · rw [pEdge_odd W h1, pEdge_even W h2, W.right_reaction, W.left_reaction] at hrx
      rw [pEdge_odd W h1, pEdge_even W h2, W.right_species, W.left_species] at hsp
      have hv := congrArg Fin.val (W.reaction_injective (Subtype.ext hrx))
      have hv2 := congrArg Fin.val (W.species_injective hsp)
      exfalso
      simp only at hv hv2
      omega
    · rw [pEdge_odd W h1, pEdge_odd W h2, W.right_reaction, W.right_reaction] at hrx
      have hv := congrArg Fin.val (W.reaction_injective (Subtype.ext hrx))
      exact Fin.ext (by simp only at hv; omega)
  vertex_simple := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases h1 : a.1 % 2 = 0 <;> by_cases h2 : b.1 % 2 = 0
    · rw [pVertex_even W h1, pVertex_even W h2] at hab
      have hv := congrArg Fin.val (W.species_injective (Sum.inl.inj hab))
      exact Fin.ext (by simp only at hv; omega)
    · rw [pVertex_even W h1, pVertex_odd W h2] at hab
      exact absurd hab (by simp)
    · rw [pVertex_odd W h1, pVertex_even W h2] at hab
      exact absurd hab (by simp)
    · rw [pVertex_odd W h1, pVertex_odd W h2] at hab
      have hv := congrArg Fin.val (W.reaction_injective (Sum.inr.inj hab))
      exact Fin.ext (by simp only at hv; omega)
  starts_at_species := by
    refine ⟨W.species ⟨0, by omega⟩, ?_⟩
    rw [pVertex_even W (by simp)]
    exact congrArg Sum.inl (congrArg W.species (Fin.ext (by simp)))
  ends_at_reaction := by
    refine ⟨W.reaction ⟨k, by omega⟩, ?_⟩
    have hl : (Fin.last (2 * k + 1)).1 = 2 * k + 1 := rfl
    rw [pVertex_odd W (by rw [hl]; omega)]
    exact congrArg Sum.inr (congrArg W.reaction (Fin.ext (by
      show (Fin.last (2 * k + 1)).1 / 2 = k
      show (2 * k + 1) / 2 = k
      omega)))

end TrueSRLinearWalk

end CRNT.Network
