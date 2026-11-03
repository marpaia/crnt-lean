import CRNT.Basic.Network
import Mathlib.Data.Fintype.Sum
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Logic.Equiv.Sum

/-!
# The species–reaction graph

The *species–reaction graph* (SR-graph) of a reaction network is the undirected
bipartite graph whose vertices are the species on one side and the reactions on the
other, with an edge joining a species `s` to a reaction `r` exactly when `s` occurs
in `r` (it has nonzero stoichiometry as a source or a target).

The vertex type is the sum `S ⊕ N.R` of the species type and the reaction index
type. `OccursIn` records the incidence relation, `srGraph` is the resulting
`SimpleGraph`, and the graph is shown to be bipartite with parts the species and the
reactions (`srGraph_isBipartiteWith`, `srGraph_isBipartite`). The adjacency is
characterised by `srGraph_adj_iff`, and the absence of same-side edges by
`srGraph_not_adj_species` and `srGraph_not_adj_reaction`.

Depends on: `CRNT.Basic.Network`,
`Mathlib.Data.Fintype.Sum`, `Mathlib.Combinatorics.SimpleGraph.Bipartite`,
`Mathlib.Logic.Equiv.Sum`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The vertex type of the species–reaction graph: a species (`Sum.inl`) or a
reaction index (`Sum.inr`). -/
abbrev SRVertex (S : Type) [DecidableEq S] [Fintype S] (N : Network S) : Type := S ⊕ N.R

/-- A species `s` *occurs in* a reaction `r` when it has nonzero stoichiometry as a
source or a target of `r`. -/
def OccursIn (N : Network S) (s : S) (r : N.R) : Prop :=
  (N.reaction r).source s ≠ 0 ∨ (N.reaction r).target s ≠ 0

instance (N : Network S) : DecidableRel (fun s r => N.OccursIn s r) :=
  fun s r => inferInstanceAs (Decidable ((N.reaction r).source s ≠ 0 ∨ (N.reaction r).target s ≠ 0))

/-- **The species–reaction graph** on the vertex type `S ⊕ N.R`: an edge joins a
species to a reaction it occurs in. There are no edges between two species or
between two reactions. -/
def srGraph (N : Network S) : SimpleGraph (S ⊕ N.R) where
  Adj x y :=
    match x, y with
    | Sum.inl s, Sum.inr r => N.OccursIn s r
    | Sum.inr r, Sum.inl s => N.OccursIn s r
    | _, _ => False
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp_all⟩
  loopless := ⟨fun x h => by cases x <;> simp_all⟩

instance (N : Network S) : DecidableRel N.srGraph.Adj := fun x y => by
  cases x <;> cases y <;>
    first
      | exact inferInstanceAs (Decidable (N.OccursIn _ _))
      | exact inferInstanceAs (Decidable False)

/-- A species is adjacent to a reaction in the SR-graph exactly when it occurs in
that reaction. -/
@[simp] theorem srGraph_adj_iff (N : Network S) (s : S) (r : N.R) :
    N.srGraph.Adj (Sum.inl s) (Sum.inr r) ↔ N.OccursIn s r := Iff.rfl

/-- No two species are adjacent in the SR-graph. -/
theorem srGraph_not_adj_species (N : Network S) (s s' : S) :
    ¬ N.srGraph.Adj (Sum.inl s) (Sum.inl s') := id

/-- No two reactions are adjacent in the SR-graph. -/
theorem srGraph_not_adj_reaction (N : Network S) (r r' : N.R) :
    ¬ N.srGraph.Adj (Sum.inr r) (Sum.inr r') := id

/-- **The SR-graph is bipartite** with parts the species and the reactions. -/
theorem srGraph_isBipartiteWith (N : Network S) :
    N.srGraph.IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := Set.isCompl_range_inl_range_inr.disjoint
  mem_of_adj := by
    rintro x y hadj
    cases x <;> cases y <;> first
      | exact absurd hadj id
      | (left; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)
      | (right; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)

/-- **The SR-graph is bipartite.** -/
theorem srGraph_isBipartite (N : Network S) : N.srGraph.IsBipartite :=
  (N.srGraph_isBipartiteWith).isBipartite

section Example

/-- A two-species, single-reaction network `A → B` realised inline: species `Fin 2`
and one reaction with source the unit complex on `0` and target the unit complex on
`1`. -/
private def exampleNetwork : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- Species `0` occurs in the reaction (it is the source). -/
example : exampleNetwork.OccursIn 0 () := by
  left
  simp [exampleNetwork]

/-- The corresponding species–reaction edge is present. -/
example : exampleNetwork.srGraph.Adj (Sum.inl 0) (Sum.inr ()) := by decide

/-- Two species are never adjacent in the SR-graph. -/
example : ¬ exampleNetwork.srGraph.Adj (Sum.inl 0) (Sum.inl 1) := by decide

end Example

end Network

end CRNT
