import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Source components of finite directed relations

The sign-causality argument uses a nonempty strongly connected set with no incoming edge.
Minimizing the number of predecessors constructs such a set without a quotient graph.
-/

namespace CRNT

/-- The simple undirected graph obtained by forgetting the orientation of a relation. -/
def relationGraph {V : Type*} (E : V → V → Prop) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (E u v ∨ E v u)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, Or.symm h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- The unoriented causal graph induced by a finite vertex set, retaining vertices as subtypes. -/
def relationGraphOn {V : Type*} (E : V → V → Prop) (T : Finset V) :
    SimpleGraph {v // v ∈ T} where
  Adj u v := u.1 ≠ v.1 ∧ (E u.1 v.1 ∨ E v.1 u.1)
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, Or.symm h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

/-- Strong connectivity of a directed relation makes its underlying induced graph connected.
This is the entry point for applying finite undirected source-block arguments while keeping the
original directed relation available for the causal inequalities. -/
theorem relationGraphOn_connected {V : Type*} (E : V → V → Prop) (T : Finset V)
    (hT : T.Nonempty)
    (hsc : ∀ a b : {v // v ∈ T}, Relation.ReflTransGen (fun x y => E x.1 y.1) a b) :
    (relationGraphOn E T).Connected := by
  classical
  refine {
    preconnected := ?_
    nonempty := ⟨⟨Classical.choose hT, Classical.choose_spec hT⟩⟩
  }
  intro a b
  apply (SimpleGraph.reachable_iff_reflTransGen a b).2
  induction hsc a b with
  | refl => exact Relation.ReflTransGen.refl
  | @tail mid finish hprior hedge ih =>
      by_cases heq : mid = finish
      · subst finish
        exact ih
      · apply Relation.ReflTransGen.tail ih
        have hval : mid.1 ≠ finish.1 := by
          intro heqval
          apply heq
          exact Subtype.ext heqval
        exact ⟨hval, Or.inl hedge⟩

/-- A predecessor-closed strongly connected source induces a connected unoriented graph.  The
closure hypothesis is what keeps the directed paths inside the selected finite vertex set. -/
theorem relationGraphOn_connected_of_source {V : Type*} (E : V → V → Prop) (T : Finset V)
    (hT : T.Nonempty)
    (hsc : ∀ a ∈ T, ∀ b ∈ T, Relation.ReflTransGen E a b)
    (hclosed : ∀ a b, E a b → b ∈ T → a ∈ T) :
    (relationGraphOn E T).Connected := by
  apply relationGraphOn_connected E T hT
  have hlift : ∀ {a b : V} (h : Relation.ReflTransGen E a b)
      (ha : a ∈ T) (hb : b ∈ T),
      Relation.ReflTransGen (fun x y : {v // v ∈ T} => E x.1 y.1)
        ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b h
    induction h with
    | refl =>
        intro ha hb
        have hproof : ha = hb := Subsingleton.elim _ _
        subst hb
        exact Relation.ReflTransGen.refl
    | @tail mid finish hpath hedge ih =>
        intro ha hfinish
        have hmid : mid ∈ T := hclosed mid finish hedge hfinish
        exact Relation.ReflTransGen.tail (ih ha hmid) hedge
  intro a b
  exact hlift (hsc a.1 a.2 b.1 b.2) a.2 b.2

/-- A predecessor-closed strongly connected source has a simple undirected path between any two
of its vertices.  These paths are the finite combinatorial objects used to locate ears and
separating vertices in the source graph. -/
theorem relationGraphOn_exists_isPath_of_source {V : Type*} (E : V → V → Prop)
    (T : Finset V) (hT : T.Nonempty)
    (hsc : ∀ a ∈ T, ∀ b ∈ T, Relation.ReflTransGen E a b)
    (hclosed : ∀ a b, E a b → b ∈ T → a ∈ T)
    (a b : V) (ha : a ∈ T) (hb : b ∈ T) :
    ∃ p : (relationGraphOn E T).Walk ⟨a, ha⟩ ⟨b, hb⟩, p.IsPath := by
  exact ((relationGraphOn_connected_of_source E T hT hsc hclosed).preconnected
    ⟨a, ha⟩ ⟨b, hb⟩).exists_isPath

/-- A finite nonempty directed graph has a nonempty strongly connected source set.
Reachability is allowed to have length zero, so singleton components are included. -/
theorem exists_finite_source {V : Type*} [Fintype V] [Nonempty V]
    (E : V → V → Prop) :
    ∃ T : Finset V, T.Nonempty ∧
      (∀ a ∈ T, ∀ b ∈ T, Relation.ReflTransGen E a b) ∧
      (∀ a b, E a b → b ∈ T → a ∈ T) := by
  classical
  let pred : V → Finset V := fun v =>
    Finset.univ.filter (fun u => Relation.ReflTransGen E u v)
  have hmem (u v : V) : u ∈ pred v ↔ Relation.ReflTransGen E u v := by
    simp [pred]
  obtain ⟨v, _, hv⟩ := Finset.univ.exists_min_image (fun v => (pred v).card)
    Finset.univ_nonempty
  have heq {u : V} (hu : u ∈ pred v) : pred u = pred v := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      exact (hmem w v).2 (((hmem w u).1 hw).trans ((hmem u v).1 hu))
    · exact hv u (Finset.mem_univ u)
  refine ⟨pred v, ⟨v, (hmem v v).2 .refl⟩, ?_, ?_⟩
  · intro a ha b hb
    exact (hmem a b).1 (heq hb ▸ ha)
  · intro a b hab hb
    exact (hmem a v).2 (Relation.ReflTransGen.head hab ((hmem b v).1 hb))

/-- A path ending in a source set lies in it throughout; in particular its initial vertex
belongs to the source. -/
theorem source_closed_under_predecessors {V : Type*} {E : V → V → Prop}
    {T : Set V} (hT : ∀ a b, E a b → b ∈ T → a ∈ T)
    {a b : V} (h : Relation.ReflTransGen E a b) (hb : b ∈ T) : a ∈ T := by
  induction h with
  | refl => exact hb
  | tail _ hbc ih => exact ih (hT _ _ hbc hb)

end CRNT
