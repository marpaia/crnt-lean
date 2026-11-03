import CRNT.Graph.FiniteSource

/-!
# Separations, nonseparability, and end blocks of a finite graph

Shinar--Feinberg, *Concordant Chemical Reaction Networks and the Species-Reaction Graph*
(arXiv:1203.6560), §5.5, draws on standard finite-graph vocabulary (Bondy--Murty, Graph
Theory, ch. 10) to decompose a source of the sign-causality graph into **source-blocks**:

* a *separation* of a connected graph splits it into two connected pieces meeting in
  exactly one vertex, the *separating vertex*;
* a *block* is a maximal nonseparable subgraph (nonseparable = connected, no separating
  vertex);
* an *end block* is a block containing at most one separating vertex of the original
  graph — equivalently, a leaf of the block-tree;
* because a source is strongly connected, each of its blocks is strongly connected and
  nonseparable, and the classification (Proposition 5.8) says each block is an S-block,
  an R-block, or a single cycle.

This file supplies the first layer of that vocabulary.  Everything is phrased for an
ambient relation `E` restricted to a vertex set: walks are `relationGraph E`-walks whose
vertices stay inside the set, matching how the repository's `RelPath E T` records paths
of a source.  The separating-vertex definition uses the path-blocking description
("every `a`–`b` walk inside the set passes through `v`"), the vertex-removal form of the
paper's edge-form separation.

**Deferred (per the session verdict on the block datum):** maximality of blocks, the
existence of the block decomposition and its block-tree (including the leaf fact used by
§5.9 leaf removal), and directed ear decomposition existence (§A.1, Proposition A.3) are
*not* in Mathlib and are not developed here.  The repository's
`DirectedEar`/`DirectedEarDecomposition` scaffolding (TrueChemistrySRCriterion.lean)
covers only the ear side and records the same gap in its docstring.
-/

namespace CRNT

variable {V : Type*}

/-- An `E`-walk from `a` to `b` whose vertices all lie in `S`: the reachability notion
used for separations below. -/
def ExistsWalkOn (E : V → V → Prop) (S : Finset V) (a b : V) : Prop :=
  ∃ W : SimpleGraph.Walk (relationGraph E) a b, ∀ x ∈ W.support, x ∈ S

/-- `v` separates `a` from `b` within `S`: the two are connected by an `E`-walk inside
`S`, but only through `v` — every walk that stays inside `S` (the walk universe of the
subgraph itself, as in the paper's separations) visits `v`.  Quantifying only over walks
keeping their vertices in `S` is essential: an ambient detour leaving `S` must not be
counted as bypassing `v`, or separation would be too easy to evade and nonseparability
too cheap to obtain. -/
def SeparatesWithin (E : V → V → Prop) (S : Finset V) (v a b : V) : Prop :=
  a ≠ v ∧ b ≠ v ∧ ExistsWalkOn E S a b ∧
    ∀ W : SimpleGraph.Walk (relationGraph E) a b, (∀ x ∈ W.support, x ∈ S) →
      v ∈ W.support

/-- `v` is a separating vertex of the graph induced by `S`: some two vertices of `S`
other than `v` are connected inside `S`, but every such walk passes through `v`
(Shinar--Feinberg §5.5). -/
def IsSeparatingVertexOn (E : V → V → Prop) (S : Finset V) (v : V) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, SeparatesWithin E S v a b

/-- The graph induced by `S` is connected: every pair of vertices of `S` is joined by an
`E`-walk staying inside `S`. -/
def ConnectedOn (E : V → V → Prop) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ExistsWalkOn E S a b

/-- The induced graph on `S` is nonseparable: connected and without a separating vertex
(Shinar--Feinberg §5.5 after Bondy--Murty). -/
def IsNonseparableOn (E : V → V → Prop) (S : Finset V) : Prop :=
  ConnectedOn E S ∧ ∀ v ∈ S, ¬ IsSeparatingVertexOn E S v

/-- An end block of the ambient graph on `T`: the induced graph on `S` is nonseparable
and `S` contains at most one separating vertex of the *ambient* graph — the defining
property of a leaf of the block-tree (§5.5).  Maximality of `S` as a block is deferred
with the block-existence theory (see the module docstring). -/
def IsEndBlockOn (E : V → V → Prop) (T S : Finset V) : Prop :=
  IsNonseparableOn E S ∧
    ∀ v1 ∈ S, ∀ v2 ∈ S, IsSeparatingVertexOn E T v1 → IsSeparatingVertexOn E T v2 → v1 = v2

/-- Sanity: if the ambient vertex set has at most two vertices, no vertex separates any
pair inside it — the witnesses would be two elements of a set of at most one element. -/
theorem not_isSeparatingVertexOn_of_card_le_two {E : V → V → Prop} [DecidableEq V]
    [Fintype V] (S : Finset V) (v : V) (h : Fintype.card V ≤ 2) :
    ¬ IsSeparatingVertexOn E S v := by
  rintro ⟨a, ha, b, hb, hav, hbv, _, hsep⟩
  have hmax : (((Finset.univ : Finset V).erase v)).card ≤ 1 := by
    have h1 := Finset.card_erase_add_one (Finset.mem_univ v)
    have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  have haE : a ∈ ((Finset.univ : Finset V).erase v) :=
    Finset.mem_erase.mpr ⟨hav, Finset.mem_univ a⟩
  have hbE : b ∈ ((Finset.univ : Finset V).erase v) :=
    Finset.mem_erase.mpr ⟨hbv, Finset.mem_univ b⟩
  have hab : a = b := Finset.card_le_one.mp hmax a haE b hbE
  rw [← hab] at hsep
  have hnil : v ∈
      (SimpleGraph.Walk.nil : SimpleGraph.Walk (relationGraph E) a a).support :=
    hsep SimpleGraph.Walk.nil (by
      intro x hx
      simp only [SimpleGraph.Walk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
      exact ha)
  simp only [SimpleGraph.Walk.support] at hnil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hnil
  exact absurd hnil (Ne.symm hav)

end CRNT
