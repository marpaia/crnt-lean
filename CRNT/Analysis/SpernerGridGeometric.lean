import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import CRNT.Analysis.SpernerMultiIncidence

/-!
# The door graph of the N = 2 subdivision, derived from its geometry

`CRNT.Analysis.SpernerGridMulti` realizes the four-cell `N = 2` subdivision as a `MultiDoorIncidence`
but *specifies* its door graph by listing the two door edges. This module instead **derives** the
door graph from the underlying geometry — vertices, a coloring, and triangles given as vertex sets —
discharging the lattice-edge incidence lemma the construction rests on.

## The geometric data

The vertices are the three corners `A, B, C` and three edge midpoints `mAB, mAC, mBC` of the
2-simplex, colored `A = 0, B = 1, C = 2, mAB = 1, mAC = 0, mBC = 2`. Each triangle is its set of
three vertices (`triVerts`):

* `up1 = {A, mAB, mAC}`, `up2 = {mAB, B, mBC}`, `up3 = {mAC, mBC, C}`, `dn = {mAB, mAC, mBC}`.

A `{0,1}`-**door edge** of the triangulation is an unordered pair of vertices, both belonging to a
common triangle, whose colors are `{0, 1}`. The door graph is then defined *geometrically*:

* two distinct triangles are adjacent (`CellAdj`) when they **share** a `{0,1}`-door edge — two
  common vertices `u ≠ v` with `isDoor (colorOf u) (colorOf v)`;
* a triangle is adjacent to a boundary outer vertex (`BoundaryAdj`) when it contains both endpoints
  of that outer vertex's door edge.

No edge list is assumed: `CellAdj` quantifies over the vertices of the triangles, so the adjacency is
computed from `triVerts` and `colorOf` alone.

## The lattice-edge incidence lemma

The two named incidence facts are proved by `decide` directly from `triVerts`:

* `interior_doorEdge_borders_two`: the interior door edge `mAB–mAC` is contained in **exactly two**
  triangles, `up1` and `dn`;
* `boundary_doorEdge_borders_one`: the boundary door edge `A–mAB` is contained in **exactly one**
  triangle, `up1`.

These are precisely "every interior `{0,1}` sub-edge borders exactly two triangles; every boundary
`{0,1}` sub-edge borders exactly one." They are what forces each triangle's geometric door degree to
equal its local door count, discharging `cell_degree`. The whole datum is assembled as a
`MultiDoorIncidence` (`multiDoorIncidence`) whose color triples are read off `colorOf ∘ triV`, and
`exists_rainbow_cell` recovers the central triangle `dn` as the rainbow triangle — the two-dimensional
Sperner conclusion from a door graph built entirely from geometry.

## Main results

* `interior_doorEdge_borders_two`, `boundary_doorEdge_borders_one` — the lattice-edge incidence lemma.
* `multiDoorIncidence` — the geometrically-derived four-cell `MultiDoorIncidence`.
* `exists_rainbow_cell` — it has a rainbow triangle.

Depends on:
`Mathlib.Combinatorics.SimpleGraph.Finite`, `Mathlib.Data.Fintype.Sum`,
`Mathlib.Tactic.DeriveFintype`, `CRNT.Analysis.SpernerMultiIncidence`.
-/

namespace CRNT.Analysis.SpernerN2Geo

open SimpleGraph CRNT.Analysis CRNT.Analysis.Sperner2D CRNT.Analysis.SpernerTriangulation

/-- Vertices of the `N = 2` subdivision: three corners and three edge midpoints. -/
inductive Vertex
  | A | B | C | mAB | mAC | mBC
  deriving DecidableEq

instance : Fintype Vertex where
  elems := {Vertex.A, Vertex.B, Vertex.C, Vertex.mAB, Vertex.mAC, Vertex.mBC}
  complete := by intro v; cases v <;> simp

/-- The four triangles. -/
inductive Cell
  | up1 | up2 | up3 | dn
  deriving DecidableEq

instance : Fintype Cell where
  elems := {Cell.up1, Cell.up2, Cell.up3, Cell.dn}
  complete := by intro t; cases t <;> simp

/-- The boundary outer vertices: one for the boundary door edge `A–mAB` on side `AB`. -/
inductive Outer
  | edgeAmAB
  deriving DecidableEq

instance : Fintype Outer where
  elems := {Outer.edgeAmAB}
  complete := by intro o; cases o <;> simp

/-- The vertex coloring: corners `0, 1, 2`; midpoints chosen in the Sperner-admissible pair of their
side (`mAB = 1, mAC = 0, mBC = 2`). -/
def colorOf : Vertex → Color
  | .A => 0 | .B => 1 | .C => 2 | .mAB => 1 | .mAC => 0 | .mBC => 2

/-- Each triangle as an ordered vertex triple. -/
def triV : Cell → Vertex × Vertex × Vertex
  | .up1 => (.A, .mAB, .mAC)
  | .up2 => (.mAB, .B, .mBC)
  | .up3 => (.mAC, .mBC, .C)
  | .dn => (.mAB, .mAC, .mBC)

/-- Each triangle as its set of three vertices. -/
def triVerts (t : Cell) : Finset Vertex := {(triV t).1, (triV t).2.1, (triV t).2.2}

/-- The color triple of a triangle, read off its vertices. -/
def col (t : Cell) : Color × Color × Color :=
  (colorOf (triV t).1, colorOf (triV t).2.1, colorOf (triV t).2.2)

/-- **Interior door adjacency, geometric.** Two distinct triangles are adjacent when they share a
`{0,1}`-door edge: two common vertices `u ≠ v` whose colors form a door. -/
def CellAdj (t t' : Cell) : Prop :=
  t ≠ t' ∧ ∃ u ∈ triVerts t, ∃ v ∈ triVerts t,
    u ≠ v ∧ u ∈ triVerts t' ∧ v ∈ triVerts t' ∧ isDoor (colorOf u) (colorOf v) = true

instance : DecidableRel CellAdj := fun t t' => by unfold CellAdj; infer_instance

/-- The door edge carried by each boundary outer vertex. -/
def outerEdge : Outer → Vertex × Vertex
  | .edgeAmAB => (.A, .mAB)

/-- **Boundary door adjacency, geometric.** A triangle is adjacent to a boundary outer vertex when it
contains both endpoints of that vertex's door edge. -/
def BoundaryAdj (t : Cell) (o : Outer) : Prop :=
  (outerEdge o).1 ∈ triVerts t ∧ (outerEdge o).2 ∈ triVerts t

instance : DecidableRel BoundaryAdj := fun t o => by unfold BoundaryAdj; infer_instance

/-- The combined door relation over `Cell ⊕ Outer`: interior adjacency between triangles, boundary
adjacency between a triangle and an outer vertex, none between outer vertices. -/
def gRel : (Cell ⊕ Outer) → (Cell ⊕ Outer) → Prop
  | Sum.inl t, Sum.inl t' => CellAdj t t'
  | Sum.inl t, Sum.inr o => BoundaryAdj t o
  | Sum.inr o, Sum.inl t => BoundaryAdj t o
  | Sum.inr _, Sum.inr _ => False

instance : DecidableRel gRel := fun a b => by cases a <;> cases b <;> unfold gRel <;> infer_instance

/-- The door graph on `Cell ⊕ Outer`, built from the geometric door relation. -/
def doorGraph : SimpleGraph (Cell ⊕ Outer) := SimpleGraph.fromRel gRel

instance : DecidableRel doorGraph.Adj := by unfold doorGraph; infer_instance

/-- **Lattice-edge incidence (interior).** The interior door edge `mAB–mAC` is contained in exactly
two triangles, `up1` and `dn`. -/
theorem interior_doorEdge_borders_two (t : Cell) :
    (Vertex.mAB ∈ triVerts t ∧ Vertex.mAC ∈ triVerts t) ↔ (t = .up1 ∨ t = .dn) := by
  cases t <;> decide

/-- **Lattice-edge incidence (boundary).** The boundary door edge `A–mAB` is contained in exactly one
triangle, `up1`. -/
theorem boundary_doorEdge_borders_one (t : Cell) :
    (Vertex.A ∈ triVerts t ∧ Vertex.mAB ∈ triVerts t) ↔ t = .up1 := by
  cases t <;> decide

/-- The geometrically-derived four-cell multi-outer door-incidence datum. Its `cell_degree` and
`outer_odd` fields hold because the door graph — defined from `triVerts` and `colorOf` — gives each
triangle exactly one neighbor per `{0,1}`-door edge, by the lattice-edge incidence lemma. -/
def multiDoorIncidence : MultiDoorIncidence Cell Outer where
  G := doorGraph
  col := col
  cell_degree := by decide
  outer_odd := by decide

/-- **Geometrically-derived two-dimensional Sperner.** The door-incidence datum built from the
`N = 2` subdivision's geometry has a rainbow triangle (the central triangle `dn`). -/
theorem exists_rainbow_cell : ∃ t : Cell, multiDoorIncidence.IsRainbowCell t :=
  multiDoorIncidence.exists_rainbow

end CRNT.Analysis.SpernerN2Geo
