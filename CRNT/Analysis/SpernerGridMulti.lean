import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import CRNT.Analysis.SpernerMultiIncidence

/-!
# A concrete multi-triangle multi-outer door-incidence datum

This module constructs a *genuinely multi-triangle* `MultiDoorIncidence` term and runs it through
`CRNT.Analysis.SpernerTriangulation.MultiDoorIncidence.exists_rainbow`, exercising the uncollapsed
door-incidence interface (door graph on `Cell ⊕ Outer`) on a real triangulation with an interior
shared door — the step the single-cell `CRNT.Analysis.SpernerGrid` could not reach.

The triangulation is the **N = 2 barycentric subdivision of the 2-simplex** `ABC`, the canonical
Sperner picture: the three corners `A, B, C`, the three edge midpoints `mAB, mAC, mBC`, and the four
small triangles

* `up1 = {A, mAB, mAC}`, `up2 = {mAB, B, mBC}`, `up3 = {mAC, mBC, C}` (the corner triangles), and
* `dn = {mAB, mAC, mBC}` (the central inverted triangle).

With the standard corner coloring `A = 0`, `B = 1`, `C = 2` and the midpoint choice `mAB = 1`,
`mAC = 0`, `mBC = 2` (each midpoint colored within the Sperner-admissible pair of its side), the
vertex-color triples are

* `up1 ↦ (0, 1, 0)`, door count `2`; `up2 ↦ (1, 1, 2)`, door count `0`;
* `up3 ↦ (0, 2, 2)`, door count `0`; `dn ↦ (1, 0, 2)`, door count `1` — the unique rainbow triangle.

The `{0,1}`-doors of this coloring are exactly two: the **interior** edge `mAB–mAC` shared by `up1`
and `dn`, and the **boundary** edge `A–mAB` of `up1` (on side `AB`). The door graph therefore has one
interior edge `up1 — dn` and one cell–outer edge `up1 — Outer.boundary`; every other triangle has
door degree `0`. The two geometric incidence fields `cell_degree` (each triangle's door degree equals
its local door count: `2, 0, 0, 1`) and `outer_odd` (the lone boundary outer vertex has odd degree)
are discharged by `decide` on this concrete finite door graph.

Feeding the datum to `exists_rainbow` recovers the central triangle `dn` as the rainbow triangle — the
full multi-outer door-incidence pipeline on a genuine four-cell triangulation with a shared interior
door.

## Main results

* `CRNT.Analysis.SpernerN2.multiDoorIncidence` — the concrete four-cell `MultiDoorIncidence`.
* `CRNT.Analysis.SpernerN2.exists_rainbow_cell` — it has a rainbow triangle.

Depends on:
`Mathlib.Combinatorics.SimpleGraph.Finite`, `Mathlib.Data.Fintype.Sum`,
`Mathlib.Tactic.DeriveFintype`, `CRNT.Analysis.SpernerMultiIncidence`.
-/

namespace CRNT.Analysis.SpernerN2

open SimpleGraph CRNT.Analysis CRNT.Analysis.Sperner2D CRNT.Analysis.SpernerTriangulation

/-- The four triangles of the `N = 2` subdivision: three corner triangles and the central inverted
one. -/
inductive Cell
  | up1
  | up2
  | up3
  | dn
  deriving DecidableEq

instance : Fintype Cell where
  elems := {Cell.up1, Cell.up2, Cell.up3, Cell.dn}
  complete := by intro t; cases t <;> simp

/-- The boundary outer vertices: a single `{0,1}`-door on side `AB` (the edge `A–mAB`). -/
inductive Outer
  | boundary
  deriving DecidableEq

instance : Fintype Outer where
  elems := {Outer.boundary}
  complete := by intro o; cases o <;> simp

/-- The vertex-color triples of the four triangles under the coloring
`A = 0, B = 1, C = 2, mAB = 1, mAC = 0, mBC = 2`. -/
def cellColors : Cell → Color × Color × Color
  | .up1 => (0, 1, 0)
  | .up2 => (1, 1, 2)
  | .up3 => (0, 2, 2)
  | .dn => (1, 0, 2)

/-- The door relation: the interior door `up1 — dn` (shared edge `mAB–mAC`) and the boundary door
`up1 — Outer.boundary` (edge `A–mAB`). `SimpleGraph.fromRel` symmetrizes and removes self-loops. -/
def doorRel : (Cell ⊕ Outer) → (Cell ⊕ Outer) → Prop := fun a b =>
  (a = Sum.inl Cell.up1 ∧ b = Sum.inl Cell.dn) ∨
    (a = Sum.inl Cell.up1 ∧ b = Sum.inr Outer.boundary)

instance : DecidableRel doorRel := fun a b => by unfold doorRel; infer_instance

/-- The door graph on `Cell ⊕ Outer`. -/
def doorGraph : SimpleGraph (Cell ⊕ Outer) := SimpleGraph.fromRel doorRel

instance : DecidableRel doorGraph.Adj := by unfold doorGraph; infer_instance

/-- The concrete four-cell multi-outer door-incidence datum. -/
def multiDoorIncidence : MultiDoorIncidence Cell Outer where
  G := doorGraph
  col := cellColors
  cell_degree := by decide
  outer_odd := by decide

/-- **Concrete multi-triangle two-dimensional Sperner.** The `N = 2` subdivision's door-incidence
datum has a rainbow triangle (it is the central triangle `dn`). -/
theorem exists_rainbow_cell : ∃ t : Cell, multiDoorIncidence.IsRainbowCell t :=
  multiDoorIncidence.exists_rainbow

end CRNT.Analysis.SpernerN2
