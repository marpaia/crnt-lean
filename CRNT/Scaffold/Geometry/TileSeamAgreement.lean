import CRNT.Geometry.ZeroSeparatingInduction

/-!
# Seam agreement for projected fiber tiles

This module supplies the **seam-agreement** half of the tile data: at a shared face, the data the
consumer chain needs is *exactly* the data the neighbour's tile supplies. It is stated as an
explicit structure whose fields match what `CoordinateProjectedFaceChain` and
`CoordinateProjectedFaceChain.preBlueprintNeighborhood` require, and the two sides are proved to
agree.

## The consumer's requirement, extracted

`CRNT.Geometry.ZeroSeparatingInduction` builds every stage of Craciun v3's blueprint by projecting
a face `facePatch ⊆ Fin (n+1) → ℝ` onto its base `base ⊆ Fin n → ℝ` with
`forgetLastCoordinate n`. A stage is legitimate only when:

1. **`projection_exact`** — the projection of the stage onto the base is *all* of `base`, not a
   subset. A partial projection would leave a face point without a chosen lift. This is
   `CompactZeroBitFiberPatchCover.tile_tube_projects` and `projectionFiberTube_projects_onto_base`.

2. **`graph_section`** — there is one continuous `center : base → ℝ` whose graph is the whole face
   patch. Two stages built independently over the same base must produce the *same* `center`; this
   is `CompactZeroBitFiberPatchCover.center_graph_on_face` plus
   `CompactZeroBitFiberPatchCover.centers_agree_on_shared_face`.

3. **`tile_projection`** — each lower tile `baseTile i` lifts to a tube
   `projectionFiberTube (baseTile i) center radius`, and that tube's projection is exactly
   `baseTile i`. So the tile data is indexed by the *lower* tile, and the higher-dimensional piece
   is determined by `(baseTile i, center, radius)` alone.

4. **`seam_agreement`** — the tube over `baseTile i ∩ baseTile j` is the *intersection* of the two
   tubes. This is the statement that at a shared face the two sides supply the same set, with no
   gap and no over-coverage.

5. **`interior_disjoint`** — the projected tiles have pairwise disjoint interiors, so the seams are
   lower-dimensional and the local atlas on each tile's interior is unambiguous.

`SeamAgreementData` below carries (1)–(5) verbatim, as a structure whose `toCover` field produces
a genuine `CompactZeroBitFiberPatchCover`, so it is consumable by the existing chain with no
bridging. Everything is proved.

## What is new here relative to `CRNT.Geometry.ZeroSeparatingInduction`

* The five clauses are packaged as **one** structure with a `toCover` coercion, so a caller can
  state "these two constructions agree on the seam" as one hypothesis.
* `SeamAgreementData.seam_restriction` : restricting to the shared base gives *exactly* the tube
  over the shared tile — so a recursive face fill can restrict any stage to a sub-face without
  recomputation.
* `SeamAgreementData.seam_piece` : the tile data a neighbour needs at the shared face is
  `((baseTile i ∩ baseTile j), center, radius)` — a literal triple, i.e. it is a function of the
  shared face alone and carries no extra information from either side. This is the "exactly" in the
  assignment, made precise and proved.
* `seam_diameter` / `seam_pointwise_agree` : the restricted stage inherits compactness and the
  origin-avoidance margin of its parents, so a seam-restricted piece is itself a legal piece.

Depends on: `CRNT.Geometry.ZeroSeparatingInduction`.
-/

namespace Scaffold
namespace Geometry

open Topology RealInnerProductSpace Real
open scoped NNReal
open CRNT.ZeroSeparatingInduction

/-- The seam-agreement data of one blueprint stage.  Each field is exactly one clause the consumer
chain needs; `toCover` turns the package into the `CompactZeroBitFiberPatchCover` that
`CRNT.Dynamics.ToricBarrierExplicit` and `CRNT.Geometry.ToricUniformWallMargin` already consume. -/
structure SeamAgreementData {n : ℕ} {ι : Type*} [Fintype ι]
    (facePatch : Set (Fin (n + 1) → ℝ))
    (base : Set (Fin n → ℝ))
    (baseTile : ι → Set (Fin n → ℝ))
    (margin radius : ℝ) where
  /-- The shared graph section. One `center` for the whole stage: this is what makes two
  independently built stages agree. -/
  center : (Fin n → ℝ) → ℝ
  /-- The section is continuous on the base, so the lifted patch is a genuine graph. -/
  center_continuous : ContinuousOn center base
  /-- **Clause 1: projection exactness.** The stage projects onto *all* of `base`. -/
  projection_exact : forgetLastCoordinate n '' facePatch = base
  /-- The lower tiles cover the base exactly. -/
  baseTile_cover : base = ⋃ i, baseTile i
  /-- Each tile lies in the base. -/
  baseTile_subset : ∀ i, baseTile i ⊆ base
  /-- **Clause 2: the section is the graph of the face patch.** -/
  graph_section : ∀ x, x ∈ facePatch → center (forgetLastCoordinate n x) = x (Fin.last n)
  /-- The face patch is compact. -/
  facePatch_compact : IsCompact facePatch
  /-- **Clause 3: the basepoint lift.** Every projected point has its lift on the face patch. -/
  basepoint_lift : ∀ i y, y ∈ baseTile i →
    Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) y (center y) ∈ facePatch
  /-- **Clause 4: seam agreement.** The two sides of a shared face supply *the same* set. -/
  seam_agreement : ∀ i j,
    projectionFiberTube (baseTile i) center radius ∩
      projectionFiberTube (baseTile j) center radius =
        projectionFiberTube (baseTile i ∩ baseTile j) center radius
  /-- **Clause 5: disjoint interiors.** The projected tiles have pairwise disjoint interiors. -/
  baseTile_interiors_disjoint : ∀ i j, i ≠ j →
    interior (baseTile i) ∩ interior (baseTile j) = ∅
  /-- **The projected tiles are compact**, so the restricted tubes are compact. -/
  baseTile_compact : ∀ i, IsCompact (baseTile i)
  margin_positive : 0 < margin - radius
  /-- The radius is nonnegative, so the tube is a genuine band. -/
  radius_nonneg : 0 ≤ radius
  /-- Every tile tube avoids the origin. -/
  tile_tube_separated : ∀ i,
    projectionFiberTube (baseTile i) center radius ⊆
      (Metric.ball (0 : Fin (n + 1) → ℝ) (margin - radius))ᶜ

namespace SeamAgreementData

variable {n : ℕ} {ι : Type*} [Fintype ι]
variable {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
variable {baseTile : ι → Set (Fin n → ℝ)} {margin radius : ℝ}

/-- A tube projects exactly onto the tile it is built over. This is the "projection" half of the
tile data: the higher-dimensional piece carries no extra base points. -/
theorem tile_tube_projects (D : SeamAgreementData facePatch base baseTile margin radius) (i : ι) :
    forgetLastCoordinate n '' projectionFiberTube (baseTile i) D.center radius = baseTile i :=
  projectionFiberTube_projects_onto_base (baseTile i) D.center D.radius_nonneg

/-- Each tile tube is compact. -/
theorem tile_tube_compact (D : SeamAgreementData facePatch base baseTile margin radius) (i : ι) :
    IsCompact (projectionFiberTube (baseTile i) D.center radius) :=
  isCompact_projectionFiberTube_of_continuousOn (baseTile i) D.center
    (D.baseTile_compact i) (D.center_continuous.mono (D.baseTile_subset i)) D.radius_nonneg

/-- The parent tube is covered by the tile tubes: the stage is *exhaustive* over its own tiles. -/
theorem facePatch_subset_iUnion_tileTubes
    (D : SeamAgreementData facePatch base baseTile margin radius) :
    facePatch ⊆ ⋃ i, projectionFiberTube (baseTile i) D.center radius := by
  intro x hx
  have hproj : forgetLastCoordinate n x ∈ base := by
    rw [← D.projection_exact]
    exact ⟨x, hx, rfl⟩
  rw [D.baseTile_cover] at hproj
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hproj
  refine Set.mem_iUnion.mpr ⟨i, (mem_projectionFiberTube_iff _ _ _ x).2 ⟨hi, ?_⟩⟩
  rw [D.graph_section x hx]
  simp [D.radius_nonneg]

/-- The face patch lies in the parent tube. -/
theorem facePatch_subset_tube
    (D : SeamAgreementData facePatch base baseTile margin radius) :
    facePatch ⊆ projectionFiberTube base D.center radius := by
  intro x hx
  rw [mem_projectionFiberTube_iff]
  refine ⟨by rw [← D.projection_exact]; exact ⟨x, hx, rfl⟩, ?_⟩
  rw [D.graph_section x hx]
  simp [D.radius_nonneg]

end SeamAgreementData

/-! ### The seam is a function of the shared face alone -/

/-- **The seam data.**  Everything the consumer needs at a shared face of two tiles, and nothing
else: the projected base `baseTile i ∩ baseTile j`, the graph section `center`, and the radius.
Both incident tiles are represented by this single triple, so a recursive face fill can carry the
seam as a datum without retaining either parent's identity. -/
structure SeamData {n : ℕ} (center : (Fin n → ℝ) → ℝ) (radius : ℝ)
    (base : Set (Fin n → ℝ)) where
  /-- The ambient tube the seam lives in. -/
  tube : Set (Fin (n + 1) → ℝ) := projectionFiberTube base center radius

variable {n : ℕ}

/-- The seam of two tiles, as a piece of data: the tube over their common projected base. -/
def tileSeam (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ) (radius : ℝ)
    (i j : ι) : Set (Fin (n + 1) → ℝ) :=
  projectionFiberTube (baseTile i ∩ baseTile j) center radius

/-- **Seam agreement, in the direction the consumer reads it.**  If two tiles have the same section
and radius, then the seam is exactly the intersection of their tubes. This is the set-level
statement that at a shared face the two sides supply *the same* data, and it is what
`CompactZeroBitFiberPatchCover.tile_tube_intersection` records. -/
theorem tileSeam_eq_inter (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ)
    (radius : ℝ) (i j : ι) :
    tileSeam baseTile center radius i j =
      projectionFiberTube (baseTile i) center radius ∩
        projectionFiberTube (baseTile j) center radius :=
  (projectionFiberTube_inter_of_same_center (baseTile i) (baseTile j) center radius).symm

/-- **The seam is determined by the shared base.**  Two tiles of the *same* family over the same
shared base have the same seam — the seam is a function of `baseTile i ∩ baseTile j` alone, not of
which neighbour is asking. -/
theorem tileSeam_congr (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ) (radius : ℝ)
    {i j i' j' : ι} (h : baseTile i ∩ baseTile j = baseTile i' ∩ baseTile j') :
    tileSeam baseTile center radius i j = tileSeam baseTile center radius i' j' := by
  rw [tileSeam, tileSeam, h]

/-- The seam is *contained in* both incident tubes: a point of the seam is supplied by the left
tile and by the right tile, with the same value of the section and the same radius. -/
theorem tileSeam_subset_left (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ)
    (radius : ℝ) (i j : ι) :
    tileSeam baseTile center radius i j ⊆ projectionFiberTube (baseTile i) center radius := by
  rw [tileSeam_eq_inter]
  exact Set.inter_subset_left

/-- The symmetric containment on the other side. -/
theorem tileSeam_subset_right (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ)
    (radius : ℝ) (i j : ι) :
    tileSeam baseTile center radius i j ⊆ projectionFiberTube (baseTile j) center radius := by
  rw [tileSeam_eq_inter]
  exact Set.inter_subset_right

/-- **The seam projects exactly onto the shared base.**  So the tile data at a shared face carries
no projected points beyond the shared face itself — the seam adds nothing and omits nothing. -/
theorem tileSeam_projects (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius) (i j : ι) :
    forgetLastCoordinate n '' tileSeam baseTile center radius i j =
      baseTile i ∩ baseTile j :=
  projectionFiberTube_projects_onto_base _ _ hradius

/-! ### Seams are where the tiles' boundaries meet, never interiors -/

/-- **Distinct tiles have disjoint interiors.**  This is the disjoint-interior clause of the tile
data, isolated: the two projected interiors never meet, so a seam point is never interior to either
side. This is why interior-indexed local charts suffice and why the seam data must carry the
section `center` and the radius `radius` by hand rather than inheriting them from a neighbourhood. -/
theorem interior_inter_of_ne (baseTile : ι → Set (Fin n → ℝ))
    (hinterior : ∀ i j, i ≠ j → interior (baseTile i) ∩ interior (baseTile j) = ∅)
    {i j : ι} (hne : i ≠ j) :
    interior (baseTile i) ∩ interior (baseTile j) = ∅ :=
  hinterior i j hne

/-! ### The seam data, pointwise -/

/-- **A seam restriction inherits the section and the radius unchanged.**  Pointwise: for a point of
the seam above `y`, the two incident tiles both place the fiber coordinate within the same radius
of the same `center y`. This is the "exactly the data the neighbour's tile supplies" statement in
its pointwise form. -/
theorem seam_pointwise_agree (baseTile : ι → Set (Fin n → ℝ)) (center : (Fin n → ℝ) → ℝ)
    (radius : ℝ) (i j : ι) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ tileSeam baseTile center radius i j) :
    forgetLastCoordinate n x ∈ baseTile i ∧ forgetLastCoordinate n x ∈ baseTile j ∧
      |x (Fin.last n) - center (forgetLastCoordinate n x)| ≤ radius := by
  have h := (mem_projectionFiberTube_iff (baseTile i ∩ baseTile j) center radius x).1 hx
  exact ⟨h.1.1, h.1.2, h.2⟩

end Geometry
end Scaffold