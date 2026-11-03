import CRNT.Geometry.ZeroSeparatingInduction
import CRNT.Geometry.FaithfulCurve
import CRNT.Geometry.ConeFace
import CRNT.Geometry.FiniteConeClosed
import Mathlib.Geometry.Convex.Cone.DualFinite
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Fan refinement and faithful transfer to a coarser fan

A ruled patch aligned simultaneously to several attracting directions has no surface normal once
those directions span the ambient space, which first occurs in dimension four
(`ZeroSeparatingInduction.over_determined_in_dim_four`). Craciun's faithful blueprint controls which
fan cones constrain a normal at each smooth point. This module proves that admissibility transfers
from a supplied fine cell to a containing coarse cell, and that an explicitly supplied constraint
family of cardinality below `finrank` admits a nonzero orthogonal normal. It does not construct the
blueprint subdivision or prove that its local patches satisfy that cardinality bound.

This module provides the transfer and finite-refinement engines:

* the **faithful-transfer engine** — admissibility for a finer cell transfers to the containing coarse
  cell, so the finer surface's normals are admissible for the coarse fan; and

* the **finite common-refinement engine** — a finite list of supplied fans can be intersected
  successively, preserving the fan axioms and dual finite generation of every cell; and

* the **projection coverage step** — images of a complete fan cover the target of a surjective
  linear map, and images of finitely generated cells are exact finitely generated cones;

* the **one-dimensional projection step** — a finite half-space description remains finite under
  projection when each fiber is a translate of a single kernel direction and a linear section is
  supplied;

* the **conditional feasibility lemma** — a supplied patch with fewer than `finrank ℝ E` active
  attracting directions admits a valid surface normal.

* the **central-arrangement fan engine** — the family of all weak sign/equality cells for a finite
  set of hyperplane normals is a complete polyhedral fan, with exposed-face closure from finite
  Farkas decomposition; and

* the **conditional arrangement-refinement engine** — for any supplied covering polyhedral fan
  whose cells have finite dual representations, the arrangement of the union of those normals
  refines the fan;

## Contents

* `Refines F' F` — the refinement relation: every cell of `F'` is contained (as a set) in some cell
  of `F`.

* `attractsToward_coarse_of_fine` — a normal admissible for a finer cell `C' ⊆ C` is admissible for
  the coarse cell `C` (`Faithful.AttractsToward` is monotone under cell containment).

* `coneDual_coarse_subset_halfPlane_of_fine_mem` — consequently the coarse cell's toric-field polar
  `coneDual C` lies in the normal's region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`: a fine-admissible
  normal makes the coarse field inward.

* `exists_coarse_cell_of_refines` — packaged over `Refines`: a normal admissible for a cell of the
  refinement is admissible for some cell of the coarse fan.

* `exists_patch_normal_of_card_lt_finrank` — an explicitly indexed patch with fewer than
  `finrank ℝ E` attracting-direction constraints admits a nonzero orthogonal surface normal.


## Scope

This module proves the refinement relation, the faithful-transfer of admissibility (and of field
inwardness) from fine to coarse cells, finite common-refinement closure for supplied polyhedral fans
with dual-finitely-generated cells, and coverage of the closed-cone image family under a surjective
linear map. It also proves that split projections with a one-dimensional kernel preserve finite
dual representations, that a finite central hyperplane arrangement gives a polyhedral fan covering
the ambient space, and that its arrangement refines any supplied covering cone family with
dual-finitely-generated cells. In particular, the arrangement refines the projected image family of
a complete polyhedral fan under such a projection, yielding a complete polyhedral fan refinement
with dual-finitely-generated cells; this does not establish that the image family itself is a fan. The
faithful blueprint, its patch decomposition, and the analysis matching per-patch attracting
directions remain separate constructions.

Depends on: `CRNT.Geometry.ZeroSeparatingInduction`,
`CRNT.Geometry.FaithfulCurve`.
-/

namespace CRNT

namespace FanRefinement

open scoped InnerProductSpace
open CRNT.Faithful ZeroSeparatingInduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The refinement relation.** `F'` refines `F` when every cell of `F'` is contained, as a set, in
some cell of `F`: each coarse cell is subdivided into finer cells, so the finer fan resolves the
coarse one. -/
def Refines [CompleteSpace E] (F' F : Fan E) : Prop :=
  ∀ C' ∈ F', ∃ C ∈ F, (C' : Set E) ⊆ (C : Set E)

/-- The actual common-face condition for a fan: every pairwise intersection is an exposed face of
both incident cones. `IsPolyhedralFan.inter_common` records only the set equality to a fan cell;
this stronger property is needed when transferring local toric-field polars across a wall. -/
def HasExposedCommonFaces [CompleteSpace E] (F : Fan E) : Prop :=
  ∀ C ∈ F, ∀ D ∈ F, ∃ G ∈ F,
    (G : Set E) = (C : Set E) ∩ (D : Set E) ∧
      IsExposedFaceOf G C ∧ IsExposedFaceOf G D

/-- Compact subsets of an open set have a uniform positive ball margin. -/
theorem IsCompact.exists_pos_uniform_ball_subset {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ x ∈ K, Metric.ball x δ ⊆ U := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact (hKempty ▸ hx).elim
  have hlocal : ∀ x ∈ K, ∃ r > 0, Metric.ball x (2 * r) ⊆ U := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU hx))
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro y hy
    apply hball
    have hy' : dist y x < r := by
      simpa only [Metric.mem_ball, show 2 * (r / 2) = r by ring] using hy
    exact Metric.mem_ball.mpr hy'
  let radius : K → ℝ := fun x => Classical.choose (hlocal x.1 x.2)
  have hradius_pos (x : K) : 0 < radius x := (Classical.choose_spec (hlocal x.1 x.2)).1
  have hlocal_ball (x : K) : Metric.ball x.1 (2 * radius x) ⊆ U :=
    (Classical.choose_spec (hlocal x.1 x.2)).2
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.1 (radius x) := by
    intro x hx
    have hxball : x ∈ Metric.ball x (radius ⟨x, hx⟩) :=
      Metric.mem_ball_self (hradius_pos ⟨x, hx⟩)
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxball⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.1 (radius x)) (fun x => Metric.isOpen_ball) hcover
  have hsne : s.Nonempty := by
    by_contra h
    have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hKempty' : K = ∅ := by
      ext x
      constructor
      · intro hx
        have hxcover := hs hx
        simp [hsempty] at hxcover
      · simp
    exact hKempty hKempty'
  let radii := s.image radius
  have hradii : radii.Nonempty := Finset.image_nonempty.mpr hsne
  let δ := radii.min' hradii
  have hδ : 0 < δ := by
    obtain ⟨x, hx, hxδ⟩ := Finset.mem_image.mp (Finset.min'_mem radii hradii)
    change 0 < radii.min' hradii
    rw [← hxδ]
    exact hradius_pos x
  refine ⟨δ, hδ, ?_⟩
  intro x hx z hz
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hδy : δ ≤ radius y := by
    exact Finset.min'_le radii (radius y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hzy : dist z y.1 < 2 * radius y := by
    calc
      dist z y.1 ≤ dist z x + dist x y.1 := dist_triangle _ _ _
      _ < δ + radius y := add_lt_add (Metric.mem_ball.mp hz) (Metric.mem_ball.mp hxy)
      _ ≤ radius y + radius y := add_le_add hδy le_rfl
      _ = 2 * radius y := by ring
  exact hlocal_ball y (Metric.mem_ball.mpr hzy)

/-- A genuine face of a cone that contains an interior point is the whole cone. -/
theorem exposedFace_eq_of_mem_interior [CompleteSpace E]
    {G D : ProperCone ℝ E} (hface : IsExposedFaceOf G D) {x : E}
    (hxD : x ∈ interior (D : Set E)) (hxG : x ∈ (G : Set E)) : G = D := by
  have hface' := isExposedFaceOf_isFaceOf hface
  have hDG : (D : Set E) ⊆ (G : Set E) := by
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hxD)
    let t : ℝ := r / (‖z‖ + 1)
    have ht : 0 < t := div_pos hr (by positivity)
    have hdist : dist (x - t • z) x = t * ‖z‖ := by
      rw [dist_eq_norm, show x - t • z - x = -(t • z) by abel,
        norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hnear : t * ‖z‖ < r := by
      calc
        t * ‖z‖ = r * ‖z‖ / (‖z‖ + 1) := by dsimp [t]; ring
        _ < r := (div_lt_iff₀ (by positivity : 0 < ‖z‖ + 1)).2 (by
          nlinarith [hr, norm_nonneg z])
    have hyD : x - t • z ∈ (D : Set E) :=
      interior_subset (hball (Metric.mem_ball.mpr (calc
        dist (x - t • z) x = t * ‖z‖ := hdist
        _ < r := hnear)))
    have hsum : t • z + (x - t • z) = x := by abel
    have hsumG : t • z + (x - t • z) ∈ (G : Set E) := by rw [hsum]; exact hxG
    exact hface'.mem_of_smul_add_mem hz hyD ht hsumG
  have hGsubD : (G : Set E) ⊆ (D : Set E) := SetLike.coe_subset_coe.mpr hface'.le
  have hGDset : (G : Set E) = (D : Set E) := Set.Subset.antisymm hGsubD hDG
  exact SetLike.coe_injective hGDset

/-- If a metric ball around a state lies inside one fan cell, every cone admitted by the toric
differential inclusion has its polar contained in that cell's polar. Hence every allowed velocity
obeys all linear inequalities given by vectors in the cell. This is the local field-to-normal
bridge used after the Craciun blueprint has placed a patch within a single fan chamber. -/
theorem toricField_subset_coneDual_of_ball_inside_cell [CompleteSpace E]
    {F : Fan E} (hFfaces : HasExposedCommonFaces F)
    {D : ProperCone ℝ E} (hD : D ∈ F) {x : E} {δ : ℝ}
    (hball : Metric.ball x δ ⊆ interior (D : Set E)) :
    (toricField F δ x : Set E) ⊆ (coneDual (D : Set E) : Set E) := by
  have hgenerators : toricGenerators F δ x ⊆ coneDual (D : Set E) := by
    intro v hv
    obtain ⟨C, hC, hnear, hvC⟩ := mem_toricGenerators.mp hv
    obtain ⟨y, hyC, hyDist⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem C⟩).mp hnear
    have hyball : y ∈ Metric.ball x δ := Metric.mem_ball.mpr (by
      rw [dist_comm]
      exact hyDist)
    have hyD : y ∈ interior (D : Set E) := hball hyball
    obtain ⟨G, _hG, hintersection, _hGC, hGD⟩ := hFfaces C hC D hD
    have hyG : y ∈ (G : Set E) := by
      rw [hintersection]
      exact ⟨hyC, interior_subset hyD⟩
    have hGD_eq : G = D := exposedFace_eq_of_mem_interior hGD hyD hyG
    have hDsubsetC : (D : Set E) ⊆ (C : Set E) := by
      intro z hz
      have hzG : z ∈ (G : Set E) := by rw [hGD_eq]; exact hz
      rw [hintersection] at hzG
      exact hzG.1
    have hvC' : v ∈ coneDual (C : Set E) := by simpa using hvC
    exact mem_coneDual.mpr (by
      intro z hz
      exact (mem_coneDual.mp hvC') (hDsubsetC hz))
  change (PointedCone.hull ℝ (toricGenerators F δ x) : Set E) ⊆
    (coneDual (D : Set E) : Set E)
  intro v hv
  change v ∈ Submodule.span (Nonneg ℝ) (toricGenerators F δ x) at hv
  have hspan : Submodule.span (Nonneg ℝ) (toricGenerators F δ x) ≤
      (coneDual (D : Set E)).toPointedCone := by
    exact Submodule.span_le.2 hgenerators
  exact hspan hv

/-- Intersecting a compact seam patch with every cell of a finite complete fan refinement gives a
finite compact cover whose pieces inherit a containing cell label from the coarse fan. This is the
compact local-patch decomposition used to pass projected tile seams into the faithful fan stage. -/
theorem compactSet_fanRefinement_patchCover [CompleteSpace E]
    (K : Set E) (hK : IsCompact K) {F' F : Fan E}
    (href : Refines F' F) (hF' : IsPolyhedralFan F') :
    (∀ C ∈ F', IsCompact (K ∩ (C : Set E))) ∧
      K = ⋃ C ∈ F', K ∩ (C : Set E) ∧
      (∀ C ∈ F', ∃ D ∈ F, (K ∩ (C : Set E)) ⊆ (D : Set E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    exact hK.inter_right C.isClosed
  · ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ C ∈ F', (C : Set E) := by
        rw [hF'.covers]
        simp
      rcases Set.mem_iUnion.mp hxcover with ⟨C, hxC⟩
      rcases Set.mem_iUnion.mp hxC with ⟨hC, hxCmem⟩
      exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC, ⟨hx, hxCmem⟩⟩⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨C, hxC⟩
      rcases Set.mem_iUnion.mp hxC with ⟨_, hxPatch⟩
      exact hxPatch.1
  · intro C hC
    obtain ⟨D, hD, hsubset⟩ := href C hC
    exact ⟨D, hD, fun x hx => hsubset hx.2⟩

/-- Two compact pieces cut from a polyhedral fan refinement overlap in the patch cut from their
common fan face. This records exact overlap compatibility for the finite chamber-labeled cover. -/
theorem compactSet_fanRefinement_patch_intersection [CompleteSpace E]
    (K : Set E) {F : Fan E} (hF : IsPolyhedralFan F)
    (C D : ProperCone ℝ E) (hC : C ∈ F) (hD : D ∈ F) :
    ∃ G ∈ F,
      (K ∩ (C : Set E)) ∩ (K ∩ (D : Set E)) = K ∩ (G : Set E) := by
  obtain ⟨G, hG, hcommon⟩ := hF.inter_common C hC D hD
  refine ⟨G, hG, ?_⟩
  rw [hcommon]
  ext x
  simp [and_assoc, and_left_comm]

/-- The finite family of closed-cone images of a fan under a continuous linear map. Since the
proper-cone image operation takes closure, this family need not itself satisfy the fan axioms. -/
noncomputable def linearImageFamily {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (f : E →L[ℝ] F) [CompleteSpace E]
    (G : Fan E) : Fan F := by
  classical
  exact G.image (fun C => ProperCone.map f C)

/-- A surjective linear map sends the complete family of a covering fan to a family that covers
the target. This is the coverage part of projection; face-to-face intersection structure still
requires a separate refinement argument. -/
theorem linearImageFamily_covers_of_surjective {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [CompleteSpace E]
    {G : Fan E} (hG : IsPolyhedralFan G) (f : E →L[ℝ] F)
    (hf : Function.Surjective f) :
    (⋃ C ∈ linearImageFamily f G, (C : Set F)) = Set.univ := by
  classical
  ext y
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨x, rfl⟩ := hf y
    have hxcover : x ∈ ⋃ C ∈ G, (C : Set E) := by
      rw [hG.covers]
      simp
    rcases Set.mem_iUnion.mp hxcover with ⟨C, hC⟩
    rcases Set.mem_iUnion.mp hC with ⟨hCG, hxC⟩
    have hfxC : f x ∈ ProperCone.map f C := by
      rw [ProperCone.mem_map]
      change f x ∈ closure (f '' (C : Set E))
      exact subset_closure ⟨x, hxC, rfl⟩
    refine Set.mem_iUnion.mpr ⟨ProperCone.map f C, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hfxC⟩
    change ProperCone.map f C ∈ G.image (fun C => ProperCone.map f C)
    exact Finset.mem_image.mpr ⟨C, hCG, rfl⟩

/-- The family of all final-coordinate deletions of a complete Euclidean coordinate fan covers the
lower coordinate space. This supplies the coverage clause before refining the projected cone family
into a fan. -/
theorem linearImageFamily_forgetLastEuclidean_covers {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G) :
    (⋃ C ∈ linearImageFamily (forgetLastEuclidean n) G,
      (C : Set (EuclideanSpace ℝ (Fin n)))) = Set.univ :=
  linearImageFamily_covers_of_surjective hG _
    (forgetLastEuclidean_surjective n)

/-- The closed-cone image of a finite-generated cone equals the cone generated by the images of
its finite generators. In particular, the closure in `ProperCone.map` adds no extra points here. -/
theorem properCone_map_eq_finiteConeImage {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [DecidableEq F]
    (f : E →L[ℝ] F) [CompleteSpace E] (S : Finset E) :
    ProperCone.map f (properConeOfFinset S) =
      properConeOfFinset (S.image (f : E →ₗ[ℝ] F)) := by
  classical
  apply ProperCone.ext
  intro y
  rw [ProperCone.mem_map]
  change y ∈ closure ((f : E →ₗ[ℝ] F) ''
    (properConeOfFinset S : Set E)) ↔
      y ∈ (properConeOfFinset (S.image (f : E →ₗ[ℝ] F)) : Set F)
  rw [linearMap_image_properConeOfFinset (f : E →ₗ[ℝ] F) S,
    (properConeOfFinset (S.image (f : E →ₗ[ℝ] F))).isClosed.closure_eq]

/-- The finite family of pairwise intersections of two cone families. Each cell lies in a cell
of either input family. This is only the cell data for a common refinement: proving exposed-face
closure is still necessary before it can be called a polyhedral fan. -/
noncomputable def intersectionFamily [CompleteSpace E] (F G : Fan E) : Fan E := by
  classical
  exact (F.product G).image (fun p : ProperCone ℝ E × ProperCone ℝ E => p.1 ⊓ p.2)

/-- Every cell in the pairwise intersection family is contained in a cell of the left family. -/
theorem intersectionFamily_refines_left [CompleteSpace E] {F G : Fan E} :
    Refines (intersectionFamily F G) F := by
  classical
  intro C' hC'
  rcases Finset.mem_image.mp hC' with ⟨⟨C, D⟩, hp, hEq⟩
  rcases Finset.mem_product.mp hp with ⟨hC, hD⟩
  subst C'
  exact ⟨C, hC, inf_le_left⟩

/-- Every cell in the pairwise intersection family is contained in a cell of the right family. -/
theorem intersectionFamily_refines_right [CompleteSpace E] {F G : Fan E} :
    Refines (intersectionFamily F G) G := by
  classical
  intro C' hC'
  rcases Finset.mem_image.mp hC' with ⟨⟨C, D⟩, hp, hEq⟩
  rcases Finset.mem_product.mp hp with ⟨hC, hD⟩
  subst C'
  exact ⟨D, hD, inf_le_right⟩

/-- Pairwise intersections of two polyhedral fans cover the ambient space. -/
theorem intersectionFamily_covers [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G) :
    (⋃ C ∈ intersectionFamily F G, (C : Set E)) = Set.univ := by
  classical
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxF : ∃ C ∈ F, x ∈ (C : Set E) := by
      have hx := congrArg (fun s : Set E => x ∈ s) hF.covers
      simpa using hx
    have hxG : ∃ D ∈ G, x ∈ (D : Set E) := by
      have hx := congrArg (fun s : Set E => x ∈ s) hG.covers
      simpa using hx
    rcases hxF with ⟨C, hC, hxC⟩
    rcases hxG with ⟨D, hD, hxD⟩
    refine Set.mem_iUnion.mpr ⟨C ⊓ D, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨(C, D), Finset.mem_product.mpr ⟨hC, hD⟩, rfl⟩
    · simpa using And.intro hxC hxD

/-- The pairwise intersection family satisfies the common-intersection axiom when both inputs
do. Exposed-face closure, the remaining polyhedral-fan axiom, is not provided by these data. -/
theorem intersectionFamily_inter_common [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G) :
    ∀ C ∈ intersectionFamily F G, ∀ D ∈ intersectionFamily F G,
      ∃ H ∈ intersectionFamily F G, (H : Set E) = (C : Set E) ∩ (D : Set E) := by
  classical
  intro C hC D hD
  rcases Finset.mem_image.mp hC with ⟨⟨C₁, D₁⟩, hpair₁, rfl⟩
  rcases Finset.mem_product.mp hpair₁ with ⟨hC₁, hD₁⟩
  rcases Finset.mem_image.mp hD with ⟨⟨C₂, D₂⟩, hpair₂, rfl⟩
  rcases Finset.mem_product.mp hpair₂ with ⟨hC₂, hD₂⟩
  obtain ⟨C₃, hC₃, hmeetC⟩ := hF.inter_common C₁ hC₁ C₂ hC₂
  obtain ⟨D₃, hD₃, hmeetD⟩ := hG.inter_common D₁ hD₁ D₂ hD₂
  refine ⟨C₃ ⊓ D₃, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(C₃, D₃), Finset.mem_product.mpr ⟨hC₃, hD₃⟩, rfl⟩
  · ext x
    simp [hmeetC, hmeetD]
    tauto


/-- Closed-cone version of a supporting hyperplane. -/
noncomputable def properSupportingHyperplane (a : E) : ProperCone ℝ E where
  toSubmodule := Submodule.restrictScalars (Nonneg ℝ) (LinearMap.ker (innerₗ E a))
  isClosed' := by
    change IsClosed {x : E | ⟪a, x⟫_ℝ = 0}
    exact isClosed_singleton.preimage (continuous_const.inner continuous_id)

@[simp] theorem mem_properSupportingHyperplane {a x : E} :
    x ∈ properSupportingHyperplane a ↔ ⟪a, x⟫_ℝ = 0 := by
  change x ∈ (LinearMap.ker (innerₗ E a) : Submodule ℝ E) ↔ _
  simp [LinearMap.mem_ker, innerₗ_apply_apply]

/-- A supporting hyperplane is the intersection of the two half-spaces with opposite normals,
so it has a finite half-space representation. -/
theorem properSupportingHyperplane_hasDualFG [CompleteSpace E] (a : E) :
    (properSupportingHyperplane a : PointedCone ℝ E).DualFG (innerₗ E) := by
  classical
  let S : Finset E := {a, -a}
  have hS : (coneDual (S : Set E) : PointedCone ℝ E).DualFG (innerₗ E) := by
    change (PointedCone.dual (innerₗ E) (S : Set E)).DualFG (innerₗ E)
    exact PointedCone.DualFG.dual_of_finset (innerₗ E) S
  have hEq : properSupportingHyperplane a = coneDual (S : Set E) := by
    apply ProperCone.ext
    intro x
    simp [S, mem_properSupportingHyperplane]
    constructor
    · intro hx
      rw [hx]
      exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨hpos, hneg⟩
      exact le_antisymm hneg hpos
  rw [hEq]
  exact hS

/-- Exposed face represented as a closed cone, for use in the closed-cone fan family. -/
noncomputable def properExposedFace (C : ProperCone ℝ E) (a : E) : ProperCone ℝ E :=
  C ⊓ properSupportingHyperplane a

@[simp] theorem mem_properExposedFace {C : ProperCone ℝ E} {a x : E} :
    x ∈ properExposedFace C a ↔ x ∈ C ∧ ⟪a, x⟫_ℝ = 0 := by
  simp [properExposedFace]

/-- Taking an exposed face preserves finite half-space representability: it adds the two
inequalities for the exposing hyperplane to the existing finite description. -/
theorem properExposedFace_hasDualFG [CompleteSpace E] {C : ProperCone ℝ E} {a : E}
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (properExposedFace C a : PointedCone ℝ E).DualFG (innerₗ E) := by
  change ((C : PointedCone ℝ E) ⊓
    (properSupportingHyperplane a : PointedCone ℝ E)).DualFG (innerₗ E)
  exact hC.inf (properSupportingHyperplane_hasDualFG a)

/-- A closed exposed face belongs to its input fan. -/
theorem properExposedFace_isExposedFaceOf [CompleteSpace E] {C : ProperCone ℝ E} {a : E}
    (ha : a ∈ coneDual (C : Set E)) : IsExposedFaceOf (properExposedFace C a) C := by
  refine ⟨a, ha, ?_⟩
  ext x
  simp [properExposedFace, properSupportingHyperplane, mem_exposedFace,
    LinearMap.mem_ker, innerₗ_apply_apply]

/-- The rank used to order Craciun's face-filling tasks is the dimension of the linear span
of a cone. -/
noncomputable def coneSpanRank (C : ProperCone ℝ E) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (C : Set E))

/-- A proper exposed face has strictly smaller span dimension than its containing cone. This is
the geometric decrease needed for the lexicographic face recursion: it is proved from the actual
exposing functional, not assumed as a property of an abstract dependency relation. -/
theorem coneSpanRank_lt_of_isExposedFaceOf_of_ne [CompleteSpace E]
    [FiniteDimensional ℝ E] {D C : ProperCone ℝ E}
    (hface : IsExposedFaceOf D C) (hne : D ≠ C) :
    coneSpanRank D < coneSpanRank C := by
  obtain ⟨a, ha, hfaceSet⟩ := hface
  have hfaceSet' : (D : Set E) = (exposedFace (C : PointedCone ℝ E) a : Set E) := by
    ext x
    have hmem := congrArg (fun A : Set E => x ∈ A) hfaceSet
    simpa using hmem
  have hsubset : (D : Set E) ⊆ (C : Set E) := by
    intro x hx
    have hface' : x ∈ exposedFace (C : PointedCone ℝ E) a := by
      change x ∈ (exposedFace (C : PointedCone ℝ E) a : Set E)
      rw [← hfaceSet']
      exact hx
    exact (mem_exposedFace.mp hface').1
  have hnotSubset : ¬ (C : Set E) ⊆ (D : Set E) := by
    intro hCD
    apply hne
    exact SetLike.coe_injective (Set.Subset.antisymm hsubset hCD)
  obtain ⟨x, hxC, hxD⟩ := Set.not_subset.mp hnotSubset
  let φ : E →ₗ[ℝ] ℝ := innerₗ E a
  have hspanKernel :
      Submodule.span ℝ (D : Set E) ≤ LinearMap.ker φ := by
    apply Submodule.span_le.2
    intro y hy
    apply LinearMap.mem_ker.mpr
    have hyFace : y ∈ exposedFace (C : PointedCone ℝ E) a := by
      change y ∈ (exposedFace (C : PointedCone ℝ E) a : Set E)
      rw [← hfaceSet']
      exact hy
    simpa [φ, innerₗ_apply_apply] using (mem_exposedFace.mp hyFace).2
  have hxNotKernel : φ x ≠ 0 := by
    intro hxKernel
    have hxFace : x ∈ exposedFace (C : PointedCone ℝ E) a :=
      (mem_exposedFace).2 ⟨hxC, by
        simpa [φ, innerₗ_apply_apply] using hxKernel⟩
    have hxD' : x ∈ D := by
      change x ∈ (D : Set E)
      rw [hfaceSet']
      exact hxFace
    exact hxD hxD'
  let SD : Submodule ℝ E := Submodule.span ℝ (D : Set E)
  let SC : Submodule ℝ E := Submodule.span ℝ (C : Set E)
  have hSDleSC : SD ≤ SC := Submodule.span_mono hsubset
  have hSDneSC : SD ≠ SC := by
    intro hEq
    have hxSD : x ∈ SD := by
      rw [hEq]
      exact Submodule.subset_span hxC
    exact hxNotKernel (hspanKernel hxSD)
  have hSDltSC : SD < SC := lt_of_le_of_ne hSDleSC hSDneSC
  simpa [coneSpanRank, SD, SC] using Submodule.finrank_lt_finrank_of_lt hSDltSC

/-- A face dependency points from the face being filled to a strictly lower-dimensional exposed
face whose data it needs. The relation is well-founded because every dependency lowers the span
rank. -/
def ProperExposedFaceDependency [CompleteSpace E]
    (required face : ProperCone ℝ E) : Prop :=
  IsExposedFaceOf required face ∧ required ≠ face

/-- The one-bit fiber cell attached to a fan cell during Craciun's face filling. A strip has one
additional geometric dimension over its projected fan cell; an endpoint graph has none. -/
inductive OneBitFiberCell (m : ℕ)
  | strip : Fin (m + 1) → OneBitFiberCell m
  | endpoint : Fin (m + 2) → OneBitFiberCell m

/-- A face-filling task identifies its fan cell, projected small-tile label, and one-bit strip or
endpoint seam. The label is kept separate from the fan cell so proper-face dependencies retain the
same projected tile while replacing the cell by its actual common face. -/
abbrev OneBitFanFaceTask (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type*) (m : ℕ) := (ProperCone ℝ E × ι) × OneBitFiberCell m

/-- Geometric dimension for the one-bit face recursion: the span rank of the fan cell, plus one
for an interval strip and zero for an endpoint face. -/
noncomputable def oneBitFanFaceTaskRank [CompleteSpace E] {m : ℕ}
    {ι : Type*} (task : OneBitFanFaceTask E ι m) : ℕ :=
  coneSpanRank task.1.1 + (match task.2 with
    | .strip _ => 1
    | .endpoint _ => 0)

/-- A fan-face or fiber-endpoint dependency points from a required lower-dimensional task to the
strip or endpoint task whose boundary uses it. -/
inductive OneBitFanFaceDependency [CompleteSpace E] {ι : Type*} {m : ℕ} :
    OneBitFanFaceTask E ι m → OneBitFanFaceTask E ι m → Prop
  | fanFace (C G : ProperCone ℝ E) (k : ι) (i : Fin (m + 1))
      (hface : IsExposedFaceOf G C) (hne : G ≠ C) :
      OneBitFanFaceDependency ((G, k), .strip i) ((C, k), .strip i)
  | fanFaceEndpoint (C G : ProperCone ℝ E) (k : ι) (j : Fin (m + 2))
      (hface : IsExposedFaceOf G C) (hne : G ≠ C) :
      OneBitFanFaceDependency ((G, k), .endpoint j) ((C, k), .endpoint j)
  | fiberEndpoint (C G : ProperCone ℝ E) (k : ι) (i : Fin (m + 1))
      (j : Fin (m + 2))
      (hface : IsExposedFaceOf G C)
      (hadjacent : j = i.castSucc ∨ j = i.succ) :
      OneBitFanFaceDependency ((G, k), .endpoint j) ((C, k), .strip i)

/-- The geometric output attached to a one-bit fan-face task: a strip task returns the face patch
inside that projected tile and fiber strip, while an endpoint task returns the face patch on the
corresponding endpoint graph. -/
def oneBitFanFaceTaskPatch {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ))
    (baseTile : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι → Set (Fin n → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (task : OneBitFanFaceTask (EuclideanSpace ℝ (Fin n)) ι m) :
    Set (Fin (n + 1) → ℝ) :=
  match task.2 with
  | .strip i =>
      facePatch ∩ projectionFiberSubdivisionTile (baseTile task.1) lower upper i
  | .endpoint j =>
      facePatch ∩ (projectionFiberSubdivisionEndpointGraphPoint lower upper j) ''
        baseTile task.1

/-- Proper exposed-face tasks carry nested geometric outputs whenever their projected tiles are
nested. This is the patch-level invariant needed by a recursive face filler: all inherited strip
or endpoint data actually lie in the parent task's patch. -/
theorem oneBitFanFaceTaskPatch_mono_of_commonFace {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ))
    (baseTile : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι → Set (Fin n → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (hbaseTile : ∀ {G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))},
      IsExposedFaceOf G C → ∀ k, baseTile (G, k) ⊆ baseTile (C, k))
    (G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (k : ι)
    (hface : IsExposedFaceOf G C) (cell : OneBitFiberCell m) :
    oneBitFanFaceTaskPatch facePatch baseTile lower upper ((G, k), cell) ⊆
      oneBitFanFaceTaskPatch facePatch baseTile lower upper ((C, k), cell) := by
  cases cell with
  | strip i =>
      intro x hx
      exact ⟨hx.1, projectionFiberSubdivisionTile_mono (hbaseTile hface k)
        lower upper i hx.2⟩
  | endpoint j =>
      intro x hx
      exact ⟨hx.1, Set.image_mono (hbaseTile hface k) hx.2⟩

/-- The combined fan-cell/one-bit-face dependency order is well-founded. Fan-face steps lower the
cone span rank; endpoint steps lower the one-bit fiber dimension, including when the fan cell is
unchanged. -/
theorem oneBitFanFaceDependency_wellFounded [CompleteSpace E] [FiniteDimensional ℝ E]
    {ι : Type*} {m : ℕ} :
    WellFounded (OneBitFanFaceDependency (E := E) (ι := ι) (m := m)) := by
  have hmeasure : WellFounded (fun a b : OneBitFanFaceTask E ι m =>
      oneBitFanFaceTaskRank a < oneBitFanFaceTaskRank b) :=
    InvImage.wf oneBitFanFaceTaskRank (Nat.lt_wfRel).2
  apply hmeasure.mono
  intro a b hab
  cases hab with
  | fanFace C G k i hface hne =>
      simp [oneBitFanFaceTaskRank]
      exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
  | fanFaceEndpoint C G k j hface hne =>
      simp [oneBitFanFaceTaskRank]
      exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
  | fiberEndpoint C G k i j hface hadjacent =>
      have hrank : coneSpanRank G ≤ coneSpanRank C := by
        by_cases hGC : G = C
        · subst G
          exact le_rfl
        · exact (coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC).le
      simp [oneBitFanFaceTaskRank]
      omega

/-- Construct data for every one-bit fan-face task by the same well-founded order. Unlike
`oneBitFanFaceDependency_induction`, this recursion is `Sort`-valued and therefore returns the
filled patch, barrier, or seam object itself from the already-constructed predecessor data. -/
noncomputable def oneBitFanFaceDependency_recursion [CompleteSpace E]
    [FiniteDimensional ℝ E] {ι : Type*} {m : ℕ}
    {P : OneBitFanFaceTask E ι m → Sort v}
    (step : ∀ task, (∀ predecessor,
      OneBitFanFaceDependency (E := E) (ι := ι) (m := m) predecessor task → P predecessor) → P task) :
    ∀ task, P task :=
  (oneBitFanFaceDependency_wellFounded (E := E) (ι := ι) (m := m)).fix step

/-- Mixed-label recursion for the actual product atlas. Ordinary face tasks use a single small-tile
label; a shared seam uses a pair label and is a predecessor of each incident single-label strip. -/
inductive OneBitFanFaceSeamDependency [CompleteSpace E] {ι : Type*} {m : ℕ} :
    OneBitFanFaceTask E (Sum ι (ι × ι)) m →
      OneBitFanFaceTask E (Sum ι (ι × ι)) m → Prop
  | inherited {a b : OneBitFanFaceTask E (Sum ι (ι × ι)) m}
      (hdep : OneBitFanFaceDependency (E := E) (ι := Sum ι (ι × ι)) (m := m) a b) :
      OneBitFanFaceSeamDependency a b
  | productSeamLeft (C G : ProperCone ℝ E) (i j : ι)
      (k : Fin (m + 1)) (endpoint : Fin (m + 2))
      (hface : IsExposedFaceOf G C)
      (hadjacent : endpoint = k.castSucc ∨ endpoint = k.succ) :
      OneBitFanFaceSeamDependency
        ((G, Sum.inr (i, j)), .endpoint endpoint)
        ((C, Sum.inl i), .strip k)
  | productSeamRight (C G : ProperCone ℝ E) (i j : ι)
      (k : Fin (m + 1)) (endpoint : Fin (m + 2))
      (hface : IsExposedFaceOf G C)
      (hadjacent : endpoint = k.castSucc ∨ endpoint = k.succ) :
      OneBitFanFaceSeamDependency
        ((G, Sum.inr (i, j)), .endpoint endpoint)
        ((C, Sum.inl j), .strip k)

/-- The inherited fan/endpoint dependencies together with pair-labelled product seams remain
well-founded under the same geometric rank: an endpoint graph has lower fiber rank than either
incident strip, and an exposed-face step never increases cone rank. -/
theorem oneBitFanFaceSeamDependency_wellFounded [CompleteSpace E]
    [FiniteDimensional ℝ E] {ι : Type*} {m : ℕ} :
    WellFounded (OneBitFanFaceSeamDependency (E := E) (ι := ι) (m := m)) := by
  have hmeasure : WellFounded (fun a b : OneBitFanFaceTask E (Sum ι (ι × ι)) m =>
      oneBitFanFaceTaskRank a < oneBitFanFaceTaskRank b) :=
    InvImage.wf oneBitFanFaceTaskRank (Nat.lt_wfRel).2
  apply hmeasure.mono
  intro a b hab
  cases hab with
  | inherited hdep =>
      cases hdep with
      | fanFace C G k i hface hne =>
          simp [oneBitFanFaceTaskRank]
          exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
      | fanFaceEndpoint C G k j hface hne =>
          simp [oneBitFanFaceTaskRank]
          exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
      | fiberEndpoint C G k i j hface hadjacent =>
          have hrank : coneSpanRank G ≤ coneSpanRank C := by
            by_cases hGC : G = C
            · subst G
              exact le_rfl
            · exact (coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC).le
          simp [oneBitFanFaceTaskRank]
          omega
  | productSeamLeft C G i j k endpoint hface hadjacent =>
      by_cases hGC : G = C
      · subst G
        simp [oneBitFanFaceTaskRank]
      · simp [oneBitFanFaceTaskRank]
        have hlt := coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC
        omega
  | productSeamRight C G i j k endpoint hface hadjacent =>
      by_cases hGC : G = C
      · subst G
        simp [oneBitFanFaceTaskRank]
      · simp [oneBitFanFaceTaskRank]
        have hlt := coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC
        omega

/-- Sort-valued recursion on the mixed-label dependency order, so each seam and strip task can
return geometric data constructed from all of its completed predecessors. -/
noncomputable def oneBitFanFaceSeamDependency_recursion [CompleteSpace E]
    [FiniteDimensional ℝ E] {ι : Type*} {m : ℕ}
    {P : OneBitFanFaceTask E (Sum ι (ι × ι)) m → Sort v}
    (step : ∀ task, (∀ predecessor,
      OneBitFanFaceSeamDependency (E := E) (ι := ι) (m := m) predecessor task →
        P predecessor) → P task) :
    ∀ task, P task :=
  (oneBitFanFaceSeamDependency_wellFounded (E := E) (ι := ι) (m := m)).fix step

/-- Prop-valued induction for the combined fan-cell/fiber-cell dependency. For constructions that
must return actual patch data rather than only a proposition, use
`oneBitFanFaceDependency_recursion`. -/
theorem oneBitFanFaceDependency_induction [CompleteSpace E] [FiniteDimensional ℝ E]
    {ι : Type*} {m : ℕ} {P : OneBitFanFaceTask E ι m → Prop}
    (step : ∀ task, (∀ predecessor,
      OneBitFanFaceDependency (E := E) (ι := ι) (m := m) predecessor task → P predecessor) → P task) :
    ∀ task, P task := by
  intro task
  exact oneBitFanFaceDependency_recursion step task

theorem properExposedFaceDependency_wellFounded [CompleteSpace E]
    [FiniteDimensional ℝ E] :
    WellFounded (ProperExposedFaceDependency (E := E)) := by
  have hacc : ∀ n : ℕ, ∀ C : ProperCone ℝ E,
      coneSpanRank C = n → Acc (ProperExposedFaceDependency (E := E)) C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro C hC
        apply Acc.intro
        intro D hdep
        have hdecrease : coneSpanRank D < n := by
          rw [← hC]
          exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hdep.1 hdep.2
        exact ih (coneSpanRank D) hdecrease D rfl
  exact ⟨fun C => hacc (coneSpanRank C) C rfl⟩

/-- Dual decomposition condition needed to prove exposed-face closure for pairwise intersections. -/
def HasIntersectionDualDecomposition [CompleteSpace E] (F G : Fan E) : Prop :=
  ∀ C ∈ F, ∀ D ∈ G, ∀ a : E,
    a ∈ coneDual ((C : Set E) ∩ (D : Set E)) →
      ∃ b c : E, a = b + c ∧ b ∈ coneDual (C : Set E) ∧ c ∈ coneDual (D : Set E)

/-- If dual vectors of each cell intersection split between input dual cones, then the
pairwise-intersection family is closed under exposed faces. -/
theorem intersectionFamily_faces_mem [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hdual : HasIntersectionDualDecomposition F G) :
    ∀ C' ∈ intersectionFamily F G, ∀ H : ProperCone ℝ E,
      IsExposedFaceOf H C' → H ∈ intersectionFamily F G := by
  classical
  intro K hK H hHK
  rcases Finset.mem_image.mp hK with ⟨⟨C, D⟩, hpair, rfl⟩
  rcases Finset.mem_product.mp hpair with ⟨hC, hD⟩
  rcases hHK with ⟨a, ha, hset⟩
  have ha' : a ∈ coneDual ((C : Set E) ∩ (D : Set E)) := by
    rw [mem_coneDual]
    rw [mem_coneDual] at ha
    intro x hx
    have hx' : x ∈ (C ⊓ D : ProperCone ℝ E) := by simpa using hx
    exact ha hx'
  obtain ⟨b, c, hab, hb, hc⟩ := hdual C hC D hD a ha'
  let C' := properExposedFace C b
  let D' := properExposedFace D c
  have hC' : C' ∈ F := hF.faces_mem C hC C' (properExposedFace_isExposedFaceOf hb)
  have hD' : D' ∈ G := hG.faces_mem D hD D' (properExposedFace_isExposedFaceOf hc)
  have hcell : C' ⊓ D' ∈ intersectionFamily F G := by
    apply Finset.mem_image.mpr
    exact ⟨(C', D'), Finset.mem_product.mpr ⟨hC', hD'⟩, rfl⟩
  have hset' : ((H : PointedCone ℝ E) : Set E) =
      ((C' ⊓ D' : ProperCone ℝ E) : PointedCone ℝ E) := by
    rw [hset]
    ext x
    change ((x ∈ C ∧ x ∈ D) ∧ ⟪a, x⟫_ℝ = 0) ↔
      ((x ∈ C ∧ ⟪b, x⟫_ℝ = 0) ∧ x ∈ D ∧ ⟪c, x⟫_ℝ = 0)
    have hinner : ⟪a, x⟫_ℝ = ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ := by
      calc
        ⟪a, x⟫_ℝ = ⟪b + c, x⟫_ℝ := by rw [hab]
        _ = ⟪x, b + c⟫_ℝ := real_inner_comm _ _
        _ = ⟪x, b⟫_ℝ + ⟪x, c⟫_ℝ := inner_add_right (𝕜 := ℝ) x b c
        _ = ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ := by rw [real_inner_comm x b, real_inner_comm x c]
    constructor
    · rintro ⟨⟨hxC, hxD⟩, hzero⟩
      have hbn := inner_nonneg_of_mem_coneDual hb hxC
      have hcn := inner_nonneg_of_mem_coneDual hc hxD
      have hsum : ⟪b, x⟫_ℝ + ⟪c, x⟫_ℝ = 0 := by rw [← hinner, hzero]
      have hbzero : ⟪b, x⟫_ℝ = 0 := by nlinarith
      have hczero : ⟪c, x⟫_ℝ = 0 := by nlinarith
      exact ⟨⟨hxC, hbzero⟩, hxD, hczero⟩
    · rintro ⟨⟨hxC, hbzero⟩, hxD, hczero⟩
      refine ⟨⟨hxC, hxD⟩, ?_⟩
      rw [hinner, hbzero, hczero]
      ring
  have hpc : (H : PointedCone ℝ E) =
      (C' ⊓ D' : ProperCone ℝ E) := SetLike.coe_injective hset'
  have hcone : H = C' ⊓ D' := ProperCone.toPointedCone_injective hpc
  rw [hcone]
  exact hcell

/-- Pairwise intersections form a polyhedral fan once the dual-decomposition condition holds. -/
theorem intersectionFamily_isPolyhedralFan [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hdual : HasIntersectionDualDecomposition F G) :
    IsPolyhedralFan (intersectionFamily F G) :=
  ⟨intersectionFamily_faces_mem hF hG hdual,
    intersectionFamily_inter_common hF hG,
    intersectionFamily_covers hF hG⟩


/-- The dual of a finitely generated cone is the dual of its generators. -/
theorem coneDual_hull_eq [CompleteSpace E] (T : Finset E) :
    (coneDual (PointedCone.hull ℝ (T : Set E) : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (T : Set E) : Set E) := by
  ext x
  change x ∈ coneDual (PointedCone.hull ℝ (T : Set E) : Set E) ↔
    x ∈ PointedCone.dual (innerₗ E) (T : Set E)
  rw [mem_coneDual]
  change (∀ ⦃y⦄, y ∈ PointedCone.hull ℝ (T : Set E) → 0 ≤ ⟪y, x⟫_ℝ) ↔
    x ∈ PointedCone.dual (innerₗ E) (T : Set E)
  rw [PointedCone.mem_dual]
  constructor
  · intro h y hy
    exact h (PointedCone.subset_hull hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h hy
    | zero => simp
    | add y z _ _ hy hz =>
        rw [inner_add_left (𝕜 := ℝ)]
        exact add_nonneg hy hz
    | smul c y _ hy =>
        rw [← Nonneg.coe_smul, real_inner_smul_left]
        exact mul_nonneg c.2 hy

/-- The dual of the finite half-space cone with normals `S` is exactly the conical hull of those
normals. This finite Farkas representation is the face-closure input for hyperplane arrangements. -/
theorem coneDual_finset_dual_eq [CompleteSpace E] (S : Finset E) :
    coneDual (coneDual (S : Set E) : Set E) = properConeOfFinset S := by
  have hHull : (properConeOfFinset S : Set E) =
      (PointedCone.hull ℝ (S : Set E) : Set E) := by
    simp [coe_properConeOfFinset]
  have hDualSet : (coneDual (properConeOfFinset S : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (S : Set E) : Set E) := by
    rw [hHull]
    exact coneDual_hull_eq S
  have hDual : coneDual (properConeOfFinset S : Set E) = coneDual (S : Set E) := by
    apply ProperCone.ext
    intro x
    change x ∈ (coneDual (properConeOfFinset S : Set E) : Set E) ↔
      x ∈ (coneDual (S : Set E) : Set E)
    rw [hDualSet]
    rfl
  rw [← hDual]
  exact cone_dual_dual (properConeOfFinset S)

/-- For dual-finitely-generated cones, every dual vector of an intersection splits as a sum
of dual vectors of the two cones. -/
theorem coneDual_intersection_decomp_of_dualFG [CompleteSpace E] {C D : ProperCone ℝ E}
    (hCfin : (C : PointedCone ℝ E).DualFG (innerₗ E))
    (hDfin : (D : PointedCone ℝ E).DualFG (innerₗ E))
    {a : E} (ha : a ∈ coneDual ((C : Set E) ∩ (D : Set E))) :
    ∃ b c : E, a = b + c ∧ b ∈ coneDual (C : Set E) ∧ c ∈ coneDual (D : Set E) := by
  classical
  obtain ⟨S, hCfin⟩ := hCfin
  obtain ⟨T, hDfin⟩ := hDfin
  let A : ProperCone ℝ E := properConeOfFinset S
  let B : ProperCone ℝ E := properConeOfFinset T
  let U : ProperCone ℝ E := properConeOfFinset (S ∪ T)
  have hAco : (A : Set E) = (PointedCone.hull ℝ (S : Set E) : Set E) := by
    simpa [A] using coe_properConeOfFinset S
  have hBco : (B : Set E) = (PointedCone.hull ℝ (T : Set E) : Set E) := by
    simpa [B] using coe_properConeOfFinset T
  have hUco : (U : Set E) = (PointedCone.hull ℝ (S ∪ T : Set E) : Set E) := by
    simpa [U] using coe_properConeOfFinset (S ∪ T)
  have hAdualSet : (coneDual (A : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (S : Set E) : Set E) := by
    rw [hAco]
    exact coneDual_hull_eq S
  have hBdualSet : (coneDual (B : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) (T : Set E) : Set E) := by
    rw [hBco]
    exact coneDual_hull_eq T
  have hUdualSet : (coneDual (U : Set E) : Set E) =
      (PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E) : Set E) := by
    rw [hUco]
    simpa only [Finset.coe_union] using coneDual_hull_eq (S ∪ T)
  have hAdual : (coneDual (A : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) (S : Set E) := SetLike.coe_injective hAdualSet
  have hBdual : (coneDual (B : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) (T : Set E) := SetLike.coe_injective hBdualSet
  have hUdual : (coneDual (U : Set E) : PointedCone ℝ E) =
      PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E) := SetLike.coe_injective hUdualSet
  have hCset : (C : Set E) = (coneDual (A : Set E) : Set E) := by
    ext x
    change x ∈ (C : PointedCone ℝ E) ↔
      x ∈ (coneDual (A : Set E) : PointedCone ℝ E)
    rw [← hCfin, hAdual]
  have hDset : (D : Set E) = (coneDual (B : Set E) : Set E) := by
    ext x
    change x ∈ (D : PointedCone ℝ E) ↔
      x ∈ (coneDual (B : Set E) : PointedCone ℝ E)
    rw [← hDfin, hBdual]
  have hCdualSet : (coneDual (C : Set E) : Set E) = (A : Set E) := by
    calc
      (coneDual (C : Set E) : Set E) =
          (coneDual (coneDual (A : Set E) : Set E) : Set E) := by rw [hCset]
      _ = (A : Set E) := congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual A)
  have hDdualSet : (coneDual (D : Set E) : Set E) = (B : Set E) := by
    calc
      (coneDual (D : Set E) : Set E) =
          (coneDual (coneDual (B : Set E) : Set E) : Set E) := by rw [hDset]
      _ = (B : Set E) := congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual B)
  have hKset : (C : Set E) ∩ (D : Set E) = (coneDual (U : Set E) : Set E) := by
    ext x
    rw [hCset, hDset, hAdualSet, hBdualSet, hUdualSet]
    change (x ∈ PointedCone.dual (innerₗ E) (S : Set E) ∧
      x ∈ PointedCone.dual (innerₗ E) (T : Set E)) ↔
      x ∈ PointedCone.dual (innerₗ E) ((S ∪ T : Finset E) : Set E)
    rw [show ((S ∪ T : Finset E) : Set E) = (S : Set E) ∪ (T : Set E) by simp]
    rw [PointedCone.dual_union]
    simp
  have hKinf : (C ⊓ D : ProperCone ℝ E) = coneDual (U : Set E) := by
    apply ProperCone.ext
    intro x
    have hmem : x ∈ (C ⊓ D : ProperCone ℝ E) ↔ x ∈ coneDual (U : Set E) := by
      change (x ∈ (C : Set E) ∧ x ∈ (D : Set E)) ↔
        x ∈ (coneDual (U : Set E) : Set E)
      exact Iff.of_eq (congrArg (fun s : Set E => x ∈ s) hKset)
    exact hmem
  have hKdual : (coneDual ((C : Set E) ∩ (D : Set E)) : Set E) = (U : Set E) := by
    have hInfSet : (C ⊓ D : ProperCone ℝ E) = (C : Set E) ∩ (D : Set E) := by
      ext x
      simp
    rw [← hInfSet, hKinf]
    exact congrArg (fun K : ProperCone ℝ E => (K : Set E)) (cone_dual_dual U)
  have haU : a ∈ (U : Set E) := by
    rw [← hKdual]
    exact ha
  have hUsup : (U : PointedCone ℝ E) =
      (A : PointedCone ℝ E) ⊔ (B : PointedCone ℝ E) := by
    apply PointedCone.ext
    intro x
    change x ∈ Submodule.span (Nonneg ℝ) ((S ∪ T : Finset E) : Set E) ↔
      x ∈ Submodule.span (Nonneg ℝ) (S : Set E) ⊔
        Submodule.span (Nonneg ℝ) (T : Set E)
    rw [Finset.coe_union, Submodule.span_union]
  have haSup : a ∈ (A : PointedCone ℝ E) ⊔ (B : PointedCone ℝ E) := by
    change a ∈ (U : PointedCone ℝ E) at haU
    rw [hUsup] at haU
    exact haU
  rcases Submodule.mem_sup.mp haSup with ⟨b, hbA, c, hcB, hbc⟩
  have hb : b ∈ coneDual (C : Set E) := by
    exact (Iff.of_eq (congrArg (fun s : Set E => b ∈ s) hCdualSet)).mpr hbA
  have hc : c ∈ coneDual (D : Set E) := by
    exact (Iff.of_eq (congrArg (fun s : Set E => c ∈ s) hDdualSet)).mpr hcB
  exact ⟨b, c, hbc.symm, hb, hc⟩

/-- Every cell of a fan is dual-finitely-generated. -/
def HasDualFGCells [CompleteSpace E] (F : Fan E) : Prop :=
  ∀ C ∈ F, (C : PointedCone ℝ E).DualFG (innerₗ E)

theorem exists_scalar_for_finite_linear_inequalities
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a b : ι → ℝ)
    (hzero : ∀ i ∈ S, b i = 0 → 0 ≤ a i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, 0 < b i → b j < 0 →
      0 ≤ b i * a j - b j * a i) :
    ∃ t : ℝ, ∀ i ∈ S, 0 ≤ a i + b i * t := by
  classical
  let Pos := S.filter (fun i => 0 < b i)
  let Neg := S.filter (fun i => b i < 0)
  let lower (i : ι) := -a i / b i
  let upper (i : ι) := a i / (-b i)
  by_cases hPos : Pos.Nonempty
  · let lowers := Pos.image lower
    have hLowers : lowers.Nonempty := Finset.image_nonempty.mpr hPos
    let t := lowers.max' hLowers
    refine ⟨t, ?_⟩
    intro i hi
    by_cases hbi : 0 < b i
    · have hiPos : i ∈ Pos := Finset.mem_filter.mpr ⟨hi, hbi⟩
      have hlow : lower i ≤ t := by
        exact Finset.le_max' lowers (lower i) (Finset.mem_image.mpr ⟨i, hiPos, rfl⟩)
      have hmul := (div_le_iff₀ hbi).mp hlow
      linarith
    · by_cases hneg : b i < 0
      · have hiNeg : i ∈ Neg := Finset.mem_filter.mpr ⟨hi, hneg⟩
        have hupper : t ≤ upper i := by
          apply (Finset.max'_le_iff lowers hLowers).2
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨j, hjPos, rfl⟩
          have hjmem : j ∈ S := (Finset.mem_filter.mp hjPos).1
          have hjpos : 0 < b j := (Finset.mem_filter.mp hjPos).2
          have hpair' := hpair j hjmem i hi hjpos hneg
          have hbi' : 0 < -b i := neg_pos.mpr hneg
          have hratio : lower j ≤ upper i := by
            apply (div_le_div_iff₀ hjpos hbi').2
            nlinarith
          exact hratio
        have hmul := (le_div_iff₀ (neg_pos.mpr hneg)).mp hupper
        linarith
      · have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hbi) (le_of_not_gt hneg)
        have ha := hzero i hi hbi0
        simpa [hbi0] using ha
  · by_cases hNeg : Neg.Nonempty
    · let uppers := Neg.image upper
      have hUppers : uppers.Nonempty := Finset.image_nonempty.mpr hNeg
      let t := uppers.min' hUppers
      refine ⟨t, ?_⟩
      intro i hi
      by_cases hbi : 0 < b i
      · exact (False.elim (hPos <| ⟨i, Finset.mem_filter.mpr ⟨hi, hbi⟩⟩))
      · by_cases hneg : b i < 0
        · have hiNeg : i ∈ Neg := Finset.mem_filter.mpr ⟨hi, hneg⟩
          have hupper : t ≤ upper i :=
            Finset.min'_le uppers (upper i) (Finset.mem_image.mpr ⟨i, hiNeg, rfl⟩)
          have hmul := (le_div_iff₀ (neg_pos.mpr hneg)).mp hupper
          linarith
        · have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hbi) (le_of_not_gt hneg)
          have ha := hzero i hi hbi0
          simpa [hbi0] using ha
    · refine ⟨0, ?_⟩
      intro i hi
      have hnotPos : ¬ 0 < b i := fun h => hPos ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩⟩
      have hnotNeg : ¬ b i < 0 := fun h => hNeg ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩⟩
      have hbi0 : b i = 0 := le_antisymm (le_of_not_gt hnotPos) (le_of_not_gt hnotNeg)
      simpa [hbi0] using hzero i hi hbi0



/-- A projection of a finitely described closed cone still has a finite half-space description when
each fiber is a translate of the supplied kernel direction. The proof is Fourier--Motzkin
elimination along that direction. -/
theorem properCone_map_dualFG_of_dualFG_of_oneDimensionalFibers
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [DecidableEq E] [DecidableEq F]
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y)
    (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v)
    (C : ProperCone ℝ E)
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (C.map f : PointedCone ℝ F).DualFG (innerₗ F) := by
  classical
  obtain ⟨S, hS⟩ := hC
  change PointedCone.dual (innerₗ E) (S : Set E) = (C : PointedCone ℝ E) at hS
  have hCset : (C : Set E) = (coneDual (S : Set E) : Set E) := by
    apply congrArg (fun K : PointedCone ℝ E => (K : Set E)) hS.symm
  let normal (s : E) : F := g.adjoint s
  let beta (s : E) : ℝ := ⟪s, v⟫_ℝ
  let alpha (s : E) (y : F) : ℝ := ⟪normal s, y⟫_ℝ
  let Pos := S.filter (fun s => 0 < beta s)
  let Neg := S.filter (fun s => beta s < 0)
  let Zero := S.filter (fun s => beta s = 0)
  let pairNormal (p : E × E) : F :=
    (-beta p.2) • normal p.1 + beta p.1 • normal p.2
  let T : Finset F := Zero.image normal ∪ (Pos.product Neg).image pairNormal
  have hinner (x : E) (t : ℝ) (ht : x = g (f x) + t • v) (s : E) :
      ⟪s, x⟫_ℝ = alpha s (f x) + beta s * t := by
    calc
      ⟪s, x⟫_ℝ = ⟪s, g (f x) + t • v⟫_ℝ := by nth_rw 1 [ht]
      _ = ⟪s, g (f x)⟫_ℝ + t * ⟪s, v⟫_ℝ := by
        rw [inner_add_right, real_inner_smul_right]
      _ = ⟪normal s, f x⟫_ℝ + beta s * t := by
        rw [← g.adjoint_inner_left (f x) s]
        dsimp [normal, beta]
        ring
      _ = alpha s (f x) + beta s * t := rfl
  have hImageSub : f '' (C : Set E) ⊆ (coneDual (T : Set F) : Set F) := by
    rintro y ⟨x, hxC, rfl⟩
    have hxS : x ∈ coneDual (S : Set E) := by
      rw [hCset] at hxC
      exact hxC
    obtain ⟨t, ht⟩ := hdecomp x
    have hAlpha (s : E) : alpha s (f x) = ⟪s, x⟫_ℝ - beta s * t := by
      have hi := hinner x t ht s
      linarith
    apply mem_coneDual.mpr
    intro u hu
    rcases Finset.mem_union.mp hu with huZero | huPair
    · rcases Finset.mem_image.mp huZero with ⟨s, hsZero, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp hsZero).1
      have hbeta : beta s = 0 := (Finset.mem_filter.mp hsZero).2
      have hxs := (mem_coneDual.mp hxS) hsS
      change 0 ≤ alpha s (f x)
      rw [hAlpha s]
      simpa [hbeta] using hxs
    · rcases Finset.mem_image.mp huPair with ⟨⟨s, j⟩, hp, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
      have hjS : j ∈ S := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
      have hsPos : 0 < beta s := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      have hjNeg : beta j < 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      have hxs := (mem_coneDual.mp hxS) hsS
      have hxj := (mem_coneDual.mp hxS) hjS
      have hcombo : ⟪pairNormal (s, j), f x⟫_ℝ =
          (-beta j) * ⟪s, x⟫_ℝ + beta s * ⟪j, x⟫_ℝ := by
        calc
          ⟪pairNormal (s, j), f x⟫_ℝ =
              (-beta j) * alpha s (f x) + beta s * alpha j (f x) := by
                simp [pairNormal, normal, alpha, inner_add_left, real_inner_smul_left]
          _ = (-beta j) * (⟪s, x⟫_ℝ - beta s * t) +
              beta s * (⟪j, x⟫_ℝ - beta j * t) := by rw [hAlpha s, hAlpha j]
          _ = _ := by ring
      rw [hcombo]
      exact add_nonneg (mul_nonneg (le_of_lt (neg_pos.mpr hjNeg)) hxs)
        (mul_nonneg hsPos.le hxj)
  have hMapEq : (C.map f : Set F) = (coneDual (T : Set F) : Set F) := by
    ext y
    change y ∈ C.map f ↔ y ∈ coneDual (T : Set F)
    constructor
    · intro hy
      rw [ProperCone.mem_map] at hy
      exact closure_minimal hImageSub (coneDual (T : Set F)).isClosed hy
    · intro hy
      have hzero (s : E) (hs : s ∈ S) (hb : beta s = 0) : 0 ≤ alpha s y := by
        have hsZero : s ∈ Zero := Finset.mem_filter.mpr ⟨hs, hb⟩
        have hn : normal s ∈ T := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hsZero, rfl⟩)
        simpa [alpha, normal] using (mem_coneDual.mp hy) hn
      have hpair (s : E) (hs : s ∈ S) (j : E) (hj : j ∈ S)
          (hbs : 0 < beta s) (hbj : beta j < 0) :
          0 ≤ beta s * alpha j y - beta j * alpha s y := by
        have hsPos : s ∈ Pos := Finset.mem_filter.mpr ⟨hs, hbs⟩
        have hjNeg : j ∈ Neg := Finset.mem_filter.mpr ⟨hj, hbj⟩
        have hp : (s, j) ∈ Pos.product Neg := Finset.mem_product.mpr ⟨hsPos, hjNeg⟩
        have hn : pairNormal (s, j) ∈ T :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(s, j), hp, rfl⟩)
        have hy' := (mem_coneDual.mp hy) hn
        have hEq : ⟪pairNormal (s, j), y⟫_ℝ =
            beta s * alpha j y - beta j * alpha s y := by
          simp [pairNormal, normal, alpha, inner_add_left, real_inner_smul_left]
          ring
        rw [hEq] at hy'
        exact hy'
      obtain ⟨t, ht⟩ := exists_scalar_for_finite_linear_inequalities S
        (fun s => alpha s y) beta hzero hpair
      let x : E := g y + t • v
      have hxS : x ∈ coneDual (S : Set E) := by
        apply mem_coneDual.mpr
        intro s hs
        have hsineq := ht s hs
        have hcalc : ⟪s, x⟫_ℝ = alpha s y + beta s * t := by
          dsimp [x, alpha, normal, beta]
          rw [inner_add_right, real_inner_smul_right, ← g.adjoint_inner_left y s]
          ring
        rw [hcalc]
        exact hsineq
      have hxC : x ∈ C := by
        change x ∈ (C : Set E)
        rw [hCset]
        exact hxS
      have hfx : f x = y := by
        dsimp [x]
        simp [hfg, hv0]
      have himage : y ∈ f '' (C : Set E) := ⟨x, hxC, hfx⟩
      change y ∈ C.map f
      rw [ProperCone.mem_map]
      exact subset_closure himage
  have hMapEqCone : C.map f = coneDual (T : Set F) :=
    ProperCone.ext (fun y => Iff.of_eq (congrArg (fun U : Set F => y ∈ U) hMapEq))
  rw [hMapEqCone]
  change (PointedCone.dual (innerₗ F) (T : Set F)).DualFG (innerₗ F)
  exact PointedCone.DualFG.dual_of_finset (innerₗ F) T


/-- A finite family of cones with fibers directed by one supplied kernel vector inherits finite dual
representations from its source cones. -/
theorem linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [DecidableEq E] [DecidableEq F] [CompleteSpace E]
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y) (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v)
    (G : Fan E) (hG : HasDualFGCells G) :
    HasDualFGCells (linearImageFamily f G) := by
  classical
  intro C hC
  change C ∈ G.image (fun D => ProperCone.map f D) at hC
  rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
  exact properCone_map_dualFG_of_dualFG_of_oneDimensionalFibers
    f g v hfg hv0 hdecomp D (hG D hD)

/-- The linear map appending a zero coordinate. -/
def appendZeroCoordinate (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]
  map_smul' c x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc]

/-- Append a zero as a continuous linear map in the Euclidean coordinate model. -/
noncomputable def appendZeroEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  let targetEquiv := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let g := sourceEquiv.symm.toLinearMap.comp
    ((appendZeroCoordinate n).comp targetEquiv.toLinearMap)
  exact ⟨g, g.continuous_of_finiteDimensional⟩

/-- The final coordinate unit vector in Euclidean coordinates. -/
noncomputable def lastBasisEuclidean (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  exact sourceEquiv.symm (Fin.lastCases 1 (fun _ : Fin n => 0))

theorem forgetLast_appendZeroEuclidean (n : ℕ) :
    (forgetLastEuclidean n).comp (appendZeroEuclidean n) = ContinuousLinearMap.id ℝ _ := by
  ext y i
  simp [forgetLastEuclidean, appendZeroEuclidean, appendZeroCoordinate, forgetLastCoordinate,
    LinearMap.comp_apply, Fin.snoc_castSucc]

theorem forgetLast_decomposeEuclidean (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ t : ℝ, x = appendZeroEuclidean n (forgetLastEuclidean n x) + t • lastBasisEuclidean n := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  refine ⟨sourceEquiv x (Fin.last n), ?_⟩
  apply sourceEquiv.injective
  rw [sourceEquiv.map_add, sourceEquiv.map_smul]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendZeroEuclidean, appendZeroCoordinate, forgetLastEuclidean,
      forgetLastCoordinate, lastBasisEuclidean, sourceEquiv, Fin.snoc_last]
  · simp [appendZeroEuclidean, appendZeroCoordinate, forgetLastEuclidean,
      forgetLastCoordinate, lastBasisEuclidean, sourceEquiv, Fin.snoc_castSucc]



theorem forgetLast_lastBasis_eq_zero (n : ℕ) :
    forgetLastEuclidean n (lastBasisEuclidean n) = 0 := by
  ext i
  simp [forgetLastEuclidean, lastBasisEuclidean, forgetLastCoordinate,
    WithLp.linearEquiv]


theorem linearImageFamily_forgetLast_hasDualFGCells {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : HasDualFGCells G) :
    HasDualFGCells (linearImageFamily (forgetLastEuclidean n) G) := by
  apply linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    (forgetLastEuclidean n) (appendZeroEuclidean n) (lastBasisEuclidean n)
  · intro y
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) => L y) (forgetLast_appendZeroEuclidean n)
    simpa using h
  · exact forgetLast_lastBasis_eq_zero n
  · exact forgetLast_decomposeEuclidean n
  · exact hG

/-- The signed half-space normals describing one cell of a central hyperplane arrangement.
Normals in `P` impose nonnegative inner products, normals in `N` impose nonpositive inner
products, and normals in neither set occur with both signs and impose equality. -/
noncomputable def signCellNormals [DecidableEq E] (T P N : Finset E) : Finset E := by
  classical
  exact (P ∪ N.image (fun a => -a)) ∪
    ((T \ (P ∪ N)) ∪ (T \ (P ∪ N)).image (fun a => -a))

/-- A closed cone cut out by the sign constraints for a finite family of central hyperplanes. -/
noncomputable def signCell [CompleteSpace E] [DecidableEq E]
    (T P N : Finset E) : ProperCone ℝ E := by
  classical
  exact coneDual (signCellNormals T P N : Set E)

/-- Membership in a signed arrangement cell is exactly its intended weak sign/equality pattern. -/
theorem mem_signCell [CompleteSpace E] [DecidableEq E] {T P N : Finset E} {x : E} :
    x ∈ signCell T P N ↔
      (∀ a ∈ P, 0 ≤ ⟪a, x⟫_ℝ) ∧
      (∀ a ∈ N, 0 ≤ ⟪-a, x⟫_ℝ) ∧
      (∀ a ∈ T \ (P ∪ N), ⟪a, x⟫_ℝ = 0) := by
  classical
  simp [signCell, signCellNormals, mem_coneDual]
  constructor
  · intro h
    have hfull : ∀ y : E,
        (y ∈ P ∨ -y ∈ N ∨
          (y ∈ T ∧ y ∉ P ∧ y ∉ N) ∨ (-y ∈ T ∧ -y ∉ P ∧ -y ∉ N)) →
        0 ≤ ⟪y, x⟫_ℝ := by
      intro y hy
      exact h hy
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      exact hfull a (Or.inl ha)
    · intro a ha
      simpa [inner_neg_left] using hfull (-a) (Or.inr (Or.inl (by simpa using ha)))
    · intro a ha hPa hNa
      have hp := hfull a (Or.inr (Or.inr (Or.inl ⟨ha, hPa, hNa⟩)))
      have hn := hfull (-a) (Or.inr (Or.inr (Or.inr (by simpa using ⟨ha, hPa, hNa⟩))))
      have hn' : ⟪a, x⟫_ℝ ≤ 0 := by simpa [inner_neg_left] using hn
      nlinarith
  · rintro ⟨hP, hN, hZ⟩
    intro y hy
    rcases hy with hyP | hyN | hyZ | hyZneg
    · exact hP y hyP
    · simpa [inner_neg_left] using hN (-y) (by simpa using hyN)
    · rcases hyZ with ⟨hyT, hyP, hyN⟩
      have hzero := hZ y hyT hyP hyN
      rw [hzero]
    · rcases hyZneg with ⟨hyT, hyP, hyN⟩
      have hzero := hZ (-y) hyT hyP hyN
      have : ⟪y, x⟫_ℝ = 0 := by simpa using hzero
      rw [this]

/-- Interior membership in a finite dual cone is strict on every nonzero defining normal. -/
theorem inner_pos_of_mem_interior_finiteDual [CompleteSpace E]
    {S : Finset E} {x v : E} (hx : x ∈ interior (coneDual (S : Set E) : Set E))
    (hv : v ∈ S) (hvne : v ≠ 0) :
    0 < ⟪v, x⟫_ℝ := by
  have hxCone : x ∈ coneDual (S : Set E) := interior_subset hx
  have hnonneg : 0 ≤ ⟪v, x⟫_ℝ := (mem_coneDual.mp hxCone) hv
  by_contra hnot
  have hzero : ⟪v, x⟫_ℝ = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hopen : IsOpen (interior (coneDual (S : Set E) : Set E)) := isOpen_interior
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hopen) x hx
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  let δ : ℝ := r / (2 * ‖v‖)
  have hδ : 0 < δ := div_pos hr (mul_pos (by norm_num) hvnorm)
  let y : E := x + δ • (-v)
  have hdist : dist y x = δ * ‖v‖ := by
    have hsub : (x + δ • (-v)) - x = δ • (-v) := by abel
    rw [dist_eq_norm, show y = x + δ • (-v) from rfl, hsub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδ, norm_neg]
  have hδnorm : δ * ‖v‖ = r / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hvnorm]
  have hdistlt : dist y x < r := by
    rw [hdist, hδnorm]
    linarith
  have hyball : y ∈ Metric.ball x r := by
    simpa only [Metric.mem_ball] using hdistlt
  have hyInterior : y ∈ interior (coneDual (S : Set E) : Set E) := hball hyball
  have hyCone : y ∈ coneDual (S : Set E) := interior_subset hyInterior
  have hynonneg : 0 ≤ ⟪v, y⟫_ℝ := (mem_coneDual.mp hyCone) hv
  have hinner : ⟪v, y⟫_ℝ = ⟪v, x⟫_ℝ - δ * ‖v‖ ^ 2 := by
    rw [show y = x + δ • (-v) from rfl, inner_add_right,
      real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  have hnegative : ⟪v, y⟫_ℝ < 0 := by
    rw [hinner, hzero]
    have hnormsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvnorm
    nlinarith
  exact (not_lt_of_ge hynonneg) hnegative

/-- The finite central hyperplane arrangement family consists of every disjoint choice of
nonnegative and nonpositive normals, with all remaining normals imposing equality. -/
noncomputable def hyperplaneArrangementFamily [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : Fan E := by
  classical
  exact ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)).image
    (fun p => signCell T p.1 p.2)

/-- The sign cells of a finite central hyperplane arrangement cover the ambient space. -/
theorem hyperplaneArrangementFamily_covers [CompleteSpace E] [DecidableEq E]
    (T : Finset E) :
    (⋃ C ∈ hyperplaneArrangementFamily T, (C : Set E)) = Set.univ := by
  classical
  ext x
  constructor
  · intro _
    simp
  · intro _
    let P := T.filter (fun a => 0 ≤ ⟪a, x⟫_ℝ)
    let N := T.filter (fun a => ⟪a, x⟫_ℝ < 0)
    have hPsub : P ⊆ T := Finset.filter_subset _ _
    have hNsub : N ⊆ T := Finset.filter_subset _ _
    have hdis : Disjoint P N := by
      rw [Finset.disjoint_left]
      intro a haP haN
      simp only [P, N, Finset.mem_filter] at haP haN
      linarith
    have hpair : (P, N) ∈
        ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mk_mem_product
          (Finset.mem_powerset.mpr hPsub) (Finset.mem_powerset.mpr hNsub)
      · exact hdis
    have hP : ∀ a ∈ P, 0 ≤ ⟪a, x⟫_ℝ := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hN : ∀ a ∈ N, 0 ≤ ⟪-a, x⟫_ℝ := by
      intro a ha
      have hneg : ⟪a, x⟫_ℝ < 0 := (Finset.mem_filter.mp ha).2
      rw [inner_neg_left]
      linarith
    have hZ : ∀ a ∈ T \ (P ∪ N), ⟪a, x⟫_ℝ = 0 := by
      intro a ha
      have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
      have hNotUnion : a ∉ P ∪ N := (Finset.mem_sdiff.mp ha).2
      have haP : a ∉ P := by
        intro h
        exact hNotUnion (Finset.mem_union.mpr (Or.inl h))
      have haN : a ∉ N := by
        intro h
        exact hNotUnion (Finset.mem_union.mpr (Or.inr h))
      have hnotPos : ¬ 0 ≤ ⟪a, x⟫_ℝ := by
        intro h
        exact haP (Finset.mem_filter.mpr ⟨haT, h⟩)
      have hnotNeg : ¬ ⟪a, x⟫_ℝ < 0 := by
        intro h
        exact haN (Finset.mem_filter.mpr ⟨haT, h⟩)
      linarith
    have hcell : x ∈ signCell T P N := mem_signCell.mpr ⟨hP, hN, hZ⟩
    have hfamily : signCell T P N ∈ hyperplaneArrangementFamily T := by
      apply Finset.mem_image.mpr
      exact ⟨(P, N), hpair, rfl⟩
    refine Set.mem_iUnion.mpr ⟨signCell T P N, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hfamily, hcell⟩

theorem mem_hyperplaneArrangementFamily_iff [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C : ProperCone ℝ E} :
    C ∈ hyperplaneArrangementFamily T ↔
      ∃ P N, P ⊆ T ∧ N ⊆ T ∧ Disjoint P N ∧ C = signCell T P N := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hdis⟩
    rcases Finset.mem_product.mp hp with ⟨hP, hN⟩
    exact ⟨p.1, p.2, Finset.mem_powerset.mp hP, Finset.mem_powerset.mp hN, hdis, rfl⟩
  · rintro ⟨P, N, hP, hN, hdis, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(P, N), Finset.mem_filter.mpr ?_, rfl⟩
    exact ⟨Finset.mk_mem_product (Finset.mem_powerset.mpr hP)
      (Finset.mem_powerset.mpr hN), hdis⟩

/-- If two cells from the same central arrangement have a common interior point, their sign
patterns agree on every nonzero normal, and hence they are the same cone. -/
theorem hyperplaneArrangementFamily_eq_of_interiors_intersect [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : D ∈ hyperplaneArrangementFamily T)
    {x : E} (hxC : x ∈ interior (C : Set E)) (hxD : x ∈ interior (D : Set E)) :
    C = D := by
  classical
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  obtain ⟨P', N', hP'T, hN'T, hP'N', rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hD
  have hpositiveC : ∀ a ∈ T, a ≠ 0 → a ∈ P → 0 < ⟪a, x⟫_ℝ := by
    intro a ha ha0 haP
    have haS : a ∈ signCellNormals T P N := by
      change a ∈ (P ∪ N.image (fun v => -v)) ∪
        ((T \ (P ∪ N)) ∪ (T \ (P ∪ N)).image (fun v => -v))
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl haP)))
    exact inner_pos_of_mem_interior_finiteDual hxC haS ha0
  have hnegativeC : ∀ a ∈ T, a ≠ 0 → a ∈ N → ⟪a, x⟫_ℝ < 0 := by
    intro a ha ha0 haN
    have hminusS : -a ∈ signCellNormals T P N := by
      change -a ∈ (P ∪ N.image (fun v => -v)) ∪
        ((T \ (P ∪ N)) ∪ (T \ (P ∪ N)).image (fun v => -v))
      apply Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      exact Finset.mem_image.mpr ⟨a, haN, by simp⟩
    have hstrict := inner_pos_of_mem_interior_finiteDual hxC hminusS (neg_ne_zero.mpr ha0)
    have hneg : ⟪-a, x⟫_ℝ = -⟪a, x⟫_ℝ := by rw [inner_neg_left]
    rw [hneg] at hstrict
    linarith
  have hpositiveD : ∀ a ∈ T, a ≠ 0 → a ∈ P' → 0 < ⟪a, x⟫_ℝ := by
    intro a ha ha0 haP
    have haS : a ∈ signCellNormals T P' N' := by
      change a ∈ (P' ∪ N'.image (fun v => -v)) ∪
        ((T \ (P' ∪ N')) ∪ (T \ (P' ∪ N')).image (fun v => -v))
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl haP)))
    exact inner_pos_of_mem_interior_finiteDual hxD haS ha0
  have hnegativeD : ∀ a ∈ T, a ≠ 0 → a ∈ N' → ⟪a, x⟫_ℝ < 0 := by
    intro a ha ha0 haN
    have hminusS : -a ∈ signCellNormals T P' N' := by
      change -a ∈ (P' ∪ N'.image (fun v => -v)) ∪
        ((T \ (P' ∪ N')) ∪ (T \ (P' ∪ N')).image (fun v => -v))
      apply Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      exact Finset.mem_image.mpr ⟨a, haN, by simp⟩
    have hstrict := inner_pos_of_mem_interior_finiteDual hxD hminusS (neg_ne_zero.mpr ha0)
    have hneg : ⟪-a, x⟫_ℝ = -⟪a, x⟫_ℝ := by rw [inner_neg_left]
    rw [hneg] at hstrict
    linarith
  have hequalC : ∀ a ∈ T, a ≠ 0 → a ∉ P → a ∉ N → False := by
    intro a ha ha0 haP haN
    have hnotunion : a ∉ P ∪ N := by
      intro hu
      rcases Finset.mem_union.mp hu with hp | hn
      · exact haP hp
      · exact haN hn
    have hrem : a ∈ T \ (P ∪ N) := Finset.mem_sdiff.mpr ⟨ha, hnotunion⟩
    have haS : a ∈ signCellNormals T P N := by
      change a ∈ (P ∪ N.image (fun v => -v)) ∪
        ((T \ (P ∪ N)) ∪ (T \ (P ∪ N)).image (fun v => -v))
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hrem)))
    have hzero := (mem_signCell.mp (interior_subset hxC)).2.2 a hrem
    have hstrict := inner_pos_of_mem_interior_finiteDual hxC haS ha0
    rw [hzero] at hstrict
    exact (lt_irrefl _ hstrict)
  have hequalD : ∀ a ∈ T, a ≠ 0 → a ∉ P' → a ∉ N' → False := by
    intro a ha ha0 haP haN
    have hnotunion : a ∉ P' ∪ N' := by
      intro hu
      rcases Finset.mem_union.mp hu with hp | hn
      · exact haP hp
      · exact haN hn
    have hrem : a ∈ T \ (P' ∪ N') := Finset.mem_sdiff.mpr ⟨ha, hnotunion⟩
    have haS : a ∈ signCellNormals T P' N' := by
      change a ∈ (P' ∪ N'.image (fun v => -v)) ∪
        ((T \ (P' ∪ N')) ∪ (T \ (P' ∪ N')).image (fun v => -v))
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl hrem)))
    have hzero := (mem_signCell.mp (interior_subset hxD)).2.2 a hrem
    have hstrict := inner_pos_of_mem_interior_finiteDual hxD haS ha0
    rw [hzero] at hstrict
    exact (lt_irrefl _ hstrict)
  have hPiff : ∀ a ∈ T, a ≠ 0 → (a ∈ P ↔ a ∈ P') := by
    intro a ha ha0
    constructor
    · intro haP
      by_contra haP'
      by_cases haN' : a ∈ N'
      · have hp := hpositiveC a ha ha0 haP
        have hn := hnegativeD a ha ha0 haN'
        linarith
      · exact hequalD a ha ha0 haP' haN'
    · intro haP'
      by_contra haP
      by_cases haN : a ∈ N
      · have hp := hpositiveD a ha ha0 haP'
        have hn := hnegativeC a ha ha0 haN
        linarith
      · exact hequalC a ha ha0 haP haN
  have hNiff : ∀ a ∈ T, a ≠ 0 → (a ∈ N ↔ a ∈ N') := by
    intro a ha ha0
    constructor
    · intro haN
      by_contra haN'
      by_cases haP' : a ∈ P'
      · have hn := hnegativeC a ha ha0 haN
        have hp := hpositiveD a ha ha0 haP'
        linarith
      · exact hequalD a ha ha0 haP' haN'
    · intro haN'
      by_contra haN
      by_cases haP : a ∈ P
      · have hn := hnegativeD a ha ha0 haN'
        have hp := hpositiveC a ha ha0 haP
        linarith
      · exact hequalC a ha ha0 haP haN
  have hcell : signCell T P N = signCell T P' N' := by
    apply ProperCone.ext
    intro y
    rw [mem_signCell, mem_signCell]
    constructor
    · rintro ⟨hP, hN, hZ⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a haP'
        have haT := hP'T haP'
        by_cases ha0 : a = 0
        · simp [ha0]
        · exact hP a ((hPiff a haT ha0).mpr haP')
      · intro a haN'
        have haT := hN'T haN'
        by_cases ha0 : a = 0
        · simp [ha0]
        · exact hN a ((hNiff a haT ha0).mpr haN')
      · intro a ha
        have haT := (Finset.mem_sdiff.mp ha).1
        have haNot := (Finset.mem_sdiff.mp ha).2
        by_cases ha0 : a = 0
        · simp [ha0]
        · have haP : a ∉ P := by
            intro hP
            exact haNot (Finset.mem_union.mpr
              (Or.inl ((hPiff a haT ha0).mp hP)))
          have haN : a ∉ N := by
            intro hN
            exact haNot (Finset.mem_union.mpr
              (Or.inr ((hNiff a haT ha0).mp hN)))
          exact hZ a (Finset.mem_sdiff.mpr ⟨haT, by
            intro hu
            rcases Finset.mem_union.mp hu with hp | hn
            · exact haP hp
            · exact haN hn⟩)
    · rintro ⟨hP', hN', hZ'⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a haP
        have haT := hPT haP
        by_cases ha0 : a = 0
        · simp [ha0]
        · exact hP' a ((hPiff a haT ha0).mp haP)
      · intro a haN
        have haT := hNT haN
        by_cases ha0 : a = 0
        · simp [ha0]
        · exact hN' a ((hNiff a haT ha0).mp haN)
      · intro a ha
        have haT := (Finset.mem_sdiff.mp ha).1
        have haNot := (Finset.mem_sdiff.mp ha).2
        by_cases ha0 : a = 0
        · simp [ha0]
        · have haP' : a ∉ P' := by
            intro hP
            exact haNot (Finset.mem_union.mpr
              (Or.inl ((hPiff a haT ha0).mpr hP)))
          have haN' : a ∉ N' := by
            intro hN
            exact haNot (Finset.mem_union.mpr
              (Or.inr ((hNiff a haT ha0).mpr hN)))
          exact hZ' a (Finset.mem_sdiff.mpr ⟨haT, by
            intro hu
            rcases Finset.mem_union.mp hu with hp | hn
            · exact haP' hp
            · exact haN' hn⟩)
  exact hcell

/-- Pairwise intersections of sign cells are sign cells: coordinates with opposite signs or a
zero assignment become equalities, while coordinates with the same strict sign retain it. -/
private theorem signCell_inter_isExposedFaceOf_left [CompleteSpace E] [DecidableEq E]
    {T P N P' N' : Finset E} (hPT : P ⊆ T) (hNT : N ⊆ T)
    (hP'T : P' ⊆ T) (hN'T : N' ⊆ T) (hPN : Disjoint P N)
    (hP'N' : Disjoint P' N') {G : ProperCone ℝ E}
    (hG : (G : Set E) = (signCell T P N : Set E) ∩ (signCell T P' N' : Set E)) :
    IsExposedFaceOf G (signCell T P N) := by
  classical
  let A := P \ P'
  let B := N \ N'
  let a : E := (∑ i ∈ A, i) + (∑ i ∈ B, -i)
  have not_union {S U : Finset E} {i : E} (hiS : i ∉ S) (hiU : i ∉ U) :
      i ∉ S ∪ U := by
    intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hiS hi
    · exact hiU hi
  have hAdual : (∑ i ∈ A, i) ∈ coneDual (signCell T P N : Set E) := by
    apply Submodule.sum_mem
    intro i hi
    change i ∈ coneDual (signCell T P N : Set E)
    apply mem_coneDual.mpr
    intro x hx
    have hpos := (mem_signCell.mp hx).1 i (Finset.mem_sdiff.mp hi).1
    simpa [real_inner_comm] using hpos
  have hBdual : (∑ i ∈ B, -i) ∈ coneDual (signCell T P N : Set E) := by
    apply Submodule.sum_mem
    intro i hi
    change -i ∈ coneDual (signCell T P N : Set E)
    apply mem_coneDual.mpr
    intro x hx
    have hneg := (mem_signCell.mp hx).2.1 i (Finset.mem_sdiff.mp hi).1
    simpa [real_inner_comm] using hneg
  have hadual : a ∈ coneDual (signCell T P N : Set E) := by
    dsimp [a]
    exact add_mem hAdual hBdual
  have hinner (x : E) : ⟪a, x⟫_ℝ =
      (∑ i ∈ A, ⟪i, x⟫_ℝ) + (∑ i ∈ B, ⟪-i, x⟫_ℝ) := by
    change ⟪(∑ i ∈ A, i) + (∑ i ∈ B, -i), x⟫_ℝ = _
    rw [inner_add_left, sum_inner, sum_inner]
  have hfaceSet : (G : Set E) =
      (exposedFace (signCell T P N : PointedCone ℝ E) a : Set E) := by
    rw [hG]
    ext x
    constructor
    · rintro ⟨hxC, hxD⟩
      refine mem_exposedFace.mpr ⟨hxC, ?_⟩
      have hP := (mem_signCell.mp hxC).1
      have hN := (mem_signCell.mp hxC).2.1
      have hDpos := (mem_signCell.mp hxD).1
      have hDneg := (mem_signCell.mp hxD).2.1
      have hDzero := (mem_signCell.mp hxD).2.2
      have hAzero : ∀ i ∈ A, ⟪i, x⟫_ℝ = 0 := by
        intro i hi
        have hnonneg := hP i (Finset.mem_sdiff.mp hi).1
        by_cases hiN' : i ∈ N'
        · have hnonpos : ⟪i, x⟫_ℝ ≤ 0 := by
            simpa [inner_neg_left] using hDneg i hiN'
          exact le_antisymm hnonpos hnonneg
        · exact hDzero i (Finset.mem_sdiff.mpr
            ⟨hPT (Finset.mem_sdiff.mp hi).1, not_union
              (Finset.mem_sdiff.mp hi).2 hiN'⟩)
      have hBzero : ∀ i ∈ B, ⟪-i, x⟫_ℝ = 0 := by
        intro i hi
        have hnonpos := hN i (Finset.mem_sdiff.mp hi).1
        by_cases hiP' : i ∈ P'
        · have hpos := hDpos i hiP'
          have hnegNonpos : ⟪-i, x⟫_ℝ ≤ 0 := by
            simpa [inner_neg_left] using hpos
          have hzero : ⟪-i, x⟫_ℝ = 0 := le_antisymm hnegNonpos hnonpos
          exact hzero
        · have hzero := hDzero i (Finset.mem_sdiff.mpr
            ⟨hNT (Finset.mem_sdiff.mp hi).1, not_union hiP'
              (Finset.mem_sdiff.mp hi).2⟩)
          simpa [inner_neg_left] using hzero
      rw [hinner x, Finset.sum_eq_zero hAzero, Finset.sum_eq_zero hBzero]
      simp
    · intro hxFace
      have hxC : x ∈ signCell T P N := (mem_exposedFace.mp hxFace).1
      have hzero : ⟪a, x⟫_ℝ = 0 := (mem_exposedFace.mp hxFace).2
      have hCpos := (mem_signCell.mp hxC).1
      have hCneg := (mem_signCell.mp hxC).2.1
      have hCzero := (mem_signCell.mp hxC).2.2
      have hAzeroNonneg : ∀ i ∈ A, 0 ≤ ⟪i, x⟫_ℝ := fun i hi => hCpos i (Finset.mem_sdiff.mp hi).1
      have hBzeroNonneg : ∀ i ∈ B, 0 ≤ ⟪-i, x⟫_ℝ := by
        intro i hi
        exact hCneg i (Finset.mem_sdiff.mp hi).1
      have hsum : (∑ i ∈ A, ⟪i, x⟫_ℝ) +
          (∑ i ∈ B, ⟪-i, x⟫_ℝ) = 0 := by rw [← hinner x, hzero]
      have hAsum : (∑ i ∈ A, ⟪i, x⟫_ℝ) = 0 := by
        have hA' := Finset.sum_nonneg hAzeroNonneg
        have hB' := Finset.sum_nonneg hBzeroNonneg
        nlinarith
      have hBsum : (∑ i ∈ B, ⟪-i, x⟫_ℝ) = 0 := by
        have hA' := Finset.sum_nonneg hAzeroNonneg
        have hB' := Finset.sum_nonneg hBzeroNonneg
        nlinarith
      have hAzero : ∀ i ∈ A, ⟪i, x⟫_ℝ = 0 := by
        intro i hi
        exact (Finset.sum_eq_zero_iff_of_nonneg hAzeroNonneg).mp hAsum i hi
      have hBzero : ∀ i ∈ B, ⟪-i, x⟫_ℝ = 0 := by
        intro i hi
        exact (Finset.sum_eq_zero_iff_of_nonneg hBzeroNonneg).mp hBsum i hi
      have hxD : x ∈ signCell T P' N' := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro i hi
          by_cases hiP : i ∈ P
          · exact hCpos i hiP
          · by_cases hiN : i ∈ N
            · have hiB : i ∈ B := Finset.mem_sdiff.mpr
                ⟨hiN, fun hiN' => (Finset.disjoint_left.mp hP'N') hi hiN'⟩
              have hz := hBzero i hiB
              have hz' : ⟪i, x⟫_ℝ = 0 := by simpa [inner_neg_left] using hz
              rw [hz']
            · have hz := hCzero i (Finset.mem_sdiff.mpr
                ⟨hP'T hi, not_union hiP hiN⟩)
              rw [hz]
        · intro i hi
          by_cases hiN : i ∈ N
          · exact hCneg i hiN
          · by_cases hiP : i ∈ P
            · have hiA : i ∈ A := Finset.mem_sdiff.mpr
                ⟨hiP, fun hiP' => (Finset.disjoint_left.mp hP'N') hiP' hi⟩
              have hz := hAzero i hiA
              simpa [inner_neg_left, hz]
            · have hz := hCzero i (Finset.mem_sdiff.mpr
                ⟨hN'T hi, not_union hiP hiN⟩)
              have hz' : ⟪-i, x⟫_ℝ = 0 := by simpa [inner_neg_left] using hz
              rw [hz']
        · intro i hi
          by_cases hiP : i ∈ P
          · have hiA : i ∈ A := Finset.mem_sdiff.mpr
              ⟨hiP, fun hiP' => (Finset.mem_sdiff.mp hi).2
                (Finset.mem_union.mpr (Or.inl hiP'))⟩
            exact hAzero i hiA
          · by_cases hiN : i ∈ N
            · have hiB : i ∈ B := Finset.mem_sdiff.mpr
                ⟨hiN, fun hiN' => (Finset.mem_sdiff.mp hi).2
                  (Finset.mem_union.mpr (Or.inr hiN'))⟩
              have hz := hBzero i hiB
              have hz' : ⟪i, x⟫_ℝ = 0 := by simpa [inner_neg_left] using hz
              exact hz'
            · exact hCzero i (Finset.mem_sdiff.mpr
                ⟨(Finset.mem_sdiff.mp hi).1, not_union hiP hiN⟩)
      exact ⟨hxC, hxD⟩
  refine ⟨a, hadual, ?_⟩
  exact hfaceSet

/-- Pairwise intersections of sign cells are sign cells: coordinates with opposite signs or a
zero assignment become equalities, while coordinates with the same strict sign retain it. -/
theorem hyperplaneArrangementFamily_inter_common [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : D ∈ hyperplaneArrangementFamily T) :
    ∃ G ∈ hyperplaneArrangementFamily T,
      (G : Set E) = (C : Set E) ∩ (D : Set E) ∧
        IsExposedFaceOf G C ∧ IsExposedFaceOf G D := by
  classical
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  obtain ⟨P', N', hP'T, hN'T, hP'N', rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hD
  let Q := P ∩ P'
  let R := N ∩ N'
  have hQT : Q ⊆ T := Finset.inter_subset_left.trans hPT
  have hRT : R ⊆ T := Finset.inter_subset_left.trans hNT
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    intro a haQ haR
    exact (Finset.disjoint_left.mp hPN) (Finset.mem_inter.mp haQ).1
      (Finset.mem_inter.mp haR).1
  have not_union {A B : Finset E} {a : E} (hA : a ∉ A) (hB : a ∉ B) :
      a ∉ A ∪ B := by
    intro hab
    rcases Finset.mem_union.mp hab with ha | hb
    · exact hA ha
    · exact hB hb
  have hpair : (Q, R) ∈
      ((T.powerset.product T.powerset).filter (fun p => Disjoint p.1 p.2)) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mk_mem_product
        (Finset.mem_powerset.mpr hQT) (Finset.mem_powerset.mpr hRT)
    · exact hQR
  let G := signCell T Q R
  have hG : G ∈ hyperplaneArrangementFamily T := by
    change signCell T Q R ∈ hyperplaneArrangementFamily T
    apply Finset.mem_image.mpr
    exact ⟨(Q, R), hpair, rfl⟩
  have hset : (G : Set E) = (signCell T P N : Set E) ∩
      (signCell T P' N' : Set E) := by
    ext x
    change x ∈ signCell T Q R ↔
      x ∈ signCell T P N ∧ x ∈ signCell T P' N'
    rw [mem_signCell, mem_signCell, mem_signCell]
    constructor
    · rintro ⟨hQ, hR, hZ⟩
      have hC' : x ∈ signCell T P N := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          by_cases haP' : a ∈ P'
          · exact hQ a (Finset.mem_inter.mpr ⟨ha, haP'⟩)
          · have hnotQ : a ∉ Q := fun h => haP' (Finset.mem_inter.mp h).2
            have hnotR : a ∉ R := by
              intro h
              exact (Finset.disjoint_left.mp hPN) ha (Finset.mem_inter.mp h).1
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hPT ha, not_union hnotQ hnotR⟩)
            rw [hz]
        · intro a ha
          by_cases haN' : a ∈ N'
          · exact hR a (Finset.mem_inter.mpr ⟨ha, haN'⟩)
          · have hnotR : a ∉ R := fun h => haN' (Finset.mem_inter.mp h).2
            have hnotQ : a ∉ Q := by
              intro h
              exact (Finset.disjoint_left.mp hPN) (Finset.mem_inter.mp h).1 ha
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hNT ha, not_union hnotQ hnotR⟩)
            rw [inner_neg_left, hz]
            simp
        · intro a ha
          have haNot := (Finset.mem_sdiff.mp ha).2
          have haP : a ∉ P := fun h => haNot (Finset.mem_union.mpr (Or.inl h))
          have haN : a ∉ N := fun h => haNot (Finset.mem_union.mpr (Or.inr h))
          have haQ : a ∉ Q := fun h => haP (Finset.mem_inter.mp h).1
          have haR : a ∉ R := fun h => haN (Finset.mem_inter.mp h).1
          exact hZ a (Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp ha).1, not_union haQ haR⟩)
      have hD' : x ∈ signCell T P' N' := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          by_cases haP : a ∈ P
          · exact hQ a (Finset.mem_inter.mpr ⟨haP, ha⟩)
          · have hnotQ : a ∉ Q := fun h => haP (Finset.mem_inter.mp h).1
            have hnotR : a ∉ R := by
              intro h
              exact (Finset.disjoint_left.mp hP'N') ha (Finset.mem_inter.mp h).2
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hP'T ha, not_union hnotQ hnotR⟩)
            rw [hz]
        · intro a ha
          by_cases haN : a ∈ N
          · exact hR a (Finset.mem_inter.mpr ⟨haN, ha⟩)
          · have hnotR : a ∉ R := fun h => haN (Finset.mem_inter.mp h).1
            have hnotQ : a ∉ Q := by
              intro h
              exact (Finset.disjoint_left.mp hP'N') (Finset.mem_inter.mp h).2 ha
            have hz := hZ a (Finset.mem_sdiff.mpr
              ⟨hN'T ha, not_union hnotQ hnotR⟩)
            rw [inner_neg_left, hz]
            simp
        · intro a ha
          have haNot := (Finset.mem_sdiff.mp ha).2
          have haP' : a ∉ P' := fun h => haNot (Finset.mem_union.mpr (Or.inl h))
          have haN' : a ∉ N' := fun h => haNot (Finset.mem_union.mpr (Or.inr h))
          have haQ : a ∉ Q := fun h => haP' (Finset.mem_inter.mp h).2
          have haR : a ∉ R := fun h => haN' (Finset.mem_inter.mp h).2
          exact hZ a (Finset.mem_sdiff.mpr
            ⟨(Finset.mem_sdiff.mp ha).1, not_union haQ haR⟩)
      exact ⟨mem_signCell.mp hC', mem_signCell.mp hD'⟩
    · rintro ⟨hC, hD⟩
      rcases hC with ⟨hP, hN, hZP⟩
      rcases hD with ⟨hP', hN', hZP'⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        exact hP a (Finset.mem_inter.mp ha).1
      · intro a ha
        exact hN a (Finset.mem_inter.mp ha).1
      · intro a ha
        have haT : a ∈ T := (Finset.mem_sdiff.mp ha).1
        have hnotUnion := (Finset.mem_sdiff.mp ha).2
        have hnotQ : a ∉ Q := fun h => hnotUnion (Finset.mem_union.mpr (Or.inl h))
        have hnotR : a ∉ R := fun h => hnotUnion (Finset.mem_union.mpr (Or.inr h))
        by_cases haP : a ∈ P
        · by_cases haP' : a ∈ P'
          · exact (hnotQ (Finset.mem_inter.mpr ⟨haP, haP'⟩)).elim
          · by_cases haN' : a ∈ N'
            · have hp := hP a haP
              have hn : ⟪a, x⟫_ℝ ≤ 0 := by
                simpa [inner_neg_left] using hN' a haN'
              exact le_antisymm hn hp
            · exact hZP' a (Finset.mem_sdiff.mpr
                ⟨haT, not_union haP' haN'⟩)
        · by_cases haN : a ∈ N
          · by_cases haP' : a ∈ P'
            · have hp := hP' a haP'
              have hn : ⟪a, x⟫_ℝ ≤ 0 := by
                simpa [inner_neg_left] using hN a haN
              exact le_antisymm hn hp
            · by_cases haN' : a ∈ N'
              · exact (hnotR (Finset.mem_inter.mpr ⟨haN, haN'⟩)).elim
              · exact hZP' a (Finset.mem_sdiff.mpr
                  ⟨haT, not_union haP' haN'⟩)
          · exact hZP a (Finset.mem_sdiff.mpr
              ⟨haT, not_union haP haN⟩)
  refine ⟨G, hG, hset, ?_, ?_⟩
  · exact signCell_inter_isExposedFaceOf_left hPT hNT hP'T hN'T hPN hP'N' hset
  · have hset' : (G : Set E) = (signCell T P' N' : Set E) ∩
        (signCell T P N : Set E) := by rw [hset, Set.inter_comm]
    exact signCell_inter_isExposedFaceOf_left hP'T hN'T hPT hNT hP'N' hPN hset'

/-- At a point of a finite central arrangement there is a canonical smallest sign cell: normals
with strictly positive or negative evaluation keep that sign, while normals vanishing at the
point become equalities. This cell is contained in every arrangement cell incident to the point.
It is the common lower-dimensional face needed when a face-filling step has more than two incident
tiles. -/
theorem hyperplaneArrangementFamily_commonFace_at [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {x : E} (cells : Finset (ProperCone ℝ E))
    (hCells : ∀ C ∈ cells, C ∈ hyperplaneArrangementFamily T)
    (hxCells : ∀ C ∈ cells, x ∈ (C : Set E)) :
    ∃ G ∈ hyperplaneArrangementFamily T, x ∈ (G : Set E) ∧
      ∀ C ∈ cells, (G : Set E) ⊆ (C : Set E) ∧ IsExposedFaceOf G C := by
  classical
  let P := T.filter (fun a => 0 < ⟪a, x⟫_ℝ)
  let N := T.filter (fun a => ⟪a, x⟫_ℝ < 0)
  have hPT : P ⊆ T := Finset.filter_subset _ _
  have hNT : N ⊆ T := Finset.filter_subset _ _
  have hPN : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro a haP haN
    simp only [P, N, Finset.mem_filter] at haP haN
    linarith
  let G := signCell T P N
  have hG : G ∈ hyperplaneArrangementFamily T :=
    mem_hyperplaneArrangementFamily_iff.mpr ⟨P, N, hPT, hNT, hPN, rfl⟩
  have hGx : x ∈ G := by
    apply mem_signCell.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      exact le_of_lt (Finset.mem_filter.mp ha).2
    · intro a ha
      rw [inner_neg_left]
      linarith [(Finset.mem_filter.mp ha).2]
    · intro a ha
      have haT := (Finset.mem_sdiff.mp ha).1
      have haNot := (Finset.mem_sdiff.mp ha).2
      have haP : a ∉ P := by
        intro h
        exact haNot (Finset.mem_union.mpr (Or.inl h))
      have haN : a ∉ N := by
        intro h
        exact haNot (Finset.mem_union.mpr (Or.inr h))
      have hnotPos : ¬ 0 < ⟪a, x⟫_ℝ := by
        intro h
        exact haP (Finset.mem_filter.mpr ⟨haT, h⟩)
      have hnotNeg : ¬ ⟪a, x⟫_ℝ < 0 := by
        intro h
        exact haN (Finset.mem_filter.mpr ⟨haT, h⟩)
      linarith
  refine ⟨G, hG, hGx, ?_⟩
  intro C hC
  have hCfam := hCells C hC
  have hxC := hxCells C hC
  obtain ⟨P', N', hP'T, hN'T, hP'N', hCeq⟩ :=
    mem_hyperplaneArrangementFamily_iff.mp hCfam
  have hxC' : x ∈ signCell T P' N' := by simpa [hCeq] using hxC
  have hGC' : (G : Set E) ⊆ (signCell T P' N' : Set E) := by
    intro y hy
    apply mem_signCell.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro a haP'
      have hax := (mem_signCell.mp hxC').1 a haP'
      by_cases hapos : 0 < ⟪a, x⟫_ℝ
      · exact (mem_signCell.mp hy).1 a (Finset.mem_filter.mpr ⟨hP'T haP', hapos⟩)
      · have hzero : ⟪a, x⟫_ℝ = 0 := by linarith
        have haP : a ∉ P := by
          intro hp
          have := (Finset.mem_filter.mp hp).2
          linarith
        have haN : a ∉ N := by
          intro hn
          have := (Finset.mem_filter.mp hn).2
          linarith
        have hyzero := (mem_signCell.mp hy).2.2 a
          (Finset.mem_sdiff.mpr ⟨hP'T haP', by
            intro hu
            rcases Finset.mem_union.mp hu with hp | hn
            · exact haP hp
            · exact haN hn⟩)
        linarith
    · intro a haN'
      have hax := (mem_signCell.mp hxC').2.1 a haN'
      have hax' : ⟪a, x⟫_ℝ ≤ 0 := by
        simpa [inner_neg_left] using hax
      by_cases haneg : ⟪a, x⟫_ℝ < 0
      · exact (mem_signCell.mp hy).2.1 a (Finset.mem_filter.mpr ⟨hN'T haN', haneg⟩)
      · have hzero : ⟪a, x⟫_ℝ = 0 := by linarith
        have haP : a ∉ P := by
          intro hp
          have := (Finset.mem_filter.mp hp).2
          linarith
        have haN : a ∉ N := by
          intro hn
          exact haneg (Finset.mem_filter.mp hn).2
        have hyzero := (mem_signCell.mp hy).2.2 a
          (Finset.mem_sdiff.mpr ⟨hN'T haN', by
            intro hu
            rcases Finset.mem_union.mp hu with hp | hn
            · exact haP hp
            · exact haN hn⟩)
        rw [inner_neg_left]
        linarith
    · intro a haZ
      have hxzero := (mem_signCell.mp hxC').2.2 a haZ
      have haP : a ∉ P := by
        intro hp
        have hpos := (Finset.mem_filter.mp hp).2
        rw [hxzero] at hpos
        linarith
      have haN : a ∉ N := by
        intro hn
        have hneg := (Finset.mem_filter.mp hn).2
        rw [hxzero] at hneg
        linarith
      exact (mem_signCell.mp hy).2.2 a
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp haZ).1, by
          intro hu
          rcases Finset.mem_union.mp hu with hp | hn
          · exact haP hp
          · exact haN hn⟩)
  have hGC : (G : Set E) ⊆ (C : Set E) := by simpa [hCeq] using hGC'
  have hmeet : (C : Set E) ∩ (G : Set E) = (G : Set E) := by
    rw [hCeq]
    ext y
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨_, hy⟩
      exact hy
    · intro hy
      exact ⟨hGC' hy, hy⟩
  have hfaceSet : (G : Set E) =
      (signCell T P' N' : Set E) ∩ (signCell T P N : Set E) := by
    rw [hCeq] at hmeet
    exact hmeet.symm
  have hface := signCell_inter_isExposedFaceOf_left
    hP'T hN'T hPT hNT hP'N' hPN hfaceSet
  exact ⟨hGC, by simpa [hCeq] using hface⟩

/-- A boundary point of a finite central-arrangement cell is also incident to another cell.
The arrangement covers the ambient space, and the family is finite and closed: if no other cell
contained the point, the point would have a neighborhood contained in the chosen cell. This is the
cell-incidence fact needed to turn geometric tile boundaries into recursive face tasks. -/
theorem hyperplaneArrangementFamily_boundary_incident_cell [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C : ProperCone ℝ E} {x : E}
    (hxnot : x ∉ interior (C : Set E)) :
    ∃ D, D ∈ hyperplaneArrangementFamily T ∧ D ≠ C ∧ x ∈ (D : Set E) := by
  classical
  let Cells := {D : ProperCone ℝ E // D ∈ hyperplaneArrangementFamily T}
  letI : Fintype Cells := Finset.fintypeCoeSort (hyperplaneArrangementFamily T)
  let others : Set E := ⋃ D : Cells, if D.1 = C then ∅ else (D.1 : Set E)
  have hclosed : IsClosed others := isClosed_iUnion_of_finite fun D => by
    by_cases hDC : D.1 = C
    · simp [hDC]
    · simpa [others, hDC] using D.1.isClosed
  by_contra hfound
  have hnone : ∀ D : Cells, D.1 ≠ C → x ∉ (D.1 : Set E) := by
    intro D hDC hxD
    exact hfound ⟨D.1, D.2, hDC, hxD⟩
  have hxOthers : x ∉ others := by
    intro hx
    simp only [others, Set.mem_iUnion] at hx
    obtain ⟨D, hD⟩ := hx
    by_cases hDC : D.1 = C
    · simp [hDC] at hD
    · exact hnone D hDC (by simpa [hDC] using hD)
  have hopen : IsOpen (othersᶜ) := hclosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hopen) x hxOthers
  have hballSubset : Metric.ball x r ⊆ (C : Set E) := by
    intro y hy
    have hyOthers : y ∉ others := hball hy
    have hyCover : y ∈ ⋃ D ∈ hyperplaneArrangementFamily T, (D : Set E) := by
      rw [hyperplaneArrangementFamily_covers]
      simp
    rcases Set.mem_iUnion.mp hyCover with ⟨D, hD⟩
    rcases Set.mem_iUnion.mp hD with ⟨hDfam, hyD⟩
    by_cases hDC : D = C
    · simpa [hDC] using hyD
    · have hyInOthers : y ∈ others := by
        apply Set.mem_iUnion.mpr
        exact ⟨⟨D, hDfam⟩, by simp [hDC, hyD]⟩
      exact (hyOthers hyInOthers).elim
  have hxInterior : x ∈ interior (C : Set E) := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hballSubset
  exact hxnot hxInterior

/-- A non-interior point of an arrangement cell gives a genuine predecessor edge among the cells
incident there. The common face is proper in at least one of the two distinct incident cells, so
this result is directly usable by the one-bit face recursion for both strip and endpoint tasks. -/
theorem hyperplaneArrangementFamily_boundary_commonFace_dependency_at [CompleteSpace E] [DecidableEq E]
    {ι : Type*} {m : ℕ} {T : Finset E} {x : E}
    (k : ι) (cell : OneBitFiberCell m) (C : ProperCone ℝ E)
    (hC : C ∈ hyperplaneArrangementFamily T) (hxC : x ∈ (C : Set E))
    (hxnot : x ∉ interior (C : Set E)) :
    ∃ D, D ∈ hyperplaneArrangementFamily T ∧ D ≠ C ∧ x ∈ (D : Set E) ∧
      ∃ G, G ∈ hyperplaneArrangementFamily T ∧ x ∈ (G : Set E) ∧
        (G ≠ C ∨ G ≠ D) ∧
        (G ≠ C → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
          ((G, k), cell) ((C, k), cell)) ∧
        (G ≠ D → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
          ((G, k), cell) ((D, k), cell)) := by
  classical
  obtain ⟨D, hD, hDC, hxD⟩ :=
    hyperplaneArrangementFamily_boundary_incident_cell (T := T) (C := C) hxnot
  let cells : Finset (ProperCone ℝ E) := {C, D}
  have hCells : ∀ Q ∈ cells, Q ∈ hyperplaneArrangementFamily T := by
    intro Q hQ
    simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · exact hC
    · exact hD
  have hxCells : ∀ Q ∈ cells, x ∈ (Q : Set E) := by
    intro Q hQ
    simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · exact hxC
    · exact hxD
  obtain ⟨G, hG, hxG, hfaces⟩ :=
    hyperplaneArrangementFamily_commonFace_at cells hCells hxCells
  have hCcells : C ∈ cells := by simp [cells]
  have hDcells : D ∈ cells := by simp [cells]
  have hfaceC := (hfaces C hCcells).2
  have hfaceD := (hfaces D hDcells).2
  have hproper : G ≠ C ∨ G ≠ D := by
    by_cases hGC : G = C
    · right
      intro hGD
      exact hDC (hGC.symm.trans hGD).symm
    · exact Or.inl hGC
  have hdepC : G ≠ C → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
      ((G, k), cell) ((C, k), cell) := by
    intro hne
    cases cell with
    | strip i => exact OneBitFanFaceDependency.fanFace C G k i hfaceC hne
    | endpoint j => exact OneBitFanFaceDependency.fanFaceEndpoint C G k j hfaceC hne
  have hdepD : G ≠ D → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
      ((G, k), cell) ((D, k), cell) := by
    intro hne
    cases cell with
    | strip i => exact OneBitFanFaceDependency.fanFace D G k i hfaceD hne
    | endpoint j => exact OneBitFanFaceDependency.fanFaceEndpoint D G k j hfaceD hne
  exact ⟨D, hD, hDC, hxD, G, hG, hxG, hproper, hdepC, hdepD⟩

/-- The common incident face at a projected basepoint supplies the proper fan-face predecessors
in Craciun's one-bit recursion. Thus a multi-cell junction can be filled after all of its
lower-dimensional strip tasks have been discharged by `oneBitFanFaceDependency_induction`. -/
theorem hyperplaneArrangementFamily_commonFace_tasks_at [CompleteSpace E]
    [DecidableEq E] [FiniteDimensional ℝ E] {ι : Type*} {m : ℕ}
    {T : Finset E} {x : E}
    (k : ι) (i : Fin (m + 1)) (cells : Finset (ProperCone ℝ E))
    (hCells : ∀ C ∈ cells, C ∈ hyperplaneArrangementFamily T)
    (hxCells : ∀ C ∈ cells, x ∈ (C : Set E)) :
    ∃ G ∈ hyperplaneArrangementFamily T, x ∈ (G : Set E) ∧
      ∀ C ∈ cells, (G : Set E) ⊆ (C : Set E) ∧ IsExposedFaceOf G C ∧
        (G ≠ C → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
          ((G, k), .strip i) ((C, k), .strip i)) := by
  obtain ⟨G, hG, hxG, hfaces⟩ :=
    hyperplaneArrangementFamily_commonFace_at cells hCells hxCells
  refine ⟨G, hG, hxG, ?_⟩
  intro C hC
  obtain ⟨hsubset, hface⟩ := hfaces C hC
  refine ⟨hsubset, hface, ?_⟩
  intro hne
  exact OneBitFanFaceDependency.fanFace C G k i hface hne

/-- At an endpoint seam, the common incident arrangement face is also a predecessor endpoint
task. This is the face-recursive counterpart to `hyperplaneArrangementFamily_commonFace_tasks_at`:
the inherited seam data must descend through proper exposed faces even when the fiber dimension is
already zero. -/
theorem hyperplaneArrangementFamily_commonEndpoint_tasks_at [CompleteSpace E]
    [DecidableEq E] [FiniteDimensional ℝ E] {ι : Type*} {m : ℕ}
    {T : Finset E} {x : E}
    (k : ι) (j : Fin (m + 2)) (cells : Finset (ProperCone ℝ E))
    (hCells : ∀ C ∈ cells, C ∈ hyperplaneArrangementFamily T)
    (hxCells : ∀ C ∈ cells, x ∈ (C : Set E)) :
    ∃ G ∈ hyperplaneArrangementFamily T, x ∈ (G : Set E) ∧
      ∀ C ∈ cells, (G : Set E) ⊆ (C : Set E) ∧ IsExposedFaceOf G C ∧
        (G ≠ C → OneBitFanFaceDependency (E := E) (ι := ι) (m := m)
          ((G, k), .endpoint j) ((C, k), .endpoint j)) := by
  obtain ⟨G, hG, hxG, hfaces⟩ :=
    hyperplaneArrangementFamily_commonFace_at cells hCells hxCells
  refine ⟨G, hG, hxG, ?_⟩
  intro C hC
  obtain ⟨hsubset, hface⟩ := hfaces C hC
  refine ⟨hsubset, hface, ?_⟩
  intro hne
  exact OneBitFanFaceDependency.fanFaceEndpoint C G k j hface hne

/-- Arrangement-cell intersections provide the actual exposed-face dependencies used by the
well-founded order. If the common cell is proper in either incident cell, its rank is strictly
smaller there; equal cells are the only zero-decrease case. -/
theorem hyperplaneArrangement_commonFace_rank_decrease [CompleteSpace E]
    [DecidableEq E] [FiniteDimensional ℝ E] {T : Finset E}
    {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T)
    (hD : D ∈ hyperplaneArrangementFamily T) :
    ∃ G ∈ hyperplaneArrangementFamily T,
      (G : Set E) = (C : Set E) ∩ (D : Set E) ∧
      IsExposedFaceOf G C ∧ IsExposedFaceOf G D ∧
      (G ≠ C → coneSpanRank G < coneSpanRank C) ∧
      (G ≠ D → coneSpanRank G < coneSpanRank D) := by
  obtain ⟨G, hG, hset, hGC, hGD⟩ :=
    hyperplaneArrangementFamily_inter_common hC hD
  refine ⟨G, hG, hset, hGC, hGD, ?_, ?_⟩
  · intro hne
    exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hGC hne
  · intro hne
    exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hGD hne

/-- Finite central arrangements satisfy the true common-face axiom, with each intersection exposed
from both incident cells. This is the face information required to transfer the local toric field
through a chamber wall. -/
theorem hyperplaneArrangementFamily_hasExposedCommonFaces [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : HasExposedCommonFaces (hyperplaneArrangementFamily T) := by
  intro C hC D hD
  exact hyperplaneArrangementFamily_inter_common hC hD

/-- A dual vector of a finite half-space sign cell is a finite nonnegative combination of its
normals. This finite Farkas representation identifies the active inequalities on an exposed face. -/
theorem signCell_dual_mem_hull [CompleteSpace E] [DecidableEq E]
    {T P N : Finset E} {a : E}
    (ha : a ∈ coneDual (signCell T P N : Set E)) :
    ∃ c : E →₀ ℝ, c.support ⊆ signCellNormals T P N ∧
      (∀ y, 0 ≤ c y) ∧ c.sum (fun i r => r • i) = a := by
  let S := signCellNormals T P N
  have ha' : a ∈ coneDual (coneDual (S : Set E) : Set E) := by
    simpa [signCell, S] using ha
  rw [coneDual_finset_dual_eq S] at ha'
  change a ∈ (properConeOfFinset S : Set E) at ha'
  rw [coe_properConeOfFinset] at ha'
  exact PointedCone.mem_hull_set.mp ha'

/-- Every exposed face of a sign cell is another sign cell: the finite Farkas representation of
the exposing normal shows that precisely its active signed inequalities become equalities. -/
theorem hyperplaneArrangementFamily_faces_mem [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : IsExposedFaceOf D C) :
    D ∈ hyperplaneArrangementFamily T := by
  classical
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  obtain ⟨a, ha, hset⟩ := hD
  have hDmem (x : E) :
      x ∈ D ↔ x ∈ exposedFace (signCell T P N : PointedCone ℝ E) a :=
    Iff.of_eq (congrArg (fun S : Set E => x ∈ S) hset)
  obtain ⟨c, hcsupp, hc0, hcsum⟩ := signCell_dual_mem_hull ha
  let A := c.support ∪ c.support.image (fun i => -i)
  let P0 := P.filter (fun i => i ∉ A)
  let N0 := N.filter (fun i => i ∉ A)
  have not_union {X Y : Finset E} {b : E} (hX : b ∉ X) (hY : b ∉ Y) :
      b ∉ X ∪ Y := by
    intro h
    rcases Finset.mem_union.mp h with hX' | hY'
    · exact hX hX'
    · exact hY hY'
  have hP0T : P0 ⊆ T := (Finset.filter_subset _ _).trans hPT
  have hN0T : N0 ⊆ T := (Finset.filter_subset _ _).trans hNT
  have hP0N0 : Disjoint P0 N0 := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    exact (Finset.disjoint_left.mp hPN) (Finset.filter_subset _ _ hiP)
      (Finset.filter_subset _ _ hiN)
  have hDfamily : signCell T P0 N0 ∈ hyperplaneArrangementFamily T :=
    mem_hyperplaneArrangementFamily_iff.mpr ⟨P0, N0, hP0T, hN0T, hP0N0, rfl⟩
  have hInnerSum (x : E) :
      ⟪a, x⟫_ℝ = ∑ i ∈ c.support, c i * ⟪i, x⟫_ℝ := by
    rw [← hcsum]
    simp [Finsupp.sum, sum_inner, real_inner_smul_left]
  have hCoeffZero (x : E) (hxD : x ∈ D) (i : E) (hi : i ∈ c.support) :
      ⟪i, x⟫_ℝ = 0 := by
    have hxFace := (hDmem x).mp hxD
    have hxC : x ∈ signCell T P N := (mem_exposedFace.mp hxFace).1
    have haZero : ⟪a, x⟫_ℝ = 0 := (mem_exposedFace.mp hxFace).2
    change x ∈ coneDual (signCellNormals T P N : Set E) at hxC
    have htermNonneg : ∀ j ∈ c.support, 0 ≤ c j * ⟪j, x⟫_ℝ := by
      intro j hj
      exact mul_nonneg (hc0 j)
        ((mem_coneDual.mp hxC) (hcsupp hj))
    have hsumZero : (∑ j ∈ c.support, c j * ⟪j, x⟫_ℝ) = 0 := by
      calc
        _ = ⟪a, x⟫_ℝ := (hInnerSum x).symm
        _ = 0 := haZero
    have htermZero := (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp hsumZero i hi
    have hci : c i ≠ 0 := by
      simpa only [Finsupp.mem_support_iff] using hi
    rcases mul_eq_zero.mp htermZero with hciZero | hiZero
    · exact (hci hciZero).elim
    · exact hiZero
  have hActiveZero (x : E) (hxD : x ∈ D) : ∀ b ∈ A, ⟪b, x⟫_ℝ = 0 := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hCoeffZero x hxD b hb
    · rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
      rw [inner_neg_left, hCoeffZero x hxD i hi]
      simp
  have hDmemCell (x : E) : x ∈ D ↔ x ∈ signCell T P0 N0 := by
    constructor
    · intro hxD
      have hxFace := (hDmem x).mp hxD
      have hxC : x ∈ signCell T P N := (mem_exposedFace.mp hxFace).1
      rcases mem_signCell.mp hxC with ⟨hP, hN, hZ⟩
      have hAzero := hActiveZero x hxD
      apply mem_signCell.mpr
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        exact hP b (Finset.filter_subset _ _ hb)
      · intro b hb
        exact hN b (Finset.filter_subset _ _ hb)
      · intro b hb
        have hbT : b ∈ T := (Finset.mem_sdiff.mp hb).1
        have hbNot := (Finset.mem_sdiff.mp hb).2
        have hbP0 : b ∉ P0 := fun h => hbNot (Finset.mem_union.mpr (Or.inl h))
        have hbN0 : b ∉ N0 := fun h => hbNot (Finset.mem_union.mpr (Or.inr h))
        by_cases hbP : b ∈ P
        · have hbA : b ∈ A := by
            by_contra hnotA
            exact hbP0 (Finset.mem_filter.mpr ⟨hbP, hnotA⟩)
          exact hAzero b hbA
        · by_cases hbN : b ∈ N
          · have hbA : b ∈ A := by
              by_contra hnotA
              exact hbN0 (Finset.mem_filter.mpr ⟨hbN, hnotA⟩)
            exact hAzero b hbA
          · exact hZ b (Finset.mem_sdiff.mpr ⟨hbT, not_union hbP hbN⟩)
    · intro hxCell
      rcases mem_signCell.mp hxCell with ⟨hP0, hN0, hZ0⟩
      have hGenZero (i : E) (hi : i ∈ c.support) : ⟪i, x⟫_ℝ = 0 := by
        have hiS : i ∈ signCellNormals T P N := hcsupp hi
        simp [signCellNormals] at hiS
        rcases hiS with hp | hn | hz | hzneg
        · have hiA : i ∈ A := Finset.mem_union.mpr (Or.inl hi)
          have hiP0 : i ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          have hiN0 : i ∉ N0 := by
            intro h
            exact (Finset.disjoint_left.mp hPN) hp
              (Finset.filter_subset _ _ h)
          exact hZ0 i (Finset.mem_sdiff.mpr
            ⟨hPT hp, not_union hiP0 hiN0⟩)
        · rcases hn with ⟨b, hb, rfl⟩
          have hbA : b ∈ A := by
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_image.mpr
            exact ⟨-b, hi, by simp⟩
          have hbP0 : b ∉ P0 := by
            intro h
            exact (Finset.disjoint_left.mp hPN) (Finset.filter_subset _ _ h) hb
          have hbN0 : b ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hz := hZ0 b (Finset.mem_sdiff.mpr
            ⟨hNT hb, not_union hbP0 hbN0⟩)
          simpa [inner_neg_left] using hz
        · have hiA : i ∈ A := Finset.mem_union.mpr (Or.inl hi)
          have hiP0 : i ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          have hiN0 : i ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hiA
          exact hZ0 i (Finset.mem_sdiff.mpr
            ⟨hz.1, not_union hiP0 hiN0⟩)
        · rcases hzneg with ⟨b, hb, rfl⟩
          have hbA : b ∈ A := by
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_image.mpr
            exact ⟨-b, hi, by simp⟩
          have hbP0 : b ∉ P0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hbN0 : b ∉ N0 := by
            intro h
            exact (Finset.mem_filter.mp h).2 hbA
          have hz := hZ0 b (Finset.mem_sdiff.mpr
            ⟨hb.1, not_union hbP0 hbN0⟩)
          simpa [inner_neg_left] using hz
      have hA0 : ∀ b ∈ A, ⟪b, x⟫_ℝ = 0 := by
        intro b hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact hGenZero b hb
        · rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
          rw [inner_neg_left, hGenZero i hi]
          simp
      have hxC : x ∈ signCell T P N := by
        apply mem_signCell.mpr
        refine ⟨?_, ?_, ?_⟩
        · intro b hb
          by_cases hbA : b ∈ A
          · rw [hA0 b hbA]
          · exact hP0 b (Finset.mem_filter.mpr ⟨hb, hbA⟩)
        · intro b hb
          by_cases hbA : b ∈ A
          · rw [inner_neg_left, hA0 b hbA]
            simp
          · exact hN0 b (Finset.mem_filter.mpr ⟨hb, hbA⟩)
        · intro b hb
          have hbT : b ∈ T := (Finset.mem_sdiff.mp hb).1
          have hbNot := (Finset.mem_sdiff.mp hb).2
          have hbP0 : b ∉ P0 := by
            intro h
            exact hbNot (Finset.mem_union.mpr (Or.inl (Finset.filter_subset _ _ h)))
          have hbN0 : b ∉ N0 := by
            intro h
            exact hbNot (Finset.mem_union.mpr (Or.inr (Finset.filter_subset _ _ h)))
          exact hZ0 b (Finset.mem_sdiff.mpr
            ⟨hbT, not_union hbP0 hbN0⟩)
      have hsumZero : (∑ i ∈ c.support, c i * ⟪i, x⟫_ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hGenZero i hi]
        simp
      have haZero : ⟪a, x⟫_ℝ = 0 := by
        rw [hInnerSum x, hsumZero]
      have hxFace : x ∈ exposedFace (signCell T P N : PointedCone ℝ E) a :=
        mem_exposedFace.mpr ⟨hxC, haZero⟩
      exact (hDmem x).mpr hxFace
  have hEq : D = signCell T P0 N0 := by
    apply ProperCone.ext
    intro x
    exact hDmemCell x
  exact mem_hyperplaneArrangementFamily_iff.mpr
    ⟨P0, N0, hP0T, hN0T, hP0N0, hEq⟩


/-- Finite central hyperplane arrangements form a complete polyhedral fan. -/
theorem hyperplaneArrangementFamily_isPolyhedralFan [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : IsPolyhedralFan (hyperplaneArrangementFamily T) where
  faces_mem := fun _ hC _ hD => hyperplaneArrangementFamily_faces_mem hC hD
  inter_common := by
    intro C hC D hD
    obtain ⟨G, hG, hcommon, _, _⟩ := hyperplaneArrangementFamily_inter_common hC hD
    exact ⟨G, hG, hcommon⟩
  covers := hyperplaneArrangementFamily_covers T

/-- Distinct cells of a central hyperplane arrangement have disjoint ordinary interiors. -/
theorem hyperplaneArrangementFamily_interiors_disjoint [CompleteSpace E] [DecidableEq E]
    {T : Finset E} {C D : ProperCone ℝ E}
    (hC : C ∈ hyperplaneArrangementFamily T) (hD : D ∈ hyperplaneArrangementFamily T)
    (hne : C ≠ D) :
    interior (C : Set E) ∩ interior (D : Set E) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hne (hyperplaneArrangementFamily_eq_of_interiors_intersect hC hD hx.1 hx.2)

/-- Every sign cell in a finite central hyperplane arrangement has a finite half-space
representation, using the signed arrangement normals themselves. -/
theorem hyperplaneArrangementFamily_hasDualFGCells [CompleteSpace E] [DecidableEq E]
    (T : Finset E) : HasDualFGCells (hyperplaneArrangementFamily T) := by
  classical
  intro C hC
  obtain ⟨P, N, _, _, _, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hC
  change (PointedCone.dual (innerₗ E) (signCellNormals T P N : Set E)).DualFG (innerₗ E)
  exact PointedCone.DualFG.dual_of_finset (innerₗ E) (signCellNormals T P N)

/-- Choose a point in a finite-dual cone that is strict on every inequality that can be strict.
The witness is the sum of one point witnessing each such inequality. -/
theorem exists_strict_point_for_finite_dual [CompleteSpace E] [DecidableEq E]
    (S : Finset E) :
    ∃ x ∈ coneDual (S : Set E), ∀ v ∈ S,
      (∃ y, y ∈ coneDual (S : Set E) ∧ 0 < ⟪v, y⟫_ℝ) →
        0 < ⟪v, x⟫_ℝ := by
  classical
  let D := coneDual (S : Set E)
  let P := S.filter (fun v => ∃ y, y ∈ D ∧ 0 < ⟪v, y⟫_ℝ)
  have hWitness (v : E) (hv : v ∈ P) : ∃ y, y ∈ D ∧ 0 < ⟪v, y⟫_ℝ :=
    (Finset.mem_filter.mp hv).2
  let w : E → E := fun v =>
    if hv : v ∈ P then Classical.choose (hWitness v hv) else 0
  have hw (v : E) (hv : v ∈ P) : w v ∈ D ∧ 0 < ⟪v, w v⟫_ℝ := by
    dsimp [w]
    rw [dite_eq_left hv]
    exact Classical.choose_spec (hWitness v hv)
  let x := ∑ v ∈ P, w v
  have hx : x ∈ D := by
    change x ∈ coneDual (S : Set E)
    apply Submodule.sum_mem
    intro v hv
    exact (hw v hv).1
  refine ⟨x, hx, ?_⟩
  intro v hv hpositive
  have hvP : v ∈ P := Finset.mem_filter.mpr ⟨hv, hpositive⟩
  have hsum : ⟪v, x⟫_ℝ = ∑ u ∈ P, ⟪v, w u⟫_ℝ := by
    simp [x, inner_sum]
  have hterms : ∀ u ∈ P, 0 ≤ ⟪v, w u⟫_ℝ := by
    intro u hu
    exact (mem_coneDual.mp (hw u hu).1) hv
  have hle := Finset.single_le_sum hterms hvP
  rw [hsum]
  exact lt_of_lt_of_le (hw v hvP).2 hle

/-- Collect one finite half-space representation for every cell in a finite fan. -/
noncomputable def fanNormalSet [CompleteSpace E] [DecidableEq E]
    (F : Fan E) (hF : HasDualFGCells F) : Finset E := by
  classical
  exact F.attach.biUnion (fun C => Classical.choose (hF C.1 C.2))

theorem mem_fanNormalSet [CompleteSpace E] [DecidableEq E]
    {F : Fan E} {hF : HasDualFGCells F} {C : ProperCone ℝ E}
    (hC : C ∈ F) {s : E} (hs : s ∈ Classical.choose (hF C hC)) :
    s ∈ fanNormalSet F hF := by
  classical
  change s ∈ F.attach.biUnion (fun C => Classical.choose (hF C.1 C.2))
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨C, hC⟩, Finset.mem_attach _ _, hs⟩

/-- The central arrangement of all finite half-space normals of a covering cone family refines that
family. The proof needs coverage, but not the fan intersection axioms: a cell chooses a point strict
on every inequality that can be strict, and a member cone containing that point contains the whole
cell. -/
theorem hyperplaneArrangementFamily_refines_of_covering_dualFG [CompleteSpace E] [DecidableEq E]
    {F : Fan E} (hCover : (⋃ C ∈ F, (C : Set E)) = Set.univ)
    (hFdual : HasDualFGCells F) :
    Refines (hyperplaneArrangementFamily (fanNormalSet F hFdual)) F := by
  classical
  let T := fanNormalSet F hFdual
  intro D hD
  obtain ⟨P, N, hPT, hNT, hPN, rfl⟩ := mem_hyperplaneArrangementFamily_iff.mp hD
  let S := signCellNormals T P N
  obtain ⟨x₀, hx₀, hstrict⟩ := exists_strict_point_for_finite_dual S
  have hx₀cell : x₀ ∈ signCell T P N := by
    change x₀ ∈ coneDual (S : Set E)
    exact hx₀
  have hsign₀ := mem_signCell.mp hx₀cell
  have hx₀cover : x₀ ∈ ⋃ C ∈ F, (C : Set E) := by
    rw [hCover]
    simp
  rcases Set.mem_iUnion.mp hx₀cover with ⟨C, hCmem⟩
  rcases Set.mem_iUnion.mp hCmem with ⟨hCF, hx₀C⟩
  let R := Classical.choose (hFdual C hCF)
  have hRrep : (coneDual (R : Set E) : Set E) = (C : Set E) := by
    have hpoint :
        (coneDual (R : Set E) : PointedCone ℝ E) = (C : PointedCone ℝ E) := by
      change PointedCone.dual (innerₗ E) (R : Set E) = (C : PointedCone ℝ E)
      exact Classical.choose_spec (hFdual C hCF)
    exact congrArg (fun K : PointedCone ℝ E => (K : Set E)) hpoint
  have hRsubT : ∀ s ∈ R, s ∈ T := by
    intro s hs
    exact mem_fanNormalSet hCF hs
  have hx₀R : ∀ s ∈ R, 0 ≤ ⟪s, x₀⟫_ℝ := by
    intro s hs
    have hx₀' : x₀ ∈ (coneDual (R : Set E) : Set E) := by
      rw [hRrep]
      exact hx₀C
    exact (mem_coneDual.mp hx₀') hs
  have hcell_subset : (signCell T P N : Set E) ⊆ (C : Set E) := by
    intro y hy
    have hyS : y ∈ coneDual (S : Set E) := by
      change y ∈ signCell T P N
      exact hy
    rcases mem_signCell.mp hy with ⟨hP, hN, hZ⟩
    have hyR : y ∈ coneDual (R : Set E) := by
      apply mem_coneDual.mpr
      intro s hs
      have hsT : s ∈ T := hRsubT s hs
      by_cases hsP : s ∈ P
      · exact hP s hsP
      · by_cases hsN : s ∈ N
        · have hnegS : -s ∈ S := by
            simp [S, signCellNormals, hsT, hsN]
          have hx₀Neg : ⟪-s, x₀⟫_ℝ = 0 := by
            have hnonneg := hx₀R s hs
            have hnonpos : ⟪s, x₀⟫_ℝ ≤ 0 := by
              have h := hsign₀.2.1 s hsN
              simpa [inner_neg_left] using h
            have hzero : ⟪s, x₀⟫_ℝ = 0 := le_antisymm hnonpos hnonneg
            simpa [inner_neg_left] using hzero
          have hnoPos : ¬ ∃ z, z ∈ signCell T P N ∧ 0 < ⟪-s, z⟫_ℝ := by
            intro hex
            have hpos := hstrict (-s) hnegS hex
            exact (ne_of_gt hpos) hx₀Neg
          have hyNeg : ⟪-s, y⟫_ℝ = 0 := by
            have hnonneg : 0 ≤ ⟪-s, y⟫_ℝ := (mem_coneDual.mp hyS) hnegS
            have hnotpos : ¬ 0 < ⟪-s, y⟫_ℝ := by
              intro hpos
              exact hnoPos ⟨y, hy, hpos⟩
            linarith
          have hyzero : ⟪s, y⟫_ℝ = 0 := by
            simpa [inner_neg_left] using hyNeg
          rw [hyzero]
        · have hz := hZ s (Finset.mem_sdiff.mpr
            ⟨hsT, by
              intro h
              rcases Finset.mem_union.mp h with hp | hn
              · exact hsP hp
              · exact hsN hn⟩)
          rw [hz]
    rw [← hRrep]
    exact hyR
  exact ⟨C, hCF, hcell_subset⟩

/-- The central arrangement of a covering polyhedral fan's finite dual normals refines the fan. -/
theorem hyperplaneArrangementFamily_refines_of_dualFG [CompleteSpace E] [DecidableEq E]
    {F : Fan E} (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F) :
    Refines (hyperplaneArrangementFamily (fanNormalSet F hFdual)) F :=
  hyperplaneArrangementFamily_refines_of_covering_dualFG hF.covers hFdual

/-- Construct compact, overlap-compatible local patches by cutting a compact seam with the central
hyperplane arrangement of all finite dual normals of a complete polyhedral fan. Each fine patch is
contained in a coarse fan cell, so its normal constraints inherit the coarse toric label. -/
theorem compactSet_hyperplaneArrangement_patchCover [CompleteSpace E] [DecidableEq E]
    (K : Set E) (hK : IsCompact K) {F : Fan E}
    (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F) :
    (∀ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
      IsCompact (K ∩ (C : Set E))) ∧
      K = ⋃ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
        K ∩ (C : Set E) ∧
      (∀ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
        ∃ D ∈ F, (K ∩ (C : Set E)) ⊆ (D : Set E)) ∧
      (∀ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
        ∀ D ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
          ∃ G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
            (K ∩ (C : Set E)) ∩ (K ∩ (D : Set E)) = K ∩ (G : Set E)) ∧
      (∀ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
        ∀ D ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual), C ≠ D →
          interior (K ∩ (C : Set E)) ∩ interior (K ∩ (D : Set E)) = ∅) := by
  let fine : Fan E := hyperplaneArrangementFamily (fanNormalSet F hFdual)
  have hfine : IsPolyhedralFan fine :=
    hyperplaneArrangementFamily_isPolyhedralFan (fanNormalSet F hFdual)
  have href : Refines fine F :=
    hyperplaneArrangementFamily_refines_of_dualFG hF hFdual
  have hcover := compactSet_fanRefinement_patchCover K hK href hfine
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    exact hcover.1 C hC
  · simpa [fine] using hcover.2.1
  · intro C hC
    exact hcover.2.2 C hC
  · intro C hC D hD
    exact compactSet_fanRefinement_patch_intersection K hfine C D hC hD
  · intro C hC D hD hne
    have hCint : interior (K ∩ (C : Set E)) ⊆ interior (C : Set E) :=
      interior_mono Set.inter_subset_right
    have hDint : interior (K ∩ (D : Set E)) ⊆ interior (D : Set E) :=
      interior_mono Set.inter_subset_right
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hx' : x ∈ interior (C : Set E) ∩ interior (D : Set E) :=
      ⟨hCint hx.1, hDint hx.2⟩
    rw [hyperplaneArrangementFamily_interiors_disjoint hC hD hne] at hx'
    simpa using hx'

/-- A lower-dimensional base tile cut out by a fan arrangement, expressed in the coordinate
function space used by the one-bit fiber blueprint. The arrangement itself lives in
`EuclideanSpace`, where the fan's inner-product geometry is available; `EuclideanSpace.equiv`
transports its cells to the coordinate chart without changing their topology. -/
def euclideanHyperplaneArrangementBaseTile {n : ℕ}
    (base : Set (Fin n → ℝ)) (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hFdual : HasDualFGCells F) :
    {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} → Set (Fin n → ℝ) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  exact fun C => e '' (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n))))

/-- The coordinate-space tile cut out by an arbitrary proper cone, before restricting its label
to the finite arrangement family. Keeping this untagged form lets the well-founded face task
retain its geometric output at every predecessor. -/
def euclideanProperConeBaseTile {n : ℕ} (base : Set (Fin n → ℝ))
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) : Set (Fin n → ℝ) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  exact e '' (baseE ∩ (C : Set (EuclideanSpace ℝ (Fin n))))

/-- Exposed-face incidence gives genuine nesting of the untagged projected cone tiles. -/
theorem euclideanProperConeBaseTile_mono {n : ℕ}
    (base : Set (Fin n → ℝ)) {G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))}
    (hsubset : (G : Set (EuclideanSpace ℝ (Fin n))) ⊆ C) :
    euclideanProperConeBaseTile base G ⊆ euclideanProperConeBaseTile base C := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  change e '' (baseE ∩ (G : Set (EuclideanSpace ℝ (Fin n)))) ⊆
    e '' (baseE ∩ (C : Set (EuclideanSpace ℝ (Fin n))))
  apply Set.image_mono
  intro x hx
  exact ⟨hx.1, hsubset hx.2⟩

/-- Projected cone/small-tile patch for a pair label, used for the exact common seam of two
incident small tiles. -/
def euclideanProperConeSmallTilePairBaseTile {n : ℕ} {ι : Type*}
    (base : Set (Fin n → ℝ)) (smallTile : ι → Set (Fin n → ℝ)) :
    ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × (ι × ι) → Set (Fin n → ℝ) :=
  fun p => euclideanProperConeBaseTile base p.1 ∩
    (smallTile p.2.1 ∩ smallTile p.2.2)

/-- Single-tile strip labels and pair-labelled seam labels in one common task base family. -/
def euclideanProperConeMixedTileBaseTile {n : ℕ} {ι : Type*}
    (base : Set (Fin n → ℝ)) (smallTile : ι → Set (Fin n → ℝ)) :
    ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × Sum ι (ι × ι) → Set (Fin n → ℝ)
  | (C, .inl i) => euclideanProperConeBaseTile base C ∩ smallTile i
  | (C, .inr (i, j)) => euclideanProperConeBaseTile base C ∩ (smallTile i ∩ smallTile j)

/-- The underlying set of an exposed face lies in its parent cone. -/
theorem properCone_subset_of_isExposedFaceOf {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G C : ProperCone ℝ E} (hface : IsExposedFaceOf G C) :
    (G : Set E) ⊆ C := by
  rcases hface with ⟨a, ha, hfaceEq⟩
  intro x hx
  have hx' : x ∈ (exposedFace (C : PointedCone ℝ E) a : Set E) := by
    rw [← hfaceEq]
    exact hx
  exact exposedFace_subset (C : PointedCone ℝ E) a hx'

/-- Specialization of the patch monotonicity theorem to the projected cone arrangement crossed
with a small blueprint tile. Thus every exposed-face predecessor has its actual strip or endpoint
patch contained in the corresponding parent patch, with the projected small-tile label fixed. -/
theorem euclideanArrangementTaskPatch_mono_of_commonFace {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ)) (base : Set (Fin n → ℝ))
    (smallTile : ι → Set (Fin n → ℝ)) (lower upper : (Fin n → ℝ) → ℝ)
    (G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (k : ι)
    (hface : IsExposedFaceOf G C) (cell : OneBitFiberCell m) :
    oneBitFanFaceTaskPatch facePatch
        (fun p : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι =>
          euclideanProperConeBaseTile base p.1 ∩ smallTile p.2)
        lower upper ((G, k), cell) ⊆
      oneBitFanFaceTaskPatch facePatch
        (fun p : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι =>
          euclideanProperConeBaseTile base p.1 ∩ smallTile p.2)
        lower upper ((C, k), cell) := by
  apply oneBitFanFaceTaskPatch_mono_of_commonFace facePatch _ lower upper ?_ G C k hface cell
  intro G C hface k
  exact Set.inter_subset_inter
    (euclideanProperConeBaseTile_mono base (properCone_subset_of_isExposedFaceOf hface))
    (fun _ hx => hx)

/-- Every endpoint graph lies in either adjacent closed strip. -/
theorem projectionFiberSubdivisionEndpointGraphPoint_mem_adjacentTile {n m : ℕ}
    (base : Set (Fin n → ℝ)) (lower upper : (Fin n → ℝ) → ℝ)
    (horder : ∀ y ∈ base, lower y ≤ upper y) (i : Fin (m + 1))
    (j : Fin (m + 2)) (hadjacent : j = i.castSucc ∨ j = i.succ)
    (y : Fin n → ℝ) (hy : y ∈ base) :
    projectionFiberSubdivisionEndpointGraphPoint lower upper j y ∈
      projectionFiberSubdivisionTile base lower upper i := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) y
    (projectionFiberSubdivisionEndpoint lower upper j y) ∈ _
  rw [mem_projectionFiberSubdivisionTile_snoc_iff]
  refine ⟨hy, ?_, ?_⟩
  · rcases hadjacent with hleft | hright
    · rw [hleft]
    · rw [hright]
      have hmono := tileScaleInterpolation_monotone_of_le (m := m) (horder y hy)
      have hindex : i.castSucc ≤ i.succ := by
        apply Fin.le_iff_val_le_val.mpr
        simp
      simpa [projectionFiberSubdivisionEndpoint] using hmono hindex
  · rcases hadjacent with hleft | hright
    · rw [hleft]
      have hmono := tileScaleInterpolation_monotone_of_le (m := m) (horder y hy)
      have hindex : i.castSucc ≤ i.succ := by
        apply Fin.le_iff_val_le_val.mpr
        simp
      simpa [projectionFiberSubdivisionEndpoint] using hmono hindex
    · rw [hright]

/-- A pair-labelled common seam output is contained in the left incident strip output. The
projected face inclusion and the first small-tile factor provide the required base inclusion. -/
theorem fanSmallTilePairEndpointTaskPatch_subset_leftStrip {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ)) (base : Set (Fin n → ℝ))
    (smallTile : ι → Set (Fin n → ℝ)) (lower upper : (Fin n → ℝ) → ℝ)
    (G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (i j : ι)
    (endpoint : Fin (m + 2)) (strip : Fin (m + 1))
    (hface : IsExposedFaceOf G C)
    (hadjacent : endpoint = strip.castSucc ∨ endpoint = strip.succ)
    (horder : ∀ y ∈ euclideanProperConeBaseTile base C ∩ smallTile i,
      lower y ≤ upper y) :
    oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((G, Sum.inr (i, j)), .endpoint endpoint) ⊆
      oneBitFanFaceTaskPatch facePatch (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((C, Sum.inl i), .strip strip) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with ⟨y, hy, rfl⟩
  change y ∈ euclideanProperConeBaseTile base G ∩ (smallTile i ∩ smallTile j) at hy
  apply projectionFiberSubdivisionEndpointGraphPoint_mem_adjacentTile
    (euclideanProperConeBaseTile base C ∩ smallTile i) lower upper horder strip endpoint
    hadjacent y
  exact ⟨euclideanProperConeBaseTile_mono base
    (properCone_subset_of_isExposedFaceOf hface) hy.1, hy.2.1⟩

/-- The same common seam output lies in the right incident strip output. -/
theorem fanSmallTilePairEndpointTaskPatch_subset_rightStrip {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ)) (base : Set (Fin n → ℝ))
    (smallTile : ι → Set (Fin n → ℝ)) (lower upper : (Fin n → ℝ) → ℝ)
    (G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (i j : ι)
    (endpoint : Fin (m + 2)) (strip : Fin (m + 1))
    (hface : IsExposedFaceOf G C)
    (hadjacent : endpoint = strip.castSucc ∨ endpoint = strip.succ)
    (horder : ∀ y ∈ euclideanProperConeBaseTile base C ∩ smallTile j,
      lower y ≤ upper y) :
    oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((G, Sum.inr (i, j)), .endpoint endpoint) ⊆
      oneBitFanFaceTaskPatch facePatch (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((C, Sum.inl j), .strip strip) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with ⟨y, hy, rfl⟩
  change y ∈ euclideanProperConeBaseTile base G ∩ (smallTile i ∩ smallTile j) at hy
  apply projectionFiberSubdivisionEndpointGraphPoint_mem_adjacentTile
    (euclideanProperConeBaseTile base C ∩ smallTile j) lower upper horder strip endpoint
    hadjacent y
  exact ⟨euclideanProperConeBaseTile_mono base
    (properCone_subset_of_isExposedFaceOf hface) hy.1, hy.2.2⟩

/-- A fiber-endpoint dependency gives inclusion of the actual endpoint task patch in its incident
strip patch, provided projected face tiles are nested. -/
theorem oneBitFanFaceTaskPatch_mono_of_fiberEndpoint {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ))
    (baseTile : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι → Set (Fin n → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (hbaseTile : ∀ {G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))},
      IsExposedFaceOf G C → ∀ k, baseTile (G, k) ⊆ baseTile (C, k))
    (G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (k : ι)
    (i : Fin (m + 1)) (j : Fin (m + 2)) (hface : IsExposedFaceOf G C)
    (hadjacent : j = i.castSucc ∨ j = i.succ)
    (horder : ∀ y ∈ baseTile (C, k), lower y ≤ upper y) :
    oneBitFanFaceTaskPatch facePatch baseTile lower upper ((G, k), .endpoint j) ⊆
      oneBitFanFaceTaskPatch facePatch baseTile lower upper ((C, k), .strip i) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with ⟨y, hy, rfl⟩
  exact projectionFiberSubdivisionEndpointGraphPoint_mem_adjacentTile
    (baseTile (C, k)) lower upper horder i j hadjacent y (hbaseTile hface k hy)

/-- Every edge of the well-founded task relation carries an inclusion between its concrete
geometric outputs. Face edges use projected-tile nesting; endpoint edges use the shared closed
fiber subdivision. -/
theorem oneBitFanFaceDependency.taskPatch_subset {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ))
    (baseTile : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι → Set (Fin n → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (hbaseTile : ∀ {G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))},
      IsExposedFaceOf G C → ∀ k, baseTile (G, k) ⊆ baseTile (C, k))
    (horder : ∀ C k y, y ∈ baseTile (C, k) → lower y ≤ upper y)
    {predecessor task : OneBitFanFaceTask (EuclideanSpace ℝ (Fin n)) ι m}
    (hdep : OneBitFanFaceDependency predecessor task) :
    oneBitFanFaceTaskPatch facePatch baseTile lower upper predecessor ⊆
      oneBitFanFaceTaskPatch facePatch baseTile lower upper task := by
  cases hdep with
  | fanFace C G k i hface hne =>
      exact oneBitFanFaceTaskPatch_mono_of_commonFace facePatch baseTile lower upper
        hbaseTile G C k hface (.strip i)
  | fanFaceEndpoint C G k j hface hne =>
      exact oneBitFanFaceTaskPatch_mono_of_commonFace facePatch baseTile lower upper
        hbaseTile G C k hface (.endpoint j)
  | fiberEndpoint C G k i j hface hadjacent =>
      exact oneBitFanFaceTaskPatch_mono_of_fiberEndpoint facePatch baseTile lower upper
        hbaseTile G C k i j hface hadjacent (horder C k)

/-- Every edge in the mixed product-seam recursion is still an inclusion between the concrete
patches: inherited edges use the ordinary face/fiber proof, while pair-labelled seam edges use
the actual adjacent-strip endpoint containment. -/
theorem oneBitFanFaceSeamDependency.taskPatch_subset {n m : ℕ} {ι : Type*}
    (facePatch : Set (Fin (n + 1) → ℝ))
    (base : Set (Fin n → ℝ)) (smallTile : ι → Set (Fin n → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (horder : ∀ C label y, y ∈ euclideanProperConeMixedTileBaseTile base smallTile
      (C, label) → lower y ≤ upper y)
    {predecessor task : OneBitFanFaceTask
      (EuclideanSpace ℝ (Fin n)) (Sum ι (ι × ι)) m}
    (hdep : OneBitFanFaceSeamDependency predecessor task) :
    oneBitFanFaceTaskPatch facePatch (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper predecessor ⊆
      oneBitFanFaceTaskPatch facePatch (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper task := by
  have hbaseTile : ∀ {G C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))},
      IsExposedFaceOf G C → ∀ label,
        euclideanProperConeMixedTileBaseTile base smallTile (G, label) ⊆
          euclideanProperConeMixedTileBaseTile base smallTile (C, label) := by
    intro G C hface label
    cases label with
    | inl i =>
        exact Set.inter_subset_inter
          (euclideanProperConeBaseTile_mono base
            (properCone_subset_of_isExposedFaceOf hface)) (fun _ hx => hx)
    | inr ij =>
        exact Set.inter_subset_inter
          (euclideanProperConeBaseTile_mono base
            (properCone_subset_of_isExposedFaceOf hface)) (fun _ hx => hx)
  cases hdep with
  | inherited hdep =>
      exact oneBitFanFaceDependency.taskPatch_subset facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile) lower upper
        hbaseTile (fun C label y hy => horder C label y hy) hdep
  | productSeamLeft C G i j k endpoint hface hadjacent =>
      exact fanSmallTilePairEndpointTaskPatch_subset_leftStrip facePatch base smallTile
        lower upper G C i j endpoint k hface hadjacent
        (fun y hy => horder C (Sum.inl i) y hy)
  | productSeamRight C G i j k endpoint hface hadjacent =>
      exact fanSmallTilePairEndpointTaskPatch_subset_rightStrip facePatch base smallTile
        lower upper G C i j endpoint k hface hadjacent
        (fun y hy => horder C (Sum.inl j) y hy)

/-- A compact one-bit cover is exactly covered by its face-task strip outputs whenever its base
labels are realized by the corresponding projected cone/small-tile patches. This connects the
recursive task geometry to the actual finite blueprint cover. -/
theorem compactOneBitFiberPatchCover_taskPatch_cover_of_baseTile_eq {n : ℕ}
    {τ ι : Type*} [Fintype τ]
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {baseTile : τ → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ}
    (cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover
      facePatch base baseTile lower upper epsilon)
    (smallTile : ι → Set (Fin n → ℝ))
    (encode : τ → ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι)
    (hbaseTile : ∀ p, baseTile p =
      euclideanProperConeBaseTile base (encode p).1 ∩ smallTile (encode p).2) :
    facePatch = ⋃ p : Σ q : τ, Fin (cover.tiling.subdivisionCount + 1),
      oneBitFanFaceTaskPatch facePatch
        (fun q => euclideanProperConeBaseTile base q.1 ∩ smallTile q.2)
        lower upper ((encode p.1, .strip p.2)) := by
  calc
    facePatch = ⋃ p : Σ q : τ, Fin (cover.tiling.subdivisionCount + 1),
        facePatch ∩ projectionFiberSubdivisionTile (baseTile p.1) lower upper p.2 :=
      cover.facePatch_eq_iUnion_tiles
    _ = ⋃ p : Σ q : τ, Fin (cover.tiling.subdivisionCount + 1),
        oneBitFanFaceTaskPatch facePatch
          (fun q => euclideanProperConeBaseTile base q.1 ∩ smallTile q.2)
          lower upper ((encode p.1, .strip p.2)) := by
      apply Set.iUnion_congr
      rintro ⟨q, i⟩
      rw [hbaseTile q]
      rfl

/-- Arrangement atlas specialization of `taskPatch_cover_of_baseTile_eq`: the actual compact
fan/small-tile cover is indexed by arrangement cells, and its pieces are exactly the corresponding
one-bit face-task outputs. -/
theorem CompactOneBitFiberPatchCover.arrangementTaskPatch_cover {n : ℕ} {ι : Type*}
    [Fintype ι] {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {lower upper : (Fin n → ℝ) → ℝ} {epsilon : ℝ}
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (smallTile : ι → Set (Fin n → ℝ))
    (cover : ZeroSeparatingInduction.CompactOneBitFiberPatchCover facePatch base
      (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι =>
          euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩ smallTile p.2)
      lower upper epsilon) :
    facePatch = ⋃ p : Σ q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι,
        Fin (cover.tiling.subdivisionCount + 1),
      oneBitFanFaceTaskPatch facePatch
        (fun q : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) × ι =>
          euclideanProperConeBaseTile base q.1 ∩ smallTile q.2)
        lower upper ((p.1.1.1, p.1.2), .strip p.2) := by
  apply compactOneBitFiberPatchCover_taskPatch_cover_of_baseTile_eq
    cover smallTile (fun p => (p.1.1, p.2))
  intro p
  rfl

/-- A normal lying in an arrangement chamber labels the whole projected tile with a coarse fan
cell whose toric polar field points into the normal's half-space. The coordinate-space tile is
transported back to Euclidean coordinates only for its cone label; the inwardness statement is in
the inner-product space used by the toric differential inclusion. -/
theorem euclideanHyperplaneArrangementBaseTile_inward_normal_label {n : ℕ}
    (base : Set (Fin n → ℝ)) (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F)
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ (C.1 : Set _)) :
    ∃ D ∈ F,
      euclideanHyperplaneArrangementBaseTile base F hFdual C ⊆
        (EuclideanSpace.equiv (Fin n) ℝ) '' (D : Set (EuclideanSpace ℝ (Fin n))) ∧
      (coneDual (D : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) ⊆
        {w | 0 ≤ ⟪v, w⟫_ℝ} := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨D, hD, hCD⟩ :=
    hyperplaneArrangementFamily_refines_of_dualFG hF hFdual C.1 C.2
  refine ⟨D, hD, ?_, ?_⟩
  · intro x hx
    change x ∈ e '' (e.symm '' base ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hCD hy.2, rfl⟩
  · exact coneDual_subset_dualHalfPlane_of_mem (hCD hv)

/-- The intersection of two coordinate-transported arrangement base tiles is cut from their
actual common fan face, with the exposed-face certificates and rank drops retained for the
lexicographic fill order. -/
theorem euclideanHyperplaneArrangementBaseTile_intersection {n : ℕ}
    (base : Set (Fin n → ℝ)) (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hFdual : HasDualFGCells F)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)),
      euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
        euclideanHyperplaneArrangementBaseTile base F hFdual D =
          euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∧
      IsExposedFaceOf G C.1 ∧ IsExposedFaceOf G D.1 ∧
      (G ≠ C.1 → coneSpanRank G < coneSpanRank C.1) ∧
      (G ≠ D.1 → coneSpanRank G < coneSpanRank D.1) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  obtain ⟨G, hG, hcommon, hGC, hGD, hrankC, hrankD⟩ :=
    hyperplaneArrangement_commonFace_rank_decrease C.2 D.2
  have hmeet :
      (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) ∩
          (baseE ∩ (D.1 : Set (EuclideanSpace ℝ (Fin n)))) =
        baseE ∩ (G : Set (EuclideanSpace ℝ (Fin n)) ) := by
    ext x
    simp [hcommon, and_assoc, and_left_comm, and_comm]
  refine ⟨G, hG, ?_, hGC, hGD, hrankC, hrankD⟩
  change e '' (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) ∩
      e '' (baseE ∩ (D.1 : Set (EuclideanSpace ℝ (Fin n)))) =
    e '' (baseE ∩ (G : Set (EuclideanSpace ℝ (Fin n))))
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
    have hba : b = a := e.injective hab
    subst b
    have hcommonMem : a ∈
        (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) ∩
          (baseE ∩ (D.1 : Set (EuclideanSpace ℝ (Fin n)))) := ⟨ha, hb⟩
    have hmeetMem := congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) => a ∈ s) hmeet
    have hGmem : a ∈ baseE ∩ (G : Set (EuclideanSpace ℝ (Fin n))) :=
      hmeetMem.mp hcommonMem
    exact ⟨a, hGmem, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have hmeetMem := congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) => a ∈ s) hmeet
    have hcommonMem := hmeetMem.mpr ha
    exact ⟨⟨a, hcommonMem.1, rfl⟩, a, hcommonMem.2, rfl⟩

/-- Craciun v3, §7.4.3: neighboring one-bit strips above arrangement tiles meet on the endpoint
graph over their actual common lower-dimensional arrangement face. The returned face label carries
its exposed-face rank certificates, giving the lexicographic fill a well-founded geometric
dependency. -/
theorem euclideanHyperplaneArrangementBaseTiles_adjacentStrip_seam {n : ℕ}
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {lower upper : (Fin n → ℝ) → ℝ} {epsilon : ℝ}
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (cover : CompactOneBitFiberPatchCover facePatch base
      (euclideanHyperplaneArrangementBaseTile base F hFdual) lower upper epsilon)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)})
    (horder : ∀ y ∈
      euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
        euclideanHyperplaneArrangementBaseTile base F hFdual D,
      lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)),
      IsExposedFaceOf G C.1 ∧ IsExposedFaceOf G D.1 ∧
      (G ≠ C.1 → coneSpanRank G < coneSpanRank C.1) ∧
      (G ≠ D.1 → coneSpanRank G < coneSpanRank D.1) ∧
      (C.1 ≠ D.1 → ProperExposedFaceDependency G C.1 ∨
        ProperExposedFaceDependency G D.1) ∧
      (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual C) lower upper k.castSucc) ∩
        (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual D) lower upper k.succ) =
      facePatch ∩ (fun y : Fin n → ℝ =>
        projectionFiberSubdivisionEndpointGraphPoint lower upper k.succ.castSucc y) ''
          euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ := by
  obtain ⟨G, hG, hintersection, hGC, hGD, hrankC, hrankD⟩ :=
    euclideanHyperplaneArrangementBaseTile_intersection base F hFdual C D
  refine ⟨G, hG, hGC, hGD, hrankC, hrankD, ?_, ?_⟩
  · intro hCD
    by_cases hGC' : G = C.1
    · right
      constructor
      · simpa [hGC'] using hGD
      · intro hGD'
        apply hCD
        apply SetLike.coe_injective
        calc
          (C.1 : Set (EuclideanSpace ℝ (Fin n))) = G := by rw [hGC']
          _ = D.1 := congrArg (fun H : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) =>
            (H : Set (EuclideanSpace ℝ (Fin n)))) hGD'
    · left
      exact ⟨hGC, hGC'⟩
  · rw [← hintersection]
    exact cover.adjacent_base_tiles_share_seam C D horder k

/-- Every adjacent-strip seam in the arrangement cover is a strict dependency of both incident
strip tasks in the combined fan/one-bit face order. This also handles `C = D`: the endpoint graph
still has one less dimension than either interval strip. -/
theorem euclideanHyperplaneArrangementBaseTiles_adjacentStrip_seam_dependency
    {n : ℕ} {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {lower upper : (Fin n → ℝ) → ℝ} {epsilon : ℝ}
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (cover : CompactOneBitFiberPatchCover facePatch base
      (euclideanHyperplaneArrangementBaseTile base F hFdual) lower upper epsilon)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)})
    (horder : ∀ y ∈
      euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
        euclideanHyperplaneArrangementBaseTile base F hFdual D,
      lower y ≤ upper y)
    (k : Fin cover.tiling.subdivisionCount) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)),
      IsExposedFaceOf G C.1 ∧ IsExposedFaceOf G D.1 ∧
      OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := Unit)
        (m := cover.tiling.subdivisionCount)
        ((G, ()), .endpoint k.succ.castSucc) ((C.1, ()), .strip k.castSucc) ∧
      OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := Unit)
        (m := cover.tiling.subdivisionCount)
        ((G, ()), .endpoint k.succ.castSucc) ((D.1, ()), .strip k.succ) ∧
      (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual C) lower upper k.castSucc) ∩
        (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual D) lower upper k.succ) =
      facePatch ∩ (fun y : Fin n → ℝ =>
        projectionFiberSubdivisionEndpointGraphPoint lower upper k.succ.castSucc y) ''
          euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ := by
  obtain ⟨G, hG, hGC, hGD, _, _, _, hseam⟩ :=
    euclideanHyperplaneArrangementBaseTiles_adjacentStrip_seam F hFdual cover C D horder k
  have hindex : k.succ.castSucc = k.castSucc.succ := by
    apply Fin.ext
    simp
  refine ⟨G, hG, hGC, hGD, ?_, ?_, hseam⟩
  · exact OneBitFanFaceDependency.fiberEndpoint C.1 G () k.castSucc
      k.succ.castSucc hGC (Or.inr hindex)
  · exact OneBitFanFaceDependency.fiberEndpoint D.1 G () k.succ
      k.succ.castSucc hGD (Or.inl rfl)

/-- Craciun's one-bit fiber subdivision can be placed over the finite central arrangement of a
complete fan in Euclidean coordinates. This is the coordinate bridge between the fan-label
refinement and the projected-base tiles of §7.4.3: the tiles cover the original base, are compact
with disjoint interiors, and each retains a containing coarse-fan cell label. -/
theorem exists_compactOneBitFiberPatchCover_of_euclideanHyperplaneArrangement {n : ℕ}
    (facePatch : Set (Fin (n + 1) → ℝ)) (hfaceCompact : IsCompact facePatch)
    (base : Set (Fin n → ℝ)) (hbaseCompact : IsCompact base)
    (lower upper : (Fin n → ℝ) → ℝ) (epsilon : ℝ)
    (hlower : Continuous lower) (hupper : Continuous upper)
    (horder : ∀ y ∈ base, lower y ≤ upper y) (hepsilon : 0 < epsilon)
    (hfaceBand : facePatch ⊆
      projectionFiberBand base (fun y => some (lower y)) (fun y => some (upper y)))
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hF : IsPolyhedralFan F)
    (hFdual : HasDualFGCells F) :
    ∃ cover : CompactOneBitFiberPatchCover facePatch base
        (euclideanHyperplaneArrangementBaseTile base F hFdual) lower upper epsilon,
      ∀ C, ∃ D ∈ F,
        euclideanHyperplaneArrangementBaseTile base F hFdual C ⊆
          (EuclideanSpace.equiv (Fin n) ℝ) '' (D : Set (EuclideanSpace ℝ (Fin n))) ∧
        ∀ k : Fin (cover.tiling.subdivisionCount + 1),
          (facePatch ∩ projectionFiberSubdivisionTile
            (euclideanHyperplaneArrangementBaseTile base F hFdual C) lower upper k).Nonempty →
          ∃ x, x ∈ facePatch ∩ projectionFiberSubdivisionTile
              (euclideanHyperplaneArrangementBaseTile base F hFdual C) lower upper k ∧
            forgetLastCoordinate n x ∈
              (EuclideanSpace.equiv (Fin n) ℝ) '' (D : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let fine := hyperplaneArrangementFamily (fanNormalSet F hFdual)
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  let baseTile := euclideanHyperplaneArrangementBaseTile base F hFdual
  have hfine : IsPolyhedralFan fine :=
    hyperplaneArrangementFamily_isPolyhedralFan (fanNormalSet F hFdual)
  have hbaseEcompact : IsCompact baseE := hbaseCompact.image e.symm.continuous
  have hpatch := compactSet_hyperplaneArrangement_patchCover baseE hbaseEcompact hF hFdual
  rcases hpatch with ⟨hcompactTile, hcoverE, hcoarseLabel, _, hinteriors⟩
  have hfineCovers (y : EuclideanSpace ℝ (Fin n)) :
      y ∈ ⋃ C ∈ fine, (C : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hyperplaneArrangementFamily_covers (fanNormalSet F hFdual)]
    simp
  have hbaseCover : base = ⋃ C, baseTile C := by
    ext x
    constructor
    · intro hx
      have hy : e.symm x ∈ baseE := ⟨x, hx, rfl⟩
      have hy' : e.symm x ∈ ⋃ C ∈ fine, baseE ∩ (C : Set (EuclideanSpace ℝ (Fin n))) := by
        rcases Set.mem_iUnion.mp (hfineCovers (e.symm x)) with ⟨C, hC⟩
        rcases Set.mem_iUnion.mp hC with ⟨hC, hyC⟩
        exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC, ⟨hy, hyC⟩⟩⟩
      rcases Set.mem_iUnion.mp hy' with ⟨C, hC⟩
      rcases Set.mem_iUnion.mp hC with ⟨hC, hyC⟩
      refine Set.mem_iUnion.mpr ⟨⟨C, hC⟩, ?_⟩
      exact ⟨e.symm x, ⟨hy, hyC.2⟩, e.apply_symm_apply x⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨C, hxC⟩
      change x ∈ e '' (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) at hxC
      rcases hxC with ⟨y, hy, rfl⟩
      rcases hy.1 with ⟨z, hz, hzy⟩
      have heq : e y = z := by rw [← hzy, e.apply_symm_apply]
      rw [heq]
      exact hz
  have htileCompact : ∀ C, IsCompact (baseTile C) := by
    intro C
    change IsCompact (e '' (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))))
    exact (hcompactTile C.1 C.2).image e.continuous
  have htileInteriorsDisjoint : ∀ C D, C ≠ D →
      interior (baseTile C) ∩ interior (baseTile D) = ∅ := by
    intro C D hCD
    have hcones : C.1 ≠ D.1 := by
      intro hEq
      exact hCD (Subtype.ext hEq)
    let tileC : Set (EuclideanSpace ℝ (Fin n)) := baseE ∩ (C.1 : Set _)
    let tileD : Set (EuclideanSpace ℝ (Fin n)) := baseE ∩ (D.1 : Set _)
    have hCeq : baseTile C = e '' tileC := rfl
    have hDeq : baseTile D = e '' tileD := rfl
    have hCpre : e ⁻¹' (e '' tileC) = tileC := by
      ext y
      simp
    have hDpre : e ⁻¹' (e '' tileD) = tileD := by
      ext y
      simp
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    rw [hCeq, hDeq] at hx
    have hyC : e.symm x ∈ interior tileC := by
      have hxpre : e.symm x ∈ e ⁻¹' interior (e '' tileC) := by
        change e (e.symm x) ∈ interior (e '' tileC)
        simpa using hx.1
      have := (preimage_interior_subset_interior_preimage (t := e '' tileC)
        e.continuous) hxpre
      simpa [hCpre] using this
    have hyD : e.symm x ∈ interior tileD := by
      have hxpre : e.symm x ∈ e ⁻¹' interior (e '' tileD) := by
        change e (e.symm x) ∈ interior (e '' tileD)
        simpa using hx.2
      have := (preimage_interior_subset_interior_preimage (t := e '' tileD)
        e.continuous) hxpre
      simpa [hDpre] using this
    have hy : e.symm x ∈ interior tileC ∩ interior tileD := ⟨hyC, hyD⟩
    have hdis := hinteriors C.1 C.2 D.1 D.2 hcones
    rw [hdis] at hy
    simpa using hy
  let cover := compactOneBitFiberPatchCover_of_compactBand
    facePatch hfaceCompact base baseTile lower upper epsilon hbaseCover htileCompact
    htileInteriorsDisjoint hlower hupper horder hepsilon hfaceBand
  refine ⟨cover, ?_⟩
  intro C
  obtain ⟨D, hD, hsubset⟩ := hcoarseLabel C.1 C.2
  have htileLabel : baseTile C ⊆ e '' (D : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    change x ∈ e '' (baseE ∩ (C.1 : Set (EuclideanSpace ℝ (Fin n)))) at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hsubset hy, rfl⟩
  refine ⟨D, hD, htileLabel, ?_⟩
  intro k hne
  obtain ⟨x, hx, hprojected⟩ :=
    cover.exists_restricted_tile_basepoint_incidence ⟨C, k⟩ hne
  exact ⟨x, hx, htileLabel hprojected⟩

/-- Intersect a small projected-patch cover with the central arrangement of a fan. The product
labels retain both properties needed by Craciun's next fill: each tile remains small enough for its
local wall chart, and its first coordinate names the actual fan cell whose common faces order the
recursive seam tasks. -/
noncomputable def exists_small_fan_labeledOneBitFiberPatchCover {n : ℕ} {ι : Type*} [Fintype ι]
    (facePatch : Set (Fin (n + 1) → ℝ)) (hfaceCompact : IsCompact facePatch)
    (base : Set (Fin n → ℝ)) (smallTile : ι → Set (Fin n → ℝ))
    (hsmallCover : base = ⋃ i, smallTile i)
    (hsmallCompact : ∀ i, IsCompact (smallTile i))
    (hsmallDisjoint : ∀ i j, i ≠ j →
      interior (smallTile i) ∩ interior (smallTile j) = ∅)
    (lower upper : (Fin n → ℝ) → ℝ) (epsilon : ℝ)
    (hlower : Continuous lower) (hupper : Continuous upper)
    (horder : ∀ y ∈ base, lower y ≤ upper y) (hepsilon : 0 < epsilon)
    (hfaceBand : facePatch ⊆
      projectionFiberBand base (fun y => some (lower y)) (fun y => some (upper y)))
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hF : IsPolyhedralFan F)
    (hFdual : HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}] :
    CompactOneBitFiberPatchCover facePatch base
      (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι =>
          euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩ smallTile p.2)
      lower upper epsilon := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let baseE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' base
  let fanTile := euclideanHyperplaneArrangementBaseTile base F hFdual
  let productTile : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι → Set (Fin n → ℝ) :=
    fun p => fanTile p.1 ∩ smallTile p.2
  have hfanCovers (y : EuclideanSpace ℝ (Fin n)) :
      y ∈ ⋃ C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual),
        (C : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hyperplaneArrangementFamily_covers (fanNormalSet F hFdual)]
    simp
  have hbaseCover : base = ⋃ p, productTile p := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp (hfanCovers (e.symm x)) with ⟨C, hCmem⟩
      rcases Set.mem_iUnion.mp hCmem with ⟨hC, hxC⟩
      rcases Set.mem_iUnion.mp (show x ∈ ⋃ i, smallTile i from by rw [← hsmallCover]; exact hx)
        with ⟨i, hxi⟩
      refine Set.mem_iUnion.mpr ⟨(⟨C, hC⟩, i), ?_⟩
      change x ∈ fanTile ⟨C, hC⟩ ∩ smallTile i
      refine ⟨?_, hxi⟩
      change x ∈ e '' (baseE ∩ (C : Set (EuclideanSpace ℝ (Fin n))))
      exact ⟨e.symm x, ⟨⟨x, hx, rfl⟩, hxC⟩, e.apply_symm_apply x⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
      rcases hp.1 with ⟨y, hy, hxy⟩
      rcases hy.1 with ⟨x', hx', hxy'⟩
      have hxy'' : e y = x' := by
        calc
          e y = e (e.symm x') := congrArg e hxy'.symm
          _ = x' := e.apply_symm_apply x'
      have hxEq : x = x' := hxy.symm.trans hxy''
      exact hxEq.symm ▸ hx'
  have hbaseCompact : IsCompact base := by
    rw [hsmallCover]
    exact isCompact_iUnion hsmallCompact
  have hbaseEcompact : IsCompact baseE := hbaseCompact.image e.symm.continuous
  have hpatch := compactSet_hyperplaneArrangement_patchCover baseE hbaseEcompact hF hFdual
  rcases hpatch with ⟨hcompactFanTile, _, _, _, hfanInteriors⟩
  have hproductCompact : ∀ p, IsCompact (productTile p) := by
    intro p
    exact ((hcompactFanTile p.1.1 p.1.2).image e.continuous).inter (hsmallCompact p.2)
  have hproductDisjoint : ∀ p q, p ≠ q →
      interior (productTile p) ∩ interior (productTile q) = ∅ := by
    intro p q hpq
    have hfanP : interior (productTile p) ⊆ interior (fanTile p.1) :=
      interior_mono Set.inter_subset_left
    have hfanQ : interior (productTile q) ⊆ interior (fanTile q.1) :=
      interior_mono Set.inter_subset_left
    by_cases hcells : p.1 = q.1
    · have hsmallne : p.2 ≠ q.2 := by
        intro heq
        apply hpq
        exact Prod.ext hcells heq
      have hs := hsmallDisjoint p.2 q.2 hsmallne
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hxsmall : x ∈ interior (smallTile p.2) ∩ interior (smallTile q.2) := by
        refine ⟨?_, ?_⟩
        · exact interior_mono Set.inter_subset_right hx.1
        · exact interior_mono Set.inter_subset_right hx.2
      rw [hs] at hxsmall
      exact hxsmall
    · have hconeNe : p.1.1 ≠ q.1.1 := by
        intro hEq
        apply hcells
        exact Subtype.ext hEq
      have hf := hfanInteriors p.1.1 p.1.2 q.1.1 q.1.2 hconeNe
      let tileP : Set (EuclideanSpace ℝ (Fin n)) := baseE ∩ (p.1.1 : Set _)
      let tileQ : Set (EuclideanSpace ℝ (Fin n)) := baseE ∩ (q.1.1 : Set _)
      have hpEq : fanTile p.1 = e '' tileP := rfl
      have hqEq : fanTile q.1 = e '' tileQ := rfl
      have hpPre : e ⁻¹' (e '' tileP) = tileP := by ext y; simp
      have hqPre : e ⁻¹' (e '' tileQ) = tileQ := by ext y; simp
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hyP : e.symm x ∈ interior tileP := by
        have hpre : e.symm x ∈ e ⁻¹' interior (e '' tileP) := by
          change e (e.symm x) ∈ interior (e '' tileP)
          simpa [hpEq] using hfanP hx.1
        have hpre' := (preimage_interior_subset_interior_preimage (t := e '' tileP)
          e.continuous) hpre
        simpa [hpPre] using hpre'
      have hyQ : e.symm x ∈ interior tileQ := by
        have hpre : e.symm x ∈ e ⁻¹' interior (e '' tileQ) := by
          change e (e.symm x) ∈ interior (e '' tileQ)
          simpa [hqEq] using hfanQ hx.2
        have hpre' := (preimage_interior_subset_interior_preimage (t := e '' tileQ)
          e.continuous) hpre
        simpa [hqPre] using hpre'
      have hboth : e.symm x ∈ interior tileP ∩ interior tileQ := ⟨hyP, hyQ⟩
      rw [hf] at hboth
      exact hboth
  exact compactOneBitFiberPatchCover_of_compactBand facePatch hfaceCompact base productTile
    lower upper epsilon hbaseCover hproductCompact hproductDisjoint hlower hupper horder
    hepsilon hfaceBand

/-- In the product small-patch/fan cover, adjacent fiber strips meet over the exact intersection
of the two small patches with their actual common fan face. The shared endpoint task is strictly
lower than both incident strip tasks in the combined well-founded face order. -/
theorem fanSmallProductTile_adjacentStrip_seam {n : ℕ} {ι : Type*} [Fintype ι]
    {facePatch : Set (Fin (n + 1) → ℝ)} {base : Set (Fin n → ℝ)}
    {smallTile : ι → Set (Fin n → ℝ)} {lower upper : (Fin n → ℝ) → ℝ}
    {epsilon : ℝ} (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hFdual : HasDualFGCells F)
    [Fintype {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}]
    (cover : CompactOneBitFiberPatchCover facePatch base
      (fun p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι =>
          euclideanHyperplaneArrangementBaseTile base F hFdual p.1 ∩ smallTile p.2)
      lower upper epsilon)
    (horder : ∀ y ∈ base, lower y ≤ upper y)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) (i j : ι)
    (k : Fin cover.tiling.subdivisionCount) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)),
      (C.1 ≠ D.1 → ProperExposedFaceDependency G C.1 ∨
        ProperExposedFaceDependency G D.1) ∧
      OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, i), .endpoint k.succ.castSucc)
          ((C.1, i), .strip k.castSucc) ∧
      OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, j), .endpoint k.succ.castSucc)
          ((D.1, j), .strip k.succ) ∧
      (C.1 ≠ G → OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, i), .endpoint k.succ.castSucc)
          ((C.1, i), .endpoint k.succ.castSucc)) ∧
      (D.1 ≠ G → OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, j), .endpoint k.succ.castSucc)
          ((D.1, j), .endpoint k.succ.castSucc)) ∧
      (C.1 ≠ G → OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, i), .strip k.castSucc)
          ((C.1, i), .strip k.castSucc)) ∧
      (D.1 ≠ G → OneBitFanFaceDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι)
        (m := cover.tiling.subdivisionCount)
        ((G, j), .strip k.succ)
          ((D.1, j), .strip k.succ)) ∧
      ((euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i) ∩
        (euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j) =
          euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∩
            (smallTile i ∩ smallTile j)) ∧
      (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i)
          lower upper k.castSucc) ∩
        (facePatch ∩ projectionFiberSubdivisionTile
          (euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j)
          lower upper k.succ) =
      facePatch ∩ (fun y : Fin n → ℝ =>
        projectionFiberSubdivisionEndpointGraphPoint lower upper k.succ.castSucc y) ''
          ((euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩) ∩
            (smallTile i ∩ smallTile j)) ∧
      (oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((C.1, Sum.inl i), .strip k.castSucc) ∩
       oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((D.1, Sum.inl j), .strip k.succ)) =
      oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((G, Sum.inr (i, j)), .endpoint k.succ.castSucc) ∧
      oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((G, Sum.inr (i, j)), .endpoint k.succ.castSucc) ⊆
       oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((C.1, Sum.inl i), .strip k.castSucc) ∧
      oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((G, Sum.inr (i, j)), .endpoint k.succ.castSucc) ⊆
       oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile)
        lower upper ((D.1, Sum.inl j), .strip k.succ) ∧
      OneBitFanFaceSeamDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι) (m := cover.tiling.subdivisionCount)
        ((G, Sum.inr (i, j)), .endpoint k.succ.castSucc)
        ((C.1, Sum.inl i), .strip k.castSucc) ∧
      OneBitFanFaceSeamDependency (E := EuclideanSpace ℝ (Fin n))
        (ι := ι) (m := cover.tiling.subdivisionCount)
        ((G, Sum.inr (i, j)), .endpoint k.succ.castSucc)
        ((D.1, Sum.inl j), .strip k.succ) := by
  obtain ⟨G, hG, hfanMeet, hGC, hGD, _, _⟩ :=
    euclideanHyperplaneArrangementBaseTile_intersection base F hFdual C D
  have hdependency : C.1 ≠ D.1 →
      ProperExposedFaceDependency G C.1 ∨ ProperExposedFaceDependency G D.1 := by
    intro hCD
    by_cases hGC' : G = C.1
    · right
      constructor
      · simpa [hGC'] using hGD
      · intro hGD'
        apply hCD
        apply SetLike.coe_injective
        calc
          (C.1 : Set (EuclideanSpace ℝ (Fin n))) = G := by rw [hGC']
          _ = D.1 := congrArg (fun H : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) =>
            (H : Set (EuclideanSpace ℝ (Fin n)))) hGD'
    · exact Or.inl ⟨hGC, hGC'⟩
  have hbaseMeet :
      (euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i) ∩
          (euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j) =
        euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∩
          (smallTile i ∩ smallTile j) := by
    calc
      (euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i) ∩
          (euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j) =
        (euclideanHyperplaneArrangementBaseTile base F hFdual C ∩
          euclideanHyperplaneArrangementBaseTile base F hFdual D) ∩
          (smallTile i ∩ smallTile j) := by
            ext y
            simp [and_assoc, and_left_comm, and_comm]
      _ = euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩ ∩
          (smallTile i ∩ smallTile j) := by rw [hfanMeet]
  let p : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι := (C, i)
  let q : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)} × ι := (D, j)
  have hseam := cover.adjacent_base_tiles_share_seam p q
    (fun y hy => horder y (cover.baseTile_subset p hy.1)) k
  have hindex : k.succ.castSucc = k.castSucc.succ := by
    apply Fin.ext
    simp
  refine ⟨G, hG, hdependency, ?_, ?_, ?_, ?_, ?_, ?_, hbaseMeet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact OneBitFanFaceDependency.fiberEndpoint C.1 G i k.castSucc
      k.succ.castSucc hGC (Or.inr hindex)
  · exact OneBitFanFaceDependency.fiberEndpoint D.1 G j k.succ
      k.succ.castSucc hGD (Or.inl rfl)
  · intro hCG
    exact OneBitFanFaceDependency.fanFaceEndpoint C.1 G i
      k.succ.castSucc hGC hCG.symm
  · intro hDG
    exact OneBitFanFaceDependency.fanFaceEndpoint D.1 G j
      k.succ.castSucc hGD hDG.symm
  · intro hCG
    exact OneBitFanFaceDependency.fanFace C.1 G i k.castSucc hGC hCG.symm
  · intro hDG
    exact OneBitFanFaceDependency.fanFace D.1 G j k.succ hGD hDG.symm
  · rw [← hbaseMeet]
    exact hseam
  · simpa [oneBitFanFaceTaskPatch, euclideanProperConeBaseTile,
      euclideanProperConeMixedTileBaseTile, euclideanHyperplaneArrangementBaseTile] using (show
        (facePatch ∩ projectionFiberSubdivisionTile
            (euclideanHyperplaneArrangementBaseTile base F hFdual C ∩ smallTile i)
            lower upper k.castSucc) ∩
          (facePatch ∩ projectionFiberSubdivisionTile
            (euclideanHyperplaneArrangementBaseTile base F hFdual D ∩ smallTile j)
            lower upper k.succ) =
        facePatch ∩ (fun y : Fin n → ℝ =>
          projectionFiberSubdivisionEndpointGraphPoint lower upper k.succ.castSucc y) ''
            ((euclideanHyperplaneArrangementBaseTile base F hFdual ⟨G, hG⟩) ∩
              (smallTile i ∩ smallTile j)) from by
          rw [← hbaseMeet]
          exact hseam)
  · exact fanSmallTilePairEndpointTaskPatch_subset_leftStrip facePatch base smallTile
      lower upper G C.1 i j k.succ.castSucc k.castSucc hGC (Or.inr hindex)
      (fun y hy => horder y (cover.baseTile_subset p hy))
  · exact fanSmallTilePairEndpointTaskPatch_subset_rightStrip facePatch base smallTile
      lower upper G D.1 i j k.succ.castSucc k.succ hGD (Or.inl rfl)
      (fun y hy => horder y (cover.baseTile_subset q hy))
  · exact OneBitFanFaceSeamDependency.productSeamLeft C.1 G i j
      k.castSucc k.succ.castSucc hGC (Or.inr hindex)
  · exact OneBitFanFaceSeamDependency.productSeamRight D.1 G i j
      k.succ k.succ.castSucc hGD (Or.inl rfl)

/-- The projected-fan version of the one-bit cover construction. Start with the fan one dimension
higher, take the finite arrangement refinement of its last-coordinate image family, and use that
refinement to label every compact projected tile by an actual projected coarse cone. This is the
fan-to-blueprint step needed when Craciun's lower-dimensional face subdivision is obtained by
projecting the next-dimensional fan. -/
theorem exists_compactOneBitFiberPatchCover_of_forgetLastFanImage {n : ℕ}
    (facePatch : Set (Fin (n + 1) → ℝ)) (hfaceCompact : IsCompact facePatch)
    (base : Set (Fin n → ℝ)) (hbaseCompact : IsCompact base)
    (lower upper : (Fin n → ℝ) → ℝ) (epsilon : ℝ)
    (hlower : Continuous lower) (hupper : Continuous upper)
    (horder : ∀ y ∈ base, lower y ≤ upper y) (hepsilon : 0 < epsilon)
    (hfaceBand : facePatch ⊆
      projectionFiberBand base (fun y => some (lower y)) (fun y => some (upper y)))
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G)
    (hGdual : HasDualFGCells G) :
    ∃ H : Fan (EuclideanSpace ℝ (Fin n)), ∃ hH : IsPolyhedralFan H,
      ∃ hHdual : HasDualFGCells H,
      ∃ href : Refines H (linearImageFamily (forgetLastEuclidean n) G),
      ∃ cover : CompactOneBitFiberPatchCover facePatch base
          (euclideanHyperplaneArrangementBaseTile base H hHdual)
          lower upper epsilon,
        ∀ C, ∃ D ∈ linearImageFamily (forgetLastEuclidean n) G,
          euclideanHyperplaneArrangementBaseTile base H hHdual C ⊆
            (EuclideanSpace.equiv (Fin n) ℝ) '' (D : Set (EuclideanSpace ℝ (Fin n))) ∧
          ∀ k : Fin (cover.tiling.subdivisionCount + 1),
            (facePatch ∩ projectionFiberSubdivisionTile
              (euclideanHyperplaneArrangementBaseTile base H hHdual C)
              lower upper k).Nonempty →
            ∃ x, x ∈ facePatch ∩ projectionFiberSubdivisionTile
                (euclideanHyperplaneArrangementBaseTile base H hHdual C)
                lower upper k ∧
              forgetLastCoordinate n x ∈
                (EuclideanSpace.equiv (Fin n) ℝ) ''
                  (D : Set (EuclideanSpace ℝ (Fin n))) := by
  let image : Fan (EuclideanSpace ℝ (Fin n)) :=
    linearImageFamily (forgetLastEuclidean n) G
  have hImageDual : HasDualFGCells image :=
    linearImageFamily_forgetLast_hasDualFGCells G hGdual
  let H : Fan (EuclideanSpace ℝ (Fin n)) := hyperplaneArrangementFamily
    (fanNormalSet image hImageDual)
  have hH : IsPolyhedralFan H := hyperplaneArrangementFamily_isPolyhedralFan _
  have hHdual : HasDualFGCells H := hyperplaneArrangementFamily_hasDualFGCells _
  have href : Refines H image :=
    hyperplaneArrangementFamily_refines_of_covering_dualFG
      (linearImageFamily_forgetLastEuclidean_covers G hG) hImageDual
  obtain ⟨cover, htiles⟩ := exists_compactOneBitFiberPatchCover_of_euclideanHyperplaneArrangement
    facePatch hfaceCompact base hbaseCompact lower upper epsilon hlower hupper horder hepsilon
    hfaceBand H hH hHdual
  refine ⟨H, hH, hHdual, href, cover, ?_⟩
  intro C
  obtain ⟨D, hD, htile, hincidence⟩ := htiles C
  obtain ⟨K, hK, hDK⟩ := href D hD
  refine ⟨K, hK, ?_, ?_⟩
  · intro x hx
    rcases htile hx with ⟨y, hy, rfl⟩
    exact ⟨y, hDK hy, rfl⟩
  · intro k hne
    obtain ⟨x, hx, hy⟩ := hincidence k hne
    exact ⟨x, hx, by
      rcases hy with ⟨y, hyD, hxy⟩
      exact ⟨y, hDK hyD, hxy⟩⟩

/-- The arrangement from finite dual normals refines the family of one-coordinate projections of a
complete polyhedral fan. The image family need not satisfy the fan intersection axioms itself. -/
theorem hyperplaneArrangementFamily_refines_forgetLastImage {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G)
    (hGdual : HasDualFGCells G) :
    Refines
      (hyperplaneArrangementFamily
        (fanNormalSet (linearImageFamily (forgetLastEuclidean n) G)
          (linearImageFamily_forgetLast_hasDualFGCells G hGdual)))
      (linearImageFamily (forgetLastEuclidean n) G) :=
  hyperplaneArrangementFamily_refines_of_covering_dualFG
    (linearImageFamily_forgetLastEuclidean_covers G hG)
    (linearImageFamily_forgetLast_hasDualFGCells G hGdual)

/-- Any surjective projection with fibers along one supplied kernel vector admits a complete
polyhedral fan refinement of its closed-cone image family. -/
theorem exists_polyhedral_fan_refinement_of_oneDimensional_projection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [DecidableEq E] [DecidableEq F]
    (G : Fan E) (hG : IsPolyhedralFan G) (hGdual : HasDualFGCells G)
    (f : E →L[ℝ] F) (g : F →L[ℝ] E) (v : E)
    (hfg : ∀ y, f (g y) = y) (hv0 : f v = 0)
    (hdecomp : ∀ x, ∃ t : ℝ, x = g (f x) + t • v) :
    ∃ H : Fan F, IsPolyhedralFan H ∧ HasDualFGCells H ∧
      Refines H (linearImageFamily f G) := by
  have hf : Function.Surjective f := fun y => ⟨g y, hfg y⟩
  have hImageCover := linearImageFamily_covers_of_surjective hG f hf
  have hImageDual := linearImageFamily_hasDualFGCells_of_oneDimensionalFibers
    f g v hfg hv0 hdecomp G hGdual
  refine ⟨hyperplaneArrangementFamily (fanNormalSet (linearImageFamily f G) hImageDual),
    hyperplaneArrangementFamily_isPolyhedralFan _,
    hyperplaneArrangementFamily_hasDualFGCells _, ?_⟩
  exact hyperplaneArrangementFamily_refines_of_covering_dualFG hImageCover hImageDual

/-- A one-coordinate projected image family admits a complete polyhedral fan refinement whose
cells have finite dual representations. This supplies fan data for the projection step without
asserting that the raw image family is itself face-to-face. -/
theorem exists_polyhedral_fan_refinement_forgetLastImage {n : ℕ}
    (G : Fan (EuclideanSpace ℝ (Fin (n + 1)))) (hG : IsPolyhedralFan G)
    (hGdual : HasDualFGCells G) :
    ∃ H : Fan (EuclideanSpace ℝ (Fin n)), IsPolyhedralFan H ∧ HasDualFGCells H ∧
      Refines H (linearImageFamily (forgetLastEuclidean n) G) := by
  refine ⟨hyperplaneArrangementFamily
    (fanNormalSet (linearImageFamily (forgetLastEuclidean n) G)
      (linearImageFamily_forgetLast_hasDualFGCells G hGdual)), ?_, ?_, ?_⟩
  · exact hyperplaneArrangementFamily_isPolyhedralFan _
  · exact hyperplaneArrangementFamily_hasDualFGCells _
  · exact hyperplaneArrangementFamily_refines_forgetLastImage G hG hGdual


/-- Negating a cone preserves dual finite generation: negate the finite set of half-space normals. -/
theorem negatedProperCone_hasDualFG [CompleteSpace E] (C : ProperCone ℝ E)
    (hC : (C : PointedCone ℝ E).DualFG (innerₗ E)) :
    (CRNT.negatedProperCone C : PointedCone ℝ E).DualFG (innerₗ E) := by
  classical
  obtain ⟨s, hs⟩ := hC
  refine ⟨s.image (fun v : E => -v), ?_⟩
  have himage : (s.image (fun v : E => -v) : Set E) = -(s : Set E) := by
    ext x
    simp
  rw [himage, PointedCone.dual_neg, hs]
  apply PointedCone.ext
  intro x
  simp [CRNT.negatedProperCone]

/-- Negating every cell of a fan preserves dual finite generation cellwise. -/
theorem negatedFan_hasDualFGCells [CompleteSpace E] (F : Fan E)
    (hF : HasDualFGCells F) : HasDualFGCells (CRNT.negatedFan F) := by
  classical
  intro C hC
  rw [CRNT.negatedFan, Finset.mem_image] at hC
  rcases hC with ⟨D, hD, rfl⟩
  exact negatedProperCone_hasDualFG D (hF D hD)

/-- Dual-finitely-generated cells provide the decomposition used for exposed-face closure. -/
theorem intersectionFamily_dualDecomposition [CompleteSpace E] {F G : Fan E}
    (hF : HasDualFGCells F) (hG : HasDualFGCells G) :
    HasIntersectionDualDecomposition F G := by
  intro C hC D hD a ha
  exact coneDual_intersection_decomp_of_dualFG (hF C hC) (hG D hD) ha

/-- The pairwise-intersection family is a polyhedral fan when both input fans have
dual-finitely-generated cells. -/
theorem intersectionFamily_isPolyhedralFan_of_dualFG [CompleteSpace E] {F G : Fan E}
    (hF : IsPolyhedralFan F) (hG : IsPolyhedralFan G)
    (hFdual : HasDualFGCells F) (hGdual : HasDualFGCells G) :
    IsPolyhedralFan (intersectionFamily F G) :=
  intersectionFamily_isPolyhedralFan hF hG (intersectionFamily_dualDecomposition hFdual hGdual)

/-- Pairwise intersections preserve dual finite generation of fan cells. This lets an iterated
common refinement keep the finite-inequality representation needed for the next exposed-face step. -/
theorem intersectionFamily_hasDualFGCells [CompleteSpace E] {F G : Fan E}
    (hFdual : HasDualFGCells F) (hGdual : HasDualFGCells G) :
    HasDualFGCells (intersectionFamily F G) := by
  classical
  intro K hK
  rcases Finset.mem_image.mp hK with ⟨⟨C, D⟩, hpair, rfl⟩
  rcases Finset.mem_product.mp hpair with ⟨hC, hD⟩
  exact PointedCone.DualFG.inf (hFdual C hC) (hGdual D hD)

/-- Iteratively intersect a finite list of fans with a starting fan. -/
noncomputable def iteratedIntersectionFamily [CompleteSpace E] (F : Fan E) : List (Fan E) → Fan E
  | [] => F
  | G :: rest => iteratedIntersectionFamily (intersectionFamily F G) rest

theorem refines_refl [CompleteSpace E] (F : Fan E) : Refines F F := by
  intro C hC
  exact ⟨C, hC, Set.Subset.rfl⟩

/-- Refinement is transitive: a cell contained in a fine cell is contained in its coarse cell. -/
theorem refines_trans [CompleteSpace E] {F G H : Fan E}
    (hFG : Refines F G) (hGH : Refines G H) : Refines F H := by
  intro C hC
  obtain ⟨D, hD, hsub₁⟩ := hFG C hC
  obtain ⟨K, hK, hsub₂⟩ := hGH D hD
  exact ⟨K, hK, hsub₁.trans hsub₂⟩

/-- The iterated intersection family refines its starting fan. -/
theorem iteratedIntersectionFamily_refines_base [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E)) :
    Refines (iteratedIntersectionFamily F Gs) F := by
  induction Gs generalizing F with
  | nil => exact refines_refl F
  | cons G Gs ih =>
      exact refines_trans (ih (intersectionFamily F G)) intersectionFamily_refines_left

/-- Every fan added to an iterated intersection family is also refined by the result. -/
theorem iteratedIntersectionFamily_refines_member [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E)) {G : Fan E} (hG : G ∈ Gs) :
    Refines (iteratedIntersectionFamily F Gs) G := by
  induction Gs generalizing F with
  | nil => simp at hG
  | cons H Gs ih =>
      rcases List.mem_cons.mp hG with hEq | hTail
      · subst G
        exact refines_trans
          (iteratedIntersectionFamily_refines_base (intersectionFamily F H) Gs)
          intersectionFamily_refines_right
      · exact ih (intersectionFamily F H) hTail

/-- If every input fan is a polyhedral fan with dual-finitely-generated cells, iterated pairwise
intersections form a polyhedral common refinement and retain dual finite generation cellwise. -/
theorem iteratedIntersectionFamily_isPolyhedralFan [CompleteSpace E]
    (F : Fan E) (Gs : List (Fan E))
    (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F)
    (hG : ∀ G ∈ Gs, IsPolyhedralFan G)
    (hGdual : ∀ G ∈ Gs, HasDualFGCells G) :
    IsPolyhedralFan (iteratedIntersectionFamily F Gs) ∧
      HasDualFGCells (iteratedIntersectionFamily F Gs) := by
  have hAux : ∀ (xs : List (Fan E)) (F : Fan E),
      IsPolyhedralFan F → HasDualFGCells F →
      (∀ G ∈ xs, IsPolyhedralFan G) → (∀ G ∈ xs, HasDualFGCells G) →
      IsPolyhedralFan (iteratedIntersectionFamily F xs) ∧
        HasDualFGCells (iteratedIntersectionFamily F xs) := by
    intro xs
    induction xs with
    | nil =>
        intro F hF hFdual _ _
        exact ⟨hF, hFdual⟩
    | cons G Gs ih =>
        intro F hF hFdual hGs hGsdual
        have hHead : IsPolyhedralFan (intersectionFamily F G) :=
          intersectionFamily_isPolyhedralFan_of_dualFG hF (hGs G (by simp)) hFdual
            (hGsdual G (by simp))
        have hHeadDual : HasDualFGCells (intersectionFamily F G) :=
          intersectionFamily_hasDualFGCells hFdual (hGsdual G (by simp))
        exact ih (intersectionFamily F G) hHead hHeadDual
          (fun H hH => hGs H (by simp [hH]))
          (fun H hH => hGsdual H (by simp [hH]))
  exact hAux Gs F hF hFdual hG hGdual

/-- **Admissibility transfers from fine to coarse.** If a finer cell `C'` is contained in a coarse
cell `C` and the normal `n` attracts toward `C'` (`n ∈ C'`), then `n` attracts toward `C`: the
attracting-direction condition is monotone under cell containment. This is why a surface faithful for
the refined fan is faithful for the coarse fan — its normals, admissible for the finer cells, are
admissible for the containing coarse cells. -/
theorem attractsToward_coarse_of_fine {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : AttractsToward n C') : AttractsToward n C :=
  hsub h

/-- **The coarse field is inward for a fine-admissible normal.** If `n ∈ C'` with the finer cell
`C'` contained in the coarse cell `C`, then the coarse cell's toric-field polar `coneDual C` lies in
the region-side half-plane `{y | 0 ≤ ⟪n, y⟫_ℝ}`. The fine-fan surface's normal makes the coarse toric
field point into the region — the support side of faithfulness transferred from fine to coarse. -/
theorem coneDual_coarse_subset_halfPlane_of_fine_mem [CompleteSpace E] {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : n ∈ (C' : Set E)) :
    (coneDual (C : Set E) : Set E) ⊆ {y : E | 0 ≤ ⟪n, y⟫_ℝ} :=
  coneDual_subset_dualHalfPlane_of_mem (hsub h)

/-- Craciun v3, §8: if a patch's full local ball stays inside a coarse fan cell and its normal
belongs to a refining cell contained there, the coarse toric differential inclusion points into
the normal's half-space. This composes the local field-to-polar bound with the refinement label. -/
theorem toricField_subset_halfPlane_of_refinement_cell [CompleteSpace E]
    {F : Fan E} (hFfaces : HasExposedCommonFaces F)
    {D C' : ProperCone ℝ E} (hD : D ∈ F)
    (hsub : (C' : Set E) ⊆ (D : Set E)) {n : E} (hn : n ∈ (C' : Set E))
    {x : E} {δ : ℝ}
    (hball : Metric.ball x δ ⊆ interior (D : Set E)) :
    (toricField F δ x : Set E) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  exact (toricField_subset_coneDual_of_ball_inside_cell hFfaces hD hball).trans
    (coneDual_coarse_subset_halfPlane_of_fine_mem hsub hn)

/-- A compact refined patch contained in the interior of one coarse chamber has a single positive
radius on which the coarse toric field points into the half-space of every normal selected from
its refining cell. The uniform radius is the compact wall margin used in the piecewise construction. -/
theorem compact_patch_toricField_subset_halfPlane [CompleteSpace E]
    {F : Fan E} (hFfaces : HasExposedCommonFaces F)
    {D C' : ProperCone ℝ E} (hD : D ∈ F)
    (hsub : (C' : Set E) ⊆ (D : Set E)) {n : E} (hn : n ∈ (C' : Set E))
    {K : Set E} (hK : IsCompact K) (hKinterior : K ⊆ interior (D : Set E)) :
    ∃ δ > 0, ∀ x ∈ K,
      (toricField F δ x : Set E) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  obtain ⟨δ, hδ, hball⟩ :=
    IsCompact.exists_pos_uniform_ball_subset hK isOpen_interior hKinterior
  exact ⟨δ, hδ, fun x hx =>
    toricField_subset_halfPlane_of_refinement_cell hFfaces hD hsub hn (hball x hx)⟩

/-- The general local inward-pointing bridge instantiated with the explicit arrangement fan from
Craciun v3, §8. The arrangement's exposed-common-face data is constructed above from its sign cells. -/
theorem hyperplaneArrangement_toricField_subset_halfPlane [CompleteSpace E] [DecidableEq E]
    (T : Finset E) {D : ProperCone ℝ E}
    (hD : D ∈ hyperplaneArrangementFamily T) {n : E} (hn : n ∈ (D : Set E))
    {x : E} {δ : ℝ}
    (hball : Metric.ball x δ ⊆ interior (D : Set E)) :
    (toricField (hyperplaneArrangementFamily T) δ x : Set E) ⊆
      {y | 0 ≤ ⟪n, y⟫_ℝ} := by
  exact toricField_subset_halfPlane_of_refinement_cell
    (hyperplaneArrangementFamily_hasExposedCommonFaces T) hD Set.Subset.rfl hn hball

/-- **Admissibility for a refinement cell gives a coarse cell.** Packaged over `Refines`: if `n`
attracts toward a cell `C'` of the refinement `F'`, then `n` attracts toward some cell `C` of the
coarse fan `F`. The faithful-transfer at the fan level. -/
theorem exists_coarse_cell_of_refines [CompleteSpace E] {F' F : Fan E} (href : Refines F' F)
    {C' : ProperCone ℝ E} (hC' : C' ∈ F') {n : E} (h : AttractsToward n C') :
    ∃ C ∈ F, AttractsToward n C := by
  obtain ⟨C, hCF, hsub⟩ := href C' hC'
  exact ⟨C, hCF, attractsToward_coarse_of_fine hsub h⟩

/-- **Conditional normal feasibility.** Given an explicitly indexed family of fewer than
`finrank ℝ E` attracting-direction constraints for a patch, a nonzero surface normal orthogonal to
all of them exists. The general-dimensional construction must still prove that its local patches
have such a constraint family. -/
theorem exists_patch_normal_of_card_lt_finrank [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : ι → E)
    (hcard : Fintype.card ι < Module.finrank ℝ E) :
    ∃ n : E, n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0 :=
  exists_orthogonal_normal_of_card_lt_finrank v hcard

/-- Compatibility name for `exists_patch_normal_of_card_lt_finrank`. The cardinality bound is
an explicit hypothesis; constructing a refinement with that bound is a separate obligation. -/
@[deprecated exists_patch_normal_of_card_lt_finrank (since := "2026-11-03")]
alias refined_patch_normal_exists := exists_patch_normal_of_card_lt_finrank

/-- Craciun v3, §7.4.3 and §8 Step 1: the bounded normalized projective source is cut by the
lower-dimensional central-arrangement cells. The last coordinate is the fiber coordinate; the
arrangement label is pulled back from the projected base. -/
noncomputable def craciunProjectiveArrangementTile {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ craciunProjectiveDomain ∧ x 0 = 1 ∧ (∀ i, x i ≤ upper i) ∧
    (EuclideanSpace.equiv (Fin n) ℝ).symm (forgetLastCoordinate n x) ∈ C.1}

theorem craciunProjectiveArrangementTile_nonnegative {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ craciunProjectiveArrangementTile upper T C) : ∀ i, 0 ≤ x i := by
  intro i
  exact le_trans (by norm_num) (hx.1.1 i)

theorem craciunProjectiveArrangementTile_anchor {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ craciunProjectiveArrangementTile upper T C) : x 0 = 1 := hx.2.1

theorem craciunProjectiveArrangementTile_nonzero {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ craciunProjectiveArrangementTile upper T C) : x ≠ 0 := by
  intro hzero
  have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
  rw [craciunProjectiveArrangementTile_anchor upper T C hx] at hcoord
  norm_num at hcoord

/-- The normalized projective slice inside a finite blue box is compact. Its inequalities are
closed, while the coordinate box supplies the finite upper bound absent from `D^P_n` itself. -/
theorem isCompact_craciunProjectiveNormalizedBox {n : ℕ} [NeZero n]
    (upper : Fin n → ℝ) :
    IsCompact {x : Fin n → ℝ | x ∈ craciunProjectiveDomain ∧ x 0 = 1 ∧
      ∀ i, x i ≤ upper i} := by
  let coordBox : Set (Fin n → ℝ) := Set.univ.pi (fun i => Set.Icc (1 : ℝ) (upper i))
  have hbox : IsCompact coordBox := isCompact_univ_pi fun i => isCompact_Icc
  have hclosed : IsClosed {x : Fin n → ℝ | x ∈ craciunProjectiveDomain ∧ x 0 = 1 ∧
      ∀ i, x i ≤ upper i} := by
    have heq : IsClosed {x : Fin n → ℝ | x 0 = 1} :=
      isClosed_eq (continuous_apply 0) continuous_const
    have hup : IsClosed {x : Fin n → ℝ | ∀ i, x i ≤ upper i} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
    exact isClosed_craciunProjectiveDomain.inter (heq.inter hup)
  apply IsCompact.of_isClosed_subset hbox hclosed
  intro x hx
  change x ∈ Set.univ.pi (fun i => Set.Icc (1 : ℝ) (upper i))
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  exact ⟨hx.1.1 i, hx.2.2 i⟩

/-- Every arrangement-labeled projective tile is compact, since a `ProperCone` is closed and the
normalized blue-box slice is compact. -/
theorem isCompact_craciunProjectiveArrangementTile {n : ℕ}
    (upper : Fin (n + 1) → ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) :
    IsCompact (craciunProjectiveArrangementTile upper T C) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let base : Set (Fin (n + 1) → ℝ) := {x | x ∈ craciunProjectiveDomain ∧ x 0 = 1 ∧
    ∀ i, x i ≤ upper i}
  have hbase : IsCompact base := isCompact_craciunProjectiveNormalizedBox upper
  have hpre : IsClosed {x : Fin (n + 1) → ℝ | e.symm (forgetLastCoordinate n x) ∈ C.1} :=
    C.1.isClosed.preimage
      (e.symm.continuous.comp (forgetLastCoordinate n).continuous_of_finiteDimensional)
  have htile : craciunProjectiveArrangementTile upper T C =
      base ∩ {x | e.symm (forgetLastCoordinate n x) ∈ C.1} := by
    ext x
    simp [craciunProjectiveArrangementTile, base, e, and_assoc, and_left_comm, and_comm]
  rw [htile]
  exact hbase.inter_right hpre

/-- The arrangement tiles cover the bounded normalized projective slice. This instantiates the
projective-diagram input used by the radial blue-box construction from §8 Step 1. -/
theorem craciunProjectiveArrangementTiles_cover {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (x : Fin (n + 1) → ℝ) (hx : x ∈ craciunProjectiveDomain) (hanchor : x 0 = 1)
    (hupper : ∀ i, x i ≤ upper i) :
    x ∈ ⋃ C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}, craciunProjectiveArrangementTile upper T C := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcover := hyperplaneArrangementFamily_covers T
  have hz : e.symm (forgetLastCoordinate n x) ∈
      ⋃ C ∈ hyperplaneArrangementFamily T, (C : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hcover]
    simp
  rcases Set.mem_iUnion.mp hz with ⟨C, hC⟩
  rcases Set.mem_iUnion.mp hC with ⟨hCF, hxC⟩
  exact Set.mem_iUnion.mpr ⟨⟨C, hCF⟩, hx, hanchor, hupper, hxC⟩

/-- Intersecting two projective tiles gives precisely the tile over their common arrangement face.
The exposed-face and rank-drop witnesses are retained for the lexicographic recursive fill order
in Craciun v3, §7.4.3. -/
theorem craciunProjectiveArrangementTile_intersection {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily T),
      craciunProjectiveArrangementTile upper T C ∩
        craciunProjectiveArrangementTile upper T D =
          craciunProjectiveArrangementTile upper T ⟨G, hG⟩ ∧
      IsExposedFaceOf G C.1 ∧ IsExposedFaceOf G D.1 ∧
      (G ≠ C.1 → coneSpanRank G < coneSpanRank C.1) ∧
      (G ≠ D.1 → coneSpanRank G < coneSpanRank D.1) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨G, hG, hcommon, hGC, hGD, hrankC, hrankD⟩ :=
    hyperplaneArrangement_commonFace_rank_decrease C.2 D.2
  have hcone (x : EuclideanSpace ℝ (Fin n)) :
      x ∈ G ↔ x ∈ C.1 ∧ x ∈ D.1 := by
    change x ∈ (G : Set (EuclideanSpace ℝ (Fin n))) ↔ _
    rw [hcommon]
    simp
  refine ⟨G, hG, ?_, hGC, hGD, hrankC, hrankD⟩
  ext x
  constructor
  · rintro ⟨⟨hdomain, hanchor, hbound, hC⟩, ⟨_, _, _, hD⟩⟩
    exact ⟨hdomain, hanchor, hbound, (hcone (e.symm (forgetLastCoordinate n x))).mpr ⟨hC, hD⟩⟩
  · rintro ⟨hdomain, hanchor, hbound, hG⟩
    have hCD := (hcone (e.symm (forgetLastCoordinate n x))).mp hG
    exact ⟨⟨hdomain, hanchor, hbound, hCD.1⟩, ⟨hdomain, hanchor, hbound, hCD.2⟩⟩

/-- Craciun's finite arrangement diagram supplies the compact radial cover required at the next
projective induction stage. This removes the previously abstract diagram-cover input for a bounded
normalized slice; the coordinate upper bounds are precisely the blue-box restriction. -/
theorem craciunProjectiveArrangement_radialCover {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hupperPositive : ∀ i, 0 < upper i) :
    IsCompact (⋃ C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T},
      radialBoxDiagramTile (craciunProjectiveArrangementTile upper T C) upper
        (fun x hx => craciunProjectiveArrangementTile_nonnegative upper T C hx)
        (fun x hx => craciunProjectiveArrangementTile_nonzero upper T C hx) hupperPositive ∩
        craciunProjectiveDomain) ∧
    (∀ p, p ∈ craciunProjectiveDomain → (∀ i, p i ≤ upper i) →
      p ∈ ⋃ C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
        C ∈ hyperplaneArrangementFamily T},
        radialBoxDiagramTile (craciunProjectiveArrangementTile upper T C) upper
          (fun x hx => craciunProjectiveArrangementTile_nonnegative upper T C hx)
          (fun x hx => craciunProjectiveArrangementTile_nonzero upper T C hx) hupperPositive ∩
          craciunProjectiveDomain) := by
  classical
  let I := {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
    C ∈ hyperplaneArrangementFamily T}
  letI : Fintype I := Finset.fintypeCoeSort (hyperplaneArrangementFamily T)
  exact isCompact_and_covers_projectiveRadialTiles
    (fun C : I => craciunProjectiveArrangementTile upper T C) upper
    (fun C x hx => craciunProjectiveArrangementTile_nonnegative upper T C hx)
    (fun C x hx => craciunProjectiveArrangementTile_anchor upper T C hx)
    (fun C => isCompact_craciunProjectiveArrangementTile upper T C)
    hupperPositive
    (fun x hx hanchor hbound => craciunProjectiveArrangementTiles_cover upper T x hx hanchor hbound)

/-- Ray lifting preserves the lower-dimensional arrangement label after projection. This is the
projected-basepoint invariant needed to pass an upper tile back to its lower-dimensional face. -/
theorem craciunProjectiveArrangementTile_radialProjection_subset {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hupper : ∀ i, 0 < upper i)
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) :
    forgetLastCoordinate n ''
      (radialBoxDiagramTile (craciunProjectiveArrangementTile upper T C) upper
        (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
        (fun x hx hzero => by
          have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
          rw [hx.2.1] at hcoord
          norm_num at hcoord)
        hupper ∩ craciunProjectiveDomain) ⊆
      (EuclideanSpace.equiv (Fin n) ℝ) '' (C.1 : Set (EuclideanSpace ℝ (Fin n))) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  rintro y ⟨p, ⟨hpTile, _⟩, rfl⟩
  rcases (mem_radialBoxDiagramTile_iff_exists_source_ray
      (craciunProjectiveArrangementTile upper T C) upper
      (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
      (fun x hx hzero => by
        have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
        rw [hx.2.1] at hcoord
        norm_num at hcoord) hupper).1 hpTile with
    ⟨x, hx, s, hs, hpx, _⟩
  have hproject : e.symm (forgetLastCoordinate n p) =
      s • e.symm (forgetLastCoordinate n x) := by
    rw [hpx, (forgetLastCoordinate n).map_smul, map_smul]
  have hsC : s • e.symm (forgetLastCoordinate n x) ∈ C.1 :=
    C.1.smul_mem hx.2.2.2 hs
  refine ⟨e.symm (forgetLastCoordinate n p), ?_, ?_⟩
  · rw [hproject]
    exact hsC
  exact e.apply_symm_apply _

/-- Transfer a projective arrangement tile's radial points to a containing cell of the original
fan. If the tile's chamber contains a candidate surface normal, the containing fan cell's toric
polar field points into that normal's half-space. This is the inwardness interface needed after
the combinatorial projective subdivision (Craciun v3, §8 Steps 1–2). -/
theorem craciunProjectiveArrangementTile_fanInwardLabel {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n)))
    (hF : IsPolyhedralFan F) (hFdual : HasDualFGCells F)
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ C.1) :
    ∃ D ∈ F,
      forgetLastCoordinate n ''
        (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
          (fanNormalSet F hFdual) C) upper
          (fun x hx i => craciunProjectiveArrangementTile_nonnegative
            upper (fanNormalSet F hFdual) C hx i)
          (fun x hx => craciunProjectiveArrangementTile_nonzero
            upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) ⊆
        (EuclideanSpace.equiv (Fin n) ℝ) '' (D : Set (EuclideanSpace ℝ (Fin n))) ∧
      (coneDual (D : Set (EuclideanSpace ℝ (Fin n))) :
        Set (EuclideanSpace ℝ (Fin n))) ⊆ {w | 0 ≤ ⟪v, w⟫_ℝ} := by
  obtain ⟨D, hD, hCD⟩ :=
    hyperplaneArrangementFamily_refines_of_dualFG hF hFdual C.1 C.2
  refine ⟨D, hD, ?_, coneDual_subset_dualHalfPlane_of_mem (hCD hv)⟩
  intro y hy
  have hCtile := craciunProjectiveArrangementTile_radialProjection_subset
    upper (fanNormalSet F hFdual) hupper C hy
  rcases hCtile with ⟨x, hx, rfl⟩
  exact ⟨x, hCD hx, rfl⟩

/-- Every clipped radial point carries a concrete fan inwardness certificate. Its projected
coordinate itself is the candidate normal: the projective tile places that point in an arrangement
chamber, and finite-dual refinement supplies an original fan cell whose polar points into it. -/
theorem craciunProjectiveArrangementRadialPoint_fanInwardLabel {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hF : IsPolyhedralFan F)
    (hFdual : HasDualFGCells F)
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)})
    {p : Fin (n + 1) → ℝ}
    (hp : p ∈ radialBoxDiagramTile
      (craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) C) upper
        (fun x hx i => craciunProjectiveArrangementTile_nonnegative
          upper (fanNormalSet F hFdual) C hx i)
        (fun x hx => craciunProjectiveArrangementTile_nonzero
          upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) :
    ∃ v : EuclideanSpace ℝ (Fin n), ∃ D ∈ F,
      (EuclideanSpace.equiv (Fin n) ℝ).symm (forgetLastCoordinate n p) = v ∧
      v ∈ C.1 ∧
      (coneDual (D : Set (EuclideanSpace ℝ (Fin n))) :
        Set (EuclideanSpace ℝ (Fin n))) ⊆ {w | 0 ≤ ⟪v, w⟫_ℝ} := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hprojectionSubset := craciunProjectiveArrangementTile_radialProjection_subset
    upper (fanNormalSet F hFdual) hupper C
  have hprojection := hprojectionSubset ⟨p, hp, rfl⟩
  rcases hprojection with ⟨v, hv, hpv⟩
  obtain ⟨D, hD, _, hpolar⟩ :=
    craciunProjectiveArrangementTile_fanInwardLabel upper hupper F hF hFdual C hv
  have hnormal : e.symm (forgetLastCoordinate n p) = v := by
    calc
      e.symm (forgetLastCoordinate n p) = e.symm (e v) := congrArg e.symm hpv.symm
      _ = v := e.symm_apply_apply v
  exact ⟨v, D, hD, hnormal, hv, hpolar⟩

/-- A radial overlap between two distinct projective arrangement tiles has its ray source in the
exact common arrangement face and therefore projects into that face. The face label, both exposed-
face certificates, and both strict rank drops are retained so the lower-dimensional overlap is a
proper recursive task. -/
theorem craciunProjectiveArrangementRadialOverlap_commonFace {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) (hne : C ≠ D) :
    ∃ (G : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
      (hG : G ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)),
      IsExposedFaceOf G C.1 ∧ IsExposedFaceOf G D.1 ∧
      (G ≠ C.1 → coneSpanRank G < coneSpanRank C.1) ∧
      (G ≠ D.1 → coneSpanRank G < coneSpanRank D.1) ∧
      (G ≠ C.1 ∨ G ≠ D.1) ∧
      (∀ p, p ∈
        (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) C) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) C hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) ∩
          (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) D) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) D hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) D hx) hupper ∩ craciunProjectiveDomain) →
        ∃ x, x ∈ craciunProjectiveArrangementTile upper
        (fanNormalSet F hFdual) ⟨G, hG⟩ ∧ ∃ s : ℝ, 0 ≤ s ∧ p = s • x) ∧
      IsCompact
        ((radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) C) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) C hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) ∩
          (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) D) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) D hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) D hx) hupper ∩ craciunProjectiveDomain)) ∧
      IsCompact (forgetLastCoordinate n ''
        ((radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) C) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) C hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) ∩
          (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) D) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) D hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) D hx) hupper ∩ craciunProjectiveDomain))) ∧
      forgetLastCoordinate n ''
        ((radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) C) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) C hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain) ∩
          (radialBoxDiagramTile (craciunProjectiveArrangementTile upper
            (fanNormalSet F hFdual) D) upper
            (fun x hx i => craciunProjectiveArrangementTile_nonnegative
              upper (fanNormalSet F hFdual) D hx i)
            (fun x hx => craciunProjectiveArrangementTile_nonzero
              upper (fanNormalSet F hFdual) D hx) hupper ∩ craciunProjectiveDomain)) ⊆
        (EuclideanSpace.equiv (Fin n) ℝ) '' (G : Set (EuclideanSpace ℝ (Fin n))) := by
  let tileC := craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) C
  let tileD := craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) D
  obtain ⟨G, hG, htileFace, hGC, hGD, hrankC, hrankD⟩ :=
    craciunProjectiveArrangementTile_intersection upper (fanNormalSet F hFdual) C D
  let tileG := craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) ⟨G, hG⟩
  let nonnegC : ∀ x, x ∈ tileC → ∀ i, 0 ≤ x i := by
    intro x hx i
    exact craciunProjectiveArrangementTile_nonnegative upper (fanNormalSet F hFdual) C hx i
  let nonzeroC : ∀ x, x ∈ tileC → x ≠ 0 := by
    intro x hx
    exact craciunProjectiveArrangementTile_nonzero upper (fanNormalSet F hFdual) C hx
  let anchorC : ∀ x, x ∈ tileC → x 0 = 1 := by
    intro x hx
    exact craciunProjectiveArrangementTile_anchor upper (fanNormalSet F hFdual) C hx
  let nonnegD : ∀ x, x ∈ tileD → ∀ i, 0 ≤ x i := by
    intro x hx i
    exact craciunProjectiveArrangementTile_nonnegative upper (fanNormalSet F hFdual) D hx i
  let nonzeroD : ∀ x, x ∈ tileD → x ≠ 0 := by
    intro x hx
    exact craciunProjectiveArrangementTile_nonzero upper (fanNormalSet F hFdual) D hx
  let anchorD : ∀ x, x ∈ tileD → x 0 = 1 := by
    intro x hx
    exact craciunProjectiveArrangementTile_anchor upper (fanNormalSet F hFdual) D hx
  let nonnegG : ∀ x, x ∈ tileG → ∀ i, 0 ≤ x i := by
    intro x hx i
    exact craciunProjectiveArrangementTile_nonnegative upper (fanNormalSet F hFdual) ⟨G, hG⟩ hx i
  let nonzeroG : ∀ x, x ∈ tileG → x ≠ 0 := by
    intro x hx
    exact craciunProjectiveArrangementTile_nonzero upper (fanNormalSet F hFdual) ⟨G, hG⟩ hx
  have hclip := radialBoxDiagramTile_intersection_clip_eq tileC tileD upper 0
    craciunProjectiveDomain nonnegC nonzeroC anchorC nonnegD nonzeroD anchorD hupper
    craciunProjectiveDomain_origin_not_mem
  have hproper : G ≠ C.1 ∨ G ≠ D.1 := by
    by_cases hGCeq : G = C.1
    · right
      intro hGDeq
      exact hne (Subtype.ext (hGCeq.symm.trans hGDeq))
    · exact Or.inl hGCeq
  have hsource : ∀ p, p ∈
      (radialBoxDiagramTile tileC upper nonnegC nonzeroC hupper ∩ craciunProjectiveDomain) ∩
        (radialBoxDiagramTile tileD upper nonnegD nonzeroD hupper ∩ craciunProjectiveDomain) →
      ∃ x, x ∈ tileG ∧ ∃ s : ℝ, 0 ≤ s ∧ p = s • x := by
    intro p hp
    have hpBoth : p ∈
        (radialBoxDiagramTile tileC upper nonnegC nonzeroC hupper ∩ craciunProjectiveDomain) ∩
          (radialBoxDiagramTile tileD upper nonnegD nonzeroD hupper ∩ craciunProjectiveDomain) := hp
    have hpCommon := (congrArg (fun s => p ∈ s) hclip).mp hpBoth
    rcases (mem_radialBoxDiagramTile_iff_exists_source_ray (tileC ∩ tileD) upper
        (fun x hx i => nonnegC x hx.1 i) (fun x hx => nonzeroC x hx.1) hupper).1
        hpCommon.1 with ⟨x, hx, s, hs, hpx, _⟩
    have hxG : x ∈ tileG := by
      have hfaceAt := congrArg (fun S => x ∈ S) htileFace
      exact hfaceAt.mp hx
    exact ⟨x, hxG, s, hs, hpx⟩
  have hcompactC := isCompact_radialBoxDiagramTile_projectiveDomain tileC upper 0
    nonnegC nonzeroC anchorC hupper
      (isCompact_craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) C)
  have hcompactD := isCompact_radialBoxDiagramTile_projectiveDomain tileD upper 0
    nonnegD nonzeroD anchorD hupper
      (isCompact_craciunProjectiveArrangementTile upper (fanNormalSet F hFdual) D)
  have hcompactOverlap : IsCompact
      ((radialBoxDiagramTile tileC upper nonnegC nonzeroC hupper ∩ craciunProjectiveDomain) ∩
        (radialBoxDiagramTile tileD upper nonnegD nonzeroD hupper ∩ craciunProjectiveDomain)) :=
    hcompactC.inter hcompactD
  refine ⟨G, hG, hGC, hGD, hrankC, hrankD, hproper, hsource, hcompactOverlap, ?_, ?_⟩
  · exact hcompactOverlap.image
      (forgetLastCoordinate n).continuous_of_finiteDimensional
  · intro y hy
    rcases hy with ⟨p, ⟨⟨hpC, hdomain⟩, ⟨hpD, _⟩⟩, rfl⟩
    obtain ⟨x, hxG, s, hs, hpx⟩ := hsource p ⟨⟨hpC, hdomain⟩, ⟨hpD, hdomain⟩⟩
    have hpBox := radialBoxDiagramTile_subset_box tileC upper nonnegC nonzeroC hupper hpC
    have hpG := radialBoxDiagramTile_contains_of_ray_in_box tileG upper nonnegG nonzeroG hupper
      hxG hs hpx (fun i => (hpBox i).2)
    have hsubsetG := craciunProjectiveArrangementTile_radialProjection_subset
      upper (fanNormalSet F hFdual) hupper ⟨G, hG⟩
    exact hsubsetG ⟨p, ⟨hpG, hdomain⟩, rfl⟩

/-- The radial blue-box tile clipped to Craciun's ordered projective domain. -/
noncomputable def craciunProjectiveArrangementRadialPatch {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (C : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) :
    Set (Fin (n + 1) → ℝ) :=
  radialBoxDiagramTile (craciunProjectiveArrangementTile upper
    (fanNormalSet F hFdual) C) upper
    (fun x hx i => craciunProjectiveArrangementTile_nonnegative
      upper (fanNormalSet F hFdual) C hx i)
    (fun x hx => craciunProjectiveArrangementTile_nonzero
      upper (fanNormalSet F hFdual) C hx) hupper ∩ craciunProjectiveDomain

/-- The clipped overlap of two radial arrangement patches; its compactness permits restriction of
the one-bit fiber atlas before passing this shared face to the recursive fill. -/
noncomputable def craciunProjectiveArrangementRadialOverlapPatch {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) :
    Set (Fin (n + 1) → ℝ) :=
  craciunProjectiveArrangementRadialPatch upper hupper F hFdual C ∩
    craciunProjectiveArrangementRadialPatch upper hupper F hFdual D

/-- The face-recursion witness supplies compactness of the actual clipped radial overlap, so that
the overlap can be used as a closed restriction domain for the neighboring one-bit patches. -/
theorem craciunProjectiveArrangementRadialOverlapPatch_isCompact {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (hupper : ∀ i, 0 < upper i)
    (F : Fan (EuclideanSpace ℝ (Fin n))) (hFdual : HasDualFGCells F)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily (fanNormalSet F hFdual)}) (hne : C ≠ D) :
    IsCompact (craciunProjectiveArrangementRadialOverlapPatch upper hupper F hFdual C D) := by
  obtain ⟨_, _, _, _, _, _, _, _, hcompact, _, _⟩ :=
    craciunProjectiveArrangementRadialOverlap_commonFace upper hupper F hFdual C D hne
  simpa [craciunProjectiveArrangementRadialOverlapPatch,
    craciunProjectiveArrangementRadialPatch] using hcompact

/-- Distinct projective arrangement tiles have disjoint projected interiors after radial lifting.
The result follows because each projection stays in its closed cone and the arrangement cone
interiors are disjoint. -/
theorem craciunProjectiveArrangementTiles_projectedInteriorsDisjoint {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hupper : ∀ i, 0 < upper i)
    (C D : {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
      C ∈ hyperplaneArrangementFamily T}) (hne : C ≠ D) :
    interior (forgetLastCoordinate n ''
      (radialBoxDiagramTile (craciunProjectiveArrangementTile upper T C) upper
        (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
        (fun x hx hzero => by
          have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
          rw [hx.2.1] at hcoord
          norm_num at hcoord)
        hupper ∩ craciunProjectiveDomain)) ∩
    interior (forgetLastCoordinate n ''
      (radialBoxDiagramTile (craciunProjectiveArrangementTile upper T D) upper
        (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
        (fun x hx hzero => by
          have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
          rw [hx.2.1] at hcoord
          norm_num at hcoord)
        hupper ∩ craciunProjectiveDomain)) = ∅ := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcone : interior (C.1 : Set (EuclideanSpace ℝ (Fin n))) ∩
      interior (D.1 : Set (EuclideanSpace ℝ (Fin n))) = ∅ :=
    hyperplaneArrangementFamily_interiors_disjoint C.2 D.2 (by
      intro h
      exact hne (Subtype.ext h))
  have hCsub : forgetLastCoordinate n ''
      (radialBoxDiagramTile (craciunProjectiveArrangementTile upper T C) upper
        (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
        (fun x hx hzero => by
          have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
          rw [hx.2.1] at hcoord
          norm_num at hcoord)
        hupper ∩ craciunProjectiveDomain) ⊆ e '' (C.1 : Set _) :=
    craciunProjectiveArrangementTile_radialProjection_subset upper T hupper C
  have hDsub : forgetLastCoordinate n ''
      (radialBoxDiagramTile (craciunProjectiveArrangementTile upper T D) upper
        (fun x hx i => le_trans (by norm_num) (hx.1.1 i))
        (fun x hx hzero => by
          have hcoord : x 0 = 0 := congrArg (fun f => f 0) hzero
          rw [hx.2.1] at hcoord
          norm_num at hcoord)
        hupper ∩ craciunProjectiveDomain) ⊆ e '' (D.1 : Set _) :=
    craciunProjectiveArrangementTile_radialProjection_subset upper T hupper D
  have hCpre : e ⁻¹' (e '' (C.1 : Set (EuclideanSpace ℝ (Fin n)))) = C.1 := by
    ext x
    simp
  have hDpre : e ⁻¹' (e '' (D.1 : Set (EuclideanSpace ℝ (Fin n)))) = D.1 := by
    ext x
    simp
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro hy
  have hyC : y ∈ interior (e '' (C.1 : Set (EuclideanSpace ℝ (Fin n)))) :=
    interior_mono hCsub hy.1
  have hyD : y ∈ interior (e '' (D.1 : Set (EuclideanSpace ℝ (Fin n)))) :=
    interior_mono hDsub hy.2
  have hpreC := preimage_interior_subset_interior_preimage
    (t := e '' (C.1 : Set (EuclideanSpace ℝ (Fin n)))) e.continuous
    (show e.symm y ∈ e ⁻¹' interior (e '' (C.1 : Set _)) by simpa using hyC)
  have hpreD := preimage_interior_subset_interior_preimage
    (t := e '' (D.1 : Set (EuclideanSpace ℝ (Fin n)))) e.continuous
    (show e.symm y ∈ e ⁻¹' interior (e '' (D.1 : Set _)) by simpa using hyD)
  have hcontr : e.symm y ∈ interior (C.1 : Set _) ∩ interior (D.1 : Set _) := by
    simpa [hCpre, hDpre] using And.intro hpreC hpreD
  rw [hcone] at hcontr
  exact hcontr

/-- Feed the concrete projective arrangement into Craciun's one-bit fiber refinement. The result
retains parent arrangement labels while subdividing each projected tile into compact pieces small
enough for local wall-chart selection (§7.4.3 Case 1.2). -/
noncomputable def craciunProjectiveArrangement_smallPatchCover {n : ℕ}
    (upper : Fin (n + 1) → ℝ) (T : Finset (EuclideanSpace ℝ (Fin n)))
    (epsilon eta : ℝ) (hupperPositive : ∀ i, 0 < upper i)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) := by
  classical
  let I := {C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)) //
    C ∈ hyperplaneArrangementFamily T}
  letI : Fintype I := Finset.fintypeCoeSort (hyperplaneArrangementFamily T)
  exact compactProjectiveRadialFamily_smallPatchCover_refiningDiagramTiles
    (fun C : I => craciunProjectiveArrangementTile upper T C) upper epsilon eta
    (fun C x hx => craciunProjectiveArrangementTile_nonnegative upper T C hx)
    (fun C x hx => craciunProjectiveArrangementTile_nonzero upper T C hx)
    (fun C x hx => craciunProjectiveArrangementTile_anchor upper T C hx)
    (fun C => isCompact_craciunProjectiveArrangementTile upper T C)
    hupperPositive hepsilon heta
    (fun x hx hanchor hbound => craciunProjectiveArrangementTiles_cover upper T x hx hanchor hbound)
    (fun C D hne => craciunProjectiveArrangementTiles_projectedInteriorsDisjoint
      upper T hupperPositive C D hne)

end FanRefinement

end CRNT
namespace CRNT
namespace FanRefinement

open ZeroSeparatingInduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

inductive FiniteOverlapDependency {q m : ℕ} :
    OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m →
      OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m → Prop
  | inherited {a b : OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m}
      (hdep : OneBitFanFaceSeamDependency (E := E) a b) :
      FiniteOverlapDependency a b
  | baseLeft (C : ProperCone ℝ E) (i j : Fin q) (cell : OneBitFiberCell m)
      (hij : i.val < j.val) :
      FiniteOverlapDependency ((C, Sum.inr (i, j)), cell) ((C, Sum.inl i), cell)
  | baseRight (C : ProperCone ℝ E) (i j : Fin q) (cell : OneBitFiberCell m)
      (hij : i.val < j.val) :
      FiniteOverlapDependency ((C, Sum.inr (i, j)), cell) ((C, Sum.inl j), cell)

def finiteSeamLabelRank {q : ℕ} : Sum (Fin q) (Fin q × Fin q) → ℕ
  | .inl i => 2 * i.val + 1
  | .inr (i, j) => 2 * min i.val j.val

noncomputable def finiteSeamTaskRank {q m : ℕ}
    (a : OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m) : ℕ :=
  (2 * q + 1) * oneBitFanFaceTaskRank a + finiteSeamLabelRank a.1.2

theorem finiteSeamLabelRank_lt_bound {q : ℕ}
    (label : Sum (Fin q) (Fin q × Fin q)) :
    finiteSeamLabelRank label < 2 * q + 1 := by
  cases label with
  | inl i => simp [finiteSeamLabelRank]
  | inr pair =>
      rcases pair with ⟨i, j⟩
      simp [finiteSeamLabelRank]

theorem finiteSeamRank_lt_of_geoRank_lt {q m : ℕ}
    {a b : OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m}
    (hgeo : oneBitFanFaceTaskRank a < oneBitFanFaceTaskRank b) :
    finiteSeamTaskRank a < finiteSeamTaskRank b := by
  have ha := finiteSeamLabelRank_lt_bound a.1.2
  have hb := finiteSeamLabelRank_lt_bound b.1.2
  calc
    (2 * q + 1) * oneBitFanFaceTaskRank a + finiteSeamLabelRank a.1.2 <
        (2 * q + 1) * oneBitFanFaceTaskRank a + (2 * q + 1) :=
      Nat.add_lt_add_left ha _
    _ = (2 * q + 1) * (oneBitFanFaceTaskRank a + 1) := by simp [Nat.mul_add]
    _ ≤ (2 * q + 1) * oneBitFanFaceTaskRank b :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hgeo)
    _ ≤ (2 * q + 1) * oneBitFanFaceTaskRank b + finiteSeamLabelRank b.1.2 :=
      Nat.le_add_right _ _

theorem finiteOverlapDependency_wellFounded [FiniteDimensional ℝ E]
    {q m : ℕ} : WellFounded (FiniteOverlapDependency (E := E) (q := q) (m := m)) := by
  have hmeasure : WellFounded (fun a b : OneBitFanFaceTask E
      (Sum (Fin q) (Fin q × Fin q)) m => finiteSeamTaskRank a < finiteSeamTaskRank b) :=
    InvImage.wf finiteSeamTaskRank (Nat.lt_wfRel).2
  apply hmeasure.mono
  intro a b hab
  cases hab with
  | inherited hdep =>
      have hgeo : oneBitFanFaceTaskRank a < oneBitFanFaceTaskRank b := by
        cases hdep with
        | inherited hdep =>
            cases hdep with
            | fanFace C G k i hface hne =>
                simp [oneBitFanFaceTaskRank]
                exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
            | fanFaceEndpoint C G k j hface hne =>
                simp [oneBitFanFaceTaskRank]
                exact coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hne
            | fiberEndpoint C G k i j hface hadjacent =>
                have hrank : coneSpanRank G ≤ coneSpanRank C := by
                  by_cases hGC : G = C
                  · subst G
                    exact le_rfl
                  · exact (coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC).le
                simp [oneBitFanFaceTaskRank]
                omega
        | productSeamLeft C G i j k endpoint hface hadjacent =>
            by_cases hGC : G = C
            · subst G
              simp [oneBitFanFaceTaskRank]
            · simp [oneBitFanFaceTaskRank]
              have hlt := coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC
              omega
        | productSeamRight C G i j k endpoint hface hadjacent =>
            by_cases hGC : G = C
            · subst G
              simp [oneBitFanFaceTaskRank]
            · simp [oneBitFanFaceTaskRank]
              have hlt := coneSpanRank_lt_of_isExposedFaceOf_of_ne hface hGC
              omega
      exact finiteSeamRank_lt_of_geoRank_lt hgeo
  | baseLeft C i j cell hij =>
      have hlabels : finiteSeamLabelRank (Sum.inr (i, j)) < finiteSeamLabelRank (Sum.inl i) := by
        change 2 * min i.val j.val < 2 * i.val + 1
        rw [Nat.min_eq_left (Nat.le_of_lt hij)]
        omega
      have hbase : oneBitFanFaceTaskRank
          (E := E) (ι := Sum (Fin q) (Fin q × Fin q)) (m := m)
          ((C, Sum.inr (i, j)), cell) = oneBitFanFaceTaskRank
          (E := E) (ι := Sum (Fin q) (Fin q × Fin q)) (m := m)
          ((C, Sum.inl i), cell) := rfl
      unfold finiteSeamTaskRank
      rw [hbase]
      exact Nat.add_lt_add_left hlabels _
  | baseRight C i j cell hij =>
      have hlabels : finiteSeamLabelRank (Sum.inr (i, j)) < finiteSeamLabelRank (Sum.inl j) := by
        change 2 * min i.val j.val < 2 * j.val + 1
        rw [Nat.min_eq_left (Nat.le_of_lt hij)]
        omega
      have hbase : oneBitFanFaceTaskRank
          (E := E) (ι := Sum (Fin q) (Fin q × Fin q)) (m := m)
          ((C, Sum.inr (i, j)), cell) = oneBitFanFaceTaskRank
          (E := E) (ι := Sum (Fin q) (Fin q × Fin q)) (m := m)
          ((C, Sum.inl j), cell) := rfl
      unfold finiteSeamTaskRank
      rw [hbase]
      exact Nat.add_lt_add_left hlabels _

noncomputable def finiteOverlapDependency_recursion [FiniteDimensional ℝ E]
    {q m : ℕ}
    {P : OneBitFanFaceTask E (Sum (Fin q) (Fin q × Fin q)) m → Sort v}
    (step : ∀ task, (∀ predecessor,
      FiniteOverlapDependency (E := E) (q := q) (m := m) predecessor task → P predecessor) →
        P task) :
    ∀ task, P task :=
  (finiteOverlapDependency_wellFounded (E := E) (q := q) (m := m)).fix step

theorem finiteOverlapDependency_taskPatch_subset {n m q : ℕ}
    (facePatch : Set (Fin (n + 1) → ℝ)) (base : Set (Fin n → ℝ))
    (smallTile : Fin q → Set (Fin n → ℝ)) (lower upper : (Fin n → ℝ) → ℝ)
    (horder : ∀ C label y, y ∈ euclideanProperConeMixedTileBaseTile base smallTile
      (C, label) → lower y ≤ upper y)
    {predecessor task : OneBitFanFaceTask (EuclideanSpace ℝ (Fin n))
      (Sum (Fin q) (Fin q × Fin q)) m}
    (hdep : FiniteOverlapDependency (E := EuclideanSpace ℝ (Fin n)) predecessor task) :
    oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile) lower upper predecessor ⊆
      oneBitFanFaceTaskPatch facePatch
        (euclideanProperConeMixedTileBaseTile base smallTile) lower upper task := by
  cases hdep with
  | inherited hdep =>
      exact oneBitFanFaceSeamDependency.taskPatch_subset facePatch base smallTile lower upper
        horder hdep
  | baseLeft C i j cell hij =>
      have hbase : euclideanProperConeMixedTileBaseTile base smallTile
          (C, Sum.inr (i, j)) ⊆
          euclideanProperConeMixedTileBaseTile base smallTile (C, Sum.inl i) := by
        intro y hy
        change y ∈ euclideanProperConeBaseTile base C ∩ (smallTile i ∩ smallTile j) at hy
        change y ∈ euclideanProperConeBaseTile base C ∩ smallTile i
        exact ⟨hy.1, hy.2.1⟩
      cases cell with
      | strip k =>
          intro x hx
          exact ⟨hx.1, projectionFiberSubdivisionTile_mono hbase lower upper k hx.2⟩
      | endpoint k =>
          intro x hx
          exact ⟨hx.1, Set.image_mono hbase hx.2⟩
  | baseRight C i j cell hij =>
      have hbase : euclideanProperConeMixedTileBaseTile base smallTile
          (C, Sum.inr (i, j)) ⊆
          euclideanProperConeMixedTileBaseTile base smallTile (C, Sum.inl j) := by
        intro y hy
        change y ∈ euclideanProperConeBaseTile base C ∩ (smallTile i ∩ smallTile j) at hy
        change y ∈ euclideanProperConeBaseTile base C ∩ smallTile j
        exact ⟨hy.1, hy.2.2⟩
      cases cell with
      | strip k =>
          intro x hx
          exact ⟨hx.1, projectionFiberSubdivisionTile_mono hbase lower upper k hx.2⟩
      | endpoint k =>
          intro x hx
          exact ⟨hx.1, Set.image_mono hbase hx.2⟩

theorem compactSmallBaseTiling_boundary_overlap_tasks_at {n m : ℕ}
    {base : Set (Fin n → ℝ)} {eta : ℝ}
    (T : ZeroSeparatingInduction.CompactSmallBaseTiling base eta)
    {i : Fin T.count} {x : Fin n → ℝ}
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) (cell : OneBitFiberCell m)
    (hxb : x ∈ interior base) (hxi : x ∈ T.tile i)
    (hxnot : x ∉ interior (T.tile i)) :
    ∃ j : Fin T.count, j ≠ i ∧ x ∈ T.tile i ∩ T.tile j ∧
      ((FiniteOverlapDependency
          ((C, Sum.inr (i, j)), cell) ((C, Sum.inl i), cell) ∧
        FiniteOverlapDependency
          ((C, Sum.inr (i, j)), cell) ((C, Sum.inl j), cell)) ∨
       (FiniteOverlapDependency
          ((C, Sum.inr (j, i)), cell) ((C, Sum.inl i), cell) ∧
        FiniteOverlapDependency
          ((C, Sum.inr (j, i)), cell) ((C, Sum.inl j), cell))) := by
  obtain ⟨j, hji, hxj⟩ := T.boundary_incident_tile hxb hxnot
  refine ⟨j, hji, ⟨hxi, hxj⟩, ?_⟩
  by_cases horder : i.val < j.val
  · left
    exact ⟨FiniteOverlapDependency.baseLeft C i j cell horder,
      FiniteOverlapDependency.baseRight C i j cell horder⟩
  · right
    have hvalNe : i.val ≠ j.val := by
      intro hval
      exact hji (Fin.ext hval.symm)
    have hrev : j.val < i.val := by omega
    exact ⟨FiniteOverlapDependency.baseRight C j i cell hrev,
      FiniteOverlapDependency.baseLeft C j i cell hrev⟩
end FanRefinement
end CRNT
namespace CRNT
namespace FanRefinement

open ZeroSeparatingInduction

theorem CompactSmallBaseTiling.boundary_overlap_patch_at {n m : ℕ}
    {base : Set (Fin n → ℝ)} {eta : ℝ}
    (T : CompactSmallBaseTiling base eta)
    (facePatch : Set (Fin (n + 1) → ℝ))
    (lower upper : (Fin n → ℝ) → ℝ)
    (horder : ∀ C label y, y ∈ euclideanProperConeMixedTileBaseTile base T.tile
      (C, label) → lower y ≤ upper y)
    {i : Fin T.count} {x : Fin (n + 1) → ℝ}
    (C : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
    (cell : OneBitFiberCell m)
    (hx : x ∈ oneBitFanFaceTaskPatch facePatch
      (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
      ((C, Sum.inl i), cell))
    (hyInterior : forgetLastCoordinate n x ∈ interior base)
    (hyNotInterior : forgetLastCoordinate n x ∉ interior (T.tile i)) :
    ∃ j : Fin T.count, j ≠ i ∧
      forgetLastCoordinate n x ∈ T.tile i ∩ T.tile j ∧
      ((FiniteOverlapDependency
          ((C, Sum.inr (i, j)), cell) ((C, Sum.inl i), cell) ∧
        FiniteOverlapDependency
          ((C, Sum.inr (i, j)), cell) ((C, Sum.inl j), cell) ∧
        oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inr (i, j)), cell) ⊆
        oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inl i), cell) ∧
        x ∈ oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inr (i, j)), cell)) ∨
       (FiniteOverlapDependency
          ((C, Sum.inr (j, i)), cell) ((C, Sum.inl i), cell) ∧
        FiniteOverlapDependency
          ((C, Sum.inr (j, i)), cell) ((C, Sum.inl j), cell) ∧
        oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inr (j, i)), cell) ⊆
        oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inl i), cell) ∧
        x ∈ oneBitFanFaceTaskPatch facePatch
          (euclideanProperConeMixedTileBaseTile base T.tile) lower upper
          ((C, Sum.inr (j, i)), cell))) := by
  cases cell with
  | strip k =>
      have hxface : x ∈ facePatch := hx.1
      have hstrip : (let y := forgetLastCoordinate n x;
          y ∈ euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inl i) ∧
            projectionFiberSubdivisionEndpoint lower upper k.castSucc y ≤ x (Fin.last n) ∧
              x (Fin.last n) ≤ projectionFiberSubdivisionEndpoint lower upper k.succ y) := by
        have hxstrip := hx.2
        change (let y := forgetLastCoordinate n x;
          y ∈ euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inl i) ∧
            projectionFiberSubdivisionEndpoint lower upper k.castSucc y ≤ x (Fin.last n) ∧
              x (Fin.last n) ≤ projectionFiberSubdivisionEndpoint lower upper k.succ y)
          at hxstrip
        exact hxstrip
      have hbase : forgetLastCoordinate n x ∈
          euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inl i) := hstrip.1
      change forgetLastCoordinate n x ∈ euclideanProperConeBaseTile base C ∩ T.tile i at hbase
      have hcone : forgetLastCoordinate n x ∈ euclideanProperConeBaseTile base C := hbase.1
      obtain ⟨j, hji, htiles, hdeps⟩ := compactSmallBaseTiling_boundary_overlap_tasks_at
        T C (.strip k)
        hyInterior hbase.2 hyNotInterior
      refine ⟨j, hji, htiles, ?_⟩
      rcases hdeps with hdeps | hdeps
      · left
        refine ⟨hdeps.1, hdeps.2, ?_, ?_⟩
        · exact finiteOverlapDependency_taskPatch_subset facePatch base T.tile lower upper
            horder hdeps.1
        refine ⟨hxface, ?_⟩
        change (let y := forgetLastCoordinate n x;
          y ∈ euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inr (i, j)) ∧
            projectionFiberSubdivisionEndpoint lower upper k.castSucc y ≤ x (Fin.last n) ∧
              x (Fin.last n) ≤ projectionFiberSubdivisionEndpoint lower upper k.succ y)
        have hpairBase : forgetLastCoordinate n x ∈
            euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inr (i, j)) := by
          change forgetLastCoordinate n x ∈
            euclideanProperConeBaseTile base C ∩ (T.tile i ∩ T.tile j)
          exact ⟨hcone, htiles.1, htiles.2⟩
        exact ⟨hpairBase, hstrip.2.1, hstrip.2.2⟩
      · right
        refine ⟨hdeps.1, hdeps.2, ?_, ?_⟩
        · exact finiteOverlapDependency_taskPatch_subset facePatch base T.tile lower upper
            horder hdeps.1
        refine ⟨hxface, ?_⟩
        change (let y := forgetLastCoordinate n x;
          y ∈ euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inr (j, i)) ∧
            projectionFiberSubdivisionEndpoint lower upper k.castSucc y ≤ x (Fin.last n) ∧
              x (Fin.last n) ≤ projectionFiberSubdivisionEndpoint lower upper k.succ y)
        have hpairBase : forgetLastCoordinate n x ∈
            euclideanProperConeMixedTileBaseTile base T.tile (C, Sum.inr (j, i)) := by
          change forgetLastCoordinate n x ∈
            euclideanProperConeBaseTile base C ∩ (T.tile j ∩ T.tile i)
          exact ⟨hcone, htiles.2, htiles.1⟩
        exact ⟨hpairBase, hstrip.2.1, hstrip.2.2⟩
  | endpoint e =>
      have hxface : x ∈ facePatch := hx.1
      rcases hx.2 with ⟨y, hybase, rfl⟩
      have hyInterior' : y ∈ interior base := by
        simpa [projectionFiberSubdivisionEndpointGraphPoint, forgetLastCoordinate] using hyInterior
      have hyNotInterior' : y ∉ interior (T.tile i) := by
        simpa [projectionFiberSubdivisionEndpointGraphPoint, forgetLastCoordinate] using hyNotInterior
      change y ∈ euclideanProperConeBaseTile base C ∩ T.tile i at hybase
      have hcone : y ∈ euclideanProperConeBaseTile base C := hybase.1
      obtain ⟨j, hji, htiles, hdeps⟩ := compactSmallBaseTiling_boundary_overlap_tasks_at
        T C (.endpoint e)
        hyInterior' hybase.2 hyNotInterior'
      refine ⟨j, hji, ?_, ?_⟩
      · simpa [projectionFiberSubdivisionEndpointGraphPoint, forgetLastCoordinate] using htiles
      rcases hdeps with hdeps | hdeps
      · left
        refine ⟨hdeps.1, hdeps.2, ?_, ?_⟩
        · exact finiteOverlapDependency_taskPatch_subset facePatch base T.tile lower upper
            horder hdeps.1
        refine ⟨hxface, ?_⟩
        exact ⟨y, by
          change y ∈ euclideanProperConeBaseTile base C ∩ (T.tile i ∩ T.tile j)
          exact ⟨hcone, htiles.1, htiles.2⟩, rfl⟩
      · right
        refine ⟨hdeps.1, hdeps.2, ?_, ?_⟩
        · exact finiteOverlapDependency_taskPatch_subset facePatch base T.tile lower upper
            horder hdeps.1
        refine ⟨hxface, ?_⟩
        exact ⟨y, by
          change y ∈ euclideanProperConeBaseTile base C ∩ (T.tile j ∩ T.tile i)
          exact ⟨hcone, htiles.2, htiles.1⟩, rfl⟩

end FanRefinement
end CRNT
