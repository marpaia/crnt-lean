import CRNT.Dynamics.ComplexBalanceCycleDecomposition
import CRNT.Dynamics.ComplexBalanceStoichFan
import CRNT.Dynamics.ToricInclusion
import CRNT.Geometry.FanRefinement

/-!
# Toric-field inclusion on stoichiometric space

This module restricts the source-order toric differential inclusion to the stoichiometric
subspace. It provides an intrinsic finite cone family covering that subspace and places the
complex-balanced mass-action vector field in the toric field at the projected relative-log
state. These are local ingredients for a zero-separating-surface argument.
-/

open scoped InnerProductSpace

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The intrinsic source-order fan has dual-finitely-generated cells, with the finite
half-space representation proved in `ComplexBalanceStoichFan`. -/
theorem relativeSourceOrderStoichFan_hasDualFGCells (N : Network S) :
    CRNT.FanRefinement.HasDualFGCells N.relativeSourceOrderStoichFan := by
  intro C hC
  rw [N.mem_relativeSourceOrderStoichFan] at hC
  rcases hC with ⟨w, rfl⟩
  exact N.relativeSourceOrderConeInStoich_dualFG w

/-- The sign-reversed source-order fan retains finite half-space representations because its
cells are negations of cells of the original source-order fan. -/
theorem relativeSourceOrderNegativeStoichFan_hasDualFGCells (N : Network S) :
    CRNT.FanRefinement.HasDualFGCells N.relativeSourceOrderNegativeStoichFan :=
  CRNT.FanRefinement.negatedFan_hasDualFGCells N.relativeSourceOrderStoichFan
    (N.relativeSourceOrderStoichFan_hasDualFGCells)

/-- Coordinates on the intrinsic stoichiometric space, indexed by its actual dimension. The
chosen finite basis is only a chart choice; the resulting complete fan refinement below carries
the network's source-order geometry into the coordinate space used by projective tile atlases. -/
noncomputable def euclideanStoichCoordinateEquiv (N : Network S) :
    N.euclideanStoichSubspace ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ N.euclideanStoichSubspace)) := by
  let b := Module.finBasis ℝ N.euclideanStoichSubspace
  exact b.equivFun.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin (Module.finrank ℝ N.euclideanStoichSubspace)) ℝ).symm

/-- A complete polyhedral fan in finite coordinates refines the transported negative source-order
fan of the network. This supplies the actual fan-label input for a Craciun projective tile chart,
rather than leaving its fan parameter unrelated to the complex-balanced network. -/
theorem exists_coordinate_refinement_of_relativeSourceOrderNegativeStoichFan
    (N : Network S) :
    ∃ F : CRNT.Fan
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ N.euclideanStoichSubspace))),
      CRNT.IsPolyhedralFan F ∧
      CRNT.FanRefinement.HasDualFGCells F ∧
      CRNT.FanRefinement.Refines F
        (CRNT.FanRefinement.linearImageFamily
          N.euclideanStoichCoordinateEquiv.toContinuousLinearMap
          N.relativeSourceOrderNegativeStoichFan) := by
  let e := N.euclideanStoichCoordinateEquiv
  let f : N.euclideanStoichSubspace →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ N.euclideanStoichSubspace)) :=
    e.toContinuousLinearMap
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ N.euclideanStoichSubspace)) →L[ℝ]
      N.euclideanStoichSubspace := e.symm.toContinuousLinearMap
  have hfg : ∀ y, f (g y) = y := by
    intro y
    exact e.apply_symm_apply y
  have hv0 : f (0 : N.euclideanStoichSubspace) = 0 := map_zero f
  have hdecomp : ∀ x : N.euclideanStoichSubspace,
      ∃ t : ℝ, x = g (f x) + t • (0 : N.euclideanStoichSubspace) := by
    intro x
    refine ⟨0, ?_⟩
    simp [f, g, e.symm_apply_apply]
  exact CRNT.FanRefinement.exists_polyhedral_fan_refinement_of_oneDimensional_projection
    N.relativeSourceOrderNegativeStoichFan
    N.relativeSourceOrderNegativeStoichFan_isPolyhedralFan
    N.relativeSourceOrderNegativeStoichFan_hasDualFGCells
    f g 0 hfg hv0 hdecomp

/-- The common refinement of the toric source-order fan with any dual-finitely-generated
polyhedral fan is again a polyhedral fan. This is the entry point for combining toric chambers
with a simplicial subdivision in the zero-separating construction. -/
theorem relativeSourceOrderStoichFan_intersection_isPolyhedralFan
    (N : Network S) (G : CRNT.Fan N.euclideanStoichSubspace)
    (hG : CRNT.IsPolyhedralFan G) (hGdual : CRNT.FanRefinement.HasDualFGCells G) :
    CRNT.IsPolyhedralFan
      (CRNT.FanRefinement.intersectionFamily N.relativeSourceOrderStoichFan G) :=
  CRNT.FanRefinement.intersectionFamily_isPolyhedralFan_of_dualFG
    N.relativeSourceOrderStoichFan_isPolyhedralFan hG
    N.relativeSourceOrderStoichFan_hasDualFGCells hGdual

/-- Iteratively intersecting the intrinsic source-order fan with a finite list of supplied
polyhedral fans preserves the fan axioms and finite half-space representation of every cell. -/
theorem relativeSourceOrderStoichFan_iteratedIntersection_isPolyhedralFan
    (N : Network S) (Gs : List (CRNT.Fan N.euclideanStoichSubspace))
    (hG : ∀ G ∈ Gs, CRNT.IsPolyhedralFan G)
    (hGdual : ∀ G ∈ Gs, CRNT.FanRefinement.HasDualFGCells G) :
    CRNT.IsPolyhedralFan
        (CRNT.FanRefinement.iteratedIntersectionFamily N.relativeSourceOrderStoichFan Gs) ∧
      CRNT.FanRefinement.HasDualFGCells
        (CRNT.FanRefinement.iteratedIntersectionFamily N.relativeSourceOrderStoichFan Gs) :=
  CRNT.FanRefinement.iteratedIntersectionFamily_isPolyhedralFan
    N.relativeSourceOrderStoichFan Gs N.relativeSourceOrderStoichFan_isPolyhedralFan
    N.relativeSourceOrderStoichFan_hasDualFGCells hG hGdual

/-- The same finite common-refinement construction applies to the sign-reversed fan consumed by
the toric field. -/
theorem relativeSourceOrderNegativeStoichFan_iteratedIntersection_isPolyhedralFan
    (N : Network S) (Gs : List (CRNT.Fan N.euclideanStoichSubspace))
    (hG : ∀ G ∈ Gs, CRNT.IsPolyhedralFan G)
    (hGdual : ∀ G ∈ Gs, CRNT.FanRefinement.HasDualFGCells G) :
    CRNT.IsPolyhedralFan
        (CRNT.FanRefinement.iteratedIntersectionFamily N.relativeSourceOrderNegativeStoichFan Gs) ∧
      CRNT.FanRefinement.HasDualFGCells
        (CRNT.FanRefinement.iteratedIntersectionFamily N.relativeSourceOrderNegativeStoichFan Gs) :=
  CRNT.FanRefinement.iteratedIntersectionFamily_isPolyhedralFan
    N.relativeSourceOrderNegativeStoichFan Gs
    N.relativeSourceOrderNegativeStoichFan_isPolyhedralFan
    N.relativeSourceOrderNegativeStoichFan_hasDualFGCells hG hGdual

/-- A common refinement preserves the coarse fan's toric field by adding admissible polar cones.
If `x` is within `δ` of a coarse cell `C`, choose a nearby point in `C` and a fine cell `D`
containing that point. The intersection cell `C ⊓ D` remains within `δ`, and its dual contains
the dual of `C`. -/
theorem toricField_subset_intersectionFamily_of_right_covers
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F G : CRNT.Fan E) (δ : ℝ) (x : E)
    (hGcover : ∀ y : E, ∃ D ∈ G, y ∈ (D : Set E)) :
    (CRNT.toricField F δ x : Set E) ⊆
      (CRNT.toricField (CRNT.FanRefinement.intersectionFamily F G) δ x : Set E) := by
  classical
  apply Submodule.span_mono
  intro z hz
  rcases CRNT.mem_toricGenerators.mp hz with ⟨C, hC, hdist, hzC⟩
  have hCne : (C : Set E).Nonempty := ⟨0, zero_mem C⟩
  obtain ⟨y, hyC, hxy⟩ := (Metric.infDist_lt_iff hCne).mp hdist
  obtain ⟨D, hD, hyD⟩ := hGcover y
  let H : ProperCone ℝ E := C ⊓ D
  have hHmem : H ∈ CRNT.FanRefinement.intersectionFamily F G := by
    apply Finset.mem_image.mpr
    exact ⟨(C, D), Finset.mem_product.mpr ⟨hC, hD⟩, rfl⟩
  have hyH : y ∈ (H : Set E) := by
    change y ∈ C ⊓ D
    exact ⟨hyC, hyD⟩
  have hdistH : Metric.infDist x (H : Set E) < δ :=
    lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hyH) hxy
  have hzH : z ∈ CRNT.coneDual (H : Set E) := by
    rw [CRNT.mem_coneDual]
    intro v hv
    have hvC : v ∈ (C : Set E) := by
      change v ∈ C ⊓ D at hv
      exact hv.1
    exact (CRNT.mem_coneDual.mp hzC) hvC
  exact CRNT.mem_toricGenerators.mpr ⟨H, hHmem, hdistH, hzH⟩

/-- Repeated common refinements preserve the original toric field whenever each added fan covers
the ambient space. This is the field-transfer invariant needed when a geometric construction uses
several successive fan subdivisions. -/
theorem toricField_subset_iteratedIntersectionFamily_of_covering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : CRNT.Fan E) (Gs : List (CRNT.Fan E)) (δ : ℝ) (x : E)
    (hcover : ∀ G ∈ Gs, ∀ y : E, ∃ D ∈ G, y ∈ (D : Set E)) :
    (CRNT.toricField F δ x : Set E) ⊆
      (CRNT.toricField (CRNT.FanRefinement.iteratedIntersectionFamily F Gs) δ x : Set E) := by
  have hAux : ∀ (xs : List (CRNT.Fan E)) (F : CRNT.Fan E) (δ : ℝ) (x : E),
      (∀ G ∈ xs, ∀ y : E, ∃ D ∈ G, y ∈ (D : Set E)) →
      (CRNT.toricField F δ x : Set E) ⊆
        (CRNT.toricField (CRNT.FanRefinement.iteratedIntersectionFamily F xs) δ x : Set E) := by
    intro xs
    induction xs with
    | nil =>
        intro F δ x _
        exact Set.Subset.rfl
    | cons G Gs ih =>
        intro F δ x hcover
        have hhead : ∀ y : E, ∃ D ∈ G, y ∈ (D : Set E) := hcover G (by simp)
        have htail : ∀ H ∈ Gs, ∀ y : E, ∃ D ∈ H, y ∈ (D : Set E) := by
          intro H hH y
          exact hcover H (by simp [hH]) y
        have hstep := toricField_subset_intersectionFamily_of_right_covers F G δ x hhead
        have hrest := ih (CRNT.FanRefinement.intersectionFamily F G) δ x htail
        exact hstep.trans hrest
  exact hAux Gs F δ x hcover

/-- The intrinsic source-order field remains included after successive intersections with any
finite list of covering fans on stoichiometric space. -/
theorem toricField_relativeSourceOrderStoichFan_subset_iteratedCommonRefinement
    (N : Network S) (Gs : List (CRNT.Fan N.euclideanStoichSubspace)) (δ : ℝ)
    (x : N.euclideanStoichSubspace)
    (hcover : ∀ G ∈ Gs, ∀ y : N.euclideanStoichSubspace,
      ∃ D ∈ G, y ∈ (D : Set N.euclideanStoichSubspace)) :
    (CRNT.toricField N.relativeSourceOrderNegativeStoichFan δ x :
        Set N.euclideanStoichSubspace) ⊆
      (CRNT.toricField
        (CRNT.FanRefinement.iteratedIntersectionFamily
          N.relativeSourceOrderNegativeStoichFan Gs) δ x :
        Set N.euclideanStoichSubspace) :=
  toricField_subset_iteratedIntersectionFamily_of_covering
    N.relativeSourceOrderNegativeStoichFan Gs δ x hcover

/-- The intrinsic complex-balanced source-order field embeds into the field of its common
refinement with any covering fan. This is the field-level transfer needed before a refined
zero-separating surface can control the original mass-action inclusion. -/
theorem toricField_relativeSourceOrderStoichFan_subset_commonRefinement
    (N : Network S) (G : CRNT.Fan N.euclideanStoichSubspace) (δ : ℝ) (x : N.euclideanStoichSubspace)
    (hG : CRNT.IsPolyhedralFan G) :
    (CRNT.toricField N.relativeSourceOrderNegativeStoichFan δ x :
        Set N.euclideanStoichSubspace) ⊆
      (CRNT.toricField
        (CRNT.FanRefinement.intersectionFamily N.relativeSourceOrderNegativeStoichFan G)
        δ x : Set N.euclideanStoichSubspace) := by
  apply toricField_subset_intersectionFamily_of_right_covers
  intro y
  have hyG : ∃ D ∈ G, y ∈ (D : Set N.euclideanStoichSubspace) := by
    have hy := congrArg (fun s : Set N.euclideanStoichSubspace => y ∈ s) hG.covers
    simpa using hy
  exact hyG

private theorem massActionVectorField_stoichForFan (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace := by
  rw [N.massActionVectorField_eq_sum κ x]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- The finite source-order chamber family, reoriented and restricted to the stoichiometric space.
Every cone is the preimage of an ambient negative source-order cone under the subspace inclusion. -/
noncomputable def relativeSourceOrderNegativeConeStoichFan (N : Network S) :
    CRNT.Fan N.euclideanStoichSubspace := by
  classical
  exact N.relativeSourceOrderNegativeConeFamily.image fun C =>
    C.comap N.euclideanStoichSubspace.subtypeL

/-- Restricting an ambient sign-reversed source-order cone to stoichiometric space is exactly the
sign-reversal of the corresponding intrinsic source-order cone. -/
theorem relativeSourceOrderNegativeCone_comap_eq_negatedIntrinsic (N : Network S)
    (w : S → ℝ) :
    (N.relativeSourceOrderNegativeCone w).comap N.euclideanStoichSubspace.subtypeL =
      CRNT.negatedProperCone (N.relativeSourceOrderConeInStoich w) := by
  apply ProperCone.ext
  intro z
  simp [relativeSourceOrderNegativeCone, relativeSourceOrderConeInStoich,
    CRNT.negatedProperCone]

/-- The earlier ambient-comap presentation of the negative fan is definitionally equivalent, as a
finite family of cones, to the complete sign-reversed fan built directly on stoichiometric space.
This identifies the fan used by the mass-action selector with the intrinsic complete fan. -/
theorem relativeSourceOrderNegativeConeStoichFan_eq_relativeSourceOrderNegativeStoichFan
    (N : Network S) :
    N.relativeSourceOrderNegativeConeStoichFan = N.relativeSourceOrderNegativeStoichFan := by
  classical
  apply Finset.ext
  intro C
  rw [relativeSourceOrderNegativeConeStoichFan, relativeSourceOrderNegativeConeFamily,
    relativeSourceOrderNegativeStoichFan, CRNT.negatedFan]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨A, ⟨D, hD, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := (N.mem_relativeSourceOrderStoichConeFamily).mp hD
    refine ⟨N.relativeSourceOrderConeInStoich w, ?_, ?_⟩
    · rw [N.mem_relativeSourceOrderStoichFan]
      exact ⟨w, rfl⟩
    · exact N.relativeSourceOrderNegativeCone_comap_eq_negatedIntrinsic w
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨w, rfl⟩ := (N.mem_relativeSourceOrderStoichFan).mp hD
    refine ⟨(N.relativeSourceOrderStoichProperCone w).comap
      (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))), ?_, ?_⟩
    · refine ⟨N.relativeSourceOrderStoichProperCone w, ?_, rfl⟩
      exact (N.mem_relativeSourceOrderStoichConeFamily).mpr ⟨w, rfl⟩
    · symm
      exact N.relativeSourceOrderNegativeCone_comap_eq_negatedIntrinsic w

/-- The ambient negative chamber selected by a projected relative logarithm occurs after restriction
in the ambient-comap presentation of the fan. -/
theorem relativeSourceOrderNegativeConeComapInStoich_mem_fan (N : Network S) (w : S → ℝ) :
    (N.relativeSourceOrderNegativeCone w).comap N.euclideanStoichSubspace.subtypeL ∈
      N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan]
  apply Finset.mem_image.mpr
  refine ⟨N.relativeSourceOrderNegativeCone w, ?_, rfl⟩
  exact N.relativeSourceOrderNegativeCone_mem_family w

/-- The restricted negative source-order cones cover the whole stoichiometric subspace. -/
theorem exists_relativeSourceOrderNegativeConeStoichFan_mem (N : Network S)
    (z : N.euclideanStoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderNegativeConeStoichFan, z ∈ C := by
  classical
  have hzstoich : CRNT.toEuclid.symm z.1 ∈ N.stoichSubspace := by
    have hzproperty := z.property
    change z.1 ∈ Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace at hzproperty
    rw [Submodule.mem_map] at hzproperty
    rcases hzproperty with ⟨u, hu, huz⟩
    rw [← huz]
    simpa using hu
  obtain ⟨C, hC, hzC⟩ := N.exists_relativeSourceOrderNegativeConeFamily_mem hzstoich
  refine ⟨C.comap N.euclideanStoichSubspace.subtypeL, ?_, ?_⟩
  · rw [relativeSourceOrderNegativeConeStoichFan]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  · exact ProperCone.mem_comap.mpr hzC

/-- The complex-balanced mass-action vector field lies in the intrinsic toric field at the
negative projected relative-log state. -/
theorem massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ) :
    let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    let w := N.relativeLogStoichProjection u
    ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩ ∈
      CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ
        (-⟨CRNT.toEuclid w, by
          rw [Network.euclideanStoichSubspace, Submodule.mem_map]
          exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩) := by
  dsimp
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w : S → ℝ := N.relativeLogStoichProjection u
  have hfieldStoich : N.massActionVectorField κ x ∈ N.stoichSubspace :=
    N.massActionVectorField_stoichForFan κ x
  let v : N.euclideanStoichSubspace := ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x, hfieldStoich, rfl⟩⟩
  have hprojStoich : w ∈ N.stoichSubspace := N.relativeLogStoichProjection_mem u
  let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨w, hprojStoich, rfl⟩⟩
  let Cambient : ProperCone ℝ (EuclideanSpace ℝ S) := N.relativeSourceOrderNegativeCone w
  let C : ProperCone ℝ N.euclideanStoichSubspace :=
    Cambient.comap N.euclideanStoichSubspace.subtypeL
  have hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan := by
    change (N.relativeSourceOrderNegativeCone w).comap
      N.euclideanStoichSubspace.subtypeL ∈ N.relativeSourceOrderNegativeConeStoichFan
    rw [N.relativeSourceOrderNegativeConeStoichFan_eq_relativeSourceOrderNegativeStoichFan]
    rw [N.relativeSourceOrderNegativeCone_comap_eq_negatedIntrinsic w]
    exact N.relativeSourceOrderNegativeConeInStoich_mem_fan w
  have hX : -X ∈ C := by
    change (N.euclideanStoichSubspace.subtypeL (-X)) ∈ Cambient
    have hstate : -CRNT.toEuclid w ∈ Cambient :=
      N.negativeRelativeLogStoichProjection_mem_relativeSourceOrderNegativeCone u
    simpa [X] using hstate
  have hdist : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) = 0 :=
    Metric.infDist_zero_of_mem hX
  have hnear : Metric.infDist (-X) (C : Set N.euclideanStoichSubspace) < δ := by
    rw [hdist]
    exact hδ
  have hpolar := N.massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    κ hx hxs hcb
  have hdual : v ∈ coneDual (C : Set N.euclideanStoichSubspace) := by
    rw [mem_coneDual]
    intro z hz
    have hzamb : z.1 ∈ Cambient := by
      change z ∈ C at hz
      exact ProperCone.mem_comap.mp hz
    have hzpos : -z.1 ∈ N.relativeSourceOrderStoichCone w := by
      change z.1 ∈ N.relativeSourceOrderNegativeCone w at hzamb
      exact (N.mem_relativeSourceOrderNegativeCone w z.1).mp hzamb
    have hle : ⟪-z.1, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ ≤ 0 := by
      rw [mem_polarCone] at hpolar
      exact hpolar hzpos
    have hinner : ⟪z, v⟫_ℝ = -⟪-z.1, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
      simp [v]
    rw [hinner]
    exact neg_nonneg.mpr hle
  have htoric := CRNT.coneDual_le_toricField hC hnear hdual
  simpa [v, X, C, Cambient] using htoric

/-- The mass-action selector theorem with the complete negative fan named intrinsically on
stoichiometric space. -/
theorem massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ) :
    let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    let w := N.relativeLogStoichProjection u
    ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩ ∈
      CRNT.toricField N.relativeSourceOrderNegativeStoichFan δ
        (-⟨CRNT.toEuclid w, by
          rw [Network.euclideanStoichSubspace, Submodule.mem_map]
          exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩) := by
  simpa only [N.relativeSourceOrderNegativeConeStoichFan_eq_relativeSourceOrderNegativeStoichFan]
    using N.massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan
      κ hx hxs hcb hδ

/-- The complex-balanced mass-action selector also lies in every covering common refinement of
the intrinsic source-order fan. This combines the network-specific selector with the field
inclusion proved above. -/
theorem massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan_intersection
    (N : Network S) (κ : N.RateConstants) (G : CRNT.Fan N.euclideanStoichSubspace)
    (hG : CRNT.IsPolyhedralFan G) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ) :
    let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
    let w := N.relativeLogStoichProjection u
    ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩ ∈
      CRNT.toricField
        (CRNT.FanRefinement.intersectionFamily N.relativeSourceOrderNegativeStoichFan G)
        δ (-⟨CRNT.toEuclid w, by
          rw [Network.euclideanStoichSubspace, Submodule.mem_map]
          exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩) := by
  dsimp
  apply N.toricField_relativeSourceOrderStoichFan_subset_commonRefinement G δ _ hG
  exact N.massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan
    κ hx hxs hcb hδ

/-- **Strict attraction inside an intrinsic source-order chamber.** At a positive
non-equilibrium, the mass-action field pairs strictly positively with every interior direction
of the selected negative source-order cone in stoichiometric space. The pointwise toric inclusion
gives the weak sign; nonvanishing of the field upgrades it to strictness on the chamber interior. -/
theorem massActionVectorField_inner_pos_of_mem_interior_sourceOrderNegativeCone
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnotcb : ¬ N.IsComplexBalanced κ x)
    {z : N.euclideanStoichSubspace}
    (hz : z ∈ interior (((N.relativeSourceOrderNegativeCone
      (N.relativeLogStoichProjection
        (fun s => Real.log (x s) - Real.log (xstar s)))).comap
          N.euclideanStoichSubspace.subtypeL :
            ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace)) :
    0 < ⟪z, ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
      rw [Network.euclideanStoichSubspace, Submodule.mem_map]
      exact ⟨N.massActionVectorField κ x,
        N.massActionVectorField_stoichForFan κ x, rfl⟩⟩⟫_ℝ := by
  let w : S → ℝ := N.relativeLogStoichProjection
    (fun s => Real.log (x s) - Real.log (xstar s))
  let v : N.euclideanStoichSubspace := ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x,
      N.massActionVectorField_stoichForFan κ x, rfl⟩⟩
  have hpolarAmbient := N.massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    κ hx hxs hcb
  have hfieldne := N.massActionVectorField_ne_zero_of_not_complexBalanced
    κ hx hxs hcb hnotcb
  have hvne : v ≠ 0 := by
    intro hv
    apply hfieldne
    apply CRNT.toEuclid.injective
    exact congrArg Subtype.val hv
  have hpolar : -v ∈ CRNT.polarCone
      (((N.relativeSourceOrderNegativeCone w).comap
        N.euclideanStoichSubspace.subtypeL :
          ProperCone ℝ N.euclideanStoichSubspace) : Set N.euclideanStoichSubspace) := by
    rw [CRNT.mem_polarCone]
    intro q hq
    have hqAmbient : q.1 ∈ N.relativeSourceOrderNegativeCone w :=
      ProperCone.mem_comap.mp hq
    have hqPositive : -q.1 ∈ N.relativeSourceOrderStoichCone w := by
      change q.1 ∈ N.relativeSourceOrderNegativeCone w at hqAmbient
      exact (N.mem_relativeSourceOrderNegativeCone w q.1).mp hqAmbient
    have hle := (CRNT.mem_polarCone.mp hpolarAmbient) hqPositive
    have hinner : ⟪q, -v⟫_ℝ =
        ⟪-q.1, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
      simp [v]
    rw [hinner]
    exact hle
  have hstrict := CRNT.polarCone_inner_lt_zero_of_mem_interior hpolar
    (by
      intro hv
      apply hvne
      exact neg_eq_zero.mp hv) hz
  have hneg : -⟪z, v⟫_ℝ < 0 := by
    simpa only [inner_neg_right] using hstrict
  have hpos : 0 < ⟪z, v⟫_ℝ := by linarith
  simpa [v] using hpos

/-- The relative-log toric field on concentrations.  Its state is a concentration vector, while
its admissible velocities are the image in concentration coordinates of the intrinsic
stoichiometric toric field. -/
noncomputable def relativeSourceOrderToricInclusionField (N : Network S)
    (xstar : Concentration S) (δ : ℝ) :
    DifferentialInclusion.Field (Concentration S) := fun x =>
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w := N.relativeLogStoichProjection u
  let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩
  (fun v : N.euclideanStoichSubspace => CRNT.toEuclid.symm v.1) ''
    (CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ (-X) :
      Set N.euclideanStoichSubspace)

/-- **Mass-action selects the relative-log toric field.** At every positive concentration, the
genuine mass-action velocity belongs to the intrinsic toric field built from the source-order fan. -/
theorem massActionVectorField_mem_relativeSourceOrderToricInclusionField
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    {x : Concentration S} (hx : x.Positive) :
    N.massActionVectorField κ x ∈
      N.relativeSourceOrderToricInclusionField xstar δ x := by
  classical
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w := N.relativeLogStoichProjection u
  let X : N.euclideanStoichSubspace := ⟨CRNT.toEuclid w, by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨w, N.relativeLogStoichProjection_mem u, rfl⟩⟩
  let v : N.euclideanStoichSubspace := ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x,
      N.massActionVectorField_stoichForFan κ x, rfl⟩⟩
  have hv := N.massActionVectorField_mem_toricField_relativeSourceOrderNegativeConeStoichFan
    κ hx hxs hcb hδ
  have hvX : v ∈ CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ (-X) := by
    simpa [v, X, u, w] using hv
  change N.massActionVectorField κ x ∈
    (fun q : N.euclideanStoichSubspace => CRNT.toEuclid.symm q.1) ''
      (CRNT.toricField N.relativeSourceOrderNegativeConeStoichFan δ (-X) :
        Set N.euclideanStoichSubspace)
  simpa [v] using Set.mem_image_of_mem
    (fun q : N.euclideanStoichSubspace => CRNT.toEuclid.symm q.1) hvX

/-- Every velocity allowed by the relative-log toric field lies in the stoichiometric subspace. -/
theorem velocity_mem_stoichSubspace_of_mem_relativeSourceOrderToricInclusionField
    (N : Network S) (xstar : Concentration S) (δ : ℝ) {x v : Concentration S}
    (hv : v ∈ N.relativeSourceOrderToricInclusionField xstar δ x) :
    v ∈ N.stoichSubspace := by
  classical
  simp only [relativeSourceOrderToricInclusionField, Set.mem_image] at hv
  rcases hv with ⟨q, _hq, hqv⟩
  have hqmem : q.1 ∈ N.euclideanStoichSubspace := q.property
  change q.1 ∈ Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace at hqmem
  rw [Submodule.mem_map] at hqmem
  rcases hqmem with ⟨z, hz, hzeq⟩
  have hqz : CRNT.toEuclid.symm q.1 = z := by
    apply CRNT.toEuclid.injective
    simpa using hzeq.symm
  have hvz : v = z := hqv.symm.trans hqz
  rw [hvz]
  exact hz

/-- A genuine mass-action trajectory is a solution of the relative-log toric inclusion. -/
theorem isInclusionSolution_massAction_relativeSourceOrder
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → Concentration S}
    (hpos : ∀ t, (γ t).Positive)
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    DifferentialInclusion.IsInclusionSolution
      (fun x => N.relativeSourceOrderToricInclusionField xstar δ x) γ := by
  intro t
  have hd := hderiv t
  have hv := N.massActionVectorField_mem_relativeSourceOrderToricInclusionField
    κ hxs hcb hδ (hpos t)
  have hderiv' : deriv γ t = N.massActionVectorField κ (γ t) := hd.deriv
  constructor
  · rw [hderiv']
    exact hd
  · rw [hderiv']
    exact hv

/-- A positive forward mass-action solution is an interval solution of the relative-log toric
inclusion on nonnegative time. -/
theorem isInclusionSolutionOn_massAction_relativeSourceOrder
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    {γ : ℝ → Concentration S}
    (hpos : ∀ t, t ∈ Set.Ici (0 : ℝ) → (γ t).Positive)
    (hderiv : ∀ t, t ∈ Set.Ici (0 : ℝ) →
      HasDerivWithinAt γ (N.massActionVectorField κ (γ t)) (Set.Ici (0 : ℝ)) t) :
    DifferentialInclusion.IsInclusionSolutionOn
      (fun x => N.relativeSourceOrderToricInclusionField xstar δ x) γ (Set.Ici 0) := by
  intro t ht
  have hd := hderiv t ht
  have hderiv' : derivWithin γ (Set.Ici (0 : ℝ)) t =
      N.massActionVectorField κ (γ t) := hd.derivWithin (uniqueDiffOn_Ici 0 t ht)
  refine ⟨?_, ?_⟩
  · rw [hderiv']
    exact hd
  · rw [hderiv']
    exact N.massActionVectorField_mem_relativeSourceOrderToricInclusionField
      κ hxs hcb hδ (hpos t ht)

/-- A curve solving the relative-log toric inclusion stays in its initial stoichiometric affine
class. -/
theorem sub_mem_stoichSubspace_of_relativeSourceOrderToricInclusionSolution
    (N : Network S) (xstar : Concentration S) (δ : ℝ)
    {γ : ℝ → Concentration S} (hsol : DifferentialInclusion.IsInclusionSolution
      (fun x => N.relativeSourceOrderToricInclusionField xstar δ x) γ)
    {a b : ℝ} (hab : a ≤ b) :
    γ b - γ a ∈ N.stoichSubspace := by
  rw [← orthSum_orthSum N.stoichSubspace, mem_orthSum]
  intro w hw
  have hp : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun τ => ∑ i, w i * γ τ i) (0 : ℝ) (Set.Icc a b) t := by
    intro t ht
    have hzero : (∑ i, w i * deriv γ t i) = 0 := by
      exact (mem_orthSum.mp hw) _
        (N.velocity_mem_stoichSubspace_of_mem_relativeSourceOrderToricInclusionField
          xstar δ (x := γ t) (v := deriv γ t) (hsol t).2)
    have hfun : (fun τ : ℝ => ∑ i, w i * γ τ i) =
        ∑ i ∈ (Finset.univ : Finset S), (fun τ : ℝ => w i * γ τ i) := by
      funext τ
      rw [Finset.sum_apply]
    have hd := HasDerivAt.sum (u := (Finset.univ : Finset S))
      (fun i _ => HasDerivAt.const_mul (w i) ((hasDerivAt_pi.mp (hsol t).1) i))
    rw [hzero] at hd
    rw [hfun]
    exact hd.hasDerivWithinAt
  have hconst : (∑ i, w i * γ b i) = (∑ i, w i * γ a i) := by
    have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hp
      (fun t _ => by simp) (convex_Icc a b) ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩
    simp only [zero_mul] at hle
    have h0 : ‖(∑ i, w i * γ b i) - (∑ i, w i * γ a i)‖ = 0 :=
      le_antisymm hle (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at h0
  calc
    ∑ i, (γ b - γ a) i * w i
        = ∑ i, (w i * γ b i - w i * γ a i) :=
          Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
    _ = (∑ i, w i * γ b i) - (∑ i, w i * γ a i) :=
          Finset.sum_sub_distrib (f := fun i => w i * γ b i) (g := fun i => w i * γ a i)
    _ = 0 := by rw [hconst, sub_self]


private theorem euclideanStoichSubspace_subtypeL_isClosedEmbedding (N : Network S) :
    Topology.IsClosedEmbedding N.euclideanStoichSubspace.subtypeL := by
  apply Submodule.isClosedEmbedding_subtypeL
  exact Submodule.closed_of_finiteDimensional N.euclideanStoichSubspace

private theorem properMap_subtype_eq_pointedMap (N : Network S)
    (C : ProperCone ℝ N.euclideanStoichSubspace) :
    ((ProperCone.map N.euclideanStoichSubspace.subtypeL C :
      ProperCone ℝ (EuclideanSpace ℝ S)) : PointedCone ℝ (EuclideanSpace ℝ S)) =
      PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
        (C : PointedCone ℝ N.euclideanStoichSubspace) := by
  apply PointedCone.ext
  intro x
  change x ∈ ProperCone.map N.euclideanStoichSubspace.subtypeL C ↔
    x ∈ PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
      (C : PointedCone ℝ N.euclideanStoichSubspace)
  rw [ProperCone.mem_map]
  have hclosed : IsClosed
      (N.euclideanStoichSubspace.subtypeL '' (C : Set N.euclideanStoichSubspace)) :=
    (N.euclideanStoichSubspace_subtypeL_isClosedEmbedding.isClosed_iff_image_isClosed).mp
      C.isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL '' (C : Set N.euclideanStoichSubspace)) ↔ _
  rw [hclosed.closure_eq, PointedCone.mem_map]
  simp only [Set.mem_image]
  exact Iff.rfl

private theorem map_comap_negativeStoichFamily (N : Network S)
    {C : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderNegativeConeFamily) :
    ProperCone.map N.euclideanStoichSubspace.subtypeL
        (C.comap N.euclideanStoichSubspace.subtypeL) = C := by
  have hV : ∀ x : EuclideanSpace ℝ S, x ∈ C →
      x ∈ N.euclideanStoichSubspace := by
    intro x hx
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    refine ⟨CRNT.toEuclid.symm x,
      N.stoich_of_mem_relativeSourceOrderNegativeConeFamily hC hx, ?_⟩
    exact CRNT.toEuclid.apply_symm_apply x
  have himage :
      N.euclideanStoichSubspace.subtypeL ''
          (C.comap N.euclideanStoichSubspace.subtypeL :
            Set N.euclideanStoichSubspace) = (C : Set (EuclideanSpace ℝ S)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ProperCone.mem_comap.mp hz
    · intro hx
      refine ⟨⟨x, hV x hx⟩, ProperCone.mem_comap.mpr hx, rfl⟩
  apply ProperCone.ext
  intro x
  rw [ProperCone.mem_map]
  have hclosed : IsClosed
      (N.euclideanStoichSubspace.subtypeL ''
        (C.comap N.euclideanStoichSubspace.subtypeL :
          Set N.euclideanStoichSubspace)) := by
    rw [himage]
    exact C.isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL ''
        (C.comap N.euclideanStoichSubspace.subtypeL :
          Set N.euclideanStoichSubspace)) ↔ _
  rw [hclosed.closure_eq, himage]
  rfl

private theorem comap_map_subtype_eq (N : Network S)
    (C : ProperCone ℝ N.euclideanStoichSubspace) :
    (ProperCone.map N.euclideanStoichSubspace.subtypeL C).comap
        N.euclideanStoichSubspace.subtypeL = C := by
  have hmap := N.properMap_subtype_eq_pointedMap C
  have hinj : Function.Injective
      N.euclideanStoichSubspace.subtypeL.toLinearMap := by
    intro x y h
    exact Subtype.ext h
  apply ProperCone.ext
  intro x
  constructor
  · intro hx
    have hproper : N.euclideanStoichSubspace.subtypeL x ∈
        (ProperCone.map N.euclideanStoichSubspace.subtypeL C :
          PointedCone ℝ (EuclideanSpace ℝ S)) := ProperCone.mem_comap.mp hx
    have hx' : N.euclideanStoichSubspace.subtypeL x ∈
        PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
          (C : PointedCone ℝ N.euclideanStoichSubspace) := by
      simpa only [hmap] using hproper
    obtain ⟨y, hy, hxy⟩ := PointedCone.mem_map.mp hx'
    have : y = x := hinj hxy
    simpa [this] using hy
  · intro hx
    apply ProperCone.mem_comap.mpr
    have hx' : N.euclideanStoichSubspace.subtypeL x ∈
        PointedCone.map N.euclideanStoichSubspace.subtypeL.toLinearMap
          (C : PointedCone ℝ N.euclideanStoichSubspace) :=
      PointedCone.mem_map.mpr ⟨x, hx, rfl⟩
    have hproper : N.euclideanStoichSubspace.subtypeL x ∈
        (ProperCone.map N.euclideanStoichSubspace.subtypeL C :
          PointedCone ℝ (EuclideanSpace ℝ S)) := by
      simpa only [hmap] using hx'
    exact ProperCone.mem_comap.mpr hproper

private theorem comap_inf_stoich (N : Network S)
    (C D : ProperCone ℝ (EuclideanSpace ℝ S)) :
    (C ⊓ D).comap N.euclideanStoichSubspace.subtypeL =
      C.comap N.euclideanStoichSubspace.subtypeL ⊓
        D.comap N.euclideanStoichSubspace.subtypeL := by
  apply ProperCone.ext
  intro z
  simp

/-- Every exposed face of a cone in the intrinsic negative source-order fan is again in the fan. -/
theorem relativeSourceOrderNegativeConeStoichFan_faces_mem (N : Network S)
    {C : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan)
    {D : ProperCone ℝ N.euclideanStoichSubspace}
    (hface : CRNT.IsExposedFaceOf D C) :
    D ∈ N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan] at hC ⊢
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  have hface' : PointedCone.IsFaceOf (D : PointedCone ℝ N.euclideanStoichSubspace)
      (C₀.comap N.euclideanStoichSubspace.subtypeL :
        PointedCone ℝ N.euclideanStoichSubspace) :=
    CRNT.isExposedFaceOf_isFaceOf hface
  have hinj : Function.Injective
      N.euclideanStoichSubspace.subtypeL.toLinearMap := by
    intro x y h
    exact Subtype.ext h
  have hmapped := PointedCone.IsFaceOf.map
    N.euclideanStoichSubspace.subtypeL.toLinearMap hinj hface'
  have hmapped' :
      ((ProperCone.map N.euclideanStoichSubspace.subtypeL D :
        ProperCone ℝ (EuclideanSpace ℝ S)) :
          PointedCone ℝ (EuclideanSpace ℝ S)).IsFaceOf C₀ := by
    rw [← N.map_comap_negativeStoichFamily hC₀,
      N.properMap_subtype_eq_pointedMap]
    simpa only [N.properMap_subtype_eq_pointedMap] using hmapped
  have hD₀ := N.relativeSourceOrderNegativeConeFamily_face_mem hC₀ hmapped'
  apply Finset.mem_image.mpr
  refine ⟨ProperCone.map N.euclideanStoichSubspace.subtypeL D, hD₀, ?_⟩
  exact N.comap_map_subtype_eq D

/-- Intersections of cones in the intrinsic negative source-order family belong to the family. -/
theorem relativeSourceOrderNegativeConeStoichFan_inter_mem (N : Network S)
    {C D : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderNegativeConeStoichFan)
    (hD : D ∈ N.relativeSourceOrderNegativeConeStoichFan) :
    C ⊓ D ∈ N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeConeStoichFan] at hC hD ⊢
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_image.mp hD
  have hCD := N.relativeSourceOrderNegativeConeFamily_inter_mem hC₀ hD₀
  refine Finset.mem_image.mpr ⟨C₀ ⊓ D₀, hCD, ?_⟩
  exact (N.comap_inf_stoich C₀ D₀).symm

/-- **The intrinsic negative source-order family is a finite polyhedral fan.** Its exposed faces and
intersections come from the ambient source-order fan; coverage follows by restricting the ambient
cover to the stoichiometric subspace. -/
theorem relativeSourceOrderNegativeConeStoichFan_isPolyhedralFan (N : Network S) :
    CRNT.IsPolyhedralFan N.relativeSourceOrderNegativeConeStoichFan := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro C hC D hface
    exact N.relativeSourceOrderNegativeConeStoichFan_faces_mem hC hface
  · intro C hC D hD
    refine ⟨C ⊓ D, N.relativeSourceOrderNegativeConeStoichFan_inter_mem hC hD, ?_⟩
    ext z
    simp
  · ext z
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨C, hC, hz⟩ := N.exists_relativeSourceOrderNegativeConeStoichFan_mem z
      exact ⟨C, hC, hz⟩

/-- The ambient source-order fan used by the complex-balanced mass-action selector satisfies the
exposed common-face property. Its common cone is the set intersection, and the source-order
construction supplies supporting normals for each incident chamber. -/
theorem relativeSourceOrderNegativeConeFamily_hasExposedCommonFaces (N : Network S) :
    FanRefinement.HasExposedCommonFaces N.relativeSourceOrderNegativeConeFamily := by
  intro C hC D hD
  have hfaces := N.relativeSourceOrderNegativeConeFamily_inter_commonExposedFace hC hD
  refine ⟨C ⊓ D, N.relativeSourceOrderNegativeConeFamily_inter_mem hC hD, ?_, hfaces.1,
    hfaces.2⟩
  ext z
  simp

/-- The actual complex-balanced mass-action vector field obeys every normal inequality of a
source-order chamber whenever the full projected-log neighborhood lies in that chamber. The
proof combines the network's toric-field selector with the exposed-face local field bridge. -/
theorem massActionVectorField_inner_nonneg_of_projectedLogBall
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ)
    {D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hD : D ∈ N.relativeSourceOrderNegativeConeFamily)
    {n : EuclideanSpace ℝ S} (hn : n ∈ (D : Set (EuclideanSpace ℝ S)))
    (hball : Metric.ball (-CRNT.toEuclid (N.relativeLogStoichProjection
      (fun s => Real.log (x s) - Real.log (xstar s)))) δ ⊆
        interior (D : Set (EuclideanSpace ℝ S))) :
    0 ≤ ⟪n, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
  have hselector := N.massActionVectorField_mem_relativeSourceOrderToricField
    κ hx hxs hcb hδ
  have hlocal := FanRefinement.toricField_subset_coneDual_of_ball_inside_cell
    (N.relativeSourceOrderNegativeConeFamily_hasExposedCommonFaces) hD hball
  exact coneDual_subset_dualHalfPlane_of_mem hn (hlocal hselector)

/-- Uniform version on a compact patch: if the projected-log states lie in a compact subset of
one source-order chamber's interior, every refined-cell normal contained in that chamber has
nonnegative pairing with the complex-balanced mass-action field, with one common radius. -/
theorem massActionVectorField_inner_nonneg_on_compact_projectedLogPatch
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {D C' : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hD : D ∈ N.relativeSourceOrderNegativeConeFamily)
    (hsub : (C' : Set (EuclideanSpace ℝ S)) ⊆ (D : Set (EuclideanSpace ℝ S)))
    {n : EuclideanSpace ℝ S} (hn : n ∈ (C' : Set (EuclideanSpace ℝ S)))
    {K : Set (EuclideanSpace ℝ S)} (hK : IsCompact K)
    (hKinterior : K ⊆ interior (D : Set (EuclideanSpace ℝ S))) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ z ∈ K, (CRNT.toricField N.relativeSourceOrderNegativeConeFamily δ z :
        Set (EuclideanSpace ℝ S)) ⊆ {y | 0 ≤ ⟪n, y⟫_ℝ}) ∧
      (∀ x : Concentration S, x.Positive →
      -CRNT.toEuclid (N.relativeLogStoichProjection
        (fun s => Real.log (x s) - Real.log (xstar s))) ∈ K →
      0 ≤ ⟪n, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ) := by
  obtain ⟨δ, hδ, hfield⟩ := FanRefinement.compact_patch_toricField_subset_halfPlane
    (N.relativeSourceOrderNegativeConeFamily_hasExposedCommonFaces)
    hD hsub hn hK hKinterior
  refine ⟨δ, hδ, hfield, ?_⟩
  intro x hx hxK
  have hselector := N.massActionVectorField_mem_relativeSourceOrderToricField
    κ hx hxs hcb hδ
  exact hfield _ hxK hselector

end Network
end CRNT
