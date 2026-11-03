import CRNT.Dynamics.ComplexBalanceCycleDecomposition
import CRNT.Geometry.ConeFace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Convex.Cone.DualFinite

/-!
# The source-order fan on stoichiometric space

The finite source-order cone family in `ComplexBalanceCycleDecomposition` is represented in the
ambient species space, where its cones cover only the stoichiometric subspace.  Restricting those
cones to the subspace itself gives the complete finite polyhedral fan needed by the toric
differential-inclusion argument.
-/

namespace CRNT
namespace Network

open scoped InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A source-order cone regarded as a cone in the stoichiometric subspace itself. -/
noncomputable def relativeSourceOrderConeInStoich (N : Network S) (w : S → ℝ) :
    ProperCone ℝ N.euclideanStoichSubspace :=
  (N.relativeSourceOrderStoichProperCone w).comap N.euclideanStoichSubspace.subtypeL

private noncomputable def sourceOrderNormal (N : Network S) (p : N.R × N.R) :
    N.euclideanStoichSubspace :=
  N.euclideanStoichSubspace.orthogonalProjectionOnto
    (toEuclid (CRNT.exponentVector (N.sourceIdx p.2).val) -
      toEuclid (CRNT.exponentVector (N.sourceIdx p.1).val))

/-- Every intrinsic source-order cone is cut out by finitely many half-spaces. Its dual-finite
generation certificate is given by the projected differences of source-complex exponent vectors
for the ordered pairs selected by `w`. -/
theorem relativeSourceOrderConeInStoich_dualFG (N : Network S) (w : S → ℝ) :
    (N.relativeSourceOrderConeInStoich w : PointedCone ℝ N.euclideanStoichSubspace).DualFG
      (innerₗ N.euclideanStoichSubspace) := by
  classical
  let I : Finset (N.R × N.R) := Finset.univ.filter fun p =>
    N.sourceLogProjection w p.1 ≤ N.sourceLogProjection w p.2
  let T : Finset N.euclideanStoichSubspace := I.image (N.sourceOrderNormal)
  refine ⟨T, ?_⟩
  apply PointedCone.ext
  intro z
  have hzstoich : toEuclid.symm z.1 ∈ N.stoichSubspace := by
    have hzproperty := z.2
    change z.1 ∈ Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace at hzproperty
    rw [Submodule.mem_map] at hzproperty
    rcases hzproperty with ⟨u, hu, huz⟩
    rw [← huz]
    simpa using hu
  rw [PointedCone.mem_dual]
  change (∀ ⦃y⦄, y ∈ (T : Set N.euclideanStoichSubspace) →
      0 ≤ ⟪y, z⟫_ℝ) ↔
    z.1 ∈ N.relativeSourceOrderStoichCone w
  rw [N.mem_relativeSourceOrderStoichCone]
  simp only [hzstoich, and_true]
  change (∀ ⦃y⦄, y ∈ (T : Set N.euclideanStoichSubspace) →
      0 ≤ ⟪y, z⟫_ℝ) ↔
    (∀ r q, N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
      N.sourceLogProjection (toEuclid.symm z.1) r ≤
        N.sourceLogProjection (toEuclid.symm z.1) q)
  have hdiff (p : N.R × N.R) :
      ⟪N.sourceOrderNormal p, z⟫_ℝ =
        N.sourceLogProjection (toEuclid.symm z.1) p.2 -
          N.sourceLogProjection (toEuclid.symm z.1) p.1 := by
    simp [sourceOrderNormal, inner_sub_left, N.sourceLogProjection_eq_inner_toEuclid]
  constructor
  · intro h r q hrq
    have hmem : N.sourceOrderNormal (r, q) ∈ T := by
      apply Finset.mem_image.mpr
      refine ⟨(r, q), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrq⟩
    have hnonneg := h hmem
    rw [hdiff] at hnonneg
    exact sub_nonneg.mp hnonneg
  · intro h y hy
    rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨_, hporder⟩
    rw [hdiff]
    exact sub_nonneg.mpr (h p.1 p.2 hporder)

private theorem finite_range_relativeSourceOrderConeInStoich (N : Network S) :
    (Set.range N.relativeSourceOrderConeInStoich).Finite := by
  let g : ProperCone ℝ (EuclideanSpace ℝ S) →
      ProperCone ℝ N.euclideanStoichSubspace :=
    fun C => C.comap N.euclideanStoichSubspace.subtypeL
  have hfinite :
      (g '' Set.range N.relativeSourceOrderStoichProperCone).Finite :=
    N.finite_relativeSourceOrderStoichProperCone_range.image g
  apply hfinite.subset
  rintro C ⟨w, rfl⟩
  exact ⟨N.relativeSourceOrderStoichProperCone w,
    ⟨w, rfl⟩, rfl⟩

/-- The finite family of source-order cones, now considered in the space they cover. -/
noncomputable def relativeSourceOrderStoichFan (N : Network S) :
    CRNT.Fan N.euclideanStoichSubspace :=
  (N.finite_range_relativeSourceOrderConeInStoich).toFinset

@[simp] theorem mem_relativeSourceOrderStoichFan (N : Network S)
    {C : ProperCone ℝ N.euclideanStoichSubspace} :
    C ∈ N.relativeSourceOrderStoichFan ↔
      C ∈ Set.range N.relativeSourceOrderConeInStoich := by
  classical
  change C ∈ (N.finite_range_relativeSourceOrderConeInStoich).toFinset ↔ _
  exact N.finite_range_relativeSourceOrderConeInStoich.mem_toFinset

private theorem comap_inf_relativeSourceOrder (N : Network S)
    (C D : ProperCone ℝ (EuclideanSpace ℝ S)) :
    (C ⊓ D).comap N.euclideanStoichSubspace.subtypeL =
      C.comap N.euclideanStoichSubspace.subtypeL ⊓
        D.comap N.euclideanStoichSubspace.subtypeL := by
  apply ProperCone.ext
  intro z
  simp

/-- Intersections of two intrinsic source-order cones are again source-order cones. -/
theorem relativeSourceOrderConeInStoich_inf_eq_member (N : Network S)
    (w₁ w₂ : S → ℝ) :
    ∃ w : S → ℝ,
      N.relativeSourceOrderConeInStoich w =
        N.relativeSourceOrderConeInStoich w₁ ⊓
          N.relativeSourceOrderConeInStoich w₂ := by
  obtain ⟨w, hw⟩ := N.relativeSourceOrderStoichProperCone_inf_eq_member w₁ w₂
  refine ⟨w, ?_⟩
  calc
    N.relativeSourceOrderConeInStoich w =
        (N.relativeSourceOrderStoichProperCone w).comap
          N.euclideanStoichSubspace.subtypeL := rfl
    _ = (N.relativeSourceOrderStoichProperCone w₁ ⊓
          N.relativeSourceOrderStoichProperCone w₂).comap
            N.euclideanStoichSubspace.subtypeL := by rw [hw]
    _ = N.relativeSourceOrderConeInStoich w₁ ⊓
          N.relativeSourceOrderConeInStoich w₂ :=
        N.comap_inf_relativeSourceOrder _ _

/-- The finite intrinsic family is closed under pairwise intersections. -/
theorem relativeSourceOrderStoichFan_inter_mem (N : Network S)
    {C D : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderStoichFan)
    (hD : D ∈ N.relativeSourceOrderStoichFan) :
    C ⊓ D ∈ N.relativeSourceOrderStoichFan := by
  rw [N.mem_relativeSourceOrderStoichFan] at hC hD ⊢
  rcases hC with ⟨w₁, rfl⟩
  rcases hD with ⟨w₂, rfl⟩
  obtain ⟨w, hw⟩ := N.relativeSourceOrderConeInStoich_inf_eq_member w₁ w₂
  exact ⟨w, hw⟩

private theorem subtypeL_isClosedEmbedding (N : Network S) :
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
    (N.subtypeL_isClosedEmbedding.isClosed_iff_image_isClosed).mp C.isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL '' (C : Set N.euclideanStoichSubspace)) ↔ _
  rw [hclosed.closure_eq, PointedCone.mem_map]
  simp only [Set.mem_image]
  exact Iff.rfl

private theorem map_comap_relativeSourceOrder (N : Network S) (w : S → ℝ) :
    ProperCone.map N.euclideanStoichSubspace.subtypeL
        (N.relativeSourceOrderConeInStoich w) =
      N.relativeSourceOrderStoichProperCone w := by
  have hV : ∀ x : EuclideanSpace ℝ S,
      x ∈ N.relativeSourceOrderStoichProperCone w →
        x ∈ N.euclideanStoichSubspace := by
    intro x hx
    rw [euclideanStoichSubspace, Submodule.mem_map]
    refine ⟨CRNT.toEuclid.symm x,
      N.stoich_of_mem_relativeSourceOrderStoichProperCone ⟨w, rfl⟩ hx, ?_⟩
    exact CRNT.toEuclid.apply_symm_apply x
  have himage :
      N.euclideanStoichSubspace.subtypeL ''
          (N.relativeSourceOrderConeInStoich w : Set N.euclideanStoichSubspace) =
        (N.relativeSourceOrderStoichProperCone w : Set (EuclideanSpace ℝ S)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (ProperCone.mem_comap.mp hz)
    · intro hx
      refine ⟨⟨x, hV x hx⟩, ?_, rfl⟩
      exact ProperCone.mem_comap.mpr hx
  apply ProperCone.ext
  intro x
  rw [ProperCone.mem_map]
  have hclosed : IsClosed
      (N.euclideanStoichSubspace.subtypeL ''
        (N.relativeSourceOrderConeInStoich w : Set N.euclideanStoichSubspace)) := by
    rw [himage]
    exact (N.relativeSourceOrderStoichProperCone w).isClosed
  change x ∈ closure
      (N.euclideanStoichSubspace.subtypeL ''
        (N.relativeSourceOrderConeInStoich w : Set N.euclideanStoichSubspace)) ↔ _
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

/-- Every exposed face of an intrinsic source-order cone is another cone in the family. -/
theorem relativeSourceOrderStoichFan_faces_mem (N : Network S)
    {C : ProperCone ℝ N.euclideanStoichSubspace}
    (hC : C ∈ N.relativeSourceOrderStoichFan)
    {D : ProperCone ℝ N.euclideanStoichSubspace}
    (hface : CRNT.IsExposedFaceOf D C) :
    D ∈ N.relativeSourceOrderStoichFan := by
  classical
  rw [N.mem_relativeSourceOrderStoichFan] at hC
  rcases hC with ⟨w, rfl⟩
  have hface' : PointedCone.IsFaceOf (D : PointedCone ℝ N.euclideanStoichSubspace)
      (N.relativeSourceOrderConeInStoich w : PointedCone ℝ N.euclideanStoichSubspace) :=
    CRNT.isExposedFaceOf_isFaceOf hface
  have hinj : Function.Injective
      N.euclideanStoichSubspace.subtypeL.toLinearMap := by
    intro x y h
    exact Subtype.ext h
  have hmapped := PointedCone.IsFaceOf.map
    N.euclideanStoichSubspace.subtypeL.toLinearMap hinj hface'
  have hmapped' :
      ((ProperCone.map N.euclideanStoichSubspace.subtypeL D :
        ProperCone ℝ (EuclideanSpace ℝ S)) : PointedCone ℝ (EuclideanSpace ℝ S)).IsFaceOf
        (N.relativeSourceOrderStoichProperCone w : PointedCone ℝ (EuclideanSpace ℝ S)) := by
    rw [← N.map_comap_relativeSourceOrder w, N.properMap_subtype_eq_pointedMap]
    simpa only [N.properMap_subtype_eq_pointedMap] using hmapped
  obtain ⟨v, hD⟩ := N.relativeSourceOrderStoichProperCone_face_eq_inter w hmapped'
  have hcomapInf (A B : ProperCone ℝ (EuclideanSpace ℝ S)) :
      (A ⊓ B).comap N.euclideanStoichSubspace.subtypeL =
        A.comap N.euclideanStoichSubspace.subtypeL ⊓
          B.comap N.euclideanStoichSubspace.subtypeL := by
    apply ProperCone.ext
    intro x
    simp
  have hD' : D = N.relativeSourceOrderConeInStoich w ⊓
      N.relativeSourceOrderConeInStoich v := by
    calc
      D = (ProperCone.map N.euclideanStoichSubspace.subtypeL D).comap
          N.euclideanStoichSubspace.subtypeL :=
            (N.comap_map_subtype_eq D).symm
      _ = (N.relativeSourceOrderStoichProperCone w ⊓
          N.relativeSourceOrderStoichProperCone v).comap
            N.euclideanStoichSubspace.subtypeL := by rw [hD]
      _ = N.relativeSourceOrderConeInStoich w ⊓
          N.relativeSourceOrderConeInStoich v := hcomapInf _ _
  have hleft : N.relativeSourceOrderConeInStoich w ∈
      N.relativeSourceOrderStoichFan := by
    apply N.mem_relativeSourceOrderStoichFan.mpr
    exact ⟨w, rfl⟩
  have hright : N.relativeSourceOrderConeInStoich v ∈
      N.relativeSourceOrderStoichFan := by
    apply N.mem_relativeSourceOrderStoichFan.mpr
    exact ⟨v, rfl⟩
  rw [hD']
  exact (N.relativeSourceOrderStoichFan_inter_mem hleft hright)

/-- The intrinsic source-order cones cover every stoichiometric direction. -/
theorem exists_relativeSourceOrderConeInStoich_mem (N : Network S)
    (z : N.euclideanStoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderStoichFan, z ∈ C := by
  let w : S → ℝ := CRNT.toEuclid.symm z.1
  have hzstoich : CRNT.toEuclid.symm z.1 ∈ N.stoichSubspace := by
    have hzproperty := z.property
    change z.1 ∈ Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace at hzproperty
    rw [Submodule.mem_map] at hzproperty
    rcases hzproperty with ⟨u, hu, huz⟩
    rw [← huz]
    simpa using hu
  have hzambient : z.1 ∈ N.relativeSourceOrderStoichProperCone w := by
    change z.1 ∈ N.relativeSourceOrderStoichCone w
    apply (N.mem_relativeSourceOrderStoichCone w).2
    exact ⟨by
      exact N.toEuclid_mem_relativeSourceOrderCone w,
      hzstoich⟩
  refine ⟨N.relativeSourceOrderConeInStoich w, ?_, ?_⟩
  · apply N.mem_relativeSourceOrderStoichFan.mpr
    exact ⟨w, rfl⟩
  · exact ProperCone.mem_comap.mpr hzambient

/-- The intrinsic source-order family is a finite polyhedral fan. Its face and intersection
closure come from the exact finite source-order arrangement; coverage follows by selecting the
weak order induced by the direction itself. -/
theorem relativeSourceOrderStoichFan_isPolyhedralFan (N : Network S) :
    CRNT.IsPolyhedralFan N.relativeSourceOrderStoichFan := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro C hC D hface
    exact N.relativeSourceOrderStoichFan_faces_mem hC hface
  · intro C hC D hD
    rw [N.mem_relativeSourceOrderStoichFan] at hC hD
    rcases hC with ⟨w₁, rfl⟩
    rcases hD with ⟨w₂, rfl⟩
    obtain ⟨w, hw⟩ := N.relativeSourceOrderConeInStoich_inf_eq_member w₁ w₂
    refine ⟨N.relativeSourceOrderConeInStoich w, ?_, ?_⟩
    · apply N.mem_relativeSourceOrderStoichFan.mpr
      exact ⟨w, rfl⟩
    · ext z
      simp [hw]
  · ext z
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨C, hC, hz⟩ := N.exists_relativeSourceOrderConeInStoich_mem z
      exact ⟨C, hC, hz⟩

/-- The sign-reversed intrinsic source-order fan. Its cones are the velocity-facing chambers used
by the toric field at the negative projected relative-log state. -/
noncomputable def relativeSourceOrderNegativeStoichFan (N : Network S) :
    CRNT.Fan N.euclideanStoichSubspace :=
  CRNT.negatedFan N.relativeSourceOrderStoichFan

/-- The negative intrinsic source-order family is also a complete polyhedral fan. -/
theorem relativeSourceOrderNegativeStoichFan_isPolyhedralFan (N : Network S) :
    CRNT.IsPolyhedralFan N.relativeSourceOrderNegativeStoichFan := by
  exact (N.relativeSourceOrderStoichFan_isPolyhedralFan).negated

/-- Every sign-reversed source-order chamber occurs in the negative intrinsic fan. -/
theorem relativeSourceOrderNegativeConeInStoich_mem_fan (N : Network S) (w : S → ℝ) :
    CRNT.negatedProperCone (N.relativeSourceOrderConeInStoich w) ∈
      N.relativeSourceOrderNegativeStoichFan := by
  classical
  rw [relativeSourceOrderNegativeStoichFan, CRNT.negatedFan, Finset.mem_image]
  refine ⟨N.relativeSourceOrderConeInStoich w, ?_, rfl⟩
  rw [N.mem_relativeSourceOrderStoichFan]
  exact ⟨w, rfl⟩

/-- The negative intrinsic source-order cones cover every stoichiometric direction. -/
theorem exists_relativeSourceOrderNegativeStoichFan_mem (N : Network S)
    (z : N.euclideanStoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderNegativeStoichFan, z ∈ C := by
  classical
  obtain ⟨C, hC, hnegz⟩ := N.exists_relativeSourceOrderConeInStoich_mem (-z)
  refine ⟨CRNT.negatedProperCone C, ?_, ?_⟩
  · rw [relativeSourceOrderNegativeStoichFan, CRNT.negatedFan]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  · exact CRNT.mem_negatedProperCone.mpr hnegz

end Network
end CRNT
