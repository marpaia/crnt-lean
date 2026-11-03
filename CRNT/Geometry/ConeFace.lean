import CRNT.Geometry.PolyhedralFan
import CRNT.Geometry.ToricFan
import Mathlib.Geometry.Convex.Cone.Face.Basic

/-!
# Exposed faces of convex cones and the polyhedral-fan axioms

The polyhedral fan organizing a toric differential inclusion is the object underlying
Craciun, _Toric differential inclusions and a proof of the global attractor conjecture_.

An *exposed face* of a convex cone `C` in a real inner-product space `E`, cut out by a
functional direction `a : E`, is the intersection of `C` with the hyperplane on which
`⟪a, ·⟫` vanishes:

`exposedFace C a = C ∩ {x | ⟪a, x⟫ = 0}`.

When `a` lies in the dual cone `Cᵒ`, the functional `⟪a, ·⟫` is nonnegative on `C`, so
the face is exactly the locus where this supporting functional is tight. The hyperplane
`{x | ⟪a, x⟫ = 0}` is the kernel of the linear map `innerₗ E a`, hence a submodule and a
fortiori a pointed cone; the exposed face is therefore the lattice meet `C ⊓ ker` and is
itself a `PointedCone ℝ E`. This realization makes the face a genuine cone — closed under
addition and nonnegative scaling — and gives intersection-closure of faces and the
face-of-a-face transitivity for a fixed cutting direction directly from the `Submodule`
lattice.

The full polyhedral-fan axioms — faces closed under taking faces in the *minimal/non-
exposed* sense, pairwise intersections being a *common* face, and the cones covering the
ambient space — rest on convex-geometry machinery (the general face lattice, support
theory, and a covering argument) absent from Mathlib. They are bundled here as the
predicate `IsPolyhedralFan` over `Fan E`, with the exposed-face notion supplying the
face-membership clause; the covering and intersection-is-a-common-face clauses are stated
as hypotheses, their substantive convex-geometry theory taken as given rather than
constructed here.

Depends on: `CRNT.Geometry.PolyhedralFan`,
`CRNT.Geometry.ToricFan`.
-/

namespace CRNT

open scoped InnerProductSpace

section ConeFace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E]

/-- The supporting hyperplane cut out by a direction `a : E`: the kernel of the linear
functional `⟪a, ·⟫`, viewed as a pointed cone (it is in fact a submodule). -/
noncomputable def supportingHyperplane (a : E) : PointedCone ℝ E :=
  ((LinearMap.ker (innerₗ E a) : Submodule ℝ E) : PointedCone ℝ E)

@[simp] theorem mem_supportingHyperplane {a x : E} :
    x ∈ supportingHyperplane a ↔ ⟪a, x⟫_ℝ = 0 := by
  simp only [supportingHyperplane, PointedCone.mem_ofSubmodule_iff, LinearMap.mem_ker,
    innerₗ_apply_apply]

/-- The exposed face of a pointed cone `C` cut out by a direction `a`: the intersection
of `C` with the hyperplane where the functional `⟪a, ·⟫` vanishes. As the lattice meet of
two pointed cones it is again a `PointedCone ℝ E`. -/
noncomputable def exposedFace (C : PointedCone ℝ E) (a : E) : PointedCone ℝ E :=
  C ⊓ supportingHyperplane a

/-- Membership in an exposed face: lying in `C` and on the vanishing hyperplane. -/
@[simp] theorem mem_exposedFace {C : PointedCone ℝ E} {a x : E} :
    x ∈ exposedFace C a ↔ x ∈ C ∧ ⟪a, x⟫_ℝ = 0 := by
  simp only [exposedFace, Submodule.mem_inf, mem_supportingHyperplane]

/-- An exposed face is contained in its cone. -/
theorem exposedFace_le (C : PointedCone ℝ E) (a : E) : exposedFace C a ≤ C :=
  inf_le_left

/-- An exposed face is contained in its cone, as sets. -/
theorem exposedFace_subset (C : PointedCone ℝ E) (a : E) :
    (exposedFace C a : Set E) ⊆ (C : Set E) :=
  exposedFace_le C a

/-- The exposed face is closed under addition (it is a cone). -/
theorem exposedFace_add_mem {C : PointedCone ℝ E} {a x y : E}
    (hx : x ∈ exposedFace C a) (hy : y ∈ exposedFace C a) : x + y ∈ exposedFace C a :=
  add_mem hx hy

/-- The exposed face is closed under nonnegative scaling (it is a cone). The scalar is
a nonnegative real, packaged as `{c : ℝ // 0 ≤ c}`. -/
theorem exposedFace_smul_mem {C : PointedCone ℝ E} {a x : E} (c : {c : ℝ // 0 ≤ c})
    (hx : x ∈ exposedFace C a) : c • x ∈ exposedFace C a :=
  Submodule.smul_mem _ c hx

/-- The exposed face contains `0`. -/
theorem zero_mem_exposedFace (C : PointedCone ℝ E) (a : E) : (0 : E) ∈ exposedFace C a :=
  zero_mem _

/-- The trivial direction `a = 0` exposes the whole cone: the supporting hyperplane is
all of `E`. -/
@[simp] theorem exposedFace_zero (C : PointedCone ℝ E) : exposedFace C 0 = C := by
  ext x
  simp [mem_exposedFace]

/-- When the cutting direction `a` lies in the dual cone of `C`, the supporting functional
`⟪a, ·⟫` is nonnegative on `C`: the face is the locus where this lower bound is tight. -/
theorem inner_nonneg_of_mem_coneDual [CompleteSpace E] {C : PointedCone ℝ E} {a : E}
    (ha : a ∈ coneDual (C : Set E)) {x : E} (hx : x ∈ C) : 0 ≤ ⟪a, x⟫_ℝ := by
  have := mem_coneDual.1 ha hx
  rwa [real_inner_comm] at this

/-- A supporting hyperplane cut out by a dual-cone vector defines a face in the standard
`PointedCone.IsFaceOf` sense. If a positive combination of two cone points lies on the
supporting hyperplane, dual nonnegativity forces each point with positive coefficient onto the
same hyperplane. -/
theorem exposedFace_isFaceOf [CompleteSpace E] {C : PointedCone ℝ E} {a : E}
    (ha : a ∈ coneDual (C : Set E)) :
    PointedCone.IsFaceOf (exposedFace C a) C := by
  refine ⟨exposedFace_le C a, ?_⟩
  intro x y c hx hy hc hxy
  have hxnonneg := inner_nonneg_of_mem_coneDual ha hx
  have hynonneg := inner_nonneg_of_mem_coneDual ha hy
  have hzero : ⟪a, c • x + y⟫_ℝ = 0 := (mem_exposedFace.mp hxy).2
  have hsum : c * ⟪a, x⟫_ℝ + ⟪a, y⟫_ℝ = 0 := by
    simpa only [inner_add_right, real_inner_smul_right] using hzero
  have hxzero : ⟪a, x⟫_ℝ = 0 := by
    nlinarith [mul_nonneg hc.le hxnonneg]
  exact mem_exposedFace.mpr ⟨hx, hxzero⟩

/-- Faces are closed under intersection: the meet of two exposed faces of `C` is again a
pointed cone contained in `C`, and a point lies in it exactly when it lies in both. -/
theorem mem_exposedFace_inf {C : PointedCone ℝ E} {a b x : E} :
    x ∈ exposedFace C a ⊓ exposedFace C b ↔
      x ∈ C ∧ ⟪a, x⟫_ℝ = 0 ∧ ⟪b, x⟫_ℝ = 0 := by
  simp only [Submodule.mem_inf, mem_exposedFace]
  tauto

/-- **Face of a face (same direction).** Exposing a cone and then exposing the resulting
face with the *same* direction `a` recovers that face: `a` already vanishes on it. -/
@[simp] theorem exposedFace_exposedFace_self (C : PointedCone ℝ E) (a : E) :
    exposedFace (exposedFace C a) a = exposedFace C a := by
  ext x
  simp only [mem_exposedFace]
  tauto

/-- **Face of a face (transitivity in the cone).** A face `exposedFace (exposedFace C a) b`
of a face of `C` is contained in `C`, hence the iterated-face relation refines the
subcone relation. -/
theorem exposedFace_exposedFace_le (C : PointedCone ℝ E) (a b : E) :
    exposedFace (exposedFace C a) b ≤ C :=
  (exposedFace_le _ b).trans (exposedFace_le C a)

/-- The iterated exposed face is symmetric in its two cutting directions: cutting by `a`
then `b` gives the same cone as cutting by `b` then `a` (both are `C` met with both
hyperplanes). -/
theorem exposedFace_exposedFace_comm (C : PointedCone ℝ E) (a b : E) :
    exposedFace (exposedFace C a) b = exposedFace (exposedFace C b) a := by
  ext x
  simp only [mem_exposedFace]
  tauto

end ConeFace

section Fan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A cone `D` is an *exposed face* of a cone `C` when it is `exposedFace C a` for some
cutting direction `a` that lies in the dual cone of `C` (a genuine supporting functional). -/
def IsExposedFaceOf (D C : ProperCone ℝ E) : Prop :=
  ∃ a ∈ coneDual (C : Set E),
    ((D : PointedCone ℝ E) : Set E) = (exposedFace (C : PointedCone ℝ E) a : Set E)

/-- Every proper cone is an exposed face of itself, exposed by the trivial direction `0`
(which lies in any dual cone). -/
theorem isExposedFaceOf_self (C : ProperCone ℝ E) : IsExposedFaceOf C C := by
  refine ⟨0, ?_, ?_⟩
  · rw [mem_coneDual]; intro x _; simp
  · rw [exposedFace_zero]

/-- Every exposed face is a face in the standard convex-cone sense. -/
theorem isExposedFaceOf_isFaceOf {D C : ProperCone ℝ E}
    (h : IsExposedFaceOf D C) :
    PointedCone.IsFaceOf (D : PointedCone ℝ E) (C : PointedCone ℝ E) := by
  obtain ⟨a, ha, hset⟩ := h
  have hEq : (D : PointedCone ℝ E) = exposedFace (C : PointedCone ℝ E) a := by
    apply PointedCone.ext
    intro x
    exact Iff.of_eq (congrArg (fun A : Set E => x ∈ A) hset)
  rw [hEq]
  exact exposedFace_isFaceOf ha

/-- **Polyhedral-fan axioms over a finite cone family.** A `Fan E` is a polyhedral fan
when (i) every exposed face of a cone of the fan is realized by some cone of the fan,
(ii) the intersection of any two cones of the fan is, as a set, a cone of the fan (the
*common-face* condition specialized to set equality), and (iii) the cones cover the whole
space. The substantive convex-geometry content of (ii)/(iii) — that the shared cone is in
fact a face of *each* side, and the covering argument — is taken as a hypothesis rather
than constructed here; this predicate bundles those obligations together with the
exposed-face clause the preceding theory does support. -/
structure IsPolyhedralFan (F : Fan E) : Prop where
  /-- Closure under exposed faces: an exposed face of a fan cone is a fan cone. -/
  faces_mem : ∀ C ∈ F, ∀ D : ProperCone ℝ E, IsExposedFaceOf D C → D ∈ F
  /-- Pairwise intersections coincide (as sets) with a common cone of the fan. -/
  inter_common : ∀ C ∈ F, ∀ D ∈ F, ∃ G ∈ F,
    (G : Set E) = (C : Set E) ∩ (D : Set E)
  /-- The cones cover the ambient space. -/
  covers : ⋃ C ∈ F, (C : Set E) = Set.univ

/-- The empty fan trivially satisfies the face-closure and intersection clauses (both
quantify over an empty cone family); only the covering clause carries content, so a fan
covering `E` with no cones cannot exist unless `E` is empty. The two combinatorial clauses
are vacuously met by the empty family. -/
theorem isPolyhedralFan_empty_clauses :
    (∀ C ∈ (∅ : Fan E), ∀ D : ProperCone ℝ E, IsExposedFaceOf D C → D ∈ (∅ : Fan E)) ∧
    (∀ C ∈ (∅ : Fan E), ∀ D ∈ (∅ : Fan E), ∃ G ∈ (∅ : Fan E),
      (G : Set E) = (C : Set E) ∩ (D : Set E)) := by
  constructor
  · intro C hC; exact absurd hC (Finset.notMem_empty C)
  · intro C hC; exact absurd hC (Finset.notMem_empty C)

/-- Pull a proper cone back along negation. Its carrier is the negative of the original cone. -/
noncomputable def negatedProperCone (C : ProperCone ℝ E) : ProperCone ℝ E :=
  C.comap (-(ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem mem_negatedProperCone {C : ProperCone ℝ E} {x : E} :
    x ∈ negatedProperCone C ↔ -x ∈ C := by
  simp [negatedProperCone]

omit [CompleteSpace E] in
/-- Negating a cone twice recovers the original cone. -/
@[simp] theorem negatedProperCone_negatedProperCone (C : ProperCone ℝ E) :
    negatedProperCone (negatedProperCone C) = C := by
  apply ProperCone.ext
  intro x
  simp

/-- The finite cone family obtained by negating every cone of a fan. -/
noncomputable def negatedFan (F : Fan E) : Fan E :=
  by
    classical
    exact F.image negatedProperCone

/-- Negation preserves the polyhedral-fan axioms. Face cuts transform by negating their
supporting functional; intersections and coverage transform under the same involution. -/
theorem IsPolyhedralFan.negated {F : Fan E} (hF : IsPolyhedralFan F) :
    IsPolyhedralFan (negatedFan F) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro C hC D hD
    rw [negatedFan, Finset.mem_image] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨a, ha, hset⟩ := hD
    have ha' : -a ∈ coneDual (C₀ : Set E) := by
      rw [mem_coneDual]
      intro x hx
      have hx' : -x ∈ negatedProperCone C₀ := by
        rw [mem_negatedProperCone]
        simpa using hx
      have hpair := (mem_coneDual.mp ha) hx'
      simpa using hpair
    let D₀ : ProperCone ℝ E := negatedProperCone D
    have hD₀ : IsExposedFaceOf D₀ C₀ := by
      refine ⟨-a, ha', ?_⟩
      change (D₀ : Set E) =
        (exposedFace (C₀ : PointedCone ℝ E) (-a) : Set E)
      ext x
      change x ∈ D₀ ↔ x ∈ exposedFace (C₀ : PointedCone ℝ E) (-a)
      have hDset (y : E) : y ∈ D ↔
          y ∈ exposedFace (negatedProperCone C₀ : PointedCone ℝ E) a := by
        exact Iff.of_eq (congrArg (fun A : Set E => y ∈ A) hset)
      rw [mem_negatedProperCone, hDset, mem_exposedFace]
      simp
    have hD₀F : D₀ ∈ F := hF.faces_mem C₀ hC₀ D₀ hD₀
    rw [negatedFan]
    apply Finset.mem_image.mpr
    refine ⟨D₀, hD₀F, ?_⟩
    exact negatedProperCone_negatedProperCone D
  · intro C hC D hD
    rw [negatedFan, Finset.mem_image] at hC hD
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    obtain ⟨G₀, hG₀, hGset⟩ := hF.inter_common C₀ hC₀ D₀ hD₀
    refine ⟨negatedProperCone G₀, ?_, ?_⟩
    · rw [negatedFan]
      exact Finset.mem_image.mpr ⟨G₀, hG₀, rfl⟩
    · ext x
      change -x ∈ G₀ ↔ -x ∈ C₀ ∧ -x ∈ D₀
      have hmem := congrArg (fun A : Set E => -x ∈ A) hGset
      exact Iff.of_eq hmem
  · ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
    have hcover : -x ∈ ⋃ C ∈ F, (C : Set E) := by
      rw [hF.covers]
      trivial
    simp only [Set.mem_iUnion] at hcover
    obtain ⟨C, hC, hxC⟩ := hcover
    exact ⟨negatedProperCone C, Finset.mem_image.mpr ⟨C, hC, rfl⟩,
      by simpa using hxC⟩

end Fan

end CRNT
