import CRNT.Analysis.BorosProjectionDecomposition
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.KineticBlock

/-!
# Linkage-class projections for the Boros decomposition

This module instantiates the generic orthogonal block projections on network complexes, using
their linkage class as the block label.  It exposes the exact coordinate projection needed by the
multi-linkage Brouwer construction.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Euclidean coordinate projection onto a chosen finite set of linkage classes. -/
noncomputable def borosLinkageProjectionSystem (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    Analysis.BorosBlockProjectionSystem (I := Quotient N.linkedSetoid)
      (E := EuclideanSpace ℝ N.ComplexIdx) := by
  classical
  exact Analysis.borosCoordinateBlockProjectionSystem N.classOf

@[simp] theorem borosLinkageProjectionSystem_apply (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (Q : Finset (Quotient N.linkedSetoid))
    (x : EuclideanSpace ℝ N.ComplexIdx) (c : N.ComplexIdx) :
    (N.borosLinkageProjectionSystem).project Q x c =
      if N.classOf c ∈ Q then x c else 0 := by
  classical
  change Analysis.borosCoordinateBlockProject N.classOf Q x c = _
  exact Analysis.borosCoordinateBlockProject_apply N.classOf Q x c

/-- Summing the restrictions to a selected set of linkage classes is the corresponding
coordinate mask. -/
theorem sum_restrictToClass_eq_linkageMask (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (Q : Finset (Quotient N.linkedSetoid)) (v : N.ComplexIdx → ℝ) :
    (∑ q ∈ Q, N.restrictToClass q v) =
      fun c => if N.classOf c ∈ Q then v c else 0 := by
  classical
  funext c
  rw [Finset.sum_apply]
  by_cases hmem : N.classOf c ∈ Q
  · rw [Finset.sum_eq_single_of_mem (N.classOf c) hmem]
    · calc
        N.restrictToClass (N.classOf c) v c = v c :=
          N.restrictToClass_apply_of_eq v rfl
        _ = if N.classOf c ∈ Q then v c else 0 := by simp [hmem]
    · intro q hq hne
      apply N.restrictToClass_apply_of_ne
      intro heq
      exact hne heq.symm
  · rw [Finset.sum_eq_zero]
    · simp [hmem]
    · intro q hq
      apply N.restrictToClass_apply_of_ne
      intro heq
      exact hmem (by simpa [heq] using hq)

/-- Under `toEuclid`, the network projection is the sum of the chosen class restrictions. -/
theorem borosLinkageProjection_eq_sum_restrictToClass (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (Q : Finset (Quotient N.linkedSetoid)) (v : N.ComplexIdx → ℝ) :
    (N.borosLinkageProjectionSystem).project Q (CRNT.toEuclid v) =
    CRNT.toEuclid (∑ q ∈ Q, N.restrictToClass q v) := by
  classical
  apply PiLp.ext
  intro c
  simpa only [borosLinkageProjectionSystem_apply, CRNT.toEuclid_apply] using
    (congrFun (N.sum_restrictToClass_eq_linkageMask Q v) c).symm

/-- Summing coordinates on one linkage-class subtype agrees with summing the ambient vector
after restricting it to that class. -/
theorem sum_classCoordinates_eq_sum_restrictToClass (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (q : Quotient N.linkedSetoid)
    (v : N.ComplexIdx → ℝ) :
    (∑ c : {c : N.ComplexIdx // N.classOf c = q}, v c.val) =
      ∑ c : N.ComplexIdx, N.restrictToClass q v c := by
  classical
  let F : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = q)
  have hfilter : ∀ c : N.ComplexIdx, c ∈ F ↔ N.classOf c = q := by
    intro c
    simp [F]
  calc
    _ = ∑ c ∈ F, v c := by
      symm
      exact Finset.sum_subtype F hfilter (fun c => v c)
    _ = ∑ c ∈ F, N.restrictToClass q v c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [N.restrictToClass_apply_of_eq v ((hfilter c).mp hc)]
    _ = ∑ c : N.ComplexIdx, N.restrictToClass q v c := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro c _ hc
      have hclass : N.classOf c ≠ q := fun h => hc ((hfilter c).mpr h)
      rw [N.restrictToClass_apply_of_ne v hclass]

/-- The Euclidean norm of a vector restricted to one linkage class is the norm of its ambient
coordinate projection onto that class. This connects the subtype zero-sum estimate with the
single-class Boros block projection. -/
theorem norm_toEuclid_classCoordinates_eq_projection_norm (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (q : Quotient N.linkedSetoid)
    (v : N.ComplexIdx → ℝ) :
    ‖CRNT.toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => v c.val)‖ =
      ‖(N.borosLinkageProjectionSystem).project {q} (CRNT.toEuclid v)‖ := by
  classical
  let C := {c : N.ComplexIdx // N.classOf c = q}
  let F : Finset N.ComplexIdx := Finset.univ.filter (fun c => N.classOf c = q)
  have hfilter : ∀ c : N.ComplexIdx, c ∈ F ↔ N.classOf c = q := by
    intro c
    simp [F]
  have hsum :
      (∑ c : C, v c.val * v c.val) =
        ∑ c : N.ComplexIdx,
          N.restrictToClass q v c * N.restrictToClass q v c := by
    calc
      _ = ∑ c ∈ F, v c * v c := by
        symm
        exact Finset.sum_subtype F hfilter (fun c => v c * v c)
      _ = ∑ c : N.ComplexIdx,
          N.restrictToClass q v c * N.restrictToClass q v c := by
        calc
          _ = ∑ c ∈ F,
              N.restrictToClass q v c * N.restrictToClass q v c := by
                apply Finset.sum_congr rfl
                intro c hcF
                rw [N.restrictToClass_apply_of_eq v ((hfilter c).mp hcF)]
          _ = ∑ c : N.ComplexIdx,
              N.restrictToClass q v c * N.restrictToClass q v c := by
                refine Finset.sum_subset (Finset.filter_subset _ _) ?_
                intro c _ hcF
                have hclass : N.classOf c ≠ q := fun hc => hcF ((hfilter c).mpr hc)
                rw [N.restrictToClass_apply_of_ne v hclass]
                simp
  have hnormSq :
      ‖CRNT.toEuclid (fun c : C => v c.val)‖ ^ 2 =
        ‖CRNT.toEuclid (N.restrictToClass q v)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      CRNT.inner_toEuclid, CRNT.inner_toEuclid]
    exact hsum
  have hnorm :
      ‖CRNT.toEuclid (fun c : C => v c.val)‖ =
        ‖CRNT.toEuclid (N.restrictToClass q v)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormSq
  rw [N.borosLinkageProjection_eq_sum_restrictToClass {q} v]
  simpa only [Finset.sum_singleton] using hnorm

/-- The selected linkage-class projection commutes with the kinetic map. This transfers the
block-diagonal identity from class restrictions to the Boros coordinate projections. -/
theorem kineticMap_commutes_borosLinkageProjection (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (κ : RateConstants N) (Q : Finset (Quotient N.linkedSetoid))
    (v : N.ComplexIdx → ℝ) :
    (N.borosLinkageProjectionSystem).project Q
        (CRNT.toEuclid (N.kineticMap κ v)) =
      CRNT.toEuclid
        (N.kineticMap κ (fun c => if N.classOf c ∈ Q then v c else 0)) := by
  calc
    _ = CRNT.toEuclid (∑ q ∈ Q, N.restrictToClass q (N.kineticMap κ v)) :=
      N.borosLinkageProjection_eq_sum_restrictToClass Q (N.kineticMap κ v)
    _ = CRNT.toEuclid (∑ q ∈ Q, N.kineticMap κ (N.restrictToClass q v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [N.kineticMap_restrictToClass]
    _ = CRNT.toEuclid
        (N.kineticMap κ (∑ q ∈ Q, N.restrictToClass q v)) := by
      congr 1
      symm
      exact map_sum (N.kineticMap κ) (fun q => N.restrictToClass q v) Q
    _ = _ := by rw [N.sum_restrictToClass_eq_linkageMask Q v]

/-- The transpose of the complex matrix, written directly in coordinates. -/
noncomputable def complexTransposeMap (N : Network S) :
    (S → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun p c := ∑ s, (c.val s : ℝ) * p s
  map_add' p p' := by
    funext c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  map_smul' a p := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

/-- The row space of one linkage class: restrict the complex transpose row vectors to that
class's complex coordinates. -/
noncomputable def borosLinkageClassRowMap (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (q : Quotient N.linkedSetoid) :
    (S → ℝ) →ₗ[ℝ] EuclideanSpace ℝ N.ComplexIdx :=
  (CRNT.toEuclid (ι := N.ComplexIdx)).toLinearMap.comp
    ((Analysis.borosCoordinateBlockMask N.classOf {q}).comp N.complexTransposeMap)

@[simp] theorem borosLinkageClassRowMap_apply (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (q : Quotient N.linkedSetoid)
    (p : S → ℝ) (c : N.ComplexIdx) :
    N.borosLinkageClassRowMap q p c =
      if N.classOf c = q then N.complexTransposeMap p c else 0 := by
  simp [borosLinkageClassRowMap, Analysis.borosCoordinateBlockMask,
    CRNT.toEuclid_apply]

/-- The product of independent species covectors, one for each linkage class, mapped into the
complex coordinate space as the sum of the corresponding restricted complex-transpose rows. -/
noncomputable def borosLinkageRowBundleMap (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    (Quotient N.linkedSetoid → S → ℝ) →ₗ[ℝ] EuclideanSpace ℝ N.ComplexIdx where
  toFun p := ∑ q, N.borosLinkageClassRowMap q (p q)
  map_add' p p' := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact (N.borosLinkageClassRowMap q).map_add (p q) (p' q)
  map_smul' a p := by
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact (N.borosLinkageClassRowMap q).map_smul a (p q)

@[simp] theorem borosLinkageRowBundleMap_apply (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (p : Quotient N.linkedSetoid → S → ℝ) (c : N.ComplexIdx) :
    N.borosLinkageRowBundleMap p c =
      N.complexTransposeMap (p (N.classOf c)) c := by
  classical
  change (∑ q, N.borosLinkageClassRowMap q (p q)) c = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem (N.classOf c) (Finset.mem_univ _)]
  · simp
  · intro q _ hq
    simp [hq.symm]

/-- Boros's product row space `Π_q range(Y_qᵀ)`, represented as the range of the row-bundle map. -/
noncomputable def borosLinkageRowSpace (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    Submodule ℝ (EuclideanSpace ℝ N.ComplexIdx) :=
  LinearMap.range N.borosLinkageRowBundleMap

/-- The row-bundle image is exactly the supremum of the per-class complex row spaces. -/
theorem borosLinkageRowSpace_eq_iSup_classRowRange (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    N.borosLinkageRowSpace =
      ⨆ q, LinearMap.range (N.borosLinkageClassRowMap q) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases LinearMap.mem_range.mp hx with ⟨p, rfl⟩
    apply Submodule.sum_mem
    intro q _
    exact Submodule.mem_iSup_of_mem q ⟨p q, rfl⟩
  · rw [iSup_le_iff]
    intro q x hx
    rcases LinearMap.mem_range.mp hx with ⟨p, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨fun q' => if q' = q then p else 0, ?_⟩
    apply PiLp.ext
    intro c
    change (∑ q', N.borosLinkageClassRowMap q' (if q' = q then p else 0)) c = _
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ _)]
    · simp
    · intro q' _ hne
      simp [hne]

/-- Projecting the product row space onto any set of linkage classes keeps it in that same
product row space, by zeroing the omitted class covectors. -/
theorem borosLinkageProjection_preservesRowSpace (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (Q : Finset (Quotient N.linkedSetoid))
    {x : EuclideanSpace ℝ N.ComplexIdx} (hx : x ∈ N.borosLinkageRowSpace) :
    (N.borosLinkageProjectionSystem).project Q x ∈ N.borosLinkageRowSpace := by
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hx
  apply LinearMap.mem_range.mpr
  refine ⟨fun q => if q ∈ Q then p q else 0, ?_⟩
  rw [← hp]
  apply PiLp.ext
  intro c
  rw [borosLinkageProjectionSystem_apply, borosLinkageRowBundleMap_apply,
    borosLinkageRowBundleMap_apply]
  by_cases hc : N.classOf c ∈ Q <;> simp [hc]

/-- Restrict a linkage-subset projection to the Boros product row space. -/
noncomputable def borosLinkageProjectionOnRowSpace (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid)) :
    N.borosLinkageRowSpace →ₗ[ℝ] N.borosLinkageRowSpace :=
  (((N.borosLinkageProjectionSystem).project Q.1).comp
    N.borosLinkageRowSpace.subtype).codRestrict N.borosLinkageRowSpace
      (fun x => N.borosLinkageProjection_preservesRowSpace Q.1 x.2)

/-- The restricted projections are continuous linear maps on the Boros product row space. -/
noncomputable def borosLinkageContinuousProjectionsOnRowSpace (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    Analysis.BorosSubsetIndex (Quotient N.linkedSetoid) →
      N.borosLinkageRowSpace →L[ℝ] N.borosLinkageRowSpace :=
  fun Q =>
    ⟨N.borosLinkageProjectionOnRowSpace Q,
      (N.borosLinkageProjectionOnRowSpace Q).continuous_of_finiteDimensional⟩

/-- The full linkage projection restricts to the identity on the Boros row space. -/
theorem borosLinkageContinuousProjectionsOnRowSpace_univ (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] :
    N.borosLinkageContinuousProjectionsOnRowSpace
        (⟨Finset.univ, by simp⟩ :
          Analysis.BorosSubsetIndex (Quotient N.linkedSetoid)) =
      ContinuousLinearMap.id ℝ N.borosLinkageRowSpace := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change ((N.borosLinkageProjectionSystem).project Finset.univ) x.1 = x.1
  rw [(N.borosLinkageProjectionSystem).project_univ]
  rfl

/-- The nested Boros projection domain inside the product of linkage-class row spaces. -/
noncomputable def borosLinkageRowSpaceNestedProjectionDomain (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ) :
    Set N.borosLinkageRowSpace :=
  Analysis.borosNestedProjectionDomain
    N.borosLinkageContinuousProjectionsOnRowSpace r

/-- The product-row-space Boros domain is nonempty, convex, and compact. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_compactConvex_nonempty
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] (r : ℕ → ℝ) :
    (N.borosLinkageRowSpaceNestedProjectionDomain r).Nonempty ∧
      Convex ℝ (N.borosLinkageRowSpaceNestedProjectionDomain r) ∧
      IsCompact (N.borosLinkageRowSpaceNestedProjectionDomain r) := by
  exact Analysis.borosNestedProjectionDomain_compactConvex_nonempty
    N.borosLinkageContinuousProjectionsOnRowSpace r
    N.borosLinkageContinuousProjectionsOnRowSpace_univ

/-- A deficiency-one network has at least one complex and therefore at least one linkage class.
This discharges the nonemptiness side condition needed by the finite linkage-projection domain. -/
theorem nonemptyLinkageClass_of_deficiencyOne (N : Network S)
    (hδ : N.DeficiencyOne) : Nonempty (Quotient N.linkedSetoid) := by
  have hdef : N.deficiency = 1 := (deficiencyOne_iff_deficiency_eq_one N).mp hδ
  have hnum : 0 < N.numComplexes := by
    rw [N.numComplexes_eq_add, hdef]
    omega
  have hcardComplex : Fintype.card N.ComplexIdx = N.numComplexes := by
    simp [Network.numComplexes, Network.ComplexIdx]
  have hcard : 0 < Fintype.card N.ComplexIdx := by
    rw [hcardComplex]
    exact hnum
  rcases Fintype.card_pos_iff.mp hcard with ⟨c⟩
  exact ⟨N.classOf c⟩

/-- Under the deficiency-one hypothesis, the Boros nested projection domain in the product of
linkage-class complex row spaces is nonempty, convex, and compact. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_compactConvex_nonempty_of_deficiencyOne
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hδ : N.DeficiencyOne) (r : ℕ → ℝ) :
    (N.borosLinkageRowSpaceNestedProjectionDomain r).Nonempty ∧
      Convex ℝ (N.borosLinkageRowSpaceNestedProjectionDomain r) ∧
      IsCompact (N.borosLinkageRowSpaceNestedProjectionDomain r) := by
  letI : Nonempty (Quotient N.linkedSetoid) := N.nonemptyLinkageClass_of_deficiencyOne hδ
  exact N.borosLinkageRowSpaceNestedProjectionDomain_compactConvex_nonempty r

/-- Subtracting a linkage-subset projection gives a feasible point in the product-row-space
Boros domain. This is the boundary test direction used with Brouwer's projected fixed point. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_sub_projection
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ)
    (Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid))
    {x : N.borosLinkageRowSpace}
    (hx : x ∈ N.borosLinkageRowSpaceNestedProjectionDomain r) :
    x - N.borosLinkageProjectionOnRowSpace Q x ∈
      N.borosLinkageRowSpaceNestedProjectionDomain r := by
  intro R
  have hxR := hx R
  have hstep := Analysis.BorosBlockProjectionSystem.project_norm_sub_smul_project_le
    N.borosLinkageProjectionSystem (t := 1) (by norm_num) (by norm_num) Q.1 R.1 x.1
  have hstep' :
      ‖N.borosLinkageProjectionSystem.project R.1
        (x.1 - N.borosLinkageProjectionSystem.project Q.1 x.1)‖ ≤
      ‖N.borosLinkageProjectionSystem.project R.1 x.1‖ := by
    simpa using hstep
  have hbound :
      ‖N.borosLinkageProjectionSystem.project R.1 x.1‖ ≤
        Analysis.borosProjectionRadius r R := by
    simpa [borosLinkageContinuousProjectionsOnRowSpace,
      borosLinkageProjectionOnRowSpace] using hxR
  change ‖N.borosLinkageContinuousProjectionsOnRowSpace R
      (x - N.borosLinkageProjectionOnRowSpace Q x)‖ ≤ _
  calc
    _ ≤ ‖N.borosLinkageProjectionSystem.project R.1 x.1‖ := by
      simpa [borosLinkageContinuousProjectionsOnRowSpace,
        borosLinkageProjectionOnRowSpace] using hstep'
    _ ≤ _ := hbound

/-- A point satisfying the Boros-domain variational inequality has nonpositive pairing with each
linkage-subset projection. At an active boundary constraint this contradicts the strict inward
estimate for the negative field. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_variational_projection_inner_nonpos
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ)
    {x v : N.borosLinkageRowSpace}
    (hx : x ∈ N.borosLinkageRowSpaceNestedProjectionDomain r)
    (hvi : ∀ y ∈ N.borosLinkageRowSpaceNestedProjectionDomain r,
      0 ≤ inner ℝ v (y - x)) :
    ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
      inner ℝ v (N.borosLinkageProjectionOnRowSpace Q x) ≤ 0 := by
  intro Q
  have hw := N.borosLinkageRowSpaceNestedProjectionDomain_sub_projection r Q hx
  have h := hvi _ hw
  have hsub :
      (x - N.borosLinkageProjectionOnRowSpace Q x) - x =
        -N.borosLinkageProjectionOnRowSpace Q x := by
    abel
  rw [hsub, inner_neg_right] at h
  linarith

/-- Strict satisfaction of every finite linkage-subset bound places a point in the relative
interior of the product-row-space Boros domain. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_mem_interior_of_strict
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ)
    {x : N.borosLinkageRowSpace}
    (hstrict : ∀ Q,
      ‖N.borosLinkageContinuousProjectionsOnRowSpace Q x‖ <
        Analysis.borosProjectionRadius r Q) :
    x ∈ interior (N.borosLinkageRowSpaceNestedProjectionDomain r) := by
  exact Analysis.mem_interior_projectionConstraintSet_of_strict
    N.borosLinkageContinuousProjectionsOnRowSpace (Analysis.borosProjectionRadius r) hstrict

/-- The Boros fixed-point interface closes once every active nested-domain boundary has a strict
inward estimate: a variational-inequality point cannot be on the boundary, hence the field is
zero at its relative-interior point. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_variational_eq_zero_of_strict_inward
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ)
    {x v : N.borosLinkageRowSpace}
    (hx : x ∈ N.borosLinkageRowSpaceNestedProjectionDomain r)
    (hvi : ∀ y ∈ N.borosLinkageRowSpaceNestedProjectionDomain r,
      0 ≤ inner ℝ v (y - x))
    (hinward : ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
      ‖N.borosLinkageContinuousProjectionsOnRowSpace Q x‖ =
        Analysis.borosProjectionRadius r Q →
      0 < inner ℝ v (N.borosLinkageProjectionOnRowSpace Q x)) :
    v = 0 := by
  have hprojIdem (Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid))
      (y : EuclideanSpace ℝ N.ComplexIdx) :
      N.borosLinkageProjectionSystem.project Q.1
          (N.borosLinkageProjectionSystem.project Q.1 y) =
        N.borosLinkageProjectionSystem.project Q.1 y := by
    have h := congrArg (fun f => f y)
      (N.borosLinkageProjectionSystem.project_comp Q.1 Q.1)
    simpa using h
  have hinner (Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid)) :
      inner ℝ (N.borosLinkageContinuousProjectionsOnRowSpace Q v)
          (N.borosLinkageContinuousProjectionsOnRowSpace Q x) =
        inner ℝ v (N.borosLinkageProjectionOnRowSpace Q x) := by
    change inner ℝ
        (N.borosLinkageProjectionSystem.project Q.1 v.1)
        (N.borosLinkageProjectionSystem.project Q.1 x.1) =
      inner ℝ v.1 (N.borosLinkageProjectionSystem.project Q.1 x.1)
    calc
      _ = inner ℝ v.1
          (N.borosLinkageProjectionSystem.project Q.1
            (N.borosLinkageProjectionSystem.project Q.1 x.1)) :=
          N.borosLinkageProjectionSystem.project_selfAdjoint Q.1 v.1
            (N.borosLinkageProjectionSystem.project Q.1 x.1)
      _ = _ := by rw [hprojIdem]
  have hstrict : ∀ Q,
      ‖N.borosLinkageContinuousProjectionsOnRowSpace Q x‖ =
        Analysis.borosProjectionRadius r Q →
      0 < inner ℝ
        (N.borosLinkageContinuousProjectionsOnRowSpace Q v)
        (N.borosLinkageContinuousProjectionsOnRowSpace Q x) := by
    intro Q hboundary
    rw [hinner Q]
    exact hinward Q hboundary
  exact Analysis.variational_eq_zero_of_active_inward_projectionConstraints
    N.borosLinkageContinuousProjectionsOnRowSpace (Analysis.borosProjectionRadius r)
    hx hvi hstrict

/-- Finite-dimensional Brouwer completes the Boros zero step on the product row space: any
continuous field with strict inward pairing at every active nested bound vanishes somewhere in the
nonempty compact convex domain. -/
theorem borosLinkageRowSpaceNestedProjectionDomain_exists_zero_of_strict_inward
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hδ : N.DeficiencyOne) (r : ℕ → ℝ)
    (v : N.borosLinkageRowSpace → N.borosLinkageRowSpace)
    (hv : ContinuousOn v (N.borosLinkageRowSpaceNestedProjectionDomain r))
    (hinward : ∀ x ∈ N.borosLinkageRowSpaceNestedProjectionDomain r,
      ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
        ‖N.borosLinkageContinuousProjectionsOnRowSpace Q x‖ =
          Analysis.borosProjectionRadius r Q →
        0 < inner ℝ (v x) (N.borosLinkageProjectionOnRowSpace Q x)) :
    ∃ x ∈ N.borosLinkageRowSpaceNestedProjectionDomain r, v x = 0 := by
  obtain ⟨hne, hconv, hcomp⟩ :=
    N.borosLinkageRowSpaceNestedProjectionDomain_compactConvex_nonempty_of_deficiencyOne
      hδ r
  obtain ⟨x, hx, hvi⟩ := Analysis.exists_variational_inequality_point_finiteDimensional
    hne hconv hcomp v hv
  refine ⟨x, hx, ?_⟩
  exact N.borosLinkageRowSpaceNestedProjectionDomain_variational_eq_zero_of_strict_inward
    r hx hvi (hinward x hx)

/-- Boros's uniform projection lower bound specialized to the product of linkage-class complex
row spaces. -/
theorem exists_positive_norm_lower_bound_borosLinkageRowSpaceResidual (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    {Q Q' : Finset (Quotient N.linkedSetoid)} (hQ' : Q' ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y,
      y ∈ Analysis.borosResidualSubspace N.borosLinkageProjectionSystem
        N.borosLinkageRowSpace Q Q' →
        ε * ‖y‖ ≤ ‖(N.borosLinkageProjectionSystem).project Q' y‖ := by
  exact Analysis.exists_positive_norm_lower_bound_borosResidual
    N.borosLinkageProjectionSystem N.borosLinkageRowSpace hQ'

/-- The Boros residual projection estimate specialized to linkage-class coordinates. -/
theorem exists_positive_norm_lower_bound_borosLinkageResidual
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [FiniteDimensional ℝ (EuclideanSpace ℝ N.ComplexIdx)]
    (H : Submodule ℝ (EuclideanSpace ℝ N.ComplexIdx))
    {Q Q' : Finset (Quotient N.linkedSetoid)} (hQ' : Q' ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y,
      y ∈ Analysis.borosResidualSubspace N.borosLinkageProjectionSystem H Q Q' →
        ε * ‖y‖ ≤ ‖(N.borosLinkageProjectionSystem).project Q' y‖ := by
  classical
  exact Analysis.exists_positive_norm_lower_bound_borosResidual
    N.borosLinkageProjectionSystem H hQ'

/-- The coordinate projections bundled as continuous linear maps for the nested Boros domain. -/
noncomputable def borosLinkageContinuousProjections (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] :
    Analysis.BorosSubsetIndex (Quotient N.linkedSetoid) →
      EuclideanSpace ℝ N.ComplexIdx →L[ℝ] EuclideanSpace ℝ N.ComplexIdx :=
  fun Q =>
    ⟨(N.borosLinkageProjectionSystem).project Q.1,
      (N.borosLinkageProjectionSystem.project Q.1).continuous_of_finiteDimensional⟩

/-- The projection indexed by all linkage classes is the identity. -/
theorem borosLinkageContinuousProjections_univ (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] :
    N.borosLinkageContinuousProjections
        (⟨Finset.univ, by simp⟩ :
          Analysis.BorosSubsetIndex (Quotient N.linkedSetoid)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ N.ComplexIdx) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro c
  change ((N.borosLinkageProjectionSystem).project Finset.univ x) c = x c
  rw [(N.borosLinkageProjectionSystem).project_univ]
  rfl

/-- The nested projection domain for linkage-class coordinates. -/
noncomputable def borosLinkageNestedProjectionDomain (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (r : ℕ → ℝ) :
    Set (EuclideanSpace ℝ N.ComplexIdx) :=
  Analysis.borosNestedProjectionDomain (N.borosLinkageContinuousProjections) r

/-- The network's nested linkage projection domain is nonempty, convex, and compact in the
finite-dimensional complex space. This supplies the geometric half of the Boros Brouwer input. -/
theorem borosLinkageNestedProjectionDomain_compactConvex_nonempty
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] (r : ℕ → ℝ) :
    (N.borosLinkageNestedProjectionDomain r).Nonempty ∧
      Convex ℝ (N.borosLinkageNestedProjectionDomain r) ∧
      IsCompact (N.borosLinkageNestedProjectionDomain r) := by
  exact Analysis.borosNestedProjectionDomain_compactConvex_nonempty
    (N.borosLinkageContinuousProjections) r N.borosLinkageContinuousProjections_univ

end Network
end CRNT
