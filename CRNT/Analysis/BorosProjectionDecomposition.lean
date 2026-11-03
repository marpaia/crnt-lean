import CRNT.Analysis.FiniteProjectionConstraints
import CRNT.Analysis.BrouwerZero
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Boros linkage-subset projection decomposition

This file formalizes the linear-algebra step behind Boros's nested projection domain.  A finite
family of mutually orthogonal block projections gives, for each subset of linkage blocks, the part
of a subspace supported on those blocks.  After removing the subspaces supported on a subset and
its complement inside a larger subset, the remaining component is still observed injectively by
either block projection.  Finite dimensionality then gives Boros's uniform positive lower bound.

The mass-action inward estimates and the Brouwer/intersection step are separate from this file.
-/

namespace CRNT.Analysis

open scoped BigOperators

noncomputable section

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coordinate projections onto unions of finitely many orthogonal blocks. -/
structure BorosBlockProjectionSystem where
  project : Finset I → E →ₗ[ℝ] E
  project_empty : project ∅ = 0
  project_univ : project Finset.univ = LinearMap.id
  project_comp : ∀ Q R, (project Q).comp (project R) = project (Q ∩ R)
  project_selfAdjoint : ∀ Q x y,
    inner ℝ (project Q x) y = inner ℝ x (project Q y)
  project_add_subset : ∀ {Q R}, R ⊆ Q → ∀ x,
    project Q x = project R x + project (Q \ R) x

namespace BorosBlockProjectionSystem

variable (P : BorosBlockProjectionSystem (I := I) (E := E))

/-- Vectors supported on the blocks in `Q`. -/
def supported (Q : Finset I) : Submodule ℝ E := (P.project Qᶜ).ker

theorem project_eq_self_of_mem_supported {Q : Finset I} {x : E}
    (hx : x ∈ P.supported Q) : P.project Q x = x := by
  have hdecomp := P.project_add_subset (Q := Finset.univ) (R := Q)
    (Finset.subset_univ Q) x
  rw [P.project_univ, LinearMap.id_apply] at hdecomp
  have hcomp : Finset.univ \ Q = Qᶜ := by
    ext i
    simp
  rw [hcomp] at hdecomp
  have hzero : P.project Qᶜ x = 0 := LinearMap.mem_ker.mp hx
  have hdecomp' : x = P.project Q x + P.project Qᶜ x := hdecomp
  rw [hzero, add_zero] at hdecomp'
  exact hdecomp'.symm

theorem supported_mono {Q R : Finset I} (hQR : Q ⊆ R) :
    P.supported Q ≤ P.supported R := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  rw [← P.project_eq_self_of_mem_supported hx]
  change ((P.project Rᶜ).comp (P.project Q)) x = 0
  rw [P.project_comp]
  have hdisj : Rᶜ ∩ Q = ∅ := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro ⟨hiR, hiQ⟩
      exact False.elim (hiR (hQR hiQ))
    · intro hi
      simp at hi
  rw [hdisj, P.project_empty]
  simp

theorem inner_eq_zero_of_supported_disjoint {Q R : Finset I} {x y : E}
    (hQR : Q ∩ R = ∅) (hx : x ∈ P.supported Q) (hy : y ∈ P.supported R) :
    inner ℝ x y = 0 := by
  have hpx := P.project_eq_self_of_mem_supported hx
  have hpy := P.project_eq_self_of_mem_supported hy
  have hproj : P.project Q y = 0 := by
    rw [← hpy]
    change ((P.project Q).comp (P.project R)) y = 0
    rw [P.project_comp, hQR, P.project_empty]
    simp
  calc
    inner ℝ x y = inner ℝ (P.project Q x) y := by rw [hpx]
    _ = inner ℝ x (P.project Q y) := P.project_selfAdjoint Q x y
    _ = 0 := by rw [hproj]; simp

/-- Moving a vector toward one linkage-subset projection cannot increase its norm after any
other linkage-subset projection, provided the step length is at most two. The projected
component is orthogonal to the complementary coordinates, so its coefficient changes from `1`
to `1 - t` while the complementary component stays fixed. -/
theorem project_norm_sub_smul_project_le
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (Q R : Finset I) (x : E) :
    ‖P.project R (x - t • P.project Q x)‖ ≤ ‖P.project R x‖ := by
  let A := R ∩ Q
  let B := R \ Q
  have hAR : A ⊆ R := by simp [A]
  have hRA : R \ A = B := by
    ext i
    simp [A, B]
  have hdecomp := P.project_add_subset (Q := R) (R := A) hAR x
  rw [hRA] at hdecomp
  let u := P.project A x
  let w := P.project B x
  have hdecomp' : P.project R x = u + w := by simpa [u, w] using hdecomp
  have hcomp : P.project R (P.project Q x) = u := by
    change ((P.project R).comp (P.project Q)) x = _
    rw [P.project_comp]
  have hstep : P.project R (x - t • P.project Q x) = (1 - t) • u + w := by
    rw [map_sub, map_smul, hcomp, hdecomp']
    simp only [u, w]
    module
  have hu : u ∈ P.supported A := by
    apply LinearMap.mem_ker.mpr
    change P.project Aᶜ (P.project A x) = 0
    rw [← LinearMap.comp_apply, P.project_comp]
    have hdisj : Aᶜ ∩ A = ∅ := by
      ext i
      simp
    rw [hdisj, P.project_empty]
    simp
  have hw : w ∈ P.supported B := by
    apply LinearMap.mem_ker.mpr
    change P.project Bᶜ (P.project B x) = 0
    rw [← LinearMap.comp_apply, P.project_comp]
    have hdisj : Bᶜ ∩ B = ∅ := by
      ext i
      simp
    rw [hdisj, P.project_empty]
    simp
  have horth : inner ℝ u w = 0 :=
    P.inner_eq_zero_of_supported_disjoint (by
      ext i
      simp [A, B]) hu hw
  have hscaledOrth : inner ℝ ((1 - t) • u) w = 0 := by
    rw [inner_smul_left, horth]
    simp
  have hnewSq : ‖(1 - t) • u + w‖ ^ 2 =
      ‖(1 - t) • u‖ ^ 2 + ‖w‖ ^ 2 :=
    by simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_real hscaledOrth
  have holdSq : ‖u + w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 :=
    by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hsmulSq : ‖(1 - t) • u‖ ^ 2 = (1 - t) ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have habs : |1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hfactor : (1 - t) ^ 2 ≤ 1 := by
    have hlo : -1 ≤ 1 - t := (abs_le.mp habs).1
    have hhi : 1 - t ≤ 1 := (abs_le.mp habs).2
    have hprod : ((1 - t) - 1) * ((1 - t) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hsq : ‖P.project R (x - t • P.project Q x)‖ ^ 2 ≤
      ‖P.project R x‖ ^ 2 := by
    rw [hstep, hnewSq, hsmulSq, hdecomp', holdSq]
    nlinarith [sq_nonneg ‖u‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Continuous family of the Boros coordinate projections in finite dimensions. -/
noncomputable def continuousProjectFamily [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) :
    BorosSubsetIndex I → E →L[ℝ] E := fun Q =>
      ⟨P.project Q.1, (P.project Q.1).continuous_of_finiteDimensional⟩

/-- A full inward step along one Boros coordinate projection stays in the nested projection
domain. This supplies a feasible test point for the variational inequality at a fixed point. -/
theorem sub_project_mem_borosNestedProjectionDomain
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (r : ℕ → ℝ)
    (Q : BorosSubsetIndex I) {x : E}
    (hx : x ∈ borosNestedProjectionDomain P.continuousProjectFamily r) :
    x - P.project Q.1 x ∈ borosNestedProjectionDomain P.continuousProjectFamily r := by
  change ∀ R, ‖P.project R.1 x‖ ≤ borosProjectionRadius r R at hx
  change ∀ R, ‖P.project R.1 (x - P.project Q.1 x)‖ ≤ borosProjectionRadius r R
  intro R
  calc
    ‖P.project R.1 (x - P.project Q.1 x)‖ ≤ ‖P.project R.1 x‖ := by
      simpa using P.project_norm_sub_smul_project_le
        (t := 1) (by norm_num) (by norm_num) Q.1 R.1 x
    _ ≤ borosProjectionRadius r R := hx R

/-- At a point satisfying the variational inequality on the Boros nested domain, every linkage
subset projection has nonpositive pairing with the vector field. -/
theorem borosNestedProjectionDomain_variational_projection_inner_nonpos
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (r : ℕ → ℝ)
    {x v : E} (hx : x ∈ borosNestedProjectionDomain P.continuousProjectFamily r)
    (hvi : ∀ y ∈ borosNestedProjectionDomain P.continuousProjectFamily r,
      0 ≤ inner ℝ v (y - x)) :
    ∀ Q : BorosSubsetIndex I, inner ℝ v (P.project Q.1 x) ≤ 0 := by
  intro Q
  have hw := P.sub_project_mem_borosNestedProjectionDomain r Q hx
  have h := hvi (x - P.project Q.1 x) hw
  have hsub : (x - P.project Q.1 x) - x = -P.project Q.1 x := by abel
  rw [hsub, inner_neg_right] at h
  linarith

end BorosBlockProjectionSystem

/-- A vector field satisfying the Brouwer variational inequality at an interior point must vanish.
The proof tests the field direction inside a small ball around that point. -/
theorem variational_eq_zero_of_mem_interior {K : Set E} {x v : E}
    (hx : x ∈ interior K)
    (hvi : ∀ y ∈ K, 0 ≤ inner ℝ v (y - x)) : v = 0 := by
  by_contra hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) x hx
  let t : ℝ := ε / (2 * ‖v‖)
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hvnorm)
  let y : E := x - t • v
  have hdist : dist y x = ε / 2 := by
    dsimp [y]
    rw [dist_eq_norm]
    have hsub : x - t • v - x = -(t • v) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hvnorm]
  have hball' : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, hdist]
    linarith
  have hy : y ∈ K := interior_subset (hball hball')
  have hvi' := hvi y hy
  have hsub : y - x = -(t • v) := by dsimp [y]; abel
  rw [hsub, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq] at hvi'
  have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvnorm
  nlinarith [mul_pos ht hsq]

/-- Every continuous vector field on a nonempty compact convex set in a finite-dimensional inner
product space has a point satisfying the Brouwer variational inequality. The proof transports the
set isometrically to a Euclidean space, where the projected-displacement fixed-point theorem
applies. -/
theorem exists_variational_inequality_point_finiteDimensional
    [FiniteDimensional ℝ E] {K : Set E}
    (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : E → E) (hv : ContinuousOn v K) :
    ∃ x ∈ K, ∀ w ∈ K, 0 ≤ inner ℝ (v x) (w - x) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) (Module.finBasis ℝ E)
  let e := b.repr
  let K' := e '' K
  have hne' : K'.Nonempty := hne.image e
  have hconv' : Convex ℝ K' := hconv.linear_image e.toLinearEquiv.toLinearMap
  have hcomp' : IsCompact K' := hcomp.image e.continuous
  let v' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun y => e (v (e.symm y))
  have hv' : ContinuousOn v' K' := by
    have hsymm : Set.MapsTo e.symm K' K := by
      rintro y ⟨x, hx, rfl⟩
      simpa using hx
    exact e.continuous.comp_continuousOn
      (hv.comp (e.symm.continuous.continuousOn) hsymm)
  obtain ⟨y, hyK, _, hvi⟩ :=
    exists_projected_fixedPoint hne' hconv' hcomp' v' hv'
  rcases hyK with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  intro w hw
  have hw' : e w ∈ K' := ⟨w, hw, rfl⟩
  have h := hvi (e w) hw'
  change 0 ≤ inner ℝ (e (v (e.symm (e x)))) (e w - e x) at h
  rw [e.symm_apply_apply, ← e.map_sub, e.inner_map_map] at h
  exact h

/-- The coordinate mask for the union of blocks selected by `Q`. -/
def borosCoordinateBlockMask {J : Type*} [Fintype J]
    (blockOf : J → I) (Q : Finset I) : (J → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun x := fun j => if blockOf j ∈ Q then x j else 0
  map_add' x y := by
    funext j
    by_cases hj : blockOf j ∈ Q <;> simp [hj]
  map_smul' a x := by
    funext j
    by_cases hj : blockOf j ∈ Q <;> simp [hj]

/-- Euclidean projection onto the coordinates whose block belongs to `Q`. -/
noncomputable def borosCoordinateBlockProject {J : Type*} [Fintype J]
    (blockOf : J → I) (Q : Finset I) :
    EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J :=
  (CRNT.toEuclid (ι := J)).toLinearMap.comp
    ((borosCoordinateBlockMask blockOf Q).comp
      (CRNT.toEuclid (ι := J)).symm.toLinearMap)

private theorem toEuclid_symm_apply {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ J) (j : J) :
    (CRNT.toEuclid (ι := J)).symm x j = x j := by
  have h := congrArg (fun v : EuclideanSpace ℝ J => v j)
    ((CRNT.toEuclid (ι := J)).apply_symm_apply x)
  simpa only [CRNT.toEuclid_apply] using h

omit [Fintype I] in
@[simp] theorem borosCoordinateBlockProject_apply {J : Type*} [Fintype J]
    (blockOf : J → I) (Q : Finset I) (x : EuclideanSpace ℝ J) (j : J) :
    borosCoordinateBlockProject (I := I) blockOf Q x j =
      if blockOf j ∈ Q then x j else 0 := by
  simp [borosCoordinateBlockProject, borosCoordinateBlockMask,
    CRNT.toEuclid_apply, toEuclid_symm_apply]

/-- Canonical mutually orthogonal coordinate projections associated to a finite block map.
Taking `J` to be network complexes and `blockOf` to be the linkage-class map gives the
linkage-subset projections used in Boros's construction. -/
noncomputable def borosCoordinateBlockProjectionSystem {J : Type*} [Fintype J]
    (blockOf : J → I) :
    BorosBlockProjectionSystem (I := I) (E := EuclideanSpace ℝ J) where
  project := borosCoordinateBlockProject blockOf
  project_empty := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro j
    simp
  project_univ := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro j
    simp
  project_comp := by
    intro Q R
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro j
    by_cases hQ : blockOf j ∈ Q <;> by_cases hR : blockOf j ∈ R <;>
      simp [LinearMap.comp_apply, Finset.mem_inter, hQ, hR]
  project_selfAdjoint := by
    intro Q x y
    simp only [PiLp.inner_apply, borosCoordinateBlockProject_apply,
      RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : blockOf j ∈ Q <;> simp [h]
  project_add_subset := by
    intro Q R hRQ x
    apply PiLp.ext
    intro j
    by_cases hR : blockOf j ∈ R
    · have hQ : blockOf j ∈ Q := hRQ hR
      simp [hR, hQ]
    · by_cases hQ : blockOf j ∈ Q
      · simp [hR, hQ, Finset.mem_sdiff]
      · simp [hR, hQ, Finset.mem_sdiff]

/-- The part of `H` supported on the blocks indexed by `Q`. -/
def borosLinkageSlice (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) (Q : Finset I) : Submodule ℝ E := H ⊓ P.supported Q

theorem borosLinkageSlice_mono (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) {Q R : Finset I} (hQR : Q ⊆ R) :
    borosLinkageSlice P H Q ≤ borosLinkageSlice P H R :=
  inf_le_inf_left H (P.supported_mono hQR)

theorem borosLinkageSlices_isOrtho (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) {Q R : Finset I} (hQR : Q ∩ R = ∅) :
    (borosLinkageSlice P H Q).IsOrtho (borosLinkageSlice P H R) := by
  intro x hx y hy
  have hRQ : R ∩ Q = ∅ := by simpa [Finset.inter_comm] using hQR
  exact P.inner_eq_zero_of_supported_disjoint hRQ hy.2 hx.2

/-- The residual part of `H_Q` after removing components supported in `Q'` or `Q \ Q'`. -/
def borosResidualSubspace (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) (Q Q' : Finset I) : Submodule ℝ E :=
  borosLinkageSlice P H Q ⊓
    (borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H (Q \ Q'))ᗮ

/- The block-supported part of H on the linkage subset Q. -/
def borosLinkageSliceWithin (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) (Q : Finset I) : Submodule ℝ H :=
  (borosLinkageSlice P H Q).comap H.subtype

/-- No nonzero vector is supported on an empty union of blocks. -/
theorem borosLinkageSliceWithin_empty
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E) :
    borosLinkageSliceWithin P H ∅ = ⊥ := by
  ext x
  simp [borosLinkageSliceWithin, borosLinkageSlice,
    BorosBlockProjectionSystem.supported, P.project_univ]

private theorem borosWithinProjection_sub_mem_orthogonal
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E)
    {A B : Finset I} (hAB : A ⊆ B) (x : H) :
    (borosLinkageSliceWithin P H B).starProjection x -
      (borosLinkageSliceWithin P H A).starProjection x ∈
        (borosLinkageSliceWithin P H A)ᗮ := by
  let U := borosLinkageSliceWithin P H A
  let V := borosLinkageSliceWithin P H B
  have hUV : U ≤ V := by
    intro a ha
    change a.1 ∈ borosLinkageSlice P H A at ha
    change a.1 ∈ borosLinkageSlice P H B
    exact borosLinkageSlice_mono P H hAB ha
  rw [Submodule.mem_orthogonal']
  intro t ht
  calc
    inner ℝ (V.starProjection x - U.starProjection x) t =
        inner ℝ (V.starProjection x) t - inner ℝ (U.starProjection x) t := by
          rw [inner_sub_left]
    _ = inner ℝ x (V.starProjection t) - inner ℝ x (U.starProjection t) := by
          rw [V.inner_starProjection_left_eq_right, U.inner_starProjection_left_eq_right]
    _ = inner ℝ x t - inner ℝ x t := by
          rw [V.starProjection_eq_self_iff.mpr (hUV ht),
            U.starProjection_eq_self_iff.mpr ht]
    _ = 0 := sub_self _

/-- The internal projection onto a union of blocks splits into the projections onto a subset
and its complement, plus a residual orthogonal to both supported subspaces. -/
theorem borosWithinProjection_decompose
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E)
    {Q Q' : Finset I} (hQ' : Q' ⊆ Q) (x : H) :
    ∃ y : H,
      (borosLinkageSliceWithin P H Q).starProjection x =
        (borosLinkageSliceWithin P H Q').starProjection x +
          (borosLinkageSliceWithin P H (Q \ Q')).starProjection x + y ∧
      y.1 ∈ borosResidualSubspace P H Q Q' ∧
      inner ℝ ((borosLinkageSliceWithin P H Q').starProjection x) y = 0 ∧
      inner ℝ ((borosLinkageSliceWithin P H (Q \ Q')).starProjection x) y = 0 ∧
      inner ℝ ((borosLinkageSliceWithin P H Q').starProjection x)
        ((borosLinkageSliceWithin P H (Q \ Q')).starProjection x) = 0 := by
  classical
  let UQ := borosLinkageSliceWithin P H Q
  let UQ' := borosLinkageSliceWithin P H Q'
  let UD := borosLinkageSliceWithin P H (Q \ Q')
  have hQ'le : UQ' ≤ UQ := by
    intro a ha
    change a.1 ∈ borosLinkageSlice P H Q' at ha
    change a.1 ∈ borosLinkageSlice P H Q
    exact borosLinkageSlice_mono P H hQ' ha
  have hDle : UD ≤ UQ := by
    intro a ha
    change a.1 ∈ borosLinkageSlice P H (Q \ Q') at ha
    change a.1 ∈ borosLinkageSlice P H Q
    exact borosLinkageSlice_mono P H Finset.sdiff_subset ha
  have hdisj : Q' ∩ (Q \ Q') = ∅ := by
    ext i
    simp
  have horth : UQ'.IsOrtho UD := by
    intro a ha
    rw [UD.mem_orthogonal']
    intro b hb
    change a.1 ∈ borosLinkageSlice P H Q' at ha
    change b.1 ∈ borosLinkageSlice P H (Q \ Q') at hb
    exact P.inner_eq_zero_of_supported_disjoint hdisj ha.2 hb.2
  let zQ : H := UQ.starProjection x
  let zQ' : H := UQ'.starProjection x
  let zD : H := UD.starProjection x
  let y : H := zQ - zQ' - zD
  have hzQ : zQ ∈ UQ := UQ.starProjection_apply_mem x
  have hzQ' : zQ' ∈ UQ' := UQ'.starProjection_apply_mem x
  have hzD : zD ∈ UD := UD.starProjection_apply_mem x
  have hyQ' : y ∈ UQ'ᗮ := by
    have hdiff : zQ - zQ' ∈ UQ'ᗮ :=
      borosWithinProjection_sub_mem_orthogonal P H hQ' x
    have hDorth : zD ∈ UQ'ᗮ := by
      rw [UQ'.mem_orthogonal']
      intro t ht
      exact (UQ'.mem_orthogonal' zD).mp (horth.symm hzD) t ht
    change (zQ - zQ') - zD ∈ UQ'ᗮ
    exact (UQ'ᗮ).sub_mem hdiff hDorth
  have hyD : y ∈ UDᗮ := by
    have hdiff : zQ - zD ∈ UDᗮ := by
      exact borosWithinProjection_sub_mem_orthogonal P H
        (Finset.sdiff_subset : Q \ Q' ⊆ Q) x
    have hQ'orth : zQ' ∈ UDᗮ := by
      rw [UD.mem_orthogonal']
      intro t ht
      exact (UD.mem_orthogonal' zQ').mp (horth hzQ') t ht
    have heq : y = (zQ - zD) - zQ' := by
      dsimp [y, zQ, zQ', zD]
      abel
    rw [heq]
    exact UDᗮ.sub_mem hdiff hQ'orth
  have hyQ : y ∈ UQ := by
    change y ∈ UQ
    exact UQ.sub_mem (UQ.sub_mem hzQ (hQ'le hzQ')) (hDle hzD)
  have hyorthQ' : (y.1 : E) ∈ (borosLinkageSlice P H Q')ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro t ht
    let tH : H := ⟨t, (Submodule.mem_inf.mp ht).1⟩
    have htH : tH ∈ UQ' := by
      change t ∈ borosLinkageSlice P H Q'
      exact ht
    have h := (UQ'.mem_orthogonal' y).mp hyQ' tH htH
    simpa using h
  have hyorthD : (y.1 : E) ∈ (borosLinkageSlice P H (Q \ Q'))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro t ht
    let tH : H := ⟨t, (Submodule.mem_inf.mp ht).1⟩
    have htH : tH ∈ UD := by
      change t ∈ borosLinkageSlice P H (Q \ Q')
      exact ht
    have h := (UD.mem_orthogonal' y).mp hyD tH htH
    simpa using h
  have hyorth : (y.1 : E) ∈
      (borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H (Q \ Q'))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro t ht
    rcases Submodule.mem_sup.mp ht with ⟨a, ha, b, hb, rfl⟩
    rw [inner_add_right]
    have hya : inner ℝ (y.1 : E) a = 0 :=
      ((borosLinkageSlice P H Q').mem_orthogonal' y.1).mp hyorthQ' a ha
    have hyb : inner ℝ (y.1 : E) b = 0 :=
      ((borosLinkageSlice P H (Q \ Q')).mem_orthogonal' y.1).mp hyorthD b hb
    rw [hya, hyb, add_zero]
  have hyres : y.1 ∈ borosResidualSubspace P H Q Q' := by
    have hySlice : y.1 ∈ borosLinkageSlice P H Q := by
      change y ∈ UQ at hyQ
      exact hyQ
    exact ⟨hySlice, hyorth⟩
  have hdecomp : zQ = zQ' + zD + y := by
    dsimp [y]
    abel
  have hcross : inner ℝ zQ' zD = 0 :=
    (UD.mem_orthogonal' zQ').mp (horth hzQ') zD hzD
  have hyD' : inner ℝ zD y = 0 :=
    Submodule.inner_right_of_mem_orthogonal hzD hyD
  have hyQ'' : inner ℝ zQ' y = 0 :=
    Submodule.inner_right_of_mem_orthogonal hzQ' hyQ'
  exact ⟨y, hdecomp, hyres, hyQ'', hyD', hcross⟩

/-- The `Q'` block projection is injective on the residual subspace in the Boros decomposition.
This is the qualitative core of Boros Lemma 13(ii). -/
theorem borosProjection_injective_on_residual
    (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) {Q Q' : Finset I} (hQ' : Q' ⊆ Q) :
    Function.Injective
      (fun y : borosResidualSubspace P H Q Q' => P.project Q' y.1) := by
  intro y z hyz
  let V := borosResidualSubspace P H Q Q'
  have hwV : (y.1 - z.1) ∈ V := V.sub_mem y.2 z.2
  have hwQ : y.1 - z.1 ∈ borosLinkageSlice P H Q := hwV.1
  have hwprojQ : P.project Q (y.1 - z.1) = y.1 - z.1 :=
    P.project_eq_self_of_mem_supported hwQ.2
  have hyz' : P.project Q' y.1 = P.project Q' z.1 := hyz
  have hwprojQ' : P.project Q' (y.1 - z.1) = 0 := by
    rw [map_sub, hyz', sub_self]
  have hdecomp := P.project_add_subset hQ' (y.1 - z.1)
  have hwprojDiff : P.project (Q \ Q') (y.1 - z.1) = y.1 - z.1 := by
    rw [hwprojQ, hwprojQ'] at hdecomp
    simpa using hdecomp.symm
  let D := Q \ Q'
  have hwSupportDiff : y.1 - z.1 ∈ P.supported D := by
    apply LinearMap.mem_ker.mpr
    rw [← hwprojDiff]
    change ((P.project Dᶜ).comp (P.project D)) (y.1 - z.1) = 0
    have hDD : Dᶜ ∩ D = ∅ := by
      ext i
      simp
    rw [P.project_comp, hDD, P.project_empty]
    simp
  have hwDiff : y.1 - z.1 ∈ borosLinkageSlice P H D :=
    ⟨hwQ.1, hwSupportDiff⟩
  have hsum : y.1 - z.1 ∈
      borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H D :=
    Submodule.mem_sup_right hwDiff
  have horth : y.1 - z.1 ∈
      (borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H D)ᗮ := hwV.2
  have hzero : y.1 - z.1 = 0 := by
    have hmem : y.1 - z.1 ∈
        (borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H D) ⊓
          (borosLinkageSlice P H Q' ⊔ borosLinkageSlice P H D)ᗮ :=
      ⟨hsum, horth⟩
    simpa only [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] using hmem
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

/-- Boros Lemma 13(ii): the block projection has a uniform positive lower norm bound on the
finite-dimensional residual subspace. -/
theorem exists_positive_norm_lower_bound_borosResidual
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) {Q Q' : Finset I} (hQ' : Q' ⊆ Q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, y ∈ borosResidualSubspace P H Q Q' →
      ε * ‖y‖ ≤ ‖P.project Q' y‖ := by
  let V := borosResidualSubspace P H Q Q'
  have hinj : Function.Injective (fun y : V => P.project Q' y.1) :=
    borosProjection_injective_on_residual P H hQ'
  obtain ⟨ε, hε, hbound⟩ :=
    exists_positive_norm_lower_bound_on_submodule (V := V) (P.project Q') hinj
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact hbound y hy

/-- A large boundary projection on Q forces a quantitatively large observed component on each
single block in Q, provided the projection on the remaining blocks stays within its previous
radius. -/
theorem borosWithinProjection_singleton_component_norm_lower
    [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) {Q : Finset I} (i : I) (hi : i ∈ Q) (x : H)
    {R a b ε : ℝ}
    (hactive :
      ‖(borosLinkageSliceWithin P H Q).starProjection x‖ ^ 2 = R ^ 2 - a ^ 2)
    (hrest :
      ‖(borosLinkageSliceWithin P H (Q \ {i})).starProjection x‖ ^ 2 ≤
        R ^ 2 - b ^ 2)
    (hgap : 0 ≤ b ^ 2 - a ^ 2) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hres : ∀ y, y ∈ borosResidualSubspace P H Q {i} →
      ε * ‖y‖ ≤ ‖P.project {i} y‖) :
    ε * Real.sqrt ((b ^ 2 - a ^ 2) / 2) ≤
      ‖P.project {i} ((borosLinkageSliceWithin P H Q).starProjection x).1‖ := by
  classical
  let Q' : Finset I := {i}
  let D : Finset I := Q \ Q'
  have hQ'sub : Q' ⊆ Q := by
    intro j hj
    simp only [Q', Finset.mem_singleton] at hj
    simpa [hj] using hi
  obtain ⟨y, hdecomp, hyres, hyQ, hyD, hcross⟩ :=
    borosWithinProjection_decompose P H hQ'sub x
  let zQ : H := (borosLinkageSliceWithin P H Q).starProjection x
  let zQ' : H := (borosLinkageSliceWithin P H Q').starProjection x
  let zD : H := (borosLinkageSliceWithin P H D).starProjection x
  have hactive' : ‖zQ.1‖ ^ 2 = R ^ 2 - a ^ 2 := by
    simpa [zQ] using hactive
  have hrest' : ‖zD.1‖ ^ 2 ≤ R ^ 2 - b ^ 2 := by
    simpa [zD, D, Q'] using hrest
  have hzQ'slice : zQ'.1 ∈ borosLinkageSlice P H Q' := by
    have hmem : zQ' ∈ borosLinkageSliceWithin P H Q' :=
      (borosLinkageSliceWithin P H Q').starProjection_apply_mem x
    change zQ'.1 ∈ borosLinkageSlice P H Q' at hmem
    exact hmem
  have hzDslice : zD.1 ∈ borosLinkageSlice P H D := by
    have hmem : zD ∈ borosLinkageSliceWithin P H D :=
      (borosLinkageSliceWithin P H D).starProjection_apply_mem x
    change zD.1 ∈ borosLinkageSlice P H D at hmem
    exact hmem
  have hzQ'fix : P.project Q' zQ'.1 = zQ'.1 :=
    P.project_eq_self_of_mem_supported hzQ'slice.2
  have hzDfix : P.project D zD.1 = zD.1 :=
    P.project_eq_self_of_mem_supported hzDslice.2
  have hdisj : Q' ∩ D = ∅ := by
    ext j
    simp [Q', D]
  have hzDzero : P.project Q' zD.1 = 0 := by
    rw [← hzDfix]
    change ((P.project Q').comp (P.project D)) zD.1 = 0
    rw [P.project_comp, hdisj, P.project_empty]
    simp
  have hdecomp' : zQ.1 = zQ'.1 + zD.1 + y.1 := by
    simpa [zQ, zQ', zD, Q', D] using congrArg Subtype.val hdecomp
  have hprojectDecomp :
      P.project Q' zQ.1 = zQ'.1 + P.project Q' y.1 := by
    rw [hdecomp', map_add, map_add, hzQ'fix, hzDzero]
    simp
  have hblockOrth : inner ℝ zQ'.1 (P.project Q' y.1) = 0 := by
    calc
      inner ℝ zQ'.1 (P.project Q' y.1) =
          inner ℝ (P.project Q' zQ'.1) y.1 :=
        (P.project_selfAdjoint Q' zQ'.1 y.1).symm
      _ = inner ℝ zQ'.1 y.1 := by rw [hzQ'fix]
      _ = 0 := by simpa [zQ', Q'] using hyQ
  have hprojectNorm :
      ‖P.project Q' zQ.1‖ ^ 2 =
        ‖zQ'.1‖ ^ 2 + ‖P.project Q' y.1‖ ^ 2 := by
    rw [hprojectDecomp]
    rw [norm_add_sq_real, hblockOrth]
    ring
  have hsumOrth : inner ℝ (zQ'.1 + zD.1) y.1 = 0 := by
    rw [inner_add_left]
    have h1 : inner ℝ zQ'.1 y.1 = 0 := by simpa using hyQ
    have h2 : inner ℝ zD.1 y.1 = 0 := by simpa using hyD
    rw [h1, h2, zero_add]
  have hdecompNorm :
      ‖zQ.1‖ ^ 2 = ‖zQ'.1‖ ^ 2 + ‖zD.1‖ ^ 2 + ‖y.1‖ ^ 2 := by
    rw [hdecomp']
    rw [norm_add_sq_real, hsumOrth, norm_add_sq_real]
    have hcross' : inner ℝ zQ'.1 zD.1 = 0 := by simpa using hcross
    rw [hcross']
    ring
  have hsumLower :
      b ^ 2 - a ^ 2 ≤ ‖zQ'.1‖ ^ 2 + ‖y.1‖ ^ 2 := by
    nlinarith [hdecompNorm, hactive', hrest']
  have hcomponentSq :
      (ε * Real.sqrt ((b ^ 2 - a ^ 2) / 2)) ^ 2 ≤
        ‖P.project Q' zQ.1‖ ^ 2 := by
    have hsqrt : Real.sqrt ((b ^ 2 - a ^ 2) / 2) ^ 2 =
        (b ^ 2 - a ^ 2) / 2 :=
      Real.sq_sqrt (by positivity)
    by_cases hySmall : ‖y.1‖ ^ 2 ≤ (b ^ 2 - a ^ 2) / 2
    · have hzQ'large : (b ^ 2 - a ^ 2) / 2 ≤ ‖zQ'.1‖ ^ 2 := by
        nlinarith [hsumLower]
      rw [mul_pow, hsqrt, hprojectNorm]
      have hεsq : ε ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ‖P.project Q' y.1‖]
    · have hyLarge : (b ^ 2 - a ^ 2) / 2 < ‖y.1‖ ^ 2 := lt_of_not_ge hySmall
      have hresSq : ε ^ 2 * ‖y.1‖ ^ 2 ≤ ‖P.project Q' y.1‖ ^ 2 := by
        calc
          ε ^ 2 * ‖y.1‖ ^ 2 = (ε * ‖y.1‖) ^ 2 := by ring
          _ ≤ ‖P.project Q' y.1‖ ^ 2 :=
            (sq_le_sq₀ (mul_nonneg hε.le (norm_nonneg _))
              (norm_nonneg _)).mpr (hres y.1 hyres)
      rw [mul_pow, hsqrt, hprojectNorm]
      nlinarith [hresSq, hyLarge, sq_nonneg ‖zQ'.1‖]
  have htargetNonneg : 0 ≤ ε * Real.sqrt ((b ^ 2 - a ^ 2) / 2) :=
    mul_nonneg hε.le (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ htargetNonneg (norm_nonneg _)).mp hcomponentSq

/-- Orthogonal projection within `H` onto its vectors supported on the linkage subset `Q`.
Unlike the ambient coordinate masks, these projections preserve an arbitrary `H`. -/
noncomputable def borosWithinSubspaceProjectionFamily [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E) :
    BorosSubsetIndex I → H →L[ℝ] H := fun Q =>
      (borosLinkageSliceWithin P H Q.1).starProjection

/-- The projection for the full set of linkage blocks is the identity on `H`. -/
theorem borosWithinSubspaceProjectionFamily_univ [FiniteDimensional ℝ E] [Nonempty I]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E) :
    borosWithinSubspaceProjectionFamily P H
        (⟨Finset.univ, by simp⟩ : BorosSubsetIndex I) =
      ContinuousLinearMap.id ℝ H := by
  have hslice : borosLinkageSliceWithin P H Finset.univ = ⊤ := by
    ext x
    simp [borosLinkageSliceWithin, borosLinkageSlice,
      BorosBlockProjectionSystem.supported, P.project_empty]
  simpa [borosWithinSubspaceProjectionFamily, hslice] using
    (Submodule.starProjection_top : (⊤ : Submodule ℝ H).starProjection =
      ContinuousLinearMap.id ℝ H)

/-- The Boros nested domain formed from the orthogonal projections internal to an arbitrary
subspace `H`. -/
noncomputable def borosWithinSubspaceNestedDomain [FiniteDimensional ℝ E]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E)
    (r : ℕ → ℝ) : Set H :=
  projectionConstraintSet (borosWithinSubspaceProjectionFamily P H) (borosProjectionRadius r)

/-- The arbitrary-subspace Boros nested domain is nonempty, convex, and compact. -/
theorem borosWithinSubspaceNestedDomain_compactConvex_nonempty
    [FiniteDimensional ℝ E] [Nonempty I]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E)
    (r : ℕ → ℝ) :
    (borosWithinSubspaceNestedDomain P H r).Nonempty ∧
      Convex ℝ (borosWithinSubspaceNestedDomain P H r) ∧
      IsCompact (borosWithinSubspaceNestedDomain P H r) := by
  let T := borosWithinSubspaceProjectionFamily P H
  let qtop : BorosSubsetIndex I := ⟨Finset.univ, by simp⟩
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · exact zero_mem_projectionConstraintSet T (borosProjectionRadius r)
      (borosProjectionRadius_nonneg r)
  · exact convex_projectionConstraintSet T (borosProjectionRadius r)
  · exact isCompact_projectionConstraintSet_of_identity T (borosProjectionRadius r)
      qtop (borosWithinSubspaceProjectionFamily_univ P H)

/-- A strict inward estimate at every active face gives a zero for a continuous field on the
arbitrary-subspace Boros domain. The indexed maps are orthogonal projections onto `H_Q`. -/
theorem borosWithinSubspaceNestedDomain_exists_zero_of_strict_inward
    [FiniteDimensional ℝ E] [Nonempty I]
    (P : BorosBlockProjectionSystem (I := I) (E := E)) (H : Submodule ℝ E)
    (r : ℕ → ℝ) (v : H → H)
    (hv : ContinuousOn v (borosWithinSubspaceNestedDomain P H r))
    (hinward : ∀ x ∈ borosWithinSubspaceNestedDomain P H r,
      ∀ Q : BorosSubsetIndex I,
        ‖borosWithinSubspaceProjectionFamily P H Q x‖ = borosProjectionRadius r Q →
        0 < inner ℝ (v x) (borosWithinSubspaceProjectionFamily P H Q x)) :
    ∃ x ∈ borosWithinSubspaceNestedDomain P H r, v x = 0 := by
  let T := borosWithinSubspaceProjectionFamily P H
  obtain ⟨hne, hconv, hcomp⟩ := borosWithinSubspaceNestedDomain_compactConvex_nonempty P H r
  obtain ⟨x, hx, hvi⟩ := exists_variational_inequality_point_finiteDimensional
    hne hconv hcomp v hv
  have hpair (Q : BorosSubsetIndex I) :
      inner ℝ (T Q (v x)) (T Q x) = inner ℝ (v x) (T Q x) := by
    let U := borosLinkageSliceWithin P H Q.1
    calc
      inner ℝ (T Q (v x)) (T Q x) = inner ℝ (v x) (T Q (T Q x)) :=
        U.inner_starProjection_left_eq_right (v x) (T Q x)
      _ = inner ℝ (v x) (T Q x) := by
        have hmem : T Q x ∈ U := U.starProjection_apply_mem x
        have hfix : T Q (T Q x) = T Q x := by
          exact U.starProjection_eq_self_iff.mpr hmem
        rw [hfix]
  have hstrict : ∀ Q : BorosSubsetIndex I,
      ‖T Q x‖ = borosProjectionRadius r Q →
        0 < inner ℝ (T Q (v x)) (T Q x) := by
    intro Q hbound
    rw [hpair Q]
    exact hinward x hx Q hbound
  refine ⟨x, hx, ?_⟩
  exact variational_eq_zero_of_active_inward_projectionConstraints
    T (borosProjectionRadius r) hx hvi hstrict

end

end CRNT.Analysis
