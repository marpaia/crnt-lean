import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import CRNT.Geometry.FiniteConeClosed

/-!
# Binary codes for dimensions along a projection chain

Section 7.2 of Craciun's construction assigns a bit to each one-coordinate projection: the bit is
`1` exactly when that projection lowers the face dimension by one. This file isolates the finite
combinatorics of that encoding and the fiber geometry it records. A `FaceProjectionDimensionProfile`
records the dimensions along the projection chain and the required zero-or-one step bound; its code
has one bit per projection, and the number of `1` bits recovers the final face dimension. For an
exactly projected affine-face chain, a `1` means the face contains the deleted-coordinate direction,
while a `0` makes projection bijective on the face. `CoordinateProjectedConeChain.ofFiniteGenerators`
constructs such a projection chain from a finitely generated cone with a nonempty normalized section.
Choosing and gluing cells so these chains respect a fan subdivision remains a separate obligation.
-/

namespace CRNT
namespace ZeroSeparatingInduction

/-- Projection from an `(n + 1)`-coordinate space to its first `n` coordinates. -/
def forgetLastCoordinate (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i.castSucc
  map_add' x y := by funext i; rfl
  map_smul' c x := by funext i; rfl

/-- The coordinate projection is onto: append zero to any target tuple. -/
theorem forgetLastCoordinate_surjective (n : ℕ) :
    Function.Surjective (forgetLastCoordinate n) := by
  intro x
  refine ⟨Fin.snoc x 0, ?_⟩
  funext i
  simp [forgetLastCoordinate]

/-- The final-coordinate projection on Euclidean spaces, transported through the canonical
`PiLp`/function linear equivalences. -/
noncomputable def forgetLastEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  let targetEquiv := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  let f := targetEquiv.symm.toLinearMap.comp
    ((forgetLastCoordinate n).comp sourceEquiv.toLinearMap)
  exact ⟨f, f.continuous_of_finiteDimensional⟩

/-- The Euclidean final-coordinate projection is surjective. -/
theorem forgetLastEuclidean_surjective (n : ℕ) :
    Function.Surjective (forgetLastEuclidean n) := by
  let sourceEquiv := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  let targetEquiv := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  intro y
  obtain ⟨x, hx⟩ := forgetLastCoordinate_surjective n (targetEquiv y)
  refine ⟨sourceEquiv.symm x, ?_⟩
  change targetEquiv.symm (forgetLastCoordinate n (sourceEquiv (sourceEquiv.symm x))) = y
  rw [sourceEquiv.apply_symm_apply, hx, targetEquiv.symm_apply_apply]

/-- The affine map underlying `forgetLastCoordinate`. -/
def forgetLastAffine (n : ℕ) :
    (Fin (n + 1) → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
  AffineMap.mk' (forgetLastCoordinate n) (forgetLastCoordinate n) 0 (by
    intro x
    funext i
    simp [forgetLastCoordinate])

/-- The section of the homogenizing hyperplane `x₀ = 1`, identified with the affine space of the
remaining coordinates. -/
def homogeneousLift (n : ℕ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 1 x

/-- The affine chart embedding is injective. -/
theorem homogeneousLift_injective (n : ℕ) : Function.Injective (homogeneousLift n) := by
  intro x y h
  funext i
  have hi := congrFun h i.succ
  simpa [homogeneousLift] using hi

/-- Coordinate projection commutes with taking the normalized section of a projected cone. -/
theorem forgetLastCoordinate_homogeneousLift (n : ℕ) (x : Fin (n + 1) → ℝ) :
    forgetLastCoordinate (n + 1) (homogeneousLift (n + 1) x) =
      homogeneousLift n (forgetLastCoordinate n x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [forgetLastCoordinate, homogeneousLift]
  ·
    have hi : (j.succ).castSucc = (j.castSucc).succ := by
      apply Fin.ext
      simp
    simp [forgetLastCoordinate, homogeneousLift, hi]

/-- The affine face cut out of a cone by the homogenizing hyperplane `x₀ = 1`. -/
def normalizedConeSection {n : ℕ} (C : Set (Fin (n + 1) → ℝ)) : Set (Fin n → ℝ) :=
  {x | homogeneousLift n x ∈ C}

/-- Slicing a cone by `x₀ = 1` commutes with deleting the last coordinate. -/
theorem forgetLastAffine_image_normalizedConeSection (n : ℕ)
    (C : Set (Fin (n + 2) → ℝ)) :
    forgetLastAffine n '' normalizedConeSection (n := n + 1) C =
      normalizedConeSection (n := n) (forgetLastCoordinate (n + 1) '' C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyC : homogeneousLift (n + 1) y ∈ C := hy
    change homogeneousLift n (forgetLastCoordinate n y) ∈
      forgetLastCoordinate (n + 1) '' C
    rw [← forgetLastCoordinate_homogeneousLift]
    exact Set.mem_image_of_mem (forgetLastCoordinate (n + 1)) hyC
  · intro hx
    change homogeneousLift n x ∈ forgetLastCoordinate (n + 1) '' C at hx
    rcases (Set.mem_image (forgetLastCoordinate (n + 1)) C
      (homogeneousLift n x)).mp hx with ⟨z, hz, hzx⟩
    let y : Fin (n + 1) → ℝ := fun i => z i.succ
    have hz0 : z 0 = 1 := by
      have hzero := congrFun hzx 0
      simpa [forgetLastCoordinate, homogeneousLift] using hzero
    have hyz : homogeneousLift (n + 1) y = z := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [homogeneousLift, y, hz0]
      ·
        rfl
    have hyC : homogeneousLift (n + 1) y ∈ C := by
      rw [hyz]
      exact hz
    have hcoords : forgetLastCoordinate n y = x := by
      apply homogeneousLift_injective n
      calc
        homogeneousLift n (forgetLastCoordinate n y) =
            forgetLastCoordinate (n + 1) (homogeneousLift (n + 1) y) :=
              (forgetLastCoordinate_homogeneousLift n y).symm
        _ = forgetLastCoordinate (n + 1) z := by rw [hyz]
        _ = homogeneousLift n x := hzx
    refine ⟨y, hyC, ?_⟩
    simpa [forgetLastAffine] using hcoords

/-- Dropping one coordinate lowers the dimension of any finite-dimensional subspace by at most
one. The kernel of the restricted projection embeds into the one-dimensional kernel of the ambient
coordinate projection. -/
theorem finrank_map_forgetLastCoordinate_bounds (n : ℕ)
    (U : Submodule ℝ (Fin (n + 1) → ℝ)) :
    Module.finrank ℝ (U.map (forgetLastCoordinate n)) ≤ Module.finrank ℝ U ∧
      Module.finrank ℝ U ≤ Module.finrank ℝ (U.map (forgetLastCoordinate n)) + 1 := by
  constructor
  · exact Submodule.finrank_map_le (forgetLastCoordinate n) U
  · let f := forgetLastCoordinate n
    let g := f.domRestrict U
    have hRank :
        Module.finrank ℝ (U.map f) + Module.finrank ℝ (LinearMap.ker g) =
          Module.finrank ℝ U := by
      have hRank' := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
      rw [LinearMap.range_domRestrict] at hRank'
      simpa [g] using hRank'
    have hMapKer : (LinearMap.ker g).map U.subtype ≤ LinearMap.ker f := by
      intro x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hy' : g y = 0 := hy
      simpa [g, f, LinearMap.domRestrict] using hy'
    have hKer : Module.finrank ℝ (LinearMap.ker g) ≤ 1 := by
      calc
        Module.finrank ℝ (LinearMap.ker g) =
            Module.finrank ℝ ((LinearMap.ker g).map U.subtype) := by
              symm
              exact Submodule.finrank_map_subtype_eq U (LinearMap.ker g)
        _ ≤ Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hMapKer
        _ = 1 := by
          have hRange : Module.finrank ℝ (LinearMap.range f) = n := by
            rw [LinearMap.range_eq_top.mpr (forgetLastCoordinate_surjective n)]
            simp
          have hDomain : Module.finrank ℝ (Fin (n + 1) → ℝ) = n + 1 := by
            simp
          have hRank' := LinearMap.finrank_range_add_finrank_ker f
          rw [hRange, hDomain] at hRank'
          omega
    have hRankFinal :
        Module.finrank ℝ (U.map (forgetLastCoordinate n)) +
          Module.finrank ℝ
            (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) =
          Module.finrank ℝ U := by
      simpa [f, g] using hRank
    have hKerFinal :
        Module.finrank ℝ
          (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) ≤ 1 := by
      simpa [f, g] using hKer
    omega

/-- A coordinate projection loses one dimension from a subspace exactly when its restricted
kernel is nontrivial. In geometric terms, the subspace contains a nonzero direction supported
entirely on the deleted coordinate. -/
theorem finrank_drop_forgetLastCoordinate_iff_kernel_ne_bot (n : ℕ)
    (U : Submodule ℝ (Fin (n + 1) → ℝ)) :
    Module.finrank ℝ U =
        Module.finrank ℝ (U.map (forgetLastCoordinate n)) + 1 ↔
    LinearMap.ker ((forgetLastCoordinate n).domRestrict U) ≠ ⊥ := by
  have hRank :
      Module.finrank ℝ (U.map (forgetLastCoordinate n)) +
          Module.finrank ℝ
            (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) =
        Module.finrank ℝ U := by
    have hRank' :=
      LinearMap.finrank_range_add_finrank_ker ((forgetLastCoordinate n).domRestrict U)
    rw [LinearMap.range_domRestrict] at hRank'
    simpa using hRank'
  have hKerLe :
      Module.finrank ℝ (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) ≤ 1 := by
    rcases finrank_map_forgetLastCoordinate_bounds n U with ⟨_, hUpper⟩
    omega
  constructor
  · intro hdrop
    have hKerEq :
        Module.finrank ℝ (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) = 1 := by
      omega
    intro hbot
    rw [hbot, finrank_bot] at hKerEq
    omega
  · intro hker
    have hKerPos :
        1 ≤ Module.finrank ℝ (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) :=
      Submodule.one_le_finrank_iff.mpr hker
    have hKerEq :
        Module.finrank ℝ (LinearMap.ker ((forgetLastCoordinate n).domRestrict U)) = 1 := by
      omega
    omega

/-- The binary letter for the projection step from `Fin (n + 1)` coordinates to `Fin n`
coordinates. It is `true` exactly when the dimension increases by one in the reverse direction,
equivalently when the projection drops dimension by one. -/
def faceProjectionDimensionLetter {n : ℕ} (dimension : Fin (n + 1) → ℕ) (j : Fin n) : Bool :=
  decide (dimension j.succ = dimension j.castSucc + 1)

/-- The binary word of successive dimension changes, in coordinate order. -/
def faceProjectionDimensionWord : (n : ℕ) → (Fin (n + 1) → ℕ) → List Bool
  | 0, _ => []
  | n + 1, dimension =>
      faceProjectionDimensionWord n (fun j => dimension j.castSucc) ++
        [faceProjectionDimensionLetter dimension (Fin.last n)]

/-- Count the `true` letters in a dimension code. -/
def faceProjectionDimensionWordWeight : List Bool → ℕ
  | [] => 0
  | true :: word => faceProjectionDimensionWordWeight word + 1
  | false :: word => faceProjectionDimensionWordWeight word

@[simp]
theorem faceProjectionDimensionWordWeight_append_singleton (word : List Bool) (bit : Bool) :
    faceProjectionDimensionWordWeight (word ++ [bit]) =
      faceProjectionDimensionWordWeight word + (if bit then 1 else 0) := by
  induction word with
  | nil => cases bit <;> rfl
  | cons head tail ih =>
      cases head
      · simp only [List.cons_append, faceProjectionDimensionWordWeight]
        exact ih
      · simp only [List.cons_append, faceProjectionDimensionWordWeight]
        rw [ih]
        omega

/-- A profile of the dimensions of one face under successive coordinate projections. The
`dimension_zero` field records that the terminal projection lands in a point, and `step` expresses
the fact that deleting one coordinate either preserves dimension or lowers it by one. -/
structure FaceProjectionDimensionProfile (n : ℕ) where
  dimension : Fin (n + 1) → ℕ
  dimension_zero : dimension 0 = 0
  step : ∀ j : Fin n,
    dimension j.castSucc ≤ dimension j.succ ∧
      dimension j.succ ≤ dimension j.castSucc + 1

/-- A chain of direction spaces for the affine hulls of successively projected faces. For a
projected subdivision face chain, these spaces are the directions of its affine hulls, and each
stage projects onto the preceding stage. -/
structure CoordinateProjectionSubspaceChain (n : ℕ) where
  subspace : (j : Fin (n + 1)) → Submodule ℝ (Fin j.val → ℝ)
  projectedSubspace : ∀ j : Fin n,
    (subspace j.succ).map (forgetLastCoordinate j.val) = subspace j.castSucc

/-- A chain of nonempty affine faces, each the coordinate projection of the next face. -/
structure CoordinateProjectedFaceChain (n : ℕ) where
  face : (j : Fin (n + 1)) → Set (Fin j.val → ℝ)
  face_nonempty : ∀ j, (face j).Nonempty
  projectedFace : ∀ j : Fin n,
    forgetLastAffine j.val '' face j.succ = face j.castSucc

/-- A chain of cones in homogeneous coordinate spaces, where each cone projects onto the
preceding cone and each normalized section is nonempty. -/
structure CoordinateProjectedConeChain (n : ℕ) where
  cone : (j : Fin (n + 1)) → Set (Fin (j.val + 1) → ℝ)
  projectedCone : ∀ j : Fin n,
    forgetLastCoordinate (j.val + 1) '' cone j.succ = cone j.castSucc
  section_nonempty : ∀ j, (normalizedConeSection (cone j)).Nonempty

/-- Project a tuple in `n + 1` coordinates onto its first `m + 1` coordinates. -/
def coordinatePrefixMap (m n : ℕ) (hmn : m ≤ n) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun x i := x (i.castLE (Nat.succ_le_succ hmn))
  map_add' x y := by funext i; rfl
  map_smul' c x := by funext i; rfl

@[simp] theorem coordinatePrefixMap_self (n : ℕ) :
    coordinatePrefixMap n n le_rfl = LinearMap.id := by
  ext x i
  rfl

/-- Finite generators project compatibly with the coordinate-prefix maps. -/
noncomputable def finiteProjectedConeGenerators {n : ℕ}
    (S : Finset (Fin (n + 1) → ℝ)) (j : Fin (n + 1)) :
    Finset (Fin (j.val + 1) → ℝ) := by
  classical
  exact S.image (coordinatePrefixMap j.val n (Nat.le_of_lt_succ j.isLt))

/-- The image of a finitely generated cone under a linear map is the cone generated by the
images of its finite generators. This gives exact images; no closure is added. -/
theorem linearMap_image_hull_eq_hull_image
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (S : Set E) :
    f '' (PointedCone.hull ℝ S : Set E) = PointedCone.hull ℝ (f '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := Submodule.image_span_subset_span (f.restrictScalars (Nonneg ℝ)) S
      ⟨x, hx, rfl⟩
    exact h
  · intro hy
    have hy' : y ∈ (Submodule.span (Nonneg ℝ) S).map
        (f.restrictScalars (Nonneg ℝ)) := by
      rw [Submodule.map_span]
      exact hy
    rcases Submodule.mem_map.mp hy' with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

/-- A finitely generated cone has an exact closed-cone image under a linear map. -/
theorem linearMap_image_properConeOfFinset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
    (f : E →ₗ[ℝ] F) (S : Finset E) :
    f '' (properConeOfFinset S : Set E) =
      (properConeOfFinset (S.image f) : Set F) := by
  rw [coe_properConeOfFinset, coe_properConeOfFinset]
  simpa only [Finset.coe_image] using linearMap_image_hull_eq_hull_image f (S : Set E)

/-- Deleting the final coordinate after a prefix projection is the shorter prefix projection. -/
theorem forgetLast_comp_coordinatePrefixMap {m n : ℕ} (hmn : m + 1 ≤ n) :
    (forgetLastCoordinate (m + 1)).comp (coordinatePrefixMap (m + 1) n hmn) =
      coordinatePrefixMap m n (Nat.le_trans (Nat.le_succ m) hmn) := by
  ext x i
  rfl

/-- The finite generator set at a projection stage is exactly the projection of the next set. -/
theorem finiteProjectedConeGenerators_projected {n : ℕ}
    (S : Finset (Fin (n + 1) → ℝ)) (j : Fin n) :
    (finiteProjectedConeGenerators S j.succ).image (forgetLastCoordinate (j.val + 1)) =
      finiteProjectedConeGenerators S j.castSucc := by
  classical
  simp only [finiteProjectedConeGenerators, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  ext i
  rfl

/-- Build the complete coordinate-projection chain of a finite-generated cone from one point in
its normalized section. Every lower cone is generated by the projected finite generators, so the
projection equalities are exact and every section remains nonempty. -/
noncomputable def CoordinateProjectedConeChain.ofFiniteGenerators {n : ℕ}
    (S : Finset (Fin (n + 1) → ℝ)) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ (properConeOfFinset S : Set (Fin (n + 1) → ℝ))) (hz0 : z 0 = 1) :
    CoordinateProjectedConeChain n := by
  classical
  let generators := finiteProjectedConeGenerators S
  let cone (j : Fin (n + 1)) : Set (Fin (j.val + 1) → ℝ) :=
    properConeOfFinset (generators j)
  refine ⟨cone, ?_, ?_⟩
  · intro j
    have hmap := linearMap_image_properConeOfFinset
      (forgetLastCoordinate (j.val + 1)) (generators j.succ)
    have hgens :
        (generators j.succ).image (forgetLastCoordinate (j.val + 1)) =
          generators j.castSucc := by
      simpa [generators] using finiteProjectedConeGenerators_projected S j
    have hcones := congrArg
      (fun T : Finset (Fin (j.val + 1) → ℝ) =>
        (properConeOfFinset T : Set (Fin (j.val + 1) → ℝ))) hgens
    simpa only [cone, Fin.val_succ, Fin.val_castSucc] using
      hmap.trans hcones
  · intro j
    let projMap := coordinatePrefixMap j.val n (Nat.le_of_lt_succ j.isLt)
    let w := projMap z
    have hw : w ∈ (properConeOfFinset (generators j) : Set (Fin (j.val + 1) → ℝ)) := by
      have himage : w ∈ projMap '' (properConeOfFinset S : Set (Fin (n + 1) → ℝ)) :=
        ⟨z, hz, rfl⟩
      rw [linearMap_image_properConeOfFinset] at himage
      simpa [generators, finiteProjectedConeGenerators, projMap] using himage
    have hw0 : w 0 = 1 := by
      simpa [w, projMap, coordinatePrefixMap] using hz0
    let x : Fin j.val → ℝ := fun i => w i.succ
    have hx : homogeneousLift j.val x = w := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [homogeneousLift, x] using hw0.symm
      · simp [homogeneousLift, x]
    refine ⟨x, ?_⟩
    change homogeneousLift j.val x ∈ cone j
    rw [hx]
    exact hw

/-- Each cone in the finite-generated chain is the literal prefix projection of the supplied top
cone. -/
theorem CoordinateProjectedConeChain.ofFiniteGenerators_cone_eq_projection {n : ℕ}
    (S : Finset (Fin (n + 1) → ℝ)) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ (properConeOfFinset S : Set (Fin (n + 1) → ℝ))) (hz0 : z 0 = 1)
    (j : Fin (n + 1)) :
    (CoordinateProjectedConeChain.ofFiniteGenerators S z hz hz0).cone j =
      coordinatePrefixMap j.val n (Nat.le_of_lt_succ j.isLt) ''
        (properConeOfFinset S : Set (Fin (n + 1) → ℝ)) := by
  classical
  change (properConeOfFinset (finiteProjectedConeGenerators S j) :
      Set (Fin (j.val + 1) → ℝ)) = _
  simpa only [finiteProjectedConeGenerators] using
    (linearMap_image_properConeOfFinset
      (coordinatePrefixMap j.val n (Nat.le_of_lt_succ j.isLt)) S).symm

/-- The terminal cone of the constructed chain is exactly the input finite-generated cone. -/
@[simp] theorem CoordinateProjectedConeChain.ofFiniteGenerators_last_cone {n : ℕ}
    (S : Finset (Fin (n + 1) → ℝ)) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ (properConeOfFinset S : Set (Fin (n + 1) → ℝ))) (hz0 : z 0 = 1) :
    (CoordinateProjectedConeChain.ofFiniteGenerators S z hz hz0).cone (Fin.last n) =
      (properConeOfFinset S : Set (Fin (n + 1) → ℝ)) := by
  have h := CoordinateProjectedConeChain.ofFiniteGenerators_cone_eq_projection
    S z hz hz0 (Fin.last n)
  simpa [coordinatePrefixMap_self] using h

/-- Normalized sections of an exactly projected cone chain form a projected affine-face chain. -/
def CoordinateProjectedConeChain.toFaceChain {n : ℕ}
    (chain : CoordinateProjectedConeChain n) : CoordinateProjectedFaceChain n := by
  refine ⟨fun j => normalizedConeSection (chain.cone j), chain.section_nonempty, ?_⟩
  intro j
  have h := forgetLastAffine_image_normalizedConeSection j.val (chain.cone j.succ)
  rw [chain.projectedCone j] at h
  exact h

/-- The finranks along a coordinate-projection subspace chain form a valid face-dimension profile.
The coordinate projection rank bound proves each dimension step is zero or one. -/
noncomputable def CoordinateProjectionSubspaceChain.dimensionProfile {n : ℕ}
    (chain : CoordinateProjectionSubspaceChain n) : FaceProjectionDimensionProfile n := by
  refine ⟨fun j => Module.finrank ℝ (chain.subspace j), ?_, ?_⟩
  · have hle := Submodule.finrank_le (chain.subspace (0 : Fin (n + 1)))
    change Module.finrank ℝ (chain.subspace (0 : Fin (n + 1))) ≤
      Module.finrank ℝ (Fin 0 → ℝ) at hle
    have hdim : Module.finrank ℝ (Fin 0 → ℝ) = 0 := by simp
    rw [hdim] at hle
    omega
  · intro j
    have hstep :=
      finrank_map_forgetLastCoordinate_bounds j.val (chain.subspace j.succ)
    rw [chain.projectedSubspace j] at hstep
    exact hstep

/-- Taking affine-hull directions sends an exactly projected face chain to a
`CoordinateProjectionSubspaceChain`. -/
noncomputable def CoordinateProjectedFaceChain.toDirectionSubspaceChain {n : ℕ}
    (chain : CoordinateProjectedFaceChain n) : CoordinateProjectionSubspaceChain n := by
  refine ⟨fun j => (affineSpan ℝ (chain.face j)).direction, ?_⟩
  intro j
  have hface :
      (affineSpan ℝ (chain.face j.succ)).map (forgetLastAffine j.val) =
        affineSpan ℝ (chain.face j.castSucc) := by
    rw [AffineSubspace.map_span, chain.projectedFace j]
  have hdirection := congrArg AffineSubspace.direction hface
  simpa [AffineSubspace.map_direction, forgetLastAffine] using hdirection

/-- The face word has one letter for each projection. -/
theorem faceProjectionDimensionWord_length {n : ℕ}
    (dimension : Fin (n + 1) → ℕ) :
    (faceProjectionDimensionWord n dimension).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [faceProjectionDimensionWord, ih]

/-- The number of `1` bits in the projection word is the dimension of the original face. -/
theorem FaceProjectionDimensionProfile.dimension_eq_wordWeight {n : ℕ}
    (profile : FaceProjectionDimensionProfile n) :
    profile.dimension (Fin.last n) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n profile.dimension) := by
  induction n with
  | zero =>
      simp [faceProjectionDimensionWord, faceProjectionDimensionWordWeight,
        profile.dimension_zero]
  | succ n ih =>
      let initial : FaceProjectionDimensionProfile n :=
        { dimension := fun j => profile.dimension j.castSucc
          dimension_zero := by simpa using profile.dimension_zero
          step := by
            intro j
            simpa using profile.step j.castSucc }
      have hprefix := ih initial
      have hprefix' :
          profile.dimension (Fin.castSucc (Fin.last n)) =
            faceProjectionDimensionWordWeight
              (faceProjectionDimensionWord n
                (fun j => profile.dimension j.castSucc)) := by
        simpa [initial] using hprefix
      let prev := profile.dimension (Fin.castSucc (Fin.last n))
      let next := profile.dimension (Fin.last (n + 1))
      let bit := decide (next = prev + 1)
      have hstepCases : next = prev ∨ next = prev + 1 := by
        rcases profile.step (Fin.last n) with ⟨hlo, hhi⟩
        have hlo' : prev ≤ next := by
          simpa [prev, next, Fin.succ_last] using hlo
        have hhi' : next ≤ prev + 1 := by
          simpa [prev, next, Fin.succ_last] using hhi
        omega
      have hnext : next = prev + (if bit then 1 else 0) := by
        rcases hstepCases with hEq | hSucc
        · simp [bit, hEq]
        · simp [bit, hSucc]
      have hword :
          faceProjectionDimensionWord (n + 1) profile.dimension =
            faceProjectionDimensionWord n (fun j => profile.dimension j.castSucc) ++ [bit] := by
        simp [faceProjectionDimensionWord, faceProjectionDimensionLetter, bit, prev, next]
      rw [hword, faceProjectionDimensionWordWeight_append_singleton, ← hprefix']
      simpa [next, prev] using hnext

/-- For a coordinate-projected subspace chain, the binary word of dimension drops has one `1` for
each dimension gained from the zero-dimensional base. -/
theorem CoordinateProjectionSubspaceChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectionSubspaceChain n) :
    Module.finrank ℝ (chain.subspace (Fin.last n)) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n (fun j => Module.finrank ℝ (chain.subspace j))) := by
  exact chain.dimensionProfile.dimension_eq_wordWeight

/-- The direction of the deleted coordinate in the ambient projection space. -/
def lastProjectionDirection (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.lastCases 1 (fun _ : Fin n => 0)

@[simp] theorem lastProjectionDirection_last (n : ℕ) :
    lastProjectionDirection n (Fin.last n) = 1 := by
  simp [lastProjectionDirection]

@[simp] theorem lastProjectionDirection_castSucc (n : ℕ) (i : Fin n) :
    lastProjectionDirection n i.castSucc = 0 := by
  simp [lastProjectionDirection]

/-- A face direction space contains the vertical projection direction exactly when its restricted
projection has a nontrivial kernel. Since the ambient projection forgets one coordinate, every
kernel vector is a scalar multiple of `lastProjectionDirection`. -/
theorem lastProjectionDirection_mem_iff_restrictedKernel_ne_bot (n : ℕ)
    (U : Submodule ℝ (Fin (n + 1) → ℝ)) :
    lastProjectionDirection n ∈ U ↔
      LinearMap.ker ((forgetLastCoordinate n).domRestrict U) ≠ ⊥ := by
  classical
  let f := forgetLastCoordinate n
  let g := f.domRestrict U
  constructor
  · intro hU hbot
    have hv : (⟨lastProjectionDirection n, hU⟩ : U) ∈ LinearMap.ker g := by
      apply LinearMap.mem_ker.mpr
      change f (lastProjectionDirection n) = 0
      funext i
      simp [f, forgetLastCoordinate, lastProjectionDirection]
    have hvzero : (⟨lastProjectionDirection n, hU⟩ : U) = 0 := by
      rw [hbot, Submodule.mem_bot] at hv
      exact hv
    have hval := congrArg Subtype.val hvzero
    have hne : lastProjectionDirection n ≠ 0 := by
      intro h
      have hlast := congrFun h (Fin.last n)
      simp [lastProjectionDirection] at hlast
    exact hne hval
  · intro hker
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hzero : (forgetLastCoordinate n) (v : Fin (n + 1) → ℝ) = 0 := by
      exact LinearMap.mem_ker.mp hv
    have hcoord : ∀ i : Fin n, (v : Fin (n + 1) → ℝ) i.castSucc = 0 := by
      intro i
      have hi := congrFun hzero i
      simpa [forgetLastCoordinate] using hi
    have hrepr : (v : Fin (n + 1) → ℝ) =
        (v : Fin (n + 1) → ℝ) (Fin.last n) • lastProjectionDirection n := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastProjectionDirection]
      · simp [lastProjectionDirection, hcoord j]
    have hlast : (v : Fin (n + 1) → ℝ) (Fin.last n) ≠ 0 := by
      intro hz
      apply hvne
      apply Subtype.ext
      rw [hrepr, hz]
      simp
    have hdir : lastProjectionDirection n =
        ((v : Fin (n + 1) → ℝ) (Fin.last n))⁻¹ • (v : Fin (n + 1) → ℝ) := by
      rw [hrepr]
      simp [hlast]
    rw [hdir]
    exact U.smul_mem _ v.property

/-- A `1` in the projection-dimension code records that the face's direction space contains the
deleted-coordinate direction. This connects the binary blueprint label to the ruling direction of
the corresponding projection fiber. -/
theorem CoordinateProjectionSubspaceChain.dimensionLetter_true_iff_lastDirection_mem
    {n : ℕ} (chain : CoordinateProjectionSubspaceChain n) (j : Fin n) :
    faceProjectionDimensionLetter
        (fun k => Module.finrank ℝ (chain.subspace k)) j = true ↔
      lastProjectionDirection j.val ∈ chain.subspace j.succ := by
  simp only [faceProjectionDimensionLetter, decide_eq_true_eq]
  rw [← chain.projectedSubspace j]
  exact (finrank_drop_forgetLastCoordinate_iff_kernel_ne_bot j.val
      (chain.subspace j.succ)).trans
    (lastProjectionDirection_mem_iff_restrictedKernel_ne_bot j.val
      (chain.subspace j.succ)).symm

/-- For an actual chain of projected affine faces, the dimension-code letter is `1` exactly when
the face contains the full direction of that coordinate-projection fiber. -/
theorem CoordinateProjectedFaceChain.dimensionLetter_true_iff_lastDirection_mem
    {n : ℕ} (chain : CoordinateProjectedFaceChain n) (j : Fin n) :
    faceProjectionDimensionLetter
        (fun k => Module.finrank ℝ ((affineSpan ℝ (chain.face k)).direction)) j = true ↔
      lastProjectionDirection j.val ∈
        (affineSpan ℝ (chain.face j.succ)).direction :=
  chain.toDirectionSubspaceChain.dimensionLetter_true_iff_lastDirection_mem j

/-- If a face's projection bit is `0`, then projection is a bijection from that face to its
projected face. The `1` case records a vertical ruling; this complementary `0` case says the face is
the graph of a single-valued lift over its projection. This is the branch used to define the
transversely thickened neighborhoods in the inductive pre-blueprint construction. -/
noncomputable def CoordinateProjectedFaceChain.projectionEquiv_of_dimensionLetter_false
    {n : ℕ} (chain : CoordinateProjectedFaceChain n) (j : Fin n)
    (hbit : faceProjectionDimensionLetter
      (fun k => Module.finrank ℝ ((affineSpan ℝ (chain.face k)).direction)) j = false) :
    {x // x ∈ chain.face j.succ} ≃ {y // y ∈ chain.face j.castSucc} := by
  let U := (affineSpan ℝ (chain.face j.succ)).direction
  let proj : {x // x ∈ chain.face j.succ} → {y // y ∈ chain.face j.castSucc} := fun x =>
    ⟨forgetLastAffine j.val x.1, by
      have hx := Set.mem_image_of_mem (forgetLastAffine j.val) x.2
      rw [chain.projectedFace j] at hx
      exact hx⟩
  apply Equiv.ofBijective proj
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hproj : forgetLastAffine j.val x.1 = forgetLastAffine j.val y.1 :=
      congrArg Subtype.val hxy
    have hcoord : ∀ i : Fin j.val, x.1 i.castSucc = y.1 i.castSucc := by
      intro i
      have hi := congrFun hproj i
      simpa [forgetLastAffine, forgetLastCoordinate] using hi
    have hvdir : x.1 - y.1 ∈ U := by
      have hmem :=
        (AffineSubspace.vsub_right_mem_direction_iff_mem
          (mem_affineSpan ℝ y.2) x.1).2 (mem_affineSpan ℝ x.2)
      simpa [U, vsub_eq_sub] using hmem
    have hrepr : x.1 - y.1 =
        (x.1 - y.1) (Fin.last j.val) • lastProjectionDirection j.val := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [lastProjectionDirection]
      · simp [lastProjectionDirection, hcoord k]
    by_cases hlast : (x.1 - y.1) (Fin.last j.val) = 0
    · have hzero : x.1 - y.1 = 0 := by rw [hrepr, hlast]; simp
      exact sub_eq_zero.mp hzero
    · have hvert : lastProjectionDirection j.val =
          ((x.1 - y.1) (Fin.last j.val))⁻¹ • (x.1 - y.1) := by
        rw [hrepr]
        have hlast' : x.1 (Fin.last j.val) - y.1 (Fin.last j.val) ≠ 0 := by
          simpa using hlast
        simp [hlast']
      have hvertical : lastProjectionDirection j.val ∈ U := by
        rw [hvert]
        exact U.smul_mem _ hvdir
      have htrue :=
        (chain.dimensionLetter_true_iff_lastDirection_mem j).2 hvertical
      rw [hbit] at htrue
      cases htrue
  · intro y
    have hy : y.1 ∈ forgetLastAffine j.val '' chain.face j.succ := by
      rw [chain.projectedFace j]
      exact y.2
    rcases (Set.mem_image (forgetLastAffine j.val) (chain.face j.succ) y.1).mp hy with
      ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- The equivalence from the zero-bit case is the actual coordinate projection, with the subtype
proof only certifying that the result belongs to the projected face. -/
@[simp] theorem CoordinateProjectedFaceChain.projectionEquiv_of_dimensionLetter_false_apply
    {n : ℕ} (chain : CoordinateProjectedFaceChain n) (j : Fin n)
    (hbit : faceProjectionDimensionLetter
      (fun k => Module.finrank ℝ ((affineSpan ℝ (chain.face k)).direction)) j = false)
    (x : {x // x ∈ chain.face j.succ}) :
    (chain.projectionEquiv_of_dimensionLetter_false j hbit x).1 =
      forgetLastAffine j.val x.1 := rfl

/-- The dimension word of an exactly projected affine-face chain records its affine-hull
dimensions, with one `1` for every dimension gained above the point projection. -/
theorem CoordinateProjectedFaceChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectedFaceChain n) :
    Module.finrank ℝ ((affineSpan ℝ (chain.face (Fin.last n))).direction) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n
          (fun j => Module.finrank ℝ ((affineSpan ℝ (chain.face j)).direction))) := by
  exact chain.toDirectionSubspaceChain.dimension_eq_wordWeight

/-- The dimension code of a normalized cone chain counts the affine-hull dimension of its final
section. -/
theorem CoordinateProjectedConeChain.dimension_eq_wordWeight {n : ℕ}
    (chain : CoordinateProjectedConeChain n) :
    Module.finrank ℝ
        ((affineSpan ℝ (normalizedConeSection (chain.cone (Fin.last n)))).direction) =
      faceProjectionDimensionWordWeight
        (faceProjectionDimensionWord n
          (fun j => Module.finrank ℝ
            ((affineSpan ℝ (normalizedConeSection (chain.cone j))).direction))) := by
  exact chain.toFaceChain.dimension_eq_wordWeight

end ZeroSeparatingInduction
end CRNT
