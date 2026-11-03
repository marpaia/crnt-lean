import CRNT.Equilibria.TreeConstants
import CRNT.Deficiency.KernelDimensionWR
import CRNT.Deficiency.PerClassKernelUnique

/-!
# Tree constants as the canonical kinetic-kernel basis

For a weakly reversible mass-action network, the kinetic Laplacian has one kernel
ray per linkage class.  The directed Matrix--Tree theorem supplies a canonical
strictly positive generator of each ray: the vector of tree constants restricted
to that class.

This file packages the usual CRNT statement

  ker A_k = span { K^θ : θ a linkage class },

where `K^θ` is the tree-constant vector on linkage class `θ` and zero elsewhere.
It also records the corresponding positive-cone statement used throughout
complex-balance theory.
-/

namespace CRNT
namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Tree constants restricted to one linkage class. -/
noncomputable def classTreeVector (N : Network S) (κ : N.RateConstants)
    (θ : Quotient N.linkedSetoid) : N.ComplexIdx → ℝ :=
  fun c => if N.classOf c = θ then N.treeConstant κ c else 0

@[simp] theorem classTreeVector_apply_of_mem (N : Network S) (κ : N.RateConstants)
    (θ : Quotient N.linkedSetoid) (c : N.ComplexIdx) (hc : N.classOf c = θ) :
    N.classTreeVector κ θ c = N.treeConstant κ c := by
  simp [classTreeVector, hc]

@[simp] theorem classTreeVector_apply_of_not_mem (N : Network S) (κ : N.RateConstants)
    (θ : Quotient N.linkedSetoid) (c : N.ComplexIdx) (hc : N.classOf c ≠ θ) :
    N.classTreeVector κ θ c = 0 := by
  simp [classTreeVector, hc]

/-- The global tree vector is the sum of the linkage-class tree vectors. -/
theorem treeConstantVector_eq_sum_classTreeVector (N : Network S) (κ : N.RateConstants) :
    N.treeConstantVector κ = ∑ θ : Quotient N.linkedSetoid, N.classTreeVector κ θ := by
  classical
  funext c
  simp [treeConstantVector, classTreeVector]

/-- Kinetic Laplacian preserves linkage-class support. -/
theorem kineticMap_restrict_classTreeVector (N : Network S) (κ : N.RateConstants)
    (θ : Quotient N.linkedSetoid) :
    N.kineticMap κ (N.classTreeVector κ θ) = 0 := by
  have hclass : N.classTreeVector κ θ =
      N.restrictToClass θ (N.treeConstantVector κ) := by
    funext c
    by_cases hc : N.classOf c = θ
    · simp [classTreeVector, hc, treeConstantVector]
    · simp [classTreeVector, hc]
  rw [hclass, N.kineticMap_restrictToClass κ, N.treeConstant_kineticKernel κ]
  funext c
  simp [restrictToClass]

/-- On a weakly reversible network the class tree vector is strictly positive
on its linkage class and vanishes elsewhere. -/
theorem classTreeVector_positive_on_class (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (θ : Quotient N.linkedSetoid) :
    (∀ c, N.classOf c = θ → 0 < N.classTreeVector κ θ c) ∧
      (∀ c, N.classOf c ≠ θ → N.classTreeVector κ θ c = 0) := by
  constructor
  · intro c hc
    simp [classTreeVector, hc, N.treeConstant_pos_of_weaklyReversible κ hwr c]
  · intro c hc
    simp [classTreeVector, hc]

/-- Any kinetic-kernel vector supported on a linkage class is a scalar multiple
of the tree-constant vector for that class. -/
theorem kernelVector_supportedOnClass_eq_smul_tree (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (θ : Quotient N.linkedSetoid) {v : N.ComplexIdx → ℝ}
    (hvoff : ∀ c, N.classOf c ≠ θ → v c = 0)
    (hvker : N.kineticMap κ v = 0) :
    ∃ a : ℝ, v = a • N.classTreeVector κ θ := by
  have hsc : ∀ c c' : N.ComplexIdx,
      N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val :=
    fun c c' hc hc' => hwr.reaches_of_linked (Quotient.exact (hc.trans hc'.symm))
  have hpos := (N.classTreeVector_positive_on_class κ hwr θ).1
  have hoff := (N.classTreeVector_positive_on_class κ hwr θ).2
  exact N.perClass_kernel_unique κ θ hsc hpos hoff
    (N.kineticMap_restrict_classTreeVector κ θ) hvoff hvker

/-- Every kinetic-kernel vector decomposes into its linkage-class restrictions. -/
theorem kineticKernel_eq_sum_restrictToClass (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0) :
    v = ∑ θ : Quotient N.linkedSetoid, N.restrictToClass θ v := by
  simpa using (N.sum_restrictToClass v).symm

/-- **Tree-constant kernel decomposition.** Every kinetic-kernel vector on a
weakly reversible network is a unique classwise linear combination of tree vectors. -/
theorem exists_treeConstant_class_coefficients (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0) :
    ∃ a : Quotient N.linkedSetoid → ℝ,
      v = ∑ θ, a θ • N.classTreeVector κ θ := by
  classical
  choose a ha using fun θ => N.kernelVector_supportedOnClass_eq_smul_tree κ hwr θ
    (v := N.restrictToClass θ v)
    (fun c hc => restrictToClass_apply_of_ne N v hc)
    (by
      rw [kineticMap_restrictToClass, hv]
      funext c
      simp [restrictToClass])
  refine ⟨a, ?_⟩
  rw [N.kineticKernel_eq_sum_restrictToClass κ hv]
  apply Finset.sum_congr rfl
  intro θ _
  exact ha θ

/-- Coefficients in the tree-constant decomposition are unique. -/
theorem treeConstant_class_coefficients_unique (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {a b : Quotient N.linkedSetoid → ℝ}
    (h : (∑ θ, a θ • N.classTreeVector κ θ) =
         ∑ θ, b θ • N.classTreeVector κ θ) :
    a = b := by
  classical
  funext θ
  obtain ⟨c, hc⟩ := Quotient.exists_rep θ
  have hcclass : N.classOf c = θ := by simpa [classOf] using hc
  have hT : 0 < N.treeConstant κ c :=
    N.treeConstant_pos_of_weaklyReversible κ hwr c
  have happ := congrFun h c
  -- all other class vectors vanish at `c`; the remaining tree constant is nonzero.
  simp [classTreeVector] at happ
  have hcoeff : a (N.classOf c) = b (N.classOf c) := happ.resolve_right hT.ne'
  simpa [hcclass] using hcoeff

/-- Canonical linear coordinate map from linkage-class coefficients into complex space. -/
noncomputable def treeKernelCoordinates (N : Network S) (κ : N.RateConstants) :
    (Quotient N.linkedSetoid → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun a := ∑ θ, a θ • N.classTreeVector κ θ
  map_add' a b := by
    classical
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    classical
    simp [smul_smul, Finset.smul_sum]

/-- Under weak reversibility, the tree-coordinate map is injective. -/
theorem treeKernelCoordinates_injective (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) :
    Function.Injective (N.treeKernelCoordinates κ) := by
  intro a b hab
  exact N.treeConstant_class_coefficients_unique κ hwr hab

/-- The range of tree coordinates is exactly the kinetic kernel. -/
theorem range_treeKernelCoordinates_eq_kineticKernel (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    LinearMap.range (N.treeKernelCoordinates κ) = LinearMap.ker (N.kineticMap κ) := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    classical
    simp only [treeKernelCoordinates, LinearMap.coe_mk, AddHom.coe_mk]
    rw [map_sum]
    simp [N.kineticMap_restrict_classTreeVector κ]
  · intro hv
    rw [LinearMap.mem_ker] at hv
    obtain ⟨a, ha⟩ := N.exists_treeConstant_class_coefficients κ hwr hv
    exact ⟨a, ha.symm⟩

/-- A kinetic-kernel vector is strictly positive exactly when all of its
linkage-class tree coefficients are strictly positive. -/
theorem treeCombination_positive_iff_coefficients_positive (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (a : Quotient N.linkedSetoid → ℝ) :
    (∀ c, 0 < (N.treeKernelCoordinates κ a) c) ↔ ∀ θ, 0 < a θ := by
  classical
  constructor
  · intro h θ
    obtain ⟨c, hc⟩ := Quotient.exists_rep θ
    have hcclass : N.classOf c = θ := by simpa [classOf] using hc
    have hK := N.treeConstant_pos_of_weaklyReversible κ hwr c
    have hcpos := h c
    simp [treeKernelCoordinates, classTreeVector] at hcpos
    rw [hcclass] at hcpos
    exact pos_of_mul_pos_left hcpos hK.le
  · intro ha c
    have hK := N.treeConstant_pos_of_weaklyReversible κ hwr c
    have hac := ha (N.classOf c)
    simp [treeKernelCoordinates, classTreeVector, hK.ne']
    positivity

/-- **Positive kinetic kernel cone theorem.** On a weakly reversible network,
strictly positive kernel vectors are exactly positive linkage-class combinations
of the canonical tree vectors. -/
theorem positive_kineticKernel_iff_treeCoefficients (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (v : N.ComplexIdx → ℝ) :
    (N.kineticMap κ v = 0 ∧ ∀ c, 0 < v c) ↔
      ∃ a : Quotient N.linkedSetoid → ℝ,
        (∀ θ, 0 < a θ) ∧ v = N.treeKernelCoordinates κ a := by
  constructor
  · rintro ⟨hvker, hvpos⟩
    obtain ⟨a, ha⟩ := N.exists_treeConstant_class_coefficients κ hwr hvker
    refine ⟨a, ?_, ?_⟩
    · rw [← N.treeCombination_positive_iff_coefficients_positive κ hwr a]
      intro c
      change 0 < (∑ θ, a θ • N.classTreeVector κ θ) c
      rw [← ha]
      exact hvpos c
    · change v = ∑ θ, a θ • N.classTreeVector κ θ
      exact ha
  · rintro ⟨a, ha, rfl⟩
    constructor
    · rw [← LinearMap.mem_ker, ← N.range_treeKernelCoordinates_eq_kineticKernel κ hwr]
      exact ⟨a, rfl⟩
    · exact (N.treeCombination_positive_iff_coefficients_positive κ hwr a).2 ha

end Network
end CRNT
