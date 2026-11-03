import CRNT.Deficiency.BorosDeficiencyOneReduction
import CRNT.Theorems.DeficiencyZero.PositiveKernel

/-! Full linkage-kernel parameter family for the Boros Type-II argument. -/
namespace CRNT.Network

open scoped BigOperators Classical Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The canonical kinetic-kernel vector with one coefficient per linkage class. -/
noncomputable def treeKernelFamily (N : Network S) (κ : N.RateConstants)
    (coeff : Quotient N.linkedSetoid → ℝ) : N.ComplexIdx → ℝ :=
  ∑ q, coeff q • N.restrictToClass q (N.treeConstantVector κ)

/-- Every linkage-kernel family lies in the kinetic kernel. -/
theorem kineticMap_treeKernelFamily_eq_zero
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (coeff : Quotient N.linkedSetoid → ℝ) :
    N.kineticMap κ (N.treeKernelFamily κ coeff) = 0 := by
  unfold treeKernelFamily
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [map_smul, N.kineticMap_restrictToClass,
    (N.treeConstantVector_positive_kernel κ hwr).2]
  funext c
  simp [restrictToClass]

/-- Coordinate formula: only the coefficient of the complex's own linkage class contributes. -/
theorem treeKernelFamily_apply
    (N : Network S) (κ : N.RateConstants)
    (coeff : Quotient N.linkedSetoid → ℝ) (c : N.ComplexIdx) :
    N.treeKernelFamily κ coeff c =
      coeff (N.classOf c) * N.treeConstantVector κ c := by
  classical
  unfold treeKernelFamily
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (N.classOf c)]
  · rw [N.restrictToClass_apply_of_eq _ rfl]
  · intro q _ hq
    rw [N.restrictToClass_apply_of_ne]
    · ring
    · exact fun hc => hq hc.symm
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- Full affine family of preimages of the deficiency line. -/
noncomputable def deficiencyKineticFamily (N : Network S) (κ : N.RateConstants)
    (z : N.ComplexIdx → ℝ) (a : ℝ) (coeff : Quotient N.linkedSetoid → ℝ) :
    N.ComplexIdx → ℝ := a • z + N.treeKernelFamily κ coeff


/-- Coordinate formula for the full deficiency kinetic family.  This exposes the parameter
space as one scalar deficiency coordinate plus one scalar kernel coordinate per linkage class. -/
theorem deficiencyKineticFamily_apply
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ)
    (a : ℝ) (coeff : Quotient N.linkedSetoid → ℝ) (c : N.ComplexIdx) :
    N.deficiencyKineticFamily κ z a coeff c =
      a * z c + coeff (N.classOf c) * N.treeConstantVector κ c := by
  rw [deficiencyKineticFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    N.treeKernelFamily_apply]

/-- The full kinetic family depends continuously on all of its finite-dimensional parameters. -/
theorem continuous_deficiencyKineticFamily
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ) :
    Continuous (fun p : ℝ × (Quotient N.linkedSetoid → ℝ) =>
      N.deficiencyKineticFamily κ z p.1 p.2) := by
  rw [continuous_pi_iff]
  intro c
  simp only [N.deficiencyKineticFamily_apply]
  fun_prop

/-- Positivity of the full kinetic family is an open condition in the joint deficiency/kernel
parameter space. -/
theorem isOpen_positiveDeficiencyKineticParameters
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ) :
    IsOpen {p : ℝ × (Quotient N.linkedSetoid → ℝ) |
      ∀ c, 0 < N.deficiencyKineticFamily κ z p.1 p.2 c} := by
  rw [show {p : ℝ × (Quotient N.linkedSetoid → ℝ) |
      ∀ c, 0 < N.deficiencyKineticFamily κ z p.1 p.2 c} =
      ⋂ c : N.ComplexIdx,
        (fun p : ℝ × (Quotient N.linkedSetoid → ℝ) =>
          N.deficiencyKineticFamily κ z p.1 p.2 c) ⁻¹' Set.Ioi 0 by
    ext p
    simp]
  apply isOpen_iInter_of_finite
  intro c
  apply Continuous.isOpen_preimage
  · exact (continuous_apply c).comp (N.continuous_deficiencyKineticFamily κ z)
  · exact isOpen_Ioi

/-- The full family maps to `a • g` whenever `z` maps to `g`. -/
theorem kineticMap_deficiencyKineticFamily
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g z : N.ComplexIdx → ℝ} (hz : N.kineticMap κ z = g)
    (a : ℝ) (coeff : Quotient N.linkedSetoid → ℝ) :
    N.kineticMap κ (N.deficiencyKineticFamily κ z a coeff) = a • g := by
  unfold deficiencyKineticFamily
  rw [map_add, map_smul, hz, N.kineticMap_treeKernelFamily_eq_zero hwr κ coeff, add_zero]

/-- Every point on the deficiency line has a positive representative in the full family. -/
theorem exists_coeff_positive_deficiencyKineticFamily
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g z : N.ComplexIdx → ℝ} (hz : N.kineticMap κ z = g) (a : ℝ) :
    ∃ coeff : Quotient N.linkedSetoid → ℝ,
      ∀ c, 0 < N.deficiencyKineticFamily κ z a coeff c := by
  have hgRange : g ∈ LinearMap.range N.incidenceMap := by
    rw [← N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ]
    exact ⟨z, hz⟩
  obtain ⟨v, hvpos, hv⟩ :=
    N.exists_strictlyPositive_kineticPreimage_of_mem_range_incidenceMap hwr κ
      (g := a • g) ((LinearMap.range N.incidenceMap).smul_mem a hgRange)
  obtain ⟨coeff, hcoeff⟩ := N.kineticPreimage_affine_treeConstants hwr κ hz hv
  refine ⟨coeff, ?_⟩
  intro c
  change 0 < (a • z + N.treeKernelFamily κ coeff) c
  rw [show N.treeKernelFamily κ coeff =
      ∑ θ, coeff θ • N.restrictToClass θ (N.treeConstantVector κ) by rfl]
  rw [← hcoeff]
  exact hvpos c

/-- Conversely, every preimage of `a • g` occurs in the full linkage-kernel family. -/
theorem exists_coeff_eq_deficiencyKineticFamily_of_kineticMap_eq
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g z v : N.ComplexIdx → ℝ} (hz : N.kineticMap κ z = g) {a : ℝ}
    (hv : N.kineticMap κ v = a • g) :
    ∃ coeff : Quotient N.linkedSetoid → ℝ,
      v = N.deficiencyKineticFamily κ z a coeff := by
  obtain ⟨coeff, hcoeff⟩ := N.kineticPreimage_affine_treeConstants hwr κ hz hv
  refine ⟨coeff, ?_⟩
  rw [deficiencyKineticFamily]
  exact hcoeff

/-- The full family is therefore exactly the affine fibre of the kinetic map over `a • g`. -/
theorem mem_deficiencyKineticFamily_iff
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g z v : N.ComplexIdx → ℝ} (hz : N.kineticMap κ z = g) {a : ℝ} :
    N.kineticMap κ v = a • g ↔
      ∃ coeff : Quotient N.linkedSetoid → ℝ,
        v = N.deficiencyKineticFamily κ z a coeff := by
  constructor
  · exact N.exists_coeff_eq_deficiencyKineticFamily_of_kineticMap_eq hwr κ hz
  · rintro ⟨coeff, rfl⟩
    exact N.kineticMap_deficiencyKineticFamily hwr κ hz a coeff

end CRNT.Network
