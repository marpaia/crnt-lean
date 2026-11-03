import CRNT.Deficiency.PositiveKineticFamily

/-! Explicit half-space description of the positive Type-II kinetic fibre. -/
namespace CRNT.Network

open scoped Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positivity of the full deficiency kinetic family is exactly a finite collection of lower
bounds on the linkage-kernel coefficients.  This is the coordinate form needed to replace the
abstract positive fibre by a translated positive orthant. -/
theorem positive_deficiencyKineticFamily_iff_coeff_lowerBounds
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (z : N.ComplexIdx → ℝ) (a : ℝ) (coeff : Quotient N.linkedSetoid → ℝ) :
    (∀ c, 0 < N.deficiencyKineticFamily κ z a coeff c) ↔
      ∀ c, -(a * z c) / N.treeConstantVector κ c < coeff (N.classOf c) := by
  constructor
  · intro h c
    have hK : 0 < N.treeConstantVector κ c :=
      (N.treeConstantVector_positive_kernel κ hwr).1 c
    have hc := h c
    rw [N.deficiencyKineticFamily_apply] at hc
    exact (div_lt_iff₀ hK).2 (by linarith)
  · intro h c
    have hK : 0 < N.treeConstantVector κ c :=
      (N.treeConstantVector_positive_kernel κ hwr).1 c
    rw [N.deficiencyKineticFamily_apply]
    have hc := (div_lt_iff₀ hK).1 (h c)
    linarith

/-- Increasing every linkage coefficient preserves positivity of the kinetic-family point. -/
theorem positive_deficiencyKineticFamily_mono_coeff
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (z : N.ComplexIdx → ℝ) (a : ℝ)
    {c d : Quotient N.linkedSetoid → ℝ}
    (hc : ∀ y, 0 < N.deficiencyKineticFamily κ z a c y)
    (hcd : ∀ q, c q ≤ d q) :
    ∀ y, 0 < N.deficiencyKineticFamily κ z a d y := by
  rw [N.positive_deficiencyKineticFamily_iff_coeff_lowerBounds hwr κ z a] at hc ⊢
  intro y
  exact lt_of_lt_of_le (hc y) (hcd (N.classOf y))

/-- Uniform positive translation of the linkage coefficients stays inside the positive fibre. -/
theorem positive_deficiencyKineticFamily_add_nonneg_coeff
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (z : N.ComplexIdx → ℝ) (a : ℝ)
    {coeff delta : Quotient N.linkedSetoid → ℝ}
    (hpos : ∀ y, 0 < N.deficiencyKineticFamily κ z a coeff y)
    (hdelta : ∀ q, 0 ≤ delta q) :
    ∀ y, 0 < N.deficiencyKineticFamily κ z a (coeff + delta) y := by
  apply N.positive_deficiencyKineticFamily_mono_coeff hwr κ z a hpos
  intro q
  simp only [Pi.add_apply]
  linarith [hdelta q]

end CRNT.Network

namespace CRNT.Network

open scoped BigOperators Classical Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A simple continuous coefficient choice lying strictly above every positivity lower bound.
It deliberately uses the same coefficient on every linkage class; this avoids finite maxima. -/
noncomputable def canonicalPositiveKineticCoeff
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ) (a : ℝ)
    (_q : Quotient N.linkedSetoid) : ℝ :=
  1 + ∑ c, |a * z c| / N.treeConstantVector κ c

/-- The canonical coefficient choice gives a positive kinetic preimage for every real deficiency
coordinate, not merely on a local interval. -/
theorem canonicalPositiveKineticFamily_pos
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (z : N.ComplexIdx → ℝ) (a : ℝ) :
    ∀ c, 0 < N.deficiencyKineticFamily κ z a
      (N.canonicalPositiveKineticCoeff κ z a) c := by
  rw [N.positive_deficiencyKineticFamily_iff_coeff_lowerBounds hwr κ z a]
  intro c
  have hK : 0 < N.treeConstantVector κ c :=
    (N.treeConstantVector_positive_kernel κ hwr).1 c
  have hterm : |a * z c| / N.treeConstantVector κ c ≤
      ∑ d, |a * z d| / N.treeConstantVector κ d := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun d : N.ComplexIdx => |a * z d| / N.treeConstantVector κ d)
      (fun d _ => div_nonneg (abs_nonneg _)
        ((N.treeConstantVector_positive_kernel κ hwr).1 d).le) (Finset.mem_univ c)
  have habs : -(a * z c) ≤ |a * z c| := neg_le_abs _
  have hdiv : -(a * z c) / N.treeConstantVector κ c ≤
      |a * z c| / N.treeConstantVector κ c :=
    (div_le_div_iff_of_pos_right hK).2 habs
  dsimp [canonicalPositiveKineticCoeff]
  exact lt_of_le_of_lt (hdiv.trans hterm) (lt_add_of_pos_left _ zero_lt_one)

/-- The canonical globally positive coefficient choice varies continuously with the deficiency
coordinate. -/
theorem continuous_canonicalPositiveKineticCoeff
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ) :
    Continuous (fun a : ℝ => N.canonicalPositiveKineticCoeff κ z a) := by
  rw [continuous_pi_iff]
  intro q
  dsimp [canonicalPositiveKineticCoeff]
  fun_prop

/-- Hence the Type-II kinetic line admits a globally defined continuous positive section. -/
theorem continuous_canonicalPositiveKineticFamily
    (N : Network S) (κ : N.RateConstants) (z : N.ComplexIdx → ℝ) :
    Continuous (fun a : ℝ => N.deficiencyKineticFamily κ z a
      (N.canonicalPositiveKineticCoeff κ z a)) := by
  exact (N.continuous_deficiencyKineticFamily κ z).comp
    (continuous_id.prodMk (N.continuous_canonicalPositiveKineticCoeff κ z))

end CRNT.Network
