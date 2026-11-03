import CRNT.Design.ShinarFeinbergTheorem
import CRNT.Equilibria.TreeConstantCriterion
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Deficiency.DeficiencyOneScalarReduction

/-!
# Tree-constant formula for Shinar--Feinberg ACR

When the two Shinar--Feinberg complexes lie in the same linkage class, the robust value
has an explicit tree-constant formula. If they differ only in species `s`, with
`m = d_s-c_s ≠ 0`, then complex/tree-kernel ratios give

`x_s^m = K_d / K_c`.

The cross-linkage branch of the general theorem uses the deficiency-one scalar coupling to
show that the same ratio is pinned even though the tree-constant binomial does not directly
connect the two complexes.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Integer stoichiometric exponent difference in the robust species. -/
def robustExponent {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s) : ℤ :=
  (H.d s : ℤ) - (H.c s : ℤ)

/-- The robust exponent is nonzero. -/
theorem robustExponent_ne_zero {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s) : robustExponent H ≠ 0 := by
  intro hzero
  apply H.differAt
  have hcast : (H.d s : ℤ) = (H.c s : ℤ) := by
    exact sub_eq_zero.mp hzero
  exact_mod_cast hcast.symm

/-- Ratio of the two monomials collapses to a pure power of the distinguished species. -/
theorem shinarFeinberg_monomialRatio_eq_speciesPower
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    {x : Concentration S} (hx : x.Positive) :
    H.d.massActionMonomial x / H.c.massActionMonomial x =
      Real.rpow (x s) (robustExponent H : ℝ) := by
  rw [Complex.massActionMonomial, Complex.massActionMonomial]
  rw [← Finset.prod_div_distrib]
  rw [Finset.prod_eq_single s]
  · rw [show (robustExponent H : ℝ) = (H.d s : ℝ) - (H.c s : ℝ) by
      simp [robustExponent]]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_sub (hx s)]
    rw [Real.rpow_eq_pow]
  · intro t _ hts
    have hdc : H.d t = H.c t := (H.differOnlyAt t hts).symm
    rw [hdc]
    exact div_self (pow_ne_zero _ (ne_of_gt (hx t)))
  · intro hsnot
    exact (hsnot (Finset.mem_univ s)).elim

/-- Same-linkage Shinar--Feinberg formula from tree constants. -/
theorem sameLinkage_ACR_treeConstant_equation
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    (hlink : N.Linked H.c H.d)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x)
    (hcb : N.IsComplexBalanced κ x) :
    Real.rpow (x s) (robustExponent H : ℝ) =
      N.treeConstant κ ⟨H.d, H.hd⟩ /
        N.treeConstant κ ⟨H.c, H.hc⟩ := by
  have hwr := N.weaklyReversible_of_positive_complexBalanced κ hx hcb
  have hratio := N.complexMonomial_ratio_eq_treeConstant_ratio κ hwr hx hcb
    (i := ⟨H.d, H.hd⟩) (j := ⟨H.c, H.hc⟩) (Network.Linked.symm hlink)
  have hmono := shinarFeinberg_monomialRatio_eq_speciesPower H hx
  rw [← hmono]
  simpa [complexMonomial] using hratio

/-- The same-linkage robust value is the unique positive solution of the tree-constant
power equation. -/
noncomputable def sameLinkageACRValue
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) : ℝ :=
  Real.rpow
    (N.treeConstant κ ⟨H.d, H.hd⟩ / N.treeConstant κ ⟨H.c, H.hc⟩)
    ((robustExponent H : ℝ)⁻¹)

/-- Explicit same-linkage ACR formula. -/
theorem species_eq_sameLinkageACRValue
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    (hlink : N.Linked H.c H.d)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x)
    (hcb : N.IsComplexBalanced κ x) :
    x s = sameLinkageACRValue H κ := by
  have heq := sameLinkage_ACR_treeConstant_equation H κ hlink hx hss hcb
  unfold sameLinkageACRValue
  rw [← heq]
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
  have hm : (robustExponent H : ℝ) ≠ 0 := by
    exact_mod_cast robustExponent_ne_zero H
  simpa using (Real.rpow_rpow_inv (hx s).le hm).symm

/-- Cross-linkage pinning is exactly the extra deficiency-one statement needed to extend
this explicit formula beyond a single linkage class. -/
def CrossLinkageTreeRatioPinned
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x : Concentration S,
      x.Positive → N.IsMassActionSteadyState κ x →
      H.d.massActionMonomial x / H.c.massActionMonomial x = C

/-- The classical cross-linkage Shinar--Feinberg kernel lemma supplies such a constant. -/
theorem crossLinkageTreeRatioPinned_of_deficiencyOne
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    (hcross : ¬ N.Linked H.c H.d) :
    CrossLinkageTreeRatioPinned H κ := by
  classical
  by_cases hex : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x
  · obtain ⟨x₀, hx₀, hss₀⟩ := hex
    let C := H.d.massActionMonomial x₀ / H.c.massActionMonomial x₀
    refine ⟨C, div_pos (Complex.massActionMonomial_pos hx₀ H.d)
      (Complex.massActionMonomial_pos hx₀ H.c), ?_⟩
    intro x hx hss
    have hpin := shinarFeinberg_pinnedRatioAt H κ x x₀ hx hss hx₀ hss₀
    have hc0 : H.c.massActionMonomial x ≠ 0 :=
      (Complex.massActionMonomial_pos hx H.c).ne'
    have hc00 : H.c.massActionMonomial x₀ ≠ 0 :=
      (Complex.massActionMonomial_pos hx₀ H.c).ne'
    dsimp [C]
    apply (div_eq_div_iff hc0 hc00).2
    simpa [mul_comm] using hpin.symm
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hss
    exact False.elim (hex ⟨x, hx, hss⟩)

end Network
end CRNT
