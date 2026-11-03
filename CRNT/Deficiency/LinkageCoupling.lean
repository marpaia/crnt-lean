import CRNT.Deficiency.LinkageDeficiency
import CRNT.LinearAlgebra.FinrankSup

/-!
# Linkage coupling deficiency

The ordinary deficiency decomposes into two conceptually different pieces:

* the sum of the deficiencies internal to individual linkage classes, and
* the rank defect caused by overlap between the stoichiometric subspaces of distinct
  linkage classes.

If `S_θ` is the stoichiometric subspace of linkage class `θ`, define

`χ = Σ_θ dim S_θ - dim (Σ_θ S_θ)`.

Then

`δ = Σ_θ δ_θ + χ`.

Thus Feinberg's linkage-class additivity condition is exactly `χ = 0`, i.e. independence
of the linkage-class stoichiometric subspaces.
-/

namespace CRNT
namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Rank overlap between linkage-class stoichiometric subspaces. -/
noncomputable def linkageCouplingDeficiency (N : Network S) : ℕ :=
  (∑ q : Quotient N.linkedSetoid, N.linkageStoichRank q) - N.stoichRank

/-- The class ranks dominate the global stoichiometric rank. -/
theorem stoichRank_add_linkageCoupling_eq_sum (N : Network S) :
    N.stoichRank + N.linkageCouplingDeficiency =
      ∑ q : Quotient N.linkedSetoid, N.linkageStoichRank q := by
  unfold linkageCouplingDeficiency
  have hle := N.stoichRank_le_sum
  omega

/-- Integer deficiency decomposition into within-linkage and between-linkage pieces. -/
theorem deficiencyInt_eq_sum_linkageDeficiency_add_coupling (N : Network S) :
    N.deficiencyInt =
      (∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q) +
        (N.linkageCouplingDeficiency : ℤ) := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hcouple : (N.stoichRank : ℤ) + (N.linkageCouplingDeficiency : ℤ) =
      ∑ q, (N.linkageStoichRank q : ℤ) := by
    exact_mod_cast N.stoichRank_add_linkageCoupling_eq_sum
  have hsum : ∑ q, N.linkageDeficiency q =
      (∑ q, (N.numComplexesIn q : ℤ)) -
        (Fintype.card (Quotient N.linkedSetoid) : ℤ) -
        ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, deficiencyInt, hn, card_quotient_eq]
  omega

/-- Natural-number version of the linkage-coupling decomposition. -/
theorem deficiency_eq_sum_linkageDeficiencyNat_add_coupling (N : Network S) :
    N.deficiency =
      Int.toNat (∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q) +
        N.linkageCouplingDeficiency := by
  have hsum_nonneg : 0 ≤ ∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q :=
    Finset.sum_nonneg fun q _ => N.linkageDeficiency_nonneg q
  have h := N.deficiencyInt_eq_sum_linkageDeficiency_add_coupling
  rw [N.deficiencyInt_eq_deficiency] at h
  have hcast : (N.deficiency : ℤ) =
      ((Int.toNat (∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q) +
        N.linkageCouplingDeficiency : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg hsum_nonneg]
    exact h
  exact_mod_cast hcast

/-- Linkage-class stoichiometric independence, expressed by rank additivity. -/
def LinkageStoichIndependent (N : Network S) : Prop :=
  N.stoichRank = ∑ q : Quotient N.linkedSetoid, N.linkageStoichRank q

/-- The coupling deficiency vanishes exactly under linkage-class stoichiometric independence. -/
theorem linkageCouplingDeficiency_eq_zero_iff (N : Network S) :
    N.linkageCouplingDeficiency = 0 ↔ N.LinkageStoichIndependent := by
  unfold linkageCouplingDeficiency LinkageStoichIndependent
  have hle := N.stoichRank_le_sum
  constructor <;> intro h
  · omega
  · omega

/-- Feinberg's linkage-deficiency additivity condition is precisely absence of
between-linkage stoichiometric coupling. -/
theorem sum_linkageDeficiency_eq_deficiencyInt_iff_independent (N : Network S) :
    (∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q) = N.deficiencyInt ↔
      N.LinkageStoichIndependent := by
  rw [N.deficiencyInt_eq_sum_linkageDeficiency_add_coupling]
  constructor
  · intro h
    have hc : N.linkageCouplingDeficiency = 0 := by omega
    exact (N.linkageCouplingDeficiency_eq_zero_iff).mp hc
  · intro h
    have hc := (N.linkageCouplingDeficiency_eq_zero_iff).mpr h
    simp [hc]

/-- If the linkage-class stoichiometric subspaces are independent, deficiency is exactly
additive over linkage classes. -/
theorem deficiency_additive_of_linkageStoichIndependent (N : Network S)
    (h : N.LinkageStoichIndependent) :
    N.deficiencyInt = ∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q := by
  exact (N.sum_linkageDeficiency_eq_deficiencyInt_iff_independent).2 h |>.symm

/-- Deficiency zero forces both zero class deficiencies and zero linkage coupling. -/
theorem deficiencyZero_forces_zero_linkageCoupling (N : Network S)
    (hδ : N.DeficiencyZero) : N.linkageCouplingDeficiency = 0 := by
  have hsum := N.deficiencyInt_eq_sum_linkageDeficiency_add_coupling
  have hclass : ∀ q : Quotient N.linkedSetoid, N.linkageDeficiency q = 0 :=
    N.linkageDeficiency_eq_zero_of_deficiencyZero hδ
  have hzsum : (∑ q : Quotient N.linkedSetoid, N.linkageDeficiency q) = 0 := by
    simp [hclass]
  rw [hδ, hzsum] at hsum
  have hc : (N.linkageCouplingDeficiency : ℤ) = 0 := by omega
  exact_mod_cast hc

end Network
end CRNT
