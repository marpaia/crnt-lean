import CRNT.Deficiency.RangeKineticWR
import CRNT.Theorems.DeficiencyZero.PositiveKernel

/-!
# Strictly positive kinetic preimages in weakly reversible networks

For a weakly reversible network, `Im A_k = Im ∂`.  Hence every cut-space vector has a
kinetic preimage.  Weak reversibility also supplies a strictly positive vector in `ker A_k`.
Adding a sufficiently large positive kernel vector to an arbitrary preimage therefore makes the
preimage strictly positive without changing its kinetic image.

This is the algebraic first step in the Boros existence proof: for a deficiency vector `g`, the
linear equation `A_k v = a g` has a strictly positive solution for every scalar `a`.  The remaining
existence problem is entirely the nonlinear monomial-realization problem.
-/

namespace CRNT
namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Every cut-space vector has a strictly positive kinetic preimage under weak reversibility.** -/
theorem exists_strictlyPositive_kineticPreimage_of_mem_range_incidenceMap
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ LinearMap.range N.incidenceMap) :
    ∃ v : N.ComplexIdx → ℝ, (∀ c, 0 < v c) ∧ N.kineticMap κ v = g := by
  have hgA : g ∈ LinearMap.range (N.kineticMap κ) := by
    rw [N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ]
    exact hg
  obtain ⟨z, hz⟩ := hgA
  obtain ⟨b, hbpos, hbker⟩ :=
    PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ
  let M : ℝ := ∑ c : N.ComplexIdx, |z c| / b c
  let t : ℝ := M + 1
  refine ⟨z + t • b, ?_, ?_⟩
  · intro c
    have hle : |z c| / b c ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (fun d _ => div_nonneg (abs_nonneg _) (hbpos d).le) (Finset.mem_univ c)
    have hmul : |z c| ≤ M * b c := by
      have := (div_le_iff₀ (hbpos c)).mp hle
      simpa [mul_comm] using this
    have habs : -|z c| ≤ z c := neg_abs_le (z c)
    change 0 < z c + t * b c
    dsimp [t]
    nlinarith [hbpos c]
  · rw [map_add, map_smul, hbker, smul_zero, add_zero]
    exact hz

/-- A deficiency-space vector is in particular a cut-space vector, so it has a strictly positive
kinetic preimage in every weakly reversible realization. -/
theorem exists_strictlyPositive_kineticPreimage_of_mem_deficiencySubspace
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) :
    ∃ v : N.ComplexIdx → ℝ, (∀ c, 0 < v c) ∧ N.kineticMap κ v = g :=
  N.exists_strictlyPositive_kineticPreimage_of_mem_range_incidenceMap hwr κ hg.2

/-- **All scalar points on a deficiency line have strictly positive kinetic preimages.** -/
theorem exists_strictlyPositive_kineticPreimage_smul_of_mem_deficiencySubspace
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) (a : ℝ) :
    ∃ v : N.ComplexIdx → ℝ, (∀ c, 0 < v c) ∧ N.kineticMap κ v = a • g := by
  apply N.exists_strictlyPositive_kineticPreimage_of_mem_deficiencySubspace hwr κ
  exact N.deficiencySubspace.smul_mem a hg

end Network
end CRNT
