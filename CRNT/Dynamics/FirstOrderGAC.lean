import CRNT.Dynamics.SiphonLinkage
import CRNT.Dynamics.GACNoCriticalSiphon
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Dynamics.KnownGlobalPersistenceClasses

/-!
# The global attractor property for first-order networks

A network is **first order** (monomolecular, `Network.IsFirstOrder`) when every complex has total
molecularity at most one, i.e. is `0` or a single species.  Its mass-action equations are linear.

**Theorem.**  A weakly reversible first-order network has no critical siphon
(`hasNoCriticalSiphon_of_firstOrder`).  Consequently every complex-balanced first-order
mass-action system has the global attractor property: the ω-limit set of every positive
trajectory is the complex-balanced equilibrium of its compatibility class
(`gac_of_firstOrder`).

**Proof.**  Let `P` be a siphon.  By the Shiu–Sturmfels characterization
(`isSiphon_iff_of_weaklyReversible`), the source of every reaction meets `P` exactly when the
target does.  At molecularity at most one, a complex that meets `P` has exactly one molecule of
`P`-species and one that avoids `P` has none, so `∑_{s ∈ P} (y'_r - y_r) s = 0` for every
reaction: the indicator of `P` is a nonnegative conservation law with support exactly `P`, so
`P` is not critical.  The global attractor statement is then
`gac_of_hasNoCriticalSiphon`, which does not depend on Hole A.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

open Classical in
/-- At molecularity `≤ 1`, the number of `P`-molecules of a complex is `1` if it meets `P` and
`0` otherwise. -/
theorem sum_mem_eq_of_molecularity_le_one {P : Finset S} {y : Complex S}
    (hy : (∑ s, y s) ≤ 1) :
    (∑ s ∈ P, y s) = if Meets P y then 1 else 0 := by
  have hle : (∑ s ∈ P, y s) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P) (fun _ _ _ => Nat.zero_le _)).trans hy
  split_ifs with hm
  · obtain ⟨s, hs, hys⟩ := hm
    have : 1 ≤ ∑ s ∈ P, y s :=
      (Nat.one_le_iff_ne_zero.mpr hys).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs)
    omega
  · simp only [Meets, not_exists, not_and, not_not] at hm
    exact Finset.sum_eq_zero fun s hs => hm s hs

/-- **First-order weakly reversible networks have no critical siphon.** -/
theorem hasNoCriticalSiphon_of_firstOrder (N : Network S) (hwr : N.WeaklyReversible)
    (hfo : N.IsFirstOrder) : N.HasNoCriticalSiphon := by
  intro P ⟨_, hsiph, hnot⟩
  apply hnot
  refine ⟨fun s => if s ∈ P then 1 else 0, fun s => by dsimp only; split_ifs <;> norm_num,
    fun s => by dsimp only; split_ifs with h <;> simp [h], fun r => ?_⟩
  have hiff := (N.isSiphon_iff_of_weaklyReversible hwr P).mp hsiph r
  have hsrc := sum_mem_eq_of_molecularity_le_one (P := P) (hfo _ (N.source_mem_complexes r))
  have htgt := sum_mem_eq_of_molecularity_le_one (P := P) (hfo _ (N.target_mem_complexes r))
  have hsum : ∑ s, (if s ∈ P then (1 : ℝ) else 0) * N.reactionVector r s =
      ((∑ s ∈ P, (N.reaction r).target s : ℕ) : ℝ) - ((∑ s ∈ P, (N.reaction r).source s : ℕ) : ℝ) := by
    simp only [reactionVector_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [hsum, hsrc, htgt]
  classical
  by_cases hm : Meets P (N.reaction r).source
  · rw [if_pos hm, if_pos (hiff.mp hm)]; norm_num
  · rw [if_neg hm, if_neg (fun h => hm (hiff.mpr h))]; norm_num

/-- **Global attractor property for first-order complex-balanced systems.** -/
theorem gac_of_firstOrder (N : Network S) (hfo : N.IsFirstOrder) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit Filter.atTop ϕ {x₀} = {xstar} := by
  have hwr := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  exact N.gac_of_hasNoCriticalSiphon hwr κ (N.hasNoCriticalSiphon_of_firstOrder hwr hfo)
    hxs hcb hx0 hx0compat

end Network
end CRNT
