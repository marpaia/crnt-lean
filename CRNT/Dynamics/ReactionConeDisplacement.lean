import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.DissipationBound
import CRNT.Geometry.FiniteConeClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mass-action displacements lie in the reaction cone

A mass-action velocity is a nonnegative combination of reaction vectors.  Integrating a genuine
nonnegative trajectory over a forward time interval preserves that conical structure: the net
state displacement is the reaction-vector combination whose coefficient at reaction `r` is the
integrated mass-action rate of `r`.

This is stronger than the usual stoichiometric-affine invariance statement.  The coefficients are
nonnegative, so the displacement lies in `Network.reactionCone`, not merely in the linear
stoichiometric subspace.

The result is the dynamical ingredient needed for the direct drainable-siphon persistence proof:
if a positive trajectory accumulates at a boundary point `w`, then `w - x₀` belongs to the closed
reaction cone.  On the zero set of `w` this displacement is strictly negative, so that zero set is
real-flux drainable and therefore drainable by the finite pathway realization theorem.
-/

open scoped BigOperators Interval
open MeasureTheory Set

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The reaction cone of a finite reaction network is closed. -/
theorem isClosed_reactionCone (N : Network S) :
    IsClosed (N.reactionCone : Set (S → ℝ)) := by
  rw [reactionCone, generatedCone]
  exact isClosed_coe_hull_of_set_finite (Set.toFinite (Set.range N.reactionVector))

/-- **Integrated reaction-flux representation.**  Along a nonnegative genuine mass-action
solution on `[a,b]`, the displacement is the reaction-vector combination with coefficients equal
to the integrated reaction rates. -/
theorem displacement_eq_integratedReactionFlux (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a ≤ b)
    (hsol : ∀ t ∈ Set.Icc a b,
      HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t ∈ Set.Icc a b, (γ t).Nonnegative) :
    γ b - γ a =
      ∑ r : N.R,
        (∫ t in a..b, N.massActionRate κ r (γ t)) • N.reactionVector r := by
  have hγcont : ContinuousOn γ (Set.Icc a b) :=
    fun t ht => (hsol t ht).continuousAt.continuousWithinAt
  have hfieldcont : ContinuousOn (fun t => N.massActionVectorField κ (γ t)) (Set.Icc a b) :=
    (continuous_massActionVectorField N κ).comp_continuousOn hγcont
  have hfieldint : IntervalIntegrable (fun t => N.massActionVectorField κ (γ t)) volume a b :=
    hfieldcont.intervalIntegrable_of_Icc hab
  have hFTC :
      (∫ t in a..b, N.massActionVectorField κ (γ t)) = γ b - γ a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hγcont
      (fun t ht => hsol t ⟨ht.1.le, ht.2.le⟩) hfieldint
  rw [← hFTC]
  have hrint : ∀ r : N.R,
      IntervalIntegrable (fun t => N.massActionRate κ r (γ t)) volume a b := by
    intro r
    exact ((continuous_massActionRate N κ r).comp_continuousOn hγcont).intervalIntegrable_of_Icc hab
  calc
    (∫ t in a..b, N.massActionVectorField κ (γ t))
        = ∫ t in a..b,
            ∑ r : N.R, (N.massActionRate κ r (γ t)) • N.reactionVector r := by
              congr 1
              funext t
              exact N.massActionVectorField_eq_sum κ (γ t)
    _ = ∑ r : N.R,
          ∫ t in a..b, (N.massActionRate κ r (γ t)) • N.reactionVector r := by
          rw [intervalIntegral.integral_finsetSum]
          intro r _
          -- `IntervalIntegrable` is the conjunction of two `IntegrableOn`s here
          exact ⟨(hrint r).1.smul_const _, (hrint r).2.smul_const _⟩
    _ = ∑ r : N.R,
          (∫ t in a..b, N.massActionRate κ r (γ t)) • N.reactionVector r := by
          apply Finset.sum_congr rfl
          intro r _
          exact intervalIntegral.integral_smul_const _ _

/-- The integrated rate of each reaction is nonnegative along a nonnegative forward trajectory. -/
theorem integratedReactionRate_nonneg (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a ≤ b)
    (hnn : ∀ t ∈ Set.Icc a b, (γ t).Nonnegative) (r : N.R) :
    0 ≤ ∫ t in a..b, N.massActionRate κ r (γ t) := by
  exact intervalIntegral.integral_nonneg hab fun t ht =>
    N.massActionRate_nonneg κ r (hnn t ht)

/-- **Forward mass-action displacement lies in the reaction cone.** -/
theorem sub_mem_reactionCone_of_solution (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a ≤ b)
    (hsol : ∀ t ∈ Set.Icc a b,
      HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t ∈ Set.Icc a b, (γ t).Nonnegative) :
    γ b - γ a ∈ N.reactionCone := by
  rw [N.displacement_eq_integratedReactionFlux κ hab hsol hnn]
  refine Submodule.sum_mem _ fun r _ => ?_
  exact PointedCone.smul_mem _ (N.integratedReactionRate_nonneg κ hab hnn r)
    (N.reactionVector_mem_reactionCone r)

end Network
end CRNT
