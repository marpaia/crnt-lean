import Scaffold.CRNTExpansion.PositiveTorusSaturation
import Scaffold.CRNTExpansion.ToricParametrization

/-!
# Consequences of positive-torus saturation

Once the saturation membership predicate has been packaged as an actual ideal, the existing
positive-zero-set theorem immediately upgrades to a reusable equivalence relation statement.  This
file records those consequences and connects the saturated CRNT ideals directly to the toric
parametrizations already formalized in the scaffold.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- An ideal and its species-coordinate saturation have the same strictly positive zero set. -/
theorem positiveTorusEquivalent_positiveTorusSaturationIdeal
    (I : Ideal (MvPolynomial S ℝ)) :
    PositiveTorusEquivalent I (positiveTorusSaturationIdeal I) := by
  intro x hx
  exact (vanishes_positiveTorusSaturationIdeal_iff I hx).symm

/-- Positive-torus equivalence is preserved by saturating both ideals. -/
theorem positiveTorusEquivalent_saturations
    {I J : Ideal (MvPolynomial S ℝ)} (h : PositiveTorusEquivalent I J) :
    PositiveTorusEquivalent (positiveTorusSaturationIdeal I)
      (positiveTorusSaturationIdeal J) := by
  intro x hx
  exact (vanishes_positiveTorusSaturationIdeal_iff I hx).trans
    ((h x hx).trans (vanishes_positiveTorusSaturationIdeal_iff J hx).symm)

/-- For weakly-reversible deficiency-zero systems, saturation preserves the common positive toric
variety of the steady-state and tree-binomial ideals. -/
theorem deficiencyZero_saturatedSteadyState_positiveTorusEquivalent_saturatedTreeBinomial
    (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) :
    PositiveTorusEquivalent
      (positiveTorusSaturationIdeal (N.steadyStateIdeal κ))
      (positiveTorusSaturationIdeal (N.treeBinomialIdeal κ)) :=
  positiveTorusEquivalent_saturations
    (N.deficiencyZero_steadyStateIdeal_positiveTorusEquivalent_treeBinomialIdeal κ hwr hδ)

/-- Positive zeros of the saturated tree-binomial ideal have the same Horn--Jackson toric
parametrization as the unsaturated ideal. -/
theorem vanishes_saturatedTreeBinomialIdeal_iff_toricParam
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    VanishesIdealAt (positiveTorusSaturationIdeal (N.treeBinomialIdeal κ)) x ↔
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  exact (vanishes_positiveTorusSaturationIdeal_iff (N.treeBinomialIdeal κ) hx).trans
    (N.vanishes_treeBinomialIdeal_iff_toricParam κ hwr hxs hcbs hx)

/-- Under weak reversibility and deficiency zero, saturation of the full steady-state ideal also
has the Horn--Jackson toric parametrization on the positive orthant. -/
theorem deficiencyZero_vanishes_saturatedSteadyStateIdeal_iff_toricParam
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    VanishesIdealAt (positiveTorusSaturationIdeal (N.steadyStateIdeal κ)) x ↔
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  exact (vanishes_positiveTorusSaturationIdeal_iff (N.steadyStateIdeal κ) hx).trans
    (N.deficiencyZero_vanishes_steadyStateIdeal_iff_toricParam κ hwr hδ hxs hcbs hx)

end Network
end CRNT
