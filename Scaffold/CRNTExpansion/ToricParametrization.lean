import CRNT.Algebra.PositiveTorusIdeals
import CRNT.Equilibria.ComplexBalanceGeometry

/-!
# Algebraic-to-geometric toric parametrization bridge

The library already proves both sides of the classical toric picture:

* the tree-binomial ideal cuts out the positive complex-balanced set; and
* the positive complex-balanced set is parametrized by `x* * exp(mu)` with
  `mu` orthogonal to the stoichiometric subspace.

This scaffold composes those results into direct ideal-zero-set parametrization theorems.  Under
weak reversibility and deficiency zero, the same parametrization describes the positive zero set of
the full steady-state ideal.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive zeros of the tree-binomial ideal are exactly the Horn--Jackson toric parametrization. -/
theorem vanishes_treeBinomialIdeal_iff_toricParam
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    VanishesIdealAt (N.treeBinomialIdeal κ) x <->
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  constructor
  · intro hvan
    have hcb : N.IsComplexBalanced κ x :=
      (N.vanishes_treeBinomialIdeal_iff_complexBalanced κ hwr hx).mp hvan
    exact (N.mem_positiveComplexBalancedSet_iff_toric κ hwr hxs hcbs x).mp ⟨hx, hcb⟩
  · rintro ⟨μ, hμ, rfl⟩
    have hcb : N.IsComplexBalanced κ (toricParam xstar μ) :=
      N.toricParam_complexBalanced κ hxs hcbs hμ
    exact (N.vanishes_treeBinomialIdeal_iff_complexBalanced κ hwr
      (toricParam_positive hxs μ)).mpr hcb

/-- Positive zeros of the complex-balance ideal have the same Horn--Jackson toric
parametrization.  Weak reversibility enters through the global log-ratio orthogonality direction of
the Horn--Jackson characterization. -/
theorem vanishes_complexBalanceIdeal_iff_toricParam
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    VanishesIdealAt (N.complexBalanceIdeal κ) x <->
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  rw [N.vanishes_complexBalanceIdeal_iff κ x]
  constructor
  · intro hcb
    exact (N.mem_positiveComplexBalancedSet_iff_toric κ hwr hxs hcbs x).mp ⟨hx, hcb⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact N.toricParam_complexBalanced κ hxs hcbs hμ

/-- In a weakly-reversible deficiency-zero system, positive zeros of the species steady-state ideal
have the same toric parametrization. -/
theorem deficiencyZero_vanishes_steadyStateIdeal_iff_toricParam
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    VanishesIdealAt (N.steadyStateIdeal κ) x <->
      ∃ μ ∈ orthSum N.stoichSubspace, x = toricParam xstar μ := by
  exact (N.deficiencyZero_steadyStateIdeal_positiveTorusEquivalent_treeBinomialIdeal
    κ hwr hδ x hx).trans
      (N.vanishes_treeBinomialIdeal_iff_toricParam κ hwr hxs hcbs hx)

end Network
end CRNT
