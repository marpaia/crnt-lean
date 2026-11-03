import Scaffold.CRNTExpansion.Elimination
import Scaffold.CRNTExpansion.PositiveTorusSaturation

/-!
# Interaction of semantic elimination and positive-torus saturation

The two algebraic operations are kept semantically separate.  Saturating first can only enlarge the
ambient ideal, so its elimination ideal contains the elimination of the original ideal.  This is a
safe algebraic statement that does not assume a Gröbner basis or an unjustified commutation theorem
between saturation and elimination.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Eliminating after saturation contains the elimination ideal of the unsaturated system. -/
theorem eliminationIdeal_le_eliminationIdeal_positiveTorusSaturation
    (I : Ideal (MvPolynomial S ℝ)) (U : Set S) :
    eliminationIdeal I U ≤ eliminationIdeal (positiveTorusSaturationIdeal I) U :=
  eliminationIdeal_mono (le_positiveTorusSaturationIdeal I) U

/-- CRNT specialization for the mass-action steady-state ideal. -/
theorem steadyStateEliminationIdeal_le_saturatedSteadyStateEliminationIdeal
    (N : Network S) (κ : N.RateConstants) (U : Set S) :
    N.steadyStateEliminationIdeal κ U ≤
      eliminationIdeal (positiveTorusSaturationIdeal (N.steadyStateIdeal κ)) U :=
  eliminationIdeal_le_eliminationIdeal_positiveTorusSaturation
    (N.steadyStateIdeal κ) U

/-- CRNT specialization for the tree-binomial ideal. -/
theorem treeBinomialEliminationIdeal_le_saturatedTreeBinomialEliminationIdeal
    (N : Network S) (κ : N.RateConstants) (U : Set S) :
    N.treeBinomialEliminationIdeal κ U ≤
      eliminationIdeal (positiveTorusSaturationIdeal (N.treeBinomialIdeal κ)) U :=
  eliminationIdeal_le_eliminationIdeal_positiveTorusSaturation
    (N.treeBinomialIdeal κ) U

end Network
end CRNT
