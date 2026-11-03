import CRNT.Stoich.Vector
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Rational reaction vectors

The stoichiometric reaction vector has integer, hence rational, coordinates.  This
small foundational module exposes those rational coordinates without importing any
of the decision-procedure stack that consumes them.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The rational reaction coefficient `target s - source s` of reaction `r` at species `s`. -/
def reactionCoeffQ (N : Network S) (r : N.R) (s : S) : ℚ :=
  ((N.reaction r).target s : ℚ) - ((N.reaction r).source s : ℚ)

@[simp] theorem cast_reactionCoeffQ (N : Network S) (r : N.R) (s : S) :
    ((N.reactionCoeffQ r s : ℚ) : ℝ) = N.reactionVector r s := by
  simp [reactionCoeffQ, reactionVector_apply]

end Network
end CRNT
