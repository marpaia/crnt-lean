import CRNT.Multistationarity.TrueSRMinimalChord
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The two-weight cyclic gain inequality

`no_strict_gain_net'` carries a **single** weight per cycle position, which forces
`hrep` — the two edges at a position must share their representative.  That is exactly what
fails when a causal closed walk is split at a repeated reaction vertex: at the closing position
the left and right edges come from *different* channels of the same true reaction, and the cause
channels along an orbit are provably distinct (`trueInternalCause_injective_on_orbit`), so the
mismatch is unavoidable.

The fix is to carry two weight families.  The telescoped conclusion is then not `False` but a
comparison of their products:

  `∏ aL < ∏ aR`.

This is what makes the repeated-vertex case work.  Splitting at a *minimal* repeat gives two
genuine cycles, both through the repeated vertex, and their closing positions carry **reciprocal**
weight ratios `|α_{r_j}|/|α_{r_i}|` and `|α_{r_i}|/|α_{r_j}|`.  Applying this lemma to each gives
`|α_{r_j}| < |α_{r_i}|` and `|α_{r_i}| < |α_{r_j}|` — a contradiction, with no appeal to `hSR.2`.
-/

namespace CRNT.Network.TrueSRCycle

open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- **Two-weight cyclic gain.**  With a separate weight family on each side, the pointwise
strict gain inequalities telescope to a strict comparison of the weight products. -/
theorem two_weight_gain (C : N.TrueSRCycle n) (hsc : C.SCycleNet)
    (hLpos : ∀ i, 0 < (C.leftEdge i).netCoeff)
    (hRpos : ∀ i, 0 < (C.rightEdge i).netCoeff)
    (aL aR : Fin n → ℝ) (haL : ∀ i, 0 < aL i) (haR : ∀ i, 0 < aR i)
    (hineq : ∀ i, (C.leftEdge (finRotate n i)).netCoeff * aL (finRotate n i) <
      (C.rightEdge i).netCoeff * aR i) :
    (∏ i, aL i) < ∏ i, aR i := by
  haveI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty
  -- multiply the pointwise inequalities
  have hprod : (∏ i, (C.leftEdge (finRotate n i)).netCoeff * aL (finRotate n i))
      < ∏ i, (C.rightEdge i).netCoeff * aR i := by
    refine prod_lt_prod_of_nonempty₀ (fun i _ => ?_) (fun i _ => hineq i) hne
    exact mul_pos (hLpos _) (haL _)
  -- split each side and reindex the left one along `finRotate`
  rw [prod_mul_distrib, prod_mul_distrib,
    Equiv.prod_comp (finRotate n) (fun i => (C.leftEdge i).netCoeff),
    Equiv.prod_comp (finRotate n) (fun i => aL i)] at hprod
  rw [hsc] at hprod
  have hRp : 0 < ∏ i, (C.rightEdge i).netCoeff :=
    prod_pos (fun i _ => hRpos i)
  exact lt_of_mul_lt_mul_left hprod hRp.le

end CRNT.Network.TrueSRCycle
