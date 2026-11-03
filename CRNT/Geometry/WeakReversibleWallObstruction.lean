import CRNT.Geometry.FanWallsCrossed

/-!
# Weak reversibility obstructs globally inward active walls

The active-wall estimates in `ToricUniformWallMargin` require every reaction vector to have
nonnegative pairing with the wall normal. For a weakly reversible network, this forces all such
normal components to vanish: a nondecreasing potential must be constant along each directed cycle.
Consequently an active wall cannot satisfy that premise. These estimates cannot construct
the separating surfaces needed for general complex-balanced permanence.

The valid toric construction must instead control the **rate-weighted total velocity** in a
region of concentration space; it cannot require every reaction to point inward.
-/

namespace CRNT.Network

open scoped InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A potential that is nondecreasing along every reaction is nondecreasing along every path. -/
theorem complexPotential_le_of_reaches_of_nonneg
    (N : Network S) {n : S → ℝ}
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    {c d : Complex S} (hcd : N.Reaches c d) :
    complexPotential n c ≤ complexPotential n d := by
  induction hcd with
  | refl => exact le_rfl
  | tail _ hedge ih =>
    obtain ⟨r, rfl, rfl⟩ := hedge
    have hr := hinward r
    rw [N.inner_reactionVector_eq_potential_sub] at hr
    exact ih.trans (sub_nonneg.mp hr)

/-- A globally nonnegative reaction pairing vanishes on a weakly reversible network. -/
theorem WeaklyReversible.inner_reactionVector_eq_zero_of_nonneg
    {N : Network S} (hwr : N.WeaklyReversible) {n : S → ℝ}
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ)
    (r : N.R) :
    ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ = 0 := by
  have hreturn := N.complexPotential_le_of_reaches_of_nonneg hinward (hwr r)
  rw [N.inner_reactionVector_eq_potential_sub]
  exact le_antisymm (sub_nonpos.mpr hreturn) (by
    simpa only [N.inner_reactionVector_eq_potential_sub] using hinward r)

/-- Mutual reachability prevents an active normal from being inward on every reaction. -/
theorem not_activeWall_of_all_reactions_nonneg
    (N : Network S) {n : S → ℝ}
    (hinward : ∀ r : N.R, 0 ≤ ⟪toEuclid n, toEuclid (N.reactionVector r)⟫_ℝ) :
    ¬ N.ActiveWall n := by
  rintro ⟨c, d, hcd, hdc, hne⟩
  exact hne (le_antisymm
    (N.complexPotential_le_of_reaches_of_nonneg hinward hcd)
    (N.complexPotential_le_of_reaches_of_nonneg hinward hdc))

end CRNT.Network
