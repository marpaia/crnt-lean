import CRNT.Persistence.WeaklyReversibleFloor

/-!
# Bounded weakly reversible trajectories have no boundary ω-limit points

Anderson–Shiu (2010, Definition 2.11) call a bounded trajectory persistent when its ω-limit set
misses the boundary of the orthant, and prove persistence (Theorem 3.4) for weakly reversible
mass-action systems whose siphons all correspond to facets or empty faces.
`omegaPoint_positive_of_weaklyReversible_bounded` removes that facet hypothesis: every
accumulation point of a bounded positive weakly reversible trajectory is positive.  It is a
corollary of the floor `weaklyReversible_forward_floor`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Persistence of bounded weakly reversible trajectories** (Anderson–Shiu 2010, Theorem 3.4,
without the facet hypothesis). Every point approached by a bounded positive solution, in
particular every ω-limit point, is positive. -/
theorem omegaPoint_positive_of_weaklyReversible_bounded (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {M : ℝ} (hbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M)
    {w : Concentration S} (hw : ∀ ε > 0, ∃ t, 0 ≤ t ∧ dist (γ t) w < ε) : w.Positive := by
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor κ hwr hγ0 hsol hbdd
  intro s
  by_contra hle
  push Not at hle
  obtain ⟨t, ht, hd⟩ := hw (η - w s) (by linarith)
  have h1 := lt_of_le_of_lt (dist_le_pi_dist _ _ s) hd
  rw [Real.dist_eq] at h1
  have := (abs_lt.mp h1).2
  linarith [hfloor t ht s]

end Network
end CRNT
