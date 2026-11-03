import CRNT.Design.ShinarFeinbergTheorem
import CRNT.Deficiency.DeficiencyOneLinkageScalars

/-!
# Closing the cross-linkage Shinar--Feinberg reduction

This module records the cross-class log-ratio consequence of the standard
Shinar--Feinberg theorem and keeps the historical linkage-scalar compatibility API.
The direct pinned-ratio theorem in `ShinarFeinbergTheorem` is independent of this
module, so the implications below are non-circular.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Cross-class log-monomial-ratio pinning for the standard Shinar--Feinberg data. -/
def StandardShinarFeinbergHypotheses.CrossClassRatioPinned
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s) : Prop :=
  ∀ (κ : N.RateConstants) (x y : Concentration S),
    x.Positive → N.IsMassActionSteadyState κ x →
    y.Positive → N.IsMassActionSteadyState κ y →
    N.logMonomialRatio x y ⟨H.c, H.hc⟩ =
      N.logMonomialRatio x y ⟨H.d, H.hd⟩

/-- The standard Shinar--Feinberg hypotheses imply the cross-class log-ratio condition. -/
theorem standardShinarFeinberg_crossClassRatioPinned
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s) :
    H.CrossClassRatioPinned := by
  intro κ x y hx hxs hy hys
  apply (N.logMonomialRatio_eq_iff_of_differOnlyAt hx hy H.differOnlyAt
    (by exact_mod_cast H.differAt)).2
  exact shinarFeinberg_species_coordinate_eq H κ hx hxs hy hys

/-- The pinned-ratio theorem, exposed under the historical linkage-scalar entry point. -/
theorem shinarFeinberg_pinnedRatioAt_via_linkageScalars
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) : H.PinnedRatioAt κ := by
  exact shinarFeinberg_pinnedRatioAt H κ

/-- Classical fixed-rate ACR through the compatibility entry point. -/
theorem shinarFeinberg_ACRAt_via_linkageScalars
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    (hne : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACRAt κ s := by
  exact HasACRAt.of_standardShinarFeinbergPinnedRatio
    H κ (N.shinarFeinberg_pinnedRatioAt_via_linkageScalars H κ) hne

end Network
end CRNT
