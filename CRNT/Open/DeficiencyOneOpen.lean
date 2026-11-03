import CRNT.Open.DeficiencyZeroOpen
import CRNT.Theorems.DeficiencyOne.Theorem
import CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence

/-!
# The deficiency one theorem for fully open systems (CFSTR form)

For the fully open extension the positive orthant is a single compatibility class
(`CRNT.Network.fullyOpen_positiveCompatibilityClass_eq`), so the deficiency one theorem takes
its open-system form (Feinberg 1995; Feinberg 2019, CFSTR chapter): under the deficiency one
hypotheses the reactor has **at most one** positive steady state for every choice of rate
constants, none on the boundary, and, if the open network is moreover weakly reversible of
deficiency one, **exactly one**.

Main results:
* `CRNT.Network.openDeficiencyOne_atMostOne_positive`.
* `CRNT.Network.openDeficiencyOne_atMostOne_nonneg`.
* `CRNT.Network.openDeficiencyOne_existsUnique_positive`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Deficiency one theorem, open form (uniqueness).** -/
theorem openDeficiencyOne_atMostOne_positive (N : Network S)
    (h : N.fullyOpen.DeficiencyOneHypotheses) (κ : RateConstants N.fullyOpen)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hxs : N.fullyOpen.IsMassActionSteadyState κ x)
    (hys : N.fullyOpen.IsMassActionSteadyState κ y) : x = y := by
  have hmem : ∀ z : Concentration S, z.Positive →
      z ∈ N.fullyOpen.positiveCompatibilityClass (fun _ => 1) := by
    intro z hz; rw [fullyOpen_positiveCompatibilityClass_eq]; exact hz
  exact N.fullyOpen.deficiencyOne_uniqueness h κ (fun _ => 1) (fun _ => one_pos)
    (hmem x hx) hxs (hmem y hy) hys

/-- Under the deficiency one hypotheses the open reactor has at most one steady state in the
closed nonnegative orthant. -/
theorem openDeficiencyOne_atMostOne_nonneg (N : Network S)
    (h : N.fullyOpen.DeficiencyOneHypotheses) (κ : RateConstants N.fullyOpen)
    {x y : Concentration S} (hx : x.Nonnegative) (hy : y.Nonnegative)
    (hxs : N.fullyOpen.IsMassActionSteadyState κ x)
    (hys : N.fullyOpen.IsMassActionSteadyState κ y) : x = y :=
  N.openDeficiencyOne_atMostOne_positive h κ (fullyOpen_steadyState_positive N κ hx hxs)
    (fullyOpen_steadyState_positive N κ hy hys) hxs hys

/-- **Deficiency one theorem, open form (existence and uniqueness).** -/
theorem openDeficiencyOne_existsUnique_positive (N : Network S)
    (h : N.fullyOpen.DeficiencyOneHypotheses) (hwr : N.fullyOpen.WeaklyReversible)
    (hδ : N.fullyOpen.DeficiencyOne) (κ : RateConstants N.fullyOpen) :
    ∃! x : Concentration S, x.Positive ∧ N.fullyOpen.IsMassActionSteadyState κ x := by
  obtain ⟨x, hxmem, hxs⟩ := N.fullyOpen.weaklyReversible_deficiencyOne_exists_positive_steadyState
    hwr hδ κ (fun _ => 1) (fun _ => one_pos)
  rw [fullyOpen_positiveCompatibilityClass_eq] at hxmem
  exact ⟨x, ⟨hxmem, hxs⟩, fun y ⟨hy, hys⟩ =>
    N.openDeficiencyOne_atMostOne_positive h κ hy hxmem hys hxs⟩

end Network

end CRNT
