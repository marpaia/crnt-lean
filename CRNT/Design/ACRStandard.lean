import CRNT.Design.ACR
import CRNT.Deficiency.DeficiencyOne

/-!
# Standard fixed-parameter absolute concentration robustness

The classical Shinar--Feinberg notion of ACR fixes the rate constants and asks that one
species have the same concentration at all positive steady states for those rate
constants.  The older `HasACR` predicate in this development quantifies a *single* value
across every choice of rate constants, which is a much stronger, parameter-independent
property.

This file adds the standard fixed-`κ` notion without changing the existing API.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Standard ACR at fixed rate constants. -/
def HasACRAt (N : Network S) (κ : N.RateConstants) (s : S) : Prop :=
  ∃ v : ℝ, ∀ x : Concentration S,
    x.Positive → N.IsMassActionSteadyState κ x → x s = v

/-- Standard structural ACR: every choice of positive rate constants has ACR, but the
robust value is allowed to depend on those rate constants. -/
def HasStandardACR (N : Network S) (s : S) : Prop :=
  ∀ κ : N.RateConstants, N.HasACRAt κ s

/-- Explicit name for the older, stronger parameter-independent notion. -/
def HasUniformACR (N : Network S) (s : S) : Prop := N.HasACR s

/-- Uniform ACR implies standard ACR. -/
theorem HasACR.hasStandardACR {N : Network S} {s : S}
    (h : N.HasACR s) : N.HasStandardACR s := by
  rcases h with ⟨v, hv⟩
  intro κ
  exact ⟨v, fun x hx hss => hv κ x hx hss⟩

/-- At fixed `κ`, pairwise equality of the output coordinate across positive steady states
is equivalent to `HasACRAt`, provided one positive steady state exists. -/
theorem hasACRAt_iff_pairwise {N : Network S} (κ : N.RateConstants) (s : S)
    (hne : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACRAt κ s ↔
      ∀ x y : Concentration S,
        x.Positive → N.IsMassActionSteadyState κ x →
        y.Positive → N.IsMassActionSteadyState κ y → x s = y s := by
  constructor
  · rintro ⟨v, hv⟩ x y hx hxs hy hys
    rw [hv x hx hxs, hv y hy hys]
  · intro h
    rcases hne with ⟨x₀, hx₀, hss₀⟩
    refine ⟨x₀ s, ?_⟩
    intro x hx hss
    exact h x x₀ hx hss hx₀ hss₀

/-- Classical Shinar--Feinberg structural data: deficiency one and two nonterminal
complexes differing only in the candidate robust species.  No distinct-linkage-class
assumption is imposed here. -/
structure StandardShinarFeinbergHypotheses (N : Network S) (s : S) where
  c : Complex S
  d : Complex S
  hc : c ∈ N.complexes
  hd : d ∈ N.complexes
  nonTerminalC : ¬ N.IsTerminalSLC c
  nonTerminalD : ¬ N.IsTerminalSLC d
  differOnlyAt : ∀ t, t ≠ s → c t = d t
  differAt : c s ≠ d s
  deficiencyOne : N.DeficiencyOne

/-- Fixed-parameter monomial-ratio pinning, which is the exact deficiency-one ingredient
needed by the algebraic ACR lever. -/
def StandardShinarFeinbergHypotheses.PinnedRatioAt
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) : Prop :=
  ∀ x y : Concentration S,
    x.Positive → N.IsMassActionSteadyState κ x →
    y.Positive → N.IsMassActionSteadyState κ y →
    H.c.massActionMonomial x * H.d.massActionMonomial y =
      H.c.massActionMonomial y * H.d.massActionMonomial x

/-- Standard ACR from fixed-parameter pinning. -/
theorem HasACRAt.of_standardShinarFeinbergPinnedRatio
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) (hpin : H.PinnedRatioAt κ)
    (hne : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACRAt κ s := by
  rw [N.hasACRAt_iff_pairwise κ s hne]
  intro x y hx hxs hy hys
  exact pin_of_pinned_ratio hx hy H.c H.d s H.differOnlyAt H.differAt
    (hpin x y hx hxs hy hys)

/-- If the deficiency-one theory supplies fixed-`κ` pinning for every rate vector, the
network has standard ACR.  This is the clean theorem interface for completing the full
Shinar--Feinberg theorem from the existing deficiency-one machinery. -/
theorem HasStandardACR.of_pinnedRatio
    {N : Network S} {s : S} (H : N.StandardShinarFeinbergHypotheses s)
    (hpin : ∀ κ : N.RateConstants, H.PinnedRatioAt κ)
    (hne : ∀ κ : N.RateConstants,
      ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasStandardACR s := by
  intro κ
  exact HasACRAt.of_standardShinarFeinbergPinnedRatio H κ (hpin κ) (hne κ)

end Network
end CRNT
