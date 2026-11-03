import CRNT.Design.ACRStandard
import CRNT.Design.ACRUnconditional
import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.SignedDrainage

/-!
# The Shinar--Feinberg absolute-concentration-robustness theorem

This module states the classical theorem with the standard fixed-rate semantics.
The only hard kernel statement is isolated as `shinarFeinberg_pinnedRatioAt`: for a
deficiency-one CRN, two nonterminal complexes differing in exactly one species have a
steady-state monomial ratio independent of the chosen positive steady state at fixed
rate constants.

The same-linkage-class branch is already supported by the existing deficiency-one ratio
machinery.  The cross-linkage-class branch is the genuine Shinar--Feinberg deficiency-one
argument and is left as the localized proof frontier here.  Everything downstream is
fully separated from that frontier.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Standard ACR whenever a positive steady state exists.  This avoids treating
nonexistence as a robustness statement. -/
def HasConditionalStandardACR (N : Network S) (s : S) : Prop :=
  ∀ κ : N.RateConstants,
    (∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) →
      N.HasACRAt κ s

/-- **Shinar--Feinberg pinned-ratio theorem, fixed-rate form.**

For any deficiency-one network, if two nonterminal complexes differ in exactly one
species, their monomial ratio is constant across all positive steady states for fixed
rate constants.

NOTE (see `docs/session-addendum.md` §5).  `Design/ShinarFeinbergCrossClass.lean` appears to
prove this statement as `shinarFeinberg_pinnedRatioAt_via_linkageScalars`, and a
normalized-statement search flags it as a transferable proof.  It is not.  That module is on
the frontier ledger and has never elaborated: its proof reads `H.toShinarFeinbergHypotheses`,
`H.deficiencyOneHypotheses`, `H.c_nonterminal` and `H.d_nonterminal`, none of which exist on
`StandardShinarFeinbergHypotheses` (whose actual fields are `nonTerminalC` / `nonTerminalD`,
with no `extends`).  It is a sketch against a nonexistent API, so the mathematics is *not*
present downstream.  Closing this needs either the structure extended to carry a
`ShinarFeinbergHypotheses` and the deficiency-one hypotheses, or the cross-class argument
rewritten against the real API. -/
theorem shinarFeinberg_pinnedRatioAt
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants) :
    H.PinnedRatioAt κ := by
  intro x y hx hxs hy hys
  obtain ⟨g, hg0, hline⟩ :=
    N.exists_kineticImage_smul_of_deficiencyOne κ H.deficiencyOne
  obtain ⟨a, ha⟩ := hline hxs
  obtain ⟨b, hb⟩ := hline hys
  have hb0 : b ≠ 0 := by
    intro hbz
    have hker : N.kineticMap κ (N.complexMonomialVector y) = 0 := by
      rw [hb, hbz, zero_smul]
    have hc0 := N.kineticMap_eq_zero_of_not_terminal κ hker
      (c := ⟨H.c, H.hc⟩) H.nonTerminalC
    have hcpos : 0 < N.complexMonomialVector y ⟨H.c, H.hc⟩ := by
      rw [complexMonomialVector_apply]
      exact Complex.massActionMonomial_pos hy H.c
    exact hcpos.ne' hc0
  let w : N.ComplexIdx → ℝ :=
    b • N.complexMonomialVector x - a • N.complexMonomialVector y
  have hwker : N.kineticMap κ w = 0 := by
    dsimp [w]
    rw [map_sub, map_smul, map_smul, ha, hb]
    simp [smul_smul, mul_comm]
  have hwc := N.kineticMap_eq_zero_of_not_terminal κ hwker
    (c := ⟨H.c, H.hc⟩) H.nonTerminalC
  have hwd := N.kineticMap_eq_zero_of_not_terminal κ hwker
    (c := ⟨H.d, H.hd⟩) H.nonTerminalD
  simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    complexMonomialVector_apply] at hwc hwd
  have hcEq : b * H.c.massActionMonomial x = a * H.c.massActionMonomial y :=
    sub_eq_zero.mp hwc
  have hdEq : b * H.d.massActionMonomial x = a * H.d.massActionMonomial y :=
    sub_eq_zero.mp hwd
  apply mul_left_cancel₀ hb0
  calc
    b * (H.c.massActionMonomial x * H.d.massActionMonomial y) =
        (b * H.c.massActionMonomial x) * H.d.massActionMonomial y := by ring
    _ = (a * H.c.massActionMonomial y) * H.d.massActionMonomial y := by rw [hcEq]
    _ = (a * H.d.massActionMonomial y) * H.c.massActionMonomial y := by ring
    _ = (b * H.d.massActionMonomial x) * H.c.massActionMonomial y := by rw [← hdEq]
    _ = b * (H.c.massActionMonomial y * H.d.massActionMonomial x) := by ring

/-- **Classical Shinar--Feinberg ACR theorem at fixed rate constants.** -/
theorem shinarFeinberg_ACRAt
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    (hne : ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACRAt κ s := by
  exact HasACRAt.of_standardShinarFeinbergPinnedRatio
    H κ (shinarFeinberg_pinnedRatioAt H κ) hne

/-- Structural form: every rate vector that admits a positive steady state has ACR in
the distinguished species. -/
theorem shinarFeinberg_conditionalStandardACR
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s) :
    N.HasConditionalStandardACR s := by
  intro κ hne
  exact shinarFeinberg_ACRAt H κ hne

/-- If positive steady states exist for every positive rate vector, the usual
`HasStandardACR` predicate follows. -/
theorem shinarFeinberg_standardACR
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (hex : ∀ κ : N.RateConstants,
      ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasStandardACR s := by
  intro κ
  exact shinarFeinberg_ACRAt H κ (hex κ)

/-- Pairwise formulation of the theorem, often the most convenient downstream form. -/
theorem shinarFeinberg_species_coordinate_eq
    {N : Network S} {s : S}
    (H : N.StandardShinarFeinbergHypotheses s)
    (κ : N.RateConstants)
    {x y : Concentration S}
    (hx : x.Positive) (hxs : N.IsMassActionSteadyState κ x)
    (hy : y.Positive) (hys : N.IsMassActionSteadyState κ y) :
    x s = y s := by
  exact pin_of_pinned_ratio hx hy H.c H.d s H.differOnlyAt H.differAt
    (shinarFeinberg_pinnedRatioAt H κ x y hx hxs hy hys)

end Network
end CRNT
