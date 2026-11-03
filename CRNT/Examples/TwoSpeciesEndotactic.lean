import CRNT.Persistence.TwoSpeciesPermanence
import CRNT.Geometry.EndotacticGlobal

/-!
# A two-species endotactic network outside the earlier persistence theorems

Species `X, Y` (indices `0, 1`), reactions

`2X → 2Y`, `2Y → 2X`, `0 → X`, `X → 0`, `X + Y → 2X`.

* Endotactic in the standard sense (`endotacticStd`): the reversible pairs dominate each other,
  and `X + Y → 2X` is dominated by `2X → 2Y` (the source `X + Y` lies between `2X` and `2Y`).
* Not weakly reversible (`not_weaklyReversible`): from `2X` only `2X` and `2Y` are reachable.
* Not strongly endotactic (`not_stronglyEndotacticStd`): for `w = (1, 1)`, which is not
  orthogonal to `0 → X`, the `w`-maximal sources `2X`, `2Y`, `X + Y` have only `w`-neutral
  reactions.
* Not conservative: `0 → X` changes the total of every positive weighting.

The weakly reversible floor needs weak reversibility and a bounded trajectory, and the strongly
endotactic permanence theorem needs strong endotacticity; neither applies.  The two-species
theorem gives structural persistence (`structurallyPersistent`) and permanence
(`structurallyPermanent`, trajectory form `genuinePermanent`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Examples
namespace TwoSpeciesEndotactic

open Network

/-- `2X → 2Y`, `2Y → 2X`, `0 → X`, `X → 0`, `X + Y → 2X`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 5, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0], ![0, 2]⟩ else if r = 1 then ⟨![0, 2], ![2, 0]⟩
    else if r = 2 then ⟨![0, 0], ![1, 0]⟩ else if r = 3 then ⟨![1, 0], ![0, 0]⟩
    else ⟨![1, 1], ![2, 0]⟩⟩

theorem endotacticStd : net.EndotacticStd := by
  intro w r hr
  fin_cases r
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
        Fin.sum_univ_two] at hr ⊢ <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
        Fin.sum_univ_two] at hr ⊢ <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
        Fin.sum_univ_two] at hr ⊢ <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
        Fin.sum_univ_two] at hr ⊢ <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
        Fin.sum_univ_two] at hr ⊢ <;> linarith

/-- From `2X` only `2X` and `2Y` are reachable. -/
theorem reaches_closed {c d : Complex (Fin 2)} (h : net.Reaches c d)
    (hc : c = ![2, 0] ∨ c = ![0, 2]) : d = ![2, 0] ∨ d = ![0, 2] := by
  induction h with
  | refl => exact hc
  | @tail b e _ hbe ih =>
    obtain ⟨r, hs, ht⟩ := hbe
    rw [← ht]
    rcases ih with hb | hb <;> rw [hb] at hs <;> fin_cases r <;>
      first
      | (left; rfl)
      | (right; rfl)
      | (exfalso; revert hs; decide)

theorem not_weaklyReversible : ¬ net.WeaklyReversible := by
  intro h
  have := reaches_closed (h 4) (Or.inl rfl)
  revert this
  decide

theorem not_stronglyEndotacticStd : ¬ net.StronglyEndotacticStd := by
  rintro ⟨-, h⟩
  obtain ⟨r, hmax, hneg⟩ := h ![1, 1] ⟨2, by
    simp [wRate, Network.dotProduct, reactionVector_apply, Fin.sum_univ_two]⟩
  have h0 := hmax 0
  fin_cases r <;>
    simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply,
      Fin.sum_univ_two] at hneg h0 <;> linarith

/-- No strictly positive conservation law: `0 → X` changes `w · x` by `w 0 > 0`. -/
theorem not_isConservative : ¬ net.IsConservative := by
  rintro ⟨w, hw, hpos⟩
  have h := (mem_orthSum.mp hw) _ (net.reactionVector_mem_stoichSubspace 2)
  simp [reactionVector_apply, Fin.sum_univ_two] at h
  linarith [hpos 0]

theorem structurallyPersistent : net.StructurallyPersistent :=
  net.twoSpecies_endotacticStd_structurallyPersistent (by simp) endotacticStd

/-- Every positive compatibility class has one compact absorbing set of positive states. -/
theorem structurallyPermanent : net.StructurallyPermanent :=
  net.twoSpecies_endotacticStd_structurallyPermanent (by simp) endotacticStd

/-- Trajectory form: every forward solution from a positive class enters one compact set of the
class and stays there. -/
theorem genuinePermanent (κ : net.RateConstants) : net.GenuinePermanentForRates κ :=
  net.twoSpecies_endotacticStd_genuinePermanent (by simp) endotacticStd κ

/-- Tempered rates: one compact absorbing set per positive class and rate band. -/
theorem permanent_varK {ρ : ℝ} (hρ : 0 < ρ) (xref : Concentration (Fin 2))
    (hxref : xref.Positive) :
    ∃ K : Set (Concentration (Fin 2)), IsCompact K ∧ K ⊆ net.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → net.RateConstants, (∀ t r, ρ ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ρ) →
      ∀ x₀ ∈ net.positiveCompatibilityClass xref, ∀ Γ : ℝ → Concentration (Fin 2), Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (net.massActionVectorField (κ t) (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K :=
  net.twoSpecies_endotacticStd_permanent_varK (by simp) endotacticStd hρ xref hxref

end TwoSpeciesEndotactic
end Examples
end CRNT
