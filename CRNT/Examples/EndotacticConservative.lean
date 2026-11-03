import CRNT.Persistence.ConservativeEndotacticPermanence
import CRNT.Geometry.EndotacticGlobal

/-!
# A conservative endotactic network that is neither weakly reversible nor strongly endotactic

Species `X, Y, Z` (indices `0, 1, 2`), reactions

`2X → 2Y`, `2Y → 2X`, `X → Z`, `Z → X`, `X + Y → 2X`.

* Endotactic in the standard sense (`endotacticStd`): the source `X + Y` lies on the segment
  between `2X` and `2Y`, so whenever `X + Y → 2X` increases `w`, the reaction `2X → 2Y` decreases
  `w` from a source with larger `w`-value.
* Not weakly reversible (`not_weaklyReversible`): from `2X` only `2X` and `2Y` are reachable, so
  `X + Y` is not.
* Not strongly endotactic (`not_stronglyEndotacticStd`): for `w = (1, 1, 0)`, which is not
  orthogonal to the reaction `X → Z`, every `w`-maximal source (`2X`, `2Y`, `X + Y`) has only
  `w`-neutral reactions.
* Conservative (`isConservative`, `X + Y + Z`).

So neither the weakly reversible floor nor the strongly endotactic permanence theorem applies, and
`endotacticStd_conservative_structurallyPersistent` gives persistence (`structurallyPersistent`),
and `endotacticStd_conservative_genuinePermanent` gives permanence (`genuinePermanent`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Examples
namespace EndotacticConservative

open Network

/-- `2X → 2Y`, `2Y → 2X`, `X → Z`, `Z → X`, `X + Y → 2X`. -/
abbrev net : Network (Fin 3) :=
  ⟨Fin 5, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![2, 0, 0], ![0, 2, 0]⟩ else if r = 1 then ⟨![0, 2, 0], ![2, 0, 0]⟩
    else if r = 2 then ⟨![1, 0, 0], ![0, 0, 1]⟩ else if r = 3 then ⟨![0, 0, 1], ![1, 0, 0]⟩
    else ⟨![1, 1, 0], ![2, 0, 0]⟩⟩

theorem endotacticStd : net.EndotacticStd := by
  intro w r hr
  fin_cases r
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
        at hr ⊢ <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
        at hr ⊢ <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
        at hr ⊢ <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
        at hr ⊢ <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
        at hr ⊢ <;> linarith

/-- From `2X` only `2X` and `2Y` are reachable. -/
theorem reaches_closed {c d : Complex (Fin 3)} (h : net.Reaches c d)
    (hc : c = ![2, 0, 0] ∨ c = ![0, 2, 0]) : d = ![2, 0, 0] ∨ d = ![0, 2, 0] := by
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
  obtain ⟨r, hmax, hneg⟩ := h ![1, 1, 0] ⟨2, by
    simp [wRate, Network.dotProduct, reactionVector_apply, Fin.sum_univ_three]⟩
  have h0 := hmax 0
  fin_cases r <;>
    simp [wRate, wValue, Network.dotProduct, exponentVector, reactionVector_apply, Fin.sum_univ_three]
      at hneg h0 <;> linarith

/-- `X + Y + Z` is conserved. -/
theorem isConservative : net.IsConservative := by
  refine ⟨fun _ => 1, ?_, fun _ => one_pos⟩
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro g ⟨r, rfl⟩
  fin_cases r <;> norm_num [reactionVector_apply, Fin.sum_univ_three]

/-- Every rate vector and every positive initial state give a trajectory confined to a compact
set of positive states. -/
theorem structurallyPersistent : net.StructurallyPersistent :=
  net.endotacticStd_conservative_structurallyPersistent endotacticStd isConservative

/-- Permanence: every positive class has one compact absorbing set of positive states, for every
rate vector. -/
theorem genuinePermanent (κ : net.RateConstants) : net.GenuinePermanentForRates κ :=
  net.endotacticStd_conservative_genuinePermanent endotacticStd isConservative κ

end EndotacticConservative
end Examples
end CRNT
