import CRNT.Geometry.EndotacticGlobal
import CRNT.Graph.WeakReversibility

/-!
# The standard definition of endotactic networks

The library's `Endotactic` asks, for every direction `w`, that reactions whose source is
`w`-maximal among **all** sources have `⟨w, y' − y⟩ ≤ 0`. The definition of
Craciun–Nazarov–Pantea 2013 and Gopalkrishnan–Miller–Shiu 2014 compares only with the sources of
`w`-essential reactions (`⟨w, y' − y⟩ ≠ 0`): every `w`-increasing reaction must be dominated by a
`w`-decreasing reaction with a strictly larger `w`-value of its source.

`EndotacticStd` is that definition. It implies `Endotactic` (`EndotacticStd.endotactic`), and the
converse fails (`CRNT.Examples.WeakEndotactic`: `0 ⇌ X₁`, `X₂ → 0`). Weakly reversible and strongly
endotactic networks are endotactic in the standard sense.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Endotactic** (Craciun–Nazarov–Pantea; Gopalkrishnan–Miller–Shiu): every `w`-increasing
reaction is dominated by a `w`-decreasing reaction whose source has a strictly larger `w`-value. -/
def EndotacticStd (N : Network S) : Prop :=
  ∀ (w : S → ℝ) (r : N.R), 0 < N.wRate w r →
    ∃ r' : N.R, N.wRate w r' < 0 ∧ N.wValue w r < N.wValue w r'

/-- The standard definition implies the library's `Endotactic`. -/
theorem EndotacticStd.endotactic {N : Network S} (h : N.EndotacticStd) : N.Endotactic := by
  intro w r hmax
  by_contra hpos
  push Not at hpos
  obtain ⟨r', -, hlt⟩ := h w r hpos
  exact absurd (hmax r') (not_le.mpr hlt)

/-- **Weakly reversible networks are endotactic** (standard definition): along the return path
from the target of a `w`-increasing reaction to its source, the last step leaving the region
above the source's level is `w`-decreasing and starts above that level. -/
theorem WeaklyReversible.endotacticStd {N : Network S} (hwr : N.WeaklyReversible) :
    N.EndotacticStd := by
  intro w r hpos
  set v₀ := complexWValue w (N.reaction r).source
  have hstep : ∀ {d : Complex S}, N.Reaches (N.reaction r).target d →
      complexWValue w d ≤ v₀ → ∃ r' : N.R, N.wRate w r' < 0 ∧ v₀ < N.wValue w r' := by
    intro d hd hdle
    induction hd with
    | refl =>
        rw [N.wRate_eq_complexWValue_sub] at hpos
        exact absurd hdle (not_le.mpr (by linarith))
    | @tail e f _ hef ih =>
        obtain ⟨redge, hs, ht⟩ := hef
        by_cases he : v₀ < complexWValue w e
        · refine ⟨redge, ?_, ?_⟩
          · rw [N.wRate_eq_complexWValue_sub, hs, ht]; linarith
          · rw [wValue_eq_complexWValue_source, hs]; exact he
        · exact ih (not_lt.mp he)
  obtain ⟨r', h1, h2⟩ := hstep (hwr r) le_rfl
  exact ⟨r', h1, h2⟩

/-- **Strongly endotactic networks are endotactic** (standard definition). -/
theorem StronglyEndotacticStd.endotacticStd {N : Network S} (h : N.StronglyEndotacticStd) :
    N.EndotacticStd := by
  intro w r hpos
  obtain ⟨r', hmax, hneg⟩ := h.2 w ⟨r, hpos.ne'⟩
  refine ⟨r', hneg, lt_of_le_of_ne (hmax r) fun heq => ?_⟩
  -- if `r` were `w`-maximal, endotacticity would give `wRate w r ≤ 0`
  have hrmax : N.IsMaxSource w r := fun r'' => heq ▸ hmax r''
  exact absurd (h.1 w r hrmax) (not_le.mpr hpos)

end Network
end CRNT
