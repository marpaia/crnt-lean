import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

/-!
# The scale-selection step in Craciun v3's faithful-blueprint construction

Section 7.4.3 of the v3 preprint assigns additional tile scales between pre-blueprint scales.
The geometric construction supplies finitely many strict intervals; each row of its hierarchy
needs a finite strictly ordered list inside one such interval. The lemmas here discharge that
real-order step constructively, including simultaneous selection for any finite family of rows.

This file formalizes only the scale-selection subargument. It does not assert that a fan's tile
incidence data or the zero-separating hypersurface has been constructed.
-/

namespace CRNT
namespace CraciunV3

universe u

/-- Insert any finite number of distinct scales strictly inside a prescribed open interval. -/
theorem exists_strictScaleChain (n : Nat) {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ xs : List ℝ,
      xs.length = n ∧
      (∀ x ∈ xs, lo < x ∧ x < hi) ∧
      xs.Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
      exact ⟨[], by simp, by simp, by simp⟩
  | succ n ih =>
      let mid := (lo + hi) / 2
      have hlo : lo < mid := by dsimp [mid]; linarith
      have hhi : mid < hi := by dsimp [mid]; linarith
      obtain ⟨xs, hlen, hbounds, hpair⟩ := ih hhi
      refine ⟨mid :: xs, ?_, ?_, ?_⟩
      · simp [hlen]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hlo, hhi⟩
        · obtain ⟨hmid, htop⟩ := hbounds x hx
          exact ⟨lt_trans hlo hmid, htop⟩
      · rw [List.pairwise_cons]
        constructor
        · intro x hx
          exact (hbounds x hx).1
        · exact hpair

/-- A finite collection of independent blueprint rows admits simultaneous scale choices. Each
row gets its own strictly increasing chain between its two already-separated pre-blueprint scales;
finiteness makes all choices available in one function. -/
theorem exists_strictScaleChains {ι : Type u} [Fintype ι]
    (lo hi : ι → ℝ) (length : ι → Nat) (hgap : ∀ i, lo i < hi i) :
    ∃ chains : ι → List ℝ,
      ∀ i, (chains i).length = length i ∧
        (∀ x ∈ chains i, lo i < x ∧ x < hi i) ∧
        (chains i).Pairwise (· < ·) := by
  classical
  choose chains hchains using fun i => exists_strictScaleChain (length i) (hgap i)
  exact ⟨chains, hchains⟩

end CraciunV3
end CRNT
