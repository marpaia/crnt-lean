import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Monotone.Basic

/-!
# Reduction to sorted points

For an ascending weight vector `N` and a point `y` at which `⟨N, y⟩` is minimal among all
rearrangements of `y`, any property `V` that is invariant under swapping two coordinates on
which `N` agrees holds at `y` as soon as it holds at every antitone rearrangement with the same
value.  The proof bubble-sorts `y`: an adjacent ascent can be swapped, minimality forces `N` to
agree there, and the potential `∑ r * y r` strictly decreases, so induction on the number of
rearrangements of smaller potential terminates.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset

variable {n : ℕ}

/-- The dot product on `Fin n → ℝ`. -/
def fdot (a x : Fin n → ℝ) : ℝ := ∑ q, a q * x q

theorem antitone_of_adjacent (x : Fin n → ℝ)
    (h : ∀ (q : Fin n) (hq : q.val + 1 < n), x ⟨q.val + 1, hq⟩ ≤ x q) : Antitone x := by
  have key : ∀ d (i j : Fin n), j.val = i.val + d → x j ≤ x i := by
    intro d
    induction d with
    | zero => intro i j hij; rw [show j = i from Fin.ext (by omega)]
    | succ d ih =>
        intro i j hij
        have hj1 : (j.val - 1) + 1 < n := by omega
        have hstep := h ⟨j.val - 1, by omega⟩ hj1
        have hjeq : (⟨(j.val - 1) + 1, hj1⟩ : Fin n) = j := Fin.ext (by simp; omega)
        rw [hjeq] at hstep
        exact le_trans hstep (ih i ⟨j.val - 1, by omega⟩ (by simp; omega))
  intro i j hij
  exact key (j.val - i.val) i j (by have : i.val ≤ j.val := hij; omega)

theorem fdot_comp_swap (N x : Fin n → ℝ) (q r : Fin n) (hqr : q ≠ r) :
    fdot N (x ∘ Equiv.swap q r) - fdot N x = (N r - N q) * (x q - x r) := by
  have e : fdot N (x ∘ Equiv.swap q r) = fdot (N ∘ Equiv.swap q r) x := by
    unfold fdot
    rw [← Equiv.sum_comp (Equiv.swap q r) (fun a => (N ∘ Equiv.swap q r) a * x a)]
    refine sum_congr rfl fun a _ => ?_
    simp [Equiv.swap_apply_self]
  rw [e]
  unfold fdot
  rw [← sum_sub_distrib]
  rw [Fintype.sum_eq_add q r hqr (fun a ha => by
    simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne ha.1 ha.2]; ring)]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- The bubble-sort potential. -/
def bubblePot (x : Fin n → ℝ) : ℝ := ∑ r, (r.val : ℝ) * x r

theorem bubblePot_swap (x : Fin n → ℝ) (q : Fin n) (hq : q.val + 1 < n) :
    bubblePot (x ∘ Equiv.swap q ⟨q.val + 1, hq⟩) - bubblePot x =
      x q - x ⟨q.val + 1, hq⟩ := by
  have hne : q ≠ ⟨q.val + 1, hq⟩ := fun h => by have := congrArg Fin.val h; simp at this
  have := fdot_comp_swap (fun r => (r.val : ℝ)) x q ⟨q.val + 1, hq⟩ hne
  unfold bubblePot; unfold fdot at this
  rw [this]; push_cast; ring

theorem sort_reduce (N : Fin n → ℝ) (hN : Monotone N) (V : (Fin n → ℝ) → Prop)
    (hVswap : ∀ (x : Fin n → ℝ) (q r : Fin n), N q = N r →
      (V (x ∘ Equiv.swap q r) ↔ V x))
    (y : Fin n → ℝ) (hmin : ∀ ρ : Equiv.Perm (Fin n), fdot N y ≤ fdot N (y ∘ ρ))
    (hsorted : ∀ ρ : Equiv.Perm (Fin n), Antitone (y ∘ ρ) → fdot N (y ∘ ρ) = fdot N y →
      V (y ∘ ρ)) :
    ∀ ρ : Equiv.Perm (Fin n), fdot N (y ∘ ρ) = fdot N y → V (y ∘ ρ) := by
  intro ρ
  induction hc : (Finset.univ.filter fun ρ' : Equiv.Perm (Fin n) =>
      bubblePot (y ∘ ρ') < bubblePot (y ∘ ρ)).card using Nat.strong_induction_on
    generalizing ρ with
  | _ c ih =>
  intro heq
  by_cases hanti : Antitone (y ∘ ρ)
  · exact hsorted ρ hanti heq
  · -- an adjacent ascent
    have : ∃ (q : Fin n) (hq : q.val + 1 < n), (y ∘ ρ) q < (y ∘ ρ) ⟨q.val + 1, hq⟩ := by
      by_contra hcon
      push Not at hcon
      exact hanti (antitone_of_adjacent _ hcon)
    obtain ⟨q, hq, hlt⟩ := this
    set r : Fin n := ⟨q.val + 1, hq⟩ with hr
    have hqr : q ≠ r := fun h => by have := congrArg Fin.val h; simp [hr] at this
    set τ := Equiv.swap q r
    have hcomp : (y ∘ ρ) ∘ τ = y ∘ ⇑(ρ * τ) := by
      funext a; simp [Equiv.Perm.mul_apply]
    have hdiff := fdot_comp_swap N (y ∘ ρ) q r hqr
    have hNqr : N q ≤ N r := hN (show q ≤ r by simp [hr, Fin.le_def])
    have hle : fdot N ((y ∘ ρ) ∘ τ) ≤ fdot N (y ∘ ρ) := by
      have : (N r - N q) * ((y ∘ ρ) q - (y ∘ ρ) r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    have hge := hmin (ρ * τ)
    rw [← hcomp] at hge
    have heq' : fdot N ((y ∘ ρ) ∘ τ) = fdot N (y ∘ ρ) := by linarith
    have hNeq : N q = N r := by
      have : (N r - N q) * ((y ∘ ρ) q - (y ∘ ρ) r) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exfalso; linarith
    -- the potential decreases
    have hpot := bubblePot_swap (y ∘ ρ) q hq
    have hpotlt : bubblePot (y ∘ ⇑(ρ * τ)) < bubblePot (y ∘ ρ) := by
      rw [← hcomp]; linarith
    have hsub : (Finset.univ.filter fun ρ' : Equiv.Perm (Fin n) =>
        bubblePot (y ∘ ρ') < bubblePot (y ∘ ⇑(ρ * τ))) ⊂
        (Finset.univ.filter fun ρ' : Equiv.Perm (Fin n) =>
        bubblePot (y ∘ ρ') < bubblePot (y ∘ ρ)) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨ρ * τ, by simpa using hpotlt, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl, not_false_eq_true]⟩
      · intro ρ' hρ'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ' ⊢
        linarith
    have hcard := Finset.card_lt_card hsub
    rw [hc] at hcard
    have hV := ih _ hcard (ρ * τ) rfl (by rw [← hcomp, heq', heq])
    rw [← hcomp] at hV
    exact (hVswap (y ∘ ρ) q r hNeq).mp hV

end Persistence
end CRNT
