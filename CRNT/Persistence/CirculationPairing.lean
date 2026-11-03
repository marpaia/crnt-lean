import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The circulation pairing inequality

For a nonnegative circulation `w` on a finite vertex set `V`, a "height" `g` and a potential `φ`
that is nonincreasing in `g` (`g a ≤ g b → φ b ≤ φ a`), the weighted sum
`∑ a b, w a b * g a * (φ b - φ a)` is nonnegative.

Proof: eliminate a vertex `v` of maximal height.  Pair each edge `a → v` with each edge `v → b`
in proportion to the flux through `v`; the pair contributes the shortcut `a → b` (a circulation on
`V \ {v}`) plus `(g v - g a) (φ b - φ v) ≥ 0`.

This is the scalar core of the decomposition of a complex-balanced mass-action field into downhill
complex differences.  Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset

theorem circulation_pairing_nonneg {α : Type*} [DecidableEq α] (g φ : α → ℝ) :
    ∀ (V : Finset α) (w : α → α → ℝ),
    (∀ a b, 0 ≤ w a b) →
    (∀ a ∈ V, ∑ b ∈ V, w a b = ∑ b ∈ V, w b a) →
    (∀ a ∈ V, ∀ b ∈ V, g a ≤ g b → φ b ≤ φ a) →
    0 ≤ ∑ a ∈ V, ∑ b ∈ V, w a b * (g a * (φ b - φ a)) := by
  intro V
  induction V using Finset.strongInduction with
  | H V ih =>
  intro w hw hcirc hmono
  rcases V.eq_empty_or_nonempty with hV | hV
  · simp [hV]
  obtain ⟨v, hvV, hvmax⟩ := V.exists_max_image g hV
  set V' := V.erase v with hV'
  have hsub : V' ⊂ V := Finset.erase_ssubset hvV
  set F := ∑ b ∈ V', w v b with hF
  have hFin : ∑ b ∈ V', w b v = F := by
    have h := hcirc v hvV
    rw [← Finset.add_sum_erase V _ hvV, ← Finset.add_sum_erase V _ hvV] at h
    linarith
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ => hw v b
  set w' : α → α → ℝ := fun a b => w a b + w a v * w v b / F with hw'
  have hw'nn : ∀ a b, 0 ≤ w' a b := fun a b => by
    have := hw a b; have := hw a v; have := hw v b; positivity
  have hcirc' : ∀ a ∈ V', ∑ b ∈ V', w' a b = ∑ b ∈ V', w' b a := by
    intro a ha
    have haV : a ∈ V := Finset.mem_of_mem_erase ha
    have h := hcirc a haV
    rw [← Finset.add_sum_erase V _ hvV, ← Finset.add_sum_erase V _ hvV] at h
    simp only [hw', Finset.sum_add_distrib]
    rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hFin]
    rcases hF0.lt_or_eq with hFp | hFz
    · rw [mul_div_assoc, div_self hFp.ne', mul_comm F (w v a), mul_div_assoc,
        div_self hFp.ne']
      linarith
    · have hva : w v a = 0 := by
        have hle : w v a ≤ F :=
          Finset.single_le_sum (f := fun b => w v b) (fun b _ => hw v b) ha
        linarith [hw v a]
      have hav : w a v = 0 := by
        have hle : w a v ≤ ∑ b ∈ V', w b v :=
          Finset.single_le_sum (f := fun b => w b v) (fun b _ => hw b v) ha
        linarith [hw a v]
      rw [hva, hav] at h
      rw [← hFz]; simp only [mul_zero, zero_mul, div_zero, add_zero] at *
      linarith
  have hmono' : ∀ a ∈ V', ∀ b ∈ V', g a ≤ g b → φ b ≤ φ a := fun a ha b hb =>
    hmono a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  have hIH := ih V' hsub w' hw'nn hcirc' hmono'
  -- the extra term
  set X := ∑ a ∈ V', ∑ b ∈ V', w a v * w v b * ((g v - g a) * (φ b - φ v)) with hX
  have hXnn : 0 ≤ X := by
    refine Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => ?_
    have h1 : g a ≤ g v := hvmax a (Finset.mem_of_mem_erase ha)
    have h2 : φ v ≤ φ b := hmono b (Finset.mem_of_mem_erase hb) v hvV
      (hvmax b (Finset.mem_of_mem_erase hb))
    have := hw a v; have := hw v b
    have : 0 ≤ (g v - g a) * (φ b - φ v) := mul_nonneg (by linarith) (by linarith)
    positivity
  -- decomposition of the full sum
  have hsplit : ∑ a ∈ V, ∑ b ∈ V, w a b * (g a * (φ b - φ a)) =
      ∑ a ∈ V', ∑ b ∈ V', w a b * (g a * (φ b - φ a))
      + ∑ a ∈ V', w a v * (g a * (φ v - φ a))
      + ∑ b ∈ V', w v b * (g v * (φ b - φ v)) := by
    rw [← Finset.add_sum_erase V _ hvV]
    simp only [← hV']
    rw [← Finset.add_sum_erase V _ hvV]
    simp only [← hV', sub_self, mul_zero, zero_add]
    have : ∀ a ∈ V', ∑ b ∈ V, w a b * (g a * (φ b - φ a)) =
        w a v * (g a * (φ v - φ a)) + ∑ b ∈ V', w a b * (g a * (φ b - φ a)) := by
      intro a _; rw [← Finset.add_sum_erase V _ hvV]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    ring
  rcases hF0.lt_or_eq with hFp | hFz
  · have hw'sum : ∑ a ∈ V', ∑ b ∈ V', w' a b * (g a * (φ b - φ a)) =
        ∑ a ∈ V', ∑ b ∈ V', w a b * (g a * (φ b - φ a))
        + ∑ a ∈ V', w a v * (g a * (φ v - φ a))
        + ∑ b ∈ V', w v b * (g v * (φ b - φ v)) - X / F := by
      have e1 : ∀ a ∈ V', ∑ b ∈ V', w' a b * (g a * (φ b - φ a)) =
          ∑ b ∈ V', w a b * (g a * (φ b - φ a))
          + (∑ b ∈ V', w a v * w v b * (g a * (φ b - φ v))) / F
          + w a v * (g a * (φ v - φ a)) := by
        intro a _
        have hsum : ∑ b ∈ V', w a v * w v b / F * (g a * (φ b - φ a)) =
            (∑ b ∈ V', w a v * w v b * (g a * (φ b - φ v))) / F
            + w a v * (g a * (φ v - φ a)) := by
          have : ∀ b ∈ V', w a v * w v b / F * (g a * (φ b - φ a)) =
              w a v * w v b * (g a * (φ b - φ v)) / F
              + w v b * (w a v * (g a * (φ v - φ a)) / F) := by
            intro b _; field_simp; ring
          rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_div,
            ← Finset.sum_mul, ← hF, mul_div_assoc', mul_comm F, mul_div_assoc,
            div_self hFp.ne', mul_one]
        simp only [hw', add_mul, Finset.sum_add_distrib]
        rw [hsum]; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_div]
      have e2 : ∑ b ∈ V', w v b * (g v * (φ b - φ v)) =
          (∑ a ∈ V', ∑ b ∈ V', w a v * w v b * (g v * (φ b - φ v))) / F := by
        have : ∑ a ∈ V', ∑ b ∈ V', w a v * w v b * (g v * (φ b - φ v)) =
            (∑ a ∈ V', w a v) * ∑ b ∈ V', w v b * (g v * (φ b - φ v)) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
        rw [this, hFin]; field_simp
        exact Finset.sum_congr rfl fun b _ => by ring
      have e3 : X = ∑ a ∈ V', ∑ b ∈ V', w a v * w v b * (g v * (φ b - φ v))
          - ∑ a ∈ V', ∑ b ∈ V', w a v * w v b * (g a * (φ b - φ v)) := by
        rw [hX, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun b _ => ?_; ring
      rw [e2, e3, sub_div]; ring
    rw [hsplit]
    have : 0 ≤ X / F := div_nonneg hXnn hFp.le
    linarith
  · have hzero1 : ∀ a ∈ V', w a v = 0 := fun a ha => by
      have hle : w a v ≤ ∑ b ∈ V', w b v :=
        Finset.single_le_sum (f := fun b => w b v) (fun b _ => hw b v) ha
      linarith [hw a v]
    have hzero2 : ∀ b ∈ V', w v b = 0 := fun b hb => by
      have hle : w v b ≤ F :=
        Finset.single_le_sum (f := fun b => w v b) (fun b _ => hw v b) hb
      linarith [hw v b]
    have hw'eq : ∀ a ∈ V', ∀ b ∈ V', w' a b = w a b := fun a ha b _ => by
      simp [hw', hzero1 a ha]
    have h1 : ∑ a ∈ V', w a v * (g a * (φ v - φ a)) = 0 :=
      Finset.sum_eq_zero (fun a ha => by rw [hzero1 a ha, zero_mul])
    have h2 : ∑ b ∈ V', w v b * (g v * (φ b - φ v)) = 0 :=
      Finset.sum_eq_zero (fun b hb => by rw [hzero2 b hb, zero_mul])
    rw [hsplit, h1, h2]
    have : ∑ a ∈ V', ∑ b ∈ V', w' a b * (g a * (φ b - φ a)) =
        ∑ a ∈ V', ∑ b ∈ V', w a b * (g a * (φ b - φ a)) :=
      Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by rw [hw'eq a ha b hb]
    linarith

end Persistence
end CRNT
