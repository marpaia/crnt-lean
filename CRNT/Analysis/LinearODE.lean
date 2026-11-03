import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Global solutions of linear ODEs on a compact interval

For a family `B : ℝ → E →L[ℝ] E` continuous on `[0, T]` and bounded by `L`, every initial value
has a solution of `φ' = B(s) φ` on the whole of `[0, T]` (`exists_linear_ode_Icc`).

Mathlib's Picard–Lindelöf theorem gives local solutions on intervals of length `h` with
`L h ≤ 1/2`, uniformly in the initial point (`linear_ode_local`, using the ball of radius
`‖x₀‖ + 1`); the global solution is obtained by gluing `⌈T/h⌉` local solutions
(`linear_ode_glue`), using `HasDerivWithinAt.union` at the junctions.
-/

open Set Filter
open scoped Topology NNReal

namespace CRNT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Local solutions, uniformly in the initial point.** -/
theorem linear_ode_local (B : ℝ → E →L[ℝ] E) {T L h : ℝ} (hB : ContinuousOn B (Icc 0 T))
    (hL0 : 0 ≤ L) (hL : ∀ s ∈ Icc 0 T, ‖B s‖ ≤ L) (hh : 0 ≤ h) (hLh : L * h ≤ 1 / 2)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (x₀ : E) :
    ∃ β : ℝ → E, β t₀ = x₀ ∧ ∀ s ∈ Icc t₀ (min (t₀ + h) T),
      HasDerivWithinAt β (B s (β s)) (Icc t₀ (min (t₀ + h) T)) s := by
  have hmem : t₀ ∈ Icc t₀ (min (t₀ + h) T) := ⟨le_rfl, le_min (by linarith) ht₀.2⟩
  have hsub : Icc t₀ (min (t₀ + h) T) ⊆ Icc 0 T :=
    Icc_subset_Icc ht₀.1 (min_le_right _ _)
  set a : ℝ≥0 := ⟨‖x₀‖ + 1, by positivity⟩ with ha
  set M : ℝ≥0 := ⟨L * (2 * ‖x₀‖ + 1), by positivity⟩ with hM
  set K : ℝ≥0 := ⟨L, hL0⟩ with hK
  have hPL : IsPicardLindelof (fun t x => B t x) (⟨t₀, hmem⟩ : Icc t₀ (min (t₀ + h) T)) x₀ a 0 M K := by
    refine ⟨fun t ht => ?_, fun x _ => ?_, fun t ht x hx => ?_, ?_⟩
    · refine (LipschitzWith.weaken (B t).lipschitz ?_).lipschitzOnWith
      show ‖B t‖₊ ≤ K
      rw [← NNReal.coe_le_coe]
      exact hL t (hsub ht)
    · exact ((ContinuousLinearMap.apply ℝ E x).continuous.comp_continuousOn hB).mono hsub
    · have hx' : ‖x‖ ≤ 2 * ‖x₀‖ + 1 := by
        have h1 := mem_closedBall_iff_norm.mp hx
        have h2 : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
          calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        have : ‖x - x₀‖ ≤ ‖x₀‖ + 1 := h1
        linarith
      show ‖B t x‖ ≤ L * (2 * ‖x₀‖ + 1)
      calc ‖B t x‖ ≤ ‖B t‖ * ‖x‖ := (B t).le_opNorm x
        _ ≤ L * (2 * ‖x₀‖ + 1) := mul_le_mul (hL t (hsub ht)) hx' (norm_nonneg _) hL0
    · show L * (2 * ‖x₀‖ + 1) * max (min (t₀ + h) T - t₀) (t₀ - t₀) ≤ (‖x₀‖ + 1 : ℝ) - 0
      have h1 : max (min (t₀ + h) T - t₀) (t₀ - t₀) ≤ h := by
        rw [sub_self]
        exact max_le (by linarith [min_le_left (t₀ + h) T]) hh
      have h2 : 0 ≤ L * (2 * ‖x₀‖ + 1) := by positivity
      calc L * (2 * ‖x₀‖ + 1) * max (min (t₀ + h) T - t₀) (t₀ - t₀) ≤ L * (2 * ‖x₀‖ + 1) * h :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (L * h) * (2 * ‖x₀‖ + 1) := by ring
        _ ≤ 1 / 2 * (2 * ‖x₀‖ + 1) := mul_le_mul_of_nonneg_right hLh (by positivity)
        _ ≤ (‖x₀‖ + 1 : ℝ) - 0 := by linarith [norm_nonneg x₀]
  obtain ⟨β, hβ0, hβ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, hβ⟩

/-- **Gluing.** Solutions on `[0, s₁]` and `[s₁, s₂]` agreeing at `s₁` combine. -/
theorem linear_ode_glue (B : ℝ → E →L[ℝ] E) {s₁ s₂ : ℝ} (h01 : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    {φ β : ℝ → E} (hφ : ∀ s ∈ Icc 0 s₁, HasDerivWithinAt φ (B s (φ s)) (Icc 0 s₁) s)
    (hβ : ∀ s ∈ Icc s₁ s₂, HasDerivWithinAt β (B s (β s)) (Icc s₁ s₂) s) (heq : β s₁ = φ s₁) :
    ∀ s ∈ Icc 0 s₂, HasDerivWithinAt (fun s => if s ≤ s₁ then φ s else β s)
      (B s (if s ≤ s₁ then φ s else β s)) (Icc 0 s₂) s := by
  set γ : ℝ → E := fun s => if s ≤ s₁ then φ s else β s with hγ
  have hγφ : ∀ s ∈ Icc 0 s₁, γ s = φ s := fun s hs => if_pos hs.2
  have hγβ : ∀ s ∈ Icc s₁ s₂, γ s = β s := by
    intro s hs
    by_cases h : s ≤ s₁
    · have : s = s₁ := le_antisymm h hs.1
      simp only [hγ, if_pos h]; rw [this, heq]
    · exact if_neg h
  have hunion : Icc 0 s₁ ∪ Icc s₁ s₂ = Icc 0 s₂ := Icc_union_Icc_eq_Icc h01 h12
  intro s hs
  rcases lt_trichotomy s s₁ with hlt | heq' | hgt
  · have hsφ : s ∈ Icc 0 s₁ := ⟨hs.1, hlt.le⟩
    have h1 := (hφ s hsφ).congr_of_mem hγφ hsφ
    rw [show (if s ≤ s₁ then φ s else β s) = φ s from hγφ s hsφ]
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [← hunion]
    refine mem_nhdsWithin.mpr ⟨Iio s₁, isOpen_Iio, hlt, fun y hy => ?_⟩
    rcases hy.2 with h | h
    · exact h
    · exact absurd hy.1 (not_lt.mpr h.1)
  · subst heq'
    have h1 := (hφ s ⟨h01, le_rfl⟩).congr_of_mem hγφ ⟨h01, le_rfl⟩
    have h2 := (hβ s ⟨le_rfl, h12⟩).congr_of_mem hγβ ⟨le_rfl, h12⟩
    rw [heq] at h2
    rw [if_pos le_rfl, ← hunion]
    exact h1.union h2
  · have hsβ : s ∈ Icc s₁ s₂ := ⟨hgt.le, hs.2⟩
    have h1 := (hβ s hsβ).congr_of_mem hγβ hsβ
    rw [show (if s ≤ s₁ then φ s else β s) = β s from hγβ s hsβ]
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [← hunion]
    refine mem_nhdsWithin.mpr ⟨Ioi s₁, isOpen_Ioi, hgt, fun y hy => ?_⟩
    rcases hy.2 with h | h
    · exact absurd hy.1 (not_lt.mpr h.2)
    · exact h

/-- **Global solutions of linear ODEs on `[0, T]`.** -/
theorem exists_linear_ode_Icc (B : ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Icc 0 T)) (x₀ : E) :
    ∃ φ : ℝ → E, φ 0 = x₀ ∧ ∀ s ∈ Icc 0 T, HasDerivWithinAt φ (B s (φ s)) (Icc 0 T) s := by
  obtain ⟨L₀, hL₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hB
  set L := max L₀ 1 with hLdef
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 ≤ L := by linarith
  have hL : ∀ s ∈ Icc 0 T, ‖B s‖ ≤ L := fun s hs => (hL₀ s hs).trans (le_max_left _ _)
  set h := 1 / (2 * L) with hhdef
  have hh : 0 < h := by positivity
  have hLh : L * h ≤ 1 / 2 := by rw [hhdef]; field_simp; rfl
  -- induction on the number of steps
  have key : ∀ k : ℕ, ∀ x₀ : E, ∃ φ : ℝ → E, φ 0 = x₀ ∧
      ∀ s ∈ Icc 0 (min ((k + 1 : ℕ) * h) T),
        HasDerivWithinAt φ (B s (φ s)) (Icc 0 (min ((k + 1 : ℕ) * h) T)) s := by
    intro k
    induction k with
    | zero =>
        intro x₀
        obtain ⟨β, hβ0, hβ⟩ := linear_ode_local B hB hL0 hL hh.le hLh ⟨le_rfl, hT⟩ x₀
        refine ⟨β, hβ0, ?_⟩
        simpa using hβ
    | succ k ih =>
        intro x₀
        obtain ⟨φ, hφ0, hφ⟩ := ih x₀
        set s₁ := min ((k + 1 : ℕ) * h) T with hs₁
        have hs₁0 : 0 ≤ s₁ := le_min (by positivity) hT
        have hs₁T : s₁ ≤ T := min_le_right _ _
        obtain ⟨β, hβ0, hβ⟩ := linear_ode_local B hB hL0 hL hh.le hLh ⟨hs₁0, hs₁T⟩ (φ s₁)
        have hs₂ : min (s₁ + h) T = min ((k + 1 + 1 : ℕ) * h) T := by
          rw [hs₁]
          push_cast
          rcases le_total ((k + 1 : ℝ) * h) T with hle | hle
          · rw [min_eq_left hle]; ring_nf
          · rw [min_eq_right hle, min_eq_right (by linarith), min_eq_right (by nlinarith)]
        have hs₁₂ : s₁ ≤ min (s₁ + h) T := le_min (by linarith) hs₁T
        have hglue := linear_ode_glue B hs₁0 hs₁₂ hφ hβ hβ0
        refine ⟨fun s => if s ≤ s₁ then φ s else β s, by simp [hs₁0, hφ0], ?_⟩
        rw [← hs₂]
        exact hglue
  obtain ⟨k, hk⟩ := exists_nat_ge (T / h)
  obtain ⟨φ, hφ0, hφ⟩ := key k x₀
  have hmin : min ((k + 1 : ℕ) * h) T = T := by
    apply min_eq_right
    have : T ≤ k * h := by rwa [div_le_iff₀ hh] at hk
    push_cast; nlinarith
  rw [hmin] at hφ
  exact ⟨φ, hφ0, hφ⟩

end CRNT
