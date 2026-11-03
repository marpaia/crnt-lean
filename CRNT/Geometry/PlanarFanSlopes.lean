import CRNT.Geometry.PlanarZSH
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
# Planar fans from finitely many slopes, and the decision of comparisons

A planar fan of the closed quadrant (`PlanarZSH.Rays`) is built from any finite set of positive
slopes `ts`: its interior rays are `(1, t)`, `t ∈ ts`, in increasing order (`Rays.ofSlopes`).

A comparison vector `D` (for a network: the difference of two projected source complexes) is
**compatible** with a fan when the sign of `⟪D, ρ j⟫` never jumps from positive to negative
between consecutive rays without passing through zero on a ray.  Every `D` of one sign is
compatible, and every `D` orthogonal to some ray is compatible (`compatible_of_perp`); so a fan
containing all the slopes `-D.1 / D.2` of the mixed-sign comparisons resolves all of them.

`pair_ge_of_good` is the quantitative payoff: if `D` is compatible, `⟪D, ρ j⟫ > 0`, and the
log-state `U` is `Good δ'` for edge `j`, then `⟪D, U⟫` grows linearly in `δ'`.  So with `δ'`
large, `Good` for edge `j` decides, up to any fixed additive error, every comparison that `ρ j`
decides.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace PlanarZSH

/-- The sorted list of slopes. -/
noncomputable def slopeList (ts : Finset ℝ) : List ℝ := ts.sort

theorem slopeList_length (ts : Finset ℝ) : (slopeList ts).length = ts.card := Finset.length_sort _

theorem slopeList_sorted (ts : Finset ℝ) : (slopeList ts).SortedLT := Finset.sortedLT_sort ts

/-- The rays of the fan with interior slopes `ts`. -/
noncomputable def slopeRay (ts : Finset ℝ) (j : ℕ) : ℝ × ℝ :=
  if j ≤ 1 then (1, 0) else if j ≤ ts.card + 1 then (1, (slopeList ts).getD (j - 2) 0) else (0, 1)

theorem slopeRay_interior (ts : Finset ℝ) (j : ℕ) (h1 : 2 ≤ j) (h2 : j ≤ ts.card + 1) :
    ∃ hi : j - 2 < (slopeList ts).length,
      slopeRay ts j = (1, (slopeList ts)[j - 2]) := by
  have hi : j - 2 < (slopeList ts).length := by rw [slopeList_length]; omega
  refine ⟨hi, ?_⟩
  simp only [slopeRay, show ¬ j ≤ 1 by omega, if_false, h2, if_true]
  rw [List.getD_eq_getElem _ _ hi]

theorem slopeList_mem (ts : Finset ℝ) {i : ℕ} (hi : i < (slopeList ts).length) :
    (slopeList ts)[i] ∈ ts :=
  (Finset.mem_sort _).mp (List.getElem_mem hi)

/-- **The fan with interior slopes `ts`.** -/
noncomputable def Rays.ofSlopes (ts : Finset ℝ) (hts : ∀ t ∈ ts, 0 < t) : Rays where
  k := ts.card
  ρ := slopeRay ts
  ρ0 := by simp [slopeRay]
  ρ1 := by simp [slopeRay]
  ρk2 := by simp [slopeRay]
  ρk3 := by simp [slopeRay]
  interior := by
    intro j h1 h2
    obtain ⟨hi, hρ⟩ := slopeRay_interior ts j h1 h2
    rw [hρ]
    exact ⟨one_pos, hts _ (slopeList_mem ts hi)⟩
  order := by
    intro i j hi hij hj
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · have hi1 : i = 1 := by omega
      subst hi1
      have hρi : slopeRay ts 1 = (1, 0) := by simp [slopeRay]
      rw [hρi]
      rcases Nat.lt_or_ge (ts.card + 1) j with hjk | hjk
      · have : slopeRay ts j = (0, 1) := by
          simp [slopeRay, show ¬ j ≤ 1 by omega, show ¬ j ≤ ts.card + 1 by omega]
        rw [this]; simp [cross]
      · obtain ⟨hj', hρj⟩ := slopeRay_interior ts j (by omega) hjk
        rw [hρj]; simp [cross]; exact hts _ (slopeList_mem ts hj')
    · obtain ⟨hi', hρi⟩ := slopeRay_interior ts i hi2 (by omega)
      rw [hρi]
      rcases Nat.lt_or_ge (ts.card + 1) j with hjk | hjk
      · have : slopeRay ts j = (0, 1) := by
          simp [slopeRay, show ¬ j ≤ 1 by omega, show ¬ j ≤ ts.card + 1 by omega]
        rw [this]; simp [cross]
      · obtain ⟨hj', hρj⟩ := slopeRay_interior ts j (by omega) hjk
        rw [hρj]; simp only [cross, one_mul, mul_one]
        have := (slopeList_sorted ts).getElem_lt_getElem_iff (hi := hi') (hj := hj')
        have hlt : (slopeList ts)[i - 2] < (slopeList ts)[j - 2] := this.mpr (by omega)
        linarith

theorem Rays.ofSlopes_k (ts : Finset ℝ) (hts : ∀ t ∈ ts, 0 < t) :
    (Rays.ofSlopes ts hts).k = ts.card := rfl

theorem Rays.ofSlopes_ρ (ts : Finset ℝ) (hts : ∀ t ∈ ts, 0 < t) :
    (Rays.ofSlopes ts hts).ρ = slopeRay ts := rfl

/-- Every slope of `ts` is a ray of the fan. -/
theorem Rays.exists_ray_of_mem (ts : Finset ℝ) (hts : ∀ t ∈ ts, 0 < t) {t : ℝ} (ht : t ∈ ts) :
    ∃ j, 2 ≤ j ∧ j ≤ (Rays.ofSlopes ts hts).k + 1 ∧ (Rays.ofSlopes ts hts).ρ j = (1, t) := by
  have hmem : t ∈ slopeList ts := (Finset.mem_sort _).mpr ht
  obtain ⟨i, hi, hit⟩ := List.getElem_of_mem hmem
  refine ⟨i + 2, by omega, ?_, ?_⟩
  · rw [Rays.ofSlopes_k]; rw [slopeList_length] at hi; omega
  · rw [Rays.ofSlopes_ρ]
    obtain ⟨hi', hρ⟩ := slopeRay_interior ts (i + 2) (by omega)
      (by rw [slopeList_length] at hi; omega)
    rw [hρ]; simp only [Nat.add_sub_cancel] at *; rw [hit]

/-! ## Compatibility of a comparison vector -/

namespace Rays

variable (F : Rays)

/-- `D` is compatible with the fan. -/
def Compatible (D : ℝ × ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ F.k + 2 → 0 < pair D (F.ρ j) →
    0 ≤ pair D (F.ρ (j - 1)) ∧ 0 ≤ pair D (F.ρ (j + 1))

theorem compatible_of_nonneg {D : ℝ × ℝ} (h1 : 0 ≤ D.1) (h2 : 0 ≤ D.2) : F.Compatible D := by
  intro j hj1 hjk _
  have hm := F.nonneg (j - 1) (by omega)
  have hp := F.nonneg (j + 1) (by omega)
  simp only [pair]
  exact ⟨add_nonneg (mul_nonneg h1 hm.1) (mul_nonneg h2 hm.2),
    add_nonneg (mul_nonneg h1 hp.1) (mul_nonneg h2 hp.2)⟩

theorem compatible_of_nonpos {D : ℝ × ℝ} (h1 : D.1 ≤ 0) (h2 : D.2 ≤ 0) : F.Compatible D := by
  intro j hj1 hjk hpos
  have h := F.nonneg j (by omega)
  simp only [pair] at hpos
  nlinarith [mul_nonneg (neg_nonneg.mpr h1) h.1, mul_nonneg (neg_nonneg.mpr h2) h.2]

/-- Sign of the cross product with a fixed ray, as the index varies. -/
theorem cross_sign (i j : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ F.k + 2) (hj : j ≤ F.k + 3) :
    (i < j → 0 ≤ cross (F.ρ i) (F.ρ j)) ∧ (j < i → cross (F.ρ i) (F.ρ j) ≤ 0) ∧
      (i = j → cross (F.ρ i) (F.ρ j) = 0) := by
  -- normalise the out-of-range indices `0` and `k+3`
  have hnorm : ∀ m, m ≤ F.k + 3 → ∃ m', 1 ≤ m' ∧ m' ≤ F.k + 2 ∧ F.ρ m = F.ρ m' ∧
      (m' = m ∨ (m = 0 ∧ m' = 1) ∨ (m = F.k + 3 ∧ m' = F.k + 2)) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      exact ⟨1, le_rfl, by omega, by rw [F.ρ0, F.ρ1], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · rcases Nat.lt_or_ge (F.k + 2) m with hbig | hsmall
      · have : m = F.k + 3 := by omega
        subst this
        exact ⟨F.k + 2, by omega, le_rfl, by rw [F.ρk3, F.ρk2], Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · exact ⟨m, hpos, hsmall, rfl, Or.inl rfl⟩
  obtain ⟨j', hj'1, hj'k, hρj, hcase⟩ := hnorm j hj
  rw [hρj]
  have hself : cross (F.ρ i) (F.ρ i) = 0 := by simp only [cross]; ring
  refine ⟨fun hij => ?_, fun hji => ?_, fun hij => ?_⟩
  · rcases Nat.lt_or_ge i j' with h | h
    · exact (F.order i j' hi1 h hj'k).le
    · have : i = j' := by omega
      subst this; exact hself.ge
  · rcases Nat.lt_or_ge j' i with h | h
    · have := F.order j' i hj'1 h hik
      simp only [cross] at this ⊢; linarith
    · have : i = j' := by omega
      subst this; exact hself.le
  · have : i = j' := by omega
    subst this; exact hself

/-- **A comparison orthogonal to a ray is compatible.** -/
theorem compatible_of_perp {D : ℝ × ℝ} (j₀ : ℕ) (hj₀1 : 1 ≤ j₀) (hj₀k : j₀ ≤ F.k + 2)
    {lam : ℝ} (hD : D = (lam * -(F.ρ j₀).2, lam * (F.ρ j₀).1)) : F.Compatible D := by
  intro j hj1 hjk hpos
  have hpair : ∀ m, pair D (F.ρ m) = lam * cross (F.ρ j₀) (F.ρ m) := by
    intro m; rw [hD]; simp only [pair, cross]; ring
  rw [hpair] at hpos ⊢
  rw [hpair]
  rcases lt_trichotomy lam 0 with hl | hl | hl
  · -- `lam < 0`: positivity means `cross < 0`, so `j < j₀`
    have hc : cross (F.ρ j₀) (F.ρ j) < 0 := by
      by_contra h; push Not at h; nlinarith
    have hjlt : j < j₀ := by
      by_contra h; push Not at h
      rcases Nat.lt_or_ge j₀ j with h' | h'
      · have := (F.cross_sign j₀ j hj₀1 hj₀k (by omega)).1 h'; linarith
      · have : j = j₀ := by omega
        have := (F.cross_sign j₀ j hj₀1 hj₀k (by omega)).2.2 this.symm; linarith
    have h1 := (F.cross_sign j₀ (j - 1) hj₀1 hj₀k (by omega)).2.1 (by omega)
    have h2 : cross (F.ρ j₀) (F.ρ (j + 1)) ≤ 0 := by
      rcases Nat.lt_or_ge (j + 1) j₀ with h | h
      · exact (F.cross_sign j₀ (j + 1) hj₀1 hj₀k (by omega)).2.1 h
      · have : j + 1 = j₀ := by omega
        exact ((F.cross_sign j₀ (j + 1) hj₀1 hj₀k (by omega)).2.2 this.symm).le
    exact ⟨by nlinarith, by nlinarith⟩
  · subst hl; simp at hpos
  · have hc : 0 < cross (F.ρ j₀) (F.ρ j) := by
      by_contra h; push Not at h; nlinarith
    have hjgt : j₀ < j := by
      by_contra h; push Not at h
      rcases Nat.lt_or_ge j j₀ with h' | h'
      · have := (F.cross_sign j₀ j hj₀1 hj₀k (by omega)).2.1 h'; linarith
      · have : j = j₀ := by omega
        have := (F.cross_sign j₀ j hj₀1 hj₀k (by omega)).2.2 this.symm; linarith
    have h1 : 0 ≤ cross (F.ρ j₀) (F.ρ (j - 1)) := by
      rcases Nat.lt_or_ge j₀ (j - 1) with h | h
      · exact (F.cross_sign j₀ (j - 1) hj₀1 hj₀k (by omega)).1 h
      · have : j - 1 = j₀ := by omega
        exact ((F.cross_sign j₀ (j - 1) hj₀1 hj₀k (by omega)).2.2 this.symm).ge
    have h2 := (F.cross_sign j₀ (j + 1) hj₀1 hj₀k (by omega)).1 (by omega)
    exact ⟨by nlinarith, by nlinarith⟩

/-- **Margin bound.**  Compatibility plus `Good δ'` for edge `j` make `⟪D, U⟫` at least
`2δ' (‖ρ (j+1)‖₁ ⟪D, ρ (j-1)⟫ + ‖ρ (j-1)‖₁ ⟪D, ρ (j+1)⟫) / (ρ (j-1) × ρ (j+1))`, and that
coefficient is positive. -/
theorem pair_ge_of_good {D U : ℝ × ℝ} (hD : F.Compatible D) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ F.k + 2) (hpos : 0 < pair D (F.ρ j)) {δ' : ℝ}
    (hgood : Good δ' (F.ρ (j - 1)) (F.ρ (j + 1)) U) :
    0 < cross (F.ρ (j - 1)) (F.ρ (j + 1)) ∧
    0 < nrm (F.ρ (j + 1)) * pair D (F.ρ (j - 1)) + nrm (F.ρ (j - 1)) * pair D (F.ρ (j + 1)) ∧
    2 * δ' * (nrm (F.ρ (j + 1)) * pair D (F.ρ (j - 1)) +
        nrm (F.ρ (j - 1)) * pair D (F.ρ (j + 1))) ≤
      cross (F.ρ (j - 1)) (F.ρ (j + 1)) * pair D U := by
  obtain ⟨hm, hp⟩ := hD j hj1 hjk hpos
  -- `ρ (j-1)` and `ρ (j+1)` are counterclockwise-ordered
  have hg : 0 < cross (F.ρ (j - 1)) (F.ρ (j + 1)) := by
    rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 1 := by omega
      subst this
      have := F.order 1 2 le_rfl (by norm_num) (by omega)
      simpa [F.ρ0, F.ρ1] using this
    · rcases Nat.lt_or_ge (F.k + 1) j with h' | h'
      · have : j = F.k + 2 := by omega
        subst this
        have := F.order (F.k + 1) (F.k + 2) (by omega) (by omega) le_rfl
        rw [show F.k + 2 + 1 = F.k + 3 by omega, F.ρk3]
        rw [F.ρk2] at this
        simpa using this
      · exact F.order (j - 1) (j + 1) (by omega) (by omega) (by omega)
  have hNm := F.nrm_pos (j - 1) (by omega)
  have hNp := F.nrm_pos (j + 1) (by omega)
  -- not both pairings vanish
  have hcoef : 0 < nrm (F.ρ (j + 1)) * pair D (F.ρ (j - 1)) +
      nrm (F.ρ (j - 1)) * pair D (F.ρ (j + 1)) := by
    by_contra hle
    push Not at hle
    have hz1 : pair D (F.ρ (j - 1)) = 0 := by nlinarith [mul_nonneg hNp.le hm, mul_nonneg hNm.le hp]
    have hz2 : pair D (F.ρ (j + 1)) = 0 := by nlinarith [mul_nonneg hNp.le hm, mul_nonneg hNm.le hp]
    -- then `D = 0`, contradicting `hpos`
    have hD0 : D = 0 := by
      simp only [pair] at hz1 hz2
      simp only [cross] at hg
      have e1 : D.1 * cross (F.ρ (j - 1)) (F.ρ (j + 1)) = 0 := by
        simp only [cross]; linear_combination (F.ρ (j + 1)).2 * hz1 - (F.ρ (j - 1)).2 * hz2
      have e2 : D.2 * cross (F.ρ (j - 1)) (F.ρ (j + 1)) = 0 := by
        simp only [cross]; linear_combination (F.ρ (j - 1)).1 * hz2 - (F.ρ (j + 1)).1 * hz1
      have hgne : cross (F.ρ (j - 1)) (F.ρ (j + 1)) ≠ 0 := by simp only [cross]; linarith
      exact Prod.ext ((mul_eq_zero.mp e1).resolve_right hgne)
        ((mul_eq_zero.mp e2).resolve_right hgne)
    rw [hD0] at hpos; simp [pair] at hpos
  refine ⟨hg, hcoef, ?_⟩
  -- Cramer: `g U = (U × ρ₊) ρ₋ + (ρ₋ × U) ρ₊`
  have hcr : cross (F.ρ (j - 1)) (F.ρ (j + 1)) * pair D U =
      (-cross (F.ρ (j + 1)) U) * pair D (F.ρ (j - 1)) +
        cross (F.ρ (j - 1)) U * pair D (F.ρ (j + 1)) := by
    simp only [cross, pair]; ring
  rw [hcr]
  obtain ⟨hg1, hg2⟩ := hgood
  nlinarith [mul_le_mul_of_nonneg_right hg1 hp, mul_le_mul_of_nonneg_right
    (show 2 * δ' * nrm (F.ρ (j + 1)) ≤ -cross (F.ρ (j + 1)) U by linarith) hm]

end Rays

end PlanarZSH
end CRNT
