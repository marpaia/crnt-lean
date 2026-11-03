import CRNT.Dynamics.SourceOrderDescent
import CRNT.Geometry.PlanarFanSlopes
import CRNT.Geometry.PlanarZSHTrap

/-!
# Transversal descent near an aligned codimension-two face

Let `P1`, `P2` be disjoint species sets.  Near a face on which both vanish, suppose the state is
*aligned*: `x s = c s * a` on `P1` and `x s = c s * b` on `P2` for transversal coordinates
`a, b > 0`, while every other species has bounded log-ratio `|log x s - log x* s| ≤ B`.  Project
each source complex `y` to `ŷ = (∑_{P1} y s, ∑_{P2} y s)`.  Then the source log-rates are, up to a
bounded error, `-⟪ŷ, U⟫` with `U = (-log a, -log b)`.

`transversal_descent` builds the planar fan whose interior rays are the slopes at which two
projected sources tie, and a threshold `δ₀`, such that for `δ' ≥ δ₀`:

  if `U` is `Good δ'` for edge `j`, then `ρ_j.1 · ∑_{P1} f + ρ_j.2 · ∑_{P2} f ≥ 0`,

which is exactly the descent hypothesis of the planar trapping theorem
`PlanarZSH.Rays.exists_trapping_polygon` in the chart `(∑_{P1} x, ∑_{P2} x)`.  The proof is the
exact source-order criterion `Network.inner_nonneg_of_sourceOrder` applied to the normal that is
`ρ_j.1` on `P1` and `ρ_j.2` on `P2`; the margin lemma `Rays.pair_ge_of_good` turns `Good δ'` into
the needed strict comparisons.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open PlanarZSH

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The projection of a reaction's source complex to the two transversal counts. -/
noncomputable def transSource (N : Network S) (P1 P2 : Finset S) (r : N.R) : ℝ × ℝ :=
  (∑ s ∈ P1, ((N.sourceIdx r).val s : ℝ), ∑ s ∈ P2, ((N.sourceIdx r).val s : ℝ))

/-- All differences of projected sources. -/
noncomputable def transDiffs (N : Network S) (P1 P2 : Finset S) : Finset (ℝ × ℝ) :=
  (Finset.univ ×ˢ Finset.univ).image
    (fun rq : N.R × N.R => N.transSource P1 P2 rq.2 - N.transSource P1 P2 rq.1)

/-- The tie slopes of mixed-sign differences. -/
noncomputable def transSlopes (N : Network S) (P1 P2 : Finset S) : Finset ℝ :=
  ((N.transDiffs P1 P2).filter (fun D => D.1 * D.2 < 0)).image (fun D => -D.1 / D.2)

theorem transSlopes_pos (N : Network S) (P1 P2 : Finset S) :
    ∀ t ∈ N.transSlopes P1 P2, 0 < t := by
  intro t ht
  simp only [transSlopes, Finset.mem_image, Finset.mem_filter] at ht
  obtain ⟨D, ⟨-, hD⟩, rfl⟩ := ht
  have h2 : D.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hD; exact lt_irrefl _ hD
  have : -D.1 / D.2 = -(D.1 * D.2) / (D.2 * D.2) := by field_simp
  rw [this]
  exact div_pos (by linarith) (mul_self_pos.mpr h2)

/-- The transversal planar fan. -/
noncomputable def transFan (N : Network S) (P1 P2 : Finset S) : Rays :=
  Rays.ofSlopes (N.transSlopes P1 P2) (N.transSlopes_pos P1 P2)

theorem transFan_compatible (N : Network S) (P1 P2 : Finset S) {D : ℝ × ℝ}
    (hD : D ∈ N.transDiffs P1 P2) : (N.transFan P1 P2).Compatible D := by
  set F := N.transFan P1 P2
  by_cases hmix : D.1 * D.2 < 0
  · have hts : -D.1 / D.2 ∈ N.transSlopes P1 P2 := by
      simp only [transSlopes, Finset.mem_image, Finset.mem_filter]
      exact ⟨D, ⟨hD, hmix⟩, rfl⟩
    obtain ⟨j₀, hj₀1, hj₀k, hρ⟩ :=
      Rays.exists_ray_of_mem (N.transSlopes P1 P2) (N.transSlopes_pos P1 P2) hts
    have h2 : D.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hmix; exact lt_irrefl _ hmix
    refine F.compatible_of_perp j₀ (by omega) (Nat.le_succ_of_le hj₀k) (lam := D.2) ?_
    change D = (D.2 * -((N.transFan P1 P2).ρ j₀).2, D.2 * ((N.transFan P1 P2).ρ j₀).1)
    simp only [transFan] at hρ ⊢
    rw [hρ]
    ext <;> simp <;> field_simp
  · push Not at hmix
    rcases le_total 0 D.1 with h1 | h1
    · rcases le_total 0 D.2 with h2 | h2
      · exact F.compatible_of_nonneg h1 h2
      · have : D.1 = 0 ∨ D.2 = 0 := by
          by_contra h; push Not at h
          have : D.1 * D.2 < 0 :=
            mul_neg_of_pos_of_neg (lt_of_le_of_ne h1 (Ne.symm h.1)) (lt_of_le_of_ne h2 h.2)
          linarith
        rcases this with h | h
        · exact F.compatible_of_nonpos (le_of_eq h) h2
        · exact F.compatible_of_nonneg h1 (le_of_eq h.symm)
    · rcases le_total 0 D.2 with h2 | h2
      · have : D.1 = 0 ∨ D.2 = 0 := by
          by_contra h; push Not at h
          have : D.1 * D.2 < 0 :=
            mul_neg_of_neg_of_pos (lt_of_le_of_ne h1 h.1) (lt_of_le_of_ne h2 (Ne.symm h.2))
          linarith
        rcases this with h | h
        · exact F.compatible_of_nonneg (le_of_eq h.symm) h2
        · exact F.compatible_of_nonpos h1 (le_of_eq h)
      · exact F.compatible_of_nonpos h1 h2

/-- The per-species log-error bound. -/
noncomputable def transErr (P1 P2 : Finset S) (c xstar : S → ℝ) (B : ℝ) (s : S) : ℝ :=
  if s ∈ P1 ∨ s ∈ P2 then |Real.log (c s) - Real.log (xstar s)| else B

/-- The total log-error bound of the source log-rates. -/
noncomputable def transErrTotal (N : Network S) (P1 P2 : Finset S) (c xstar : S → ℝ)
    (B : ℝ) : ℝ :=
  ∑ r : N.R, ∑ s, ((N.sourceIdx r).val s : ℝ) * transErr P1 P2 c xstar B s

/-- **Source log-rates in the aligned chart.** -/
theorem sourceLogProjection_aligned (N : Network S) {P1 P2 : Finset S} (hdisj : Disjoint P1 P2)
    {c : S → ℝ} (hc : ∀ s, s ∈ P1 ∨ s ∈ P2 → 0 < c s) {B : ℝ} (hB : 0 ≤ B)
    {x xstar : Concentration S} (hx : x.Positive) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hxa : ∀ s ∈ P1, x s = c s * a) (hxb : ∀ s ∈ P2, x s = c s * b)
    (hrest : ∀ s, s ∉ P1 → s ∉ P2 → |Real.log (x s) - Real.log (xstar s)| ≤ B) (r : N.R) :
    |N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r +
        pair (N.transSource P1 P2 r) (logState (a, b))| ≤
      N.transErrTotal P1 P2 c xstar B := by
  set u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  -- pointwise decomposition `u s = 1_{P1} log a + 1_{P2} log b + e s`
  set e : S → ℝ := fun s => u s - (if s ∈ P1 then Real.log a else 0) -
    (if s ∈ P2 then Real.log b else 0) with he
  have he_bd : ∀ s, |e s| ≤ transErr P1 P2 c xstar B s := by
    intro s
    by_cases h1 : s ∈ P1
    · have h2 : s ∉ P2 := Finset.disjoint_left.mp hdisj h1
      have hcs := hc s (Or.inl h1)
      simp only [he, u, h1, h2, if_true, if_false, transErr, true_or, sub_zero]
      rw [hxa s h1, Real.log_mul hcs.ne' ha.ne']
      rw [show Real.log (c s) + Real.log a - Real.log (xstar s) - Real.log a =
        Real.log (c s) - Real.log (xstar s) by ring]
    · by_cases h2 : s ∈ P2
      · have hcs := hc s (Or.inr h2)
        simp only [he, u, h1, h2, if_true, if_false, transErr, or_true, sub_zero]
        rw [hxb s h2, Real.log_mul hcs.ne' hb.ne']
        rw [show Real.log (c s) + Real.log b - Real.log (xstar s) - Real.log b =
          Real.log (c s) - Real.log (xstar s) by ring]
      · simp only [he, u, h1, h2, if_false, transErr, or_self, sub_zero]
        exact hrest s h1 h2
  have hdecomp : N.sourceLogProjection u r + pair (N.transSource P1 P2 r) (logState (a, b)) =
      ∑ s, ((N.sourceIdx r).val s : ℝ) * e s := by
    simp only [sourceLogProjection, pair, transSource, logState, he]
    have h1 : ∑ s, ((N.sourceIdx r).val s : ℝ) * (if s ∈ P1 then Real.log a else 0) =
        (∑ s ∈ P1, ((N.sourceIdx r).val s : ℝ)) * Real.log a := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_mul]
    have h2 : ∑ s, ((N.sourceIdx r).val s : ℝ) * (if s ∈ P2 then Real.log b else 0) =
        (∑ s ∈ P2, ((N.sourceIdx r).val s : ℝ)) * Real.log b := by
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_mul]
    have hsplit : ∀ s, ((N.sourceIdx r).val s : ℝ) * u s =
        ((N.sourceIdx r).val s : ℝ) * (if s ∈ P1 then Real.log a else 0) +
        ((N.sourceIdx r).val s : ℝ) * (if s ∈ P2 then Real.log b else 0) +
        ((N.sourceIdx r).val s : ℝ) * e s := by
      intro s; simp only [he]; ring
    rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib,
      Finset.sum_add_distrib, h1, h2]
    simp only [u]
    ring
  rw [hdecomp]
  calc |∑ s, ((N.sourceIdx r).val s : ℝ) * e s|
      ≤ ∑ s, |((N.sourceIdx r).val s : ℝ) * e s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, ((N.sourceIdx r).val s : ℝ) * transErr P1 P2 c xstar B s := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (he_bd s) (Nat.cast_nonneg _)
    _ ≤ N.transErrTotal P1 P2 c xstar B := by
        unfold transErrTotal
        apply Finset.single_le_sum (f := fun r : N.R =>
          ∑ s, ((N.sourceIdx r).val s : ℝ) * transErr P1 P2 c xstar B s) _ (Finset.mem_univ r)
        intro q _
        apply Finset.sum_nonneg
        intro s _
        apply mul_nonneg (Nat.cast_nonneg _)
        unfold transErr
        split_ifs
        · exact abs_nonneg _
        · exact hB

/-- Splitting a weighted sum by two disjoint species sets. -/
theorem sum_mul_twoSets {P1 P2 : Finset S} (hdisj : Disjoint P1 P2) (w : S → ℝ) (ρ1 ρ2 : ℝ) :
    ∑ s, w s * (if s ∈ P1 then ρ1 else if s ∈ P2 then ρ2 else 0) =
      ρ1 * ∑ s ∈ P1, w s + ρ2 * ∑ s ∈ P2, w s := by
  have hpt : ∀ s, w s * (if s ∈ P1 then ρ1 else if s ∈ P2 then ρ2 else 0) =
      (if s ∈ P1 then w s * ρ1 else 0) + (if s ∈ P2 then w s * ρ2 else 0) := by
    intro s
    by_cases h1 : s ∈ P1
    · have h2 : s ∉ P2 := Finset.disjoint_left.mp hdisj h1
      simp [h1, h2]
    · by_cases h2 : s ∈ P2 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Transversal descent near an aligned codimension-two face.** -/
theorem transversal_descent (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {P1 P2 : Finset S} (hdisj : Disjoint P1 P2) {c : S → ℝ}
    (hc : ∀ s, s ∈ P1 ∨ s ∈ P2 → 0 < c s) {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ', δ₀ ≤ δ' → ∀ x : Concentration S, x.Positive →
      ∀ a b : ℝ, 0 < a → 0 < b → (∀ s ∈ P1, x s = c s * a) → (∀ s ∈ P2, x s = c s * b) →
      (∀ s, s ∉ P1 → s ∉ P2 → |Real.log (x s) - Real.log (xstar s)| ≤ B) →
      ∀ j, 1 ≤ j → j ≤ (N.transFan P1 P2).k + 2 →
        Good δ' ((N.transFan P1 P2).ρ (j - 1)) ((N.transFan P1 P2).ρ (j + 1))
          (logState (a, b)) →
        0 ≤ ((N.transFan P1 P2).ρ j).1 * ∑ s ∈ P1, N.massActionVectorField κ x s +
            ((N.transFan P1 P2).ρ j).2 * ∑ s ∈ P2, N.massActionVectorField κ x s := by
  set F := N.transFan P1 P2 with hF
  set E := N.transErrTotal P1 P2 c xstar B with hE
  set C : ℝ := 2 * E + 1 with hC
  set Dv : N.R → N.R → ℝ × ℝ := fun r q => N.transSource P1 P2 q - N.transSource P1 P2 r
  set coef : ℝ × ℝ → ℕ → ℝ := fun D j =>
    nrm (F.ρ (j + 1)) * pair D (F.ρ (j - 1)) + nrm (F.ρ (j - 1)) * pair D (F.ρ (j + 1))
  set thr : N.R → N.R → ℕ → ℝ := fun r q j =>
    if 0 < pair (Dv r q) (F.ρ j) then
      |C * cross (F.ρ (j - 1)) (F.ρ (j + 1)) / (2 * coef (Dv r q) j)| else 0
  have hthr0 : ∀ r q j, 0 ≤ thr r q j := by
    intro r q j; simp only [thr]; split_ifs <;> simp
  set δ₀ : ℝ := 1 + ∑ r : N.R, ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j
  have hthr_le : ∀ r q j, j ∈ Finset.Icc 1 (F.k + 2) → thr r q j ≤ δ₀ := by
    intro r q j hj
    have h3 : thr r q j ≤ ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j :=
      Finset.single_le_sum (f := fun j => thr r q j) (fun j _ => hthr0 r q j) hj
    have h2 : ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j ≤
        ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j :=
      Finset.single_le_sum (f := fun q => ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j)
        (fun q _ => Finset.sum_nonneg fun j _ => hthr0 r q j) (Finset.mem_univ q)
    have h1 : ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j ≤
        ∑ r : N.R, ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j :=
      Finset.single_le_sum (f := fun r => ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j)
        (fun r _ => Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun j _ => hthr0 r q j)
        (Finset.mem_univ r)
    simp only [δ₀]; linarith
  have hδ₀pos : 0 < δ₀ := by
    have : 0 ≤ ∑ r : N.R, ∑ q : N.R, ∑ j ∈ Finset.Icc 1 (F.k + 2), thr r q j :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun q _ =>
        Finset.sum_nonneg fun j _ => hthr0 r q j
    simp only [δ₀]; linarith
  have hE0 : 0 ≤ E := by
    have := N.sourceLogProjection_aligned hdisj hc hB (x := xstar) (xstar := xstar) hxs
      one_pos one_pos
    -- `E` is a sum of nonnegative terms
    simp only [hE, transErrTotal]
    apply Finset.sum_nonneg; intro r _; apply Finset.sum_nonneg; intro s _
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold transErr; split_ifs
    · exact abs_nonneg _
    · exact hB
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro δ' hδ' x hx a b ha hb hxa hxb hrest j hj1 hjk hgood
  set ρ := F.ρ j with hρ
  set n : S → ℝ := fun s => if s ∈ P1 then ρ.1 else if s ∈ P2 then ρ.2 else 0 with hn
  have hsLPn : ∀ r : N.R, N.sourceLogProjection n r = pair (N.transSource P1 P2 r) ρ := by
    intro r
    simp only [sourceLogProjection, hn, transSource, pair]
    rw [sum_mul_twoSets hdisj]; ring
  have hfield : ∑ s, n s * N.massActionVectorField κ x s =
      ρ.1 * ∑ s ∈ P1, N.massActionVectorField κ x s +
        ρ.2 * ∑ s ∈ P2, N.massActionVectorField κ x s := by
    have := sum_mul_twoSets hdisj (fun s => N.massActionVectorField κ x s) ρ.1 ρ.2
    rw [← this]
    apply Finset.sum_congr rfl; intro s _; simp only [hn]; ring
  rw [← hfield]
  apply N.inner_nonneg_of_sourceOrder κ hx hxs hcb n
  intro r q hrq
  rw [hsLPn, hsLPn] at hrq
  -- the comparison vector
  have hDpos : 0 < pair (Dv r q) (F.ρ j) := by
    simp only [Dv, pair, Prod.fst_sub, Prod.snd_sub, ← hρ] at hrq ⊢; linarith
  have hDmem : Dv r q ∈ N.transDiffs P1 P2 := by
    simp only [transDiffs, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨(r, q), rfl⟩
  have hcompat := N.transFan_compatible P1 P2 hDmem
  obtain ⟨hg, hcoef, hbound⟩ := F.pair_ge_of_good hcompat hj1 hjk hDpos hgood
  have hthr : C * cross (F.ρ (j - 1)) (F.ρ (j + 1)) / (2 * coef (Dv r q) j) ≤ δ' := by
    have h1 := hthr_le r q j (Finset.mem_Icc.mpr ⟨hj1, hjk⟩)
    have h2 : thr r q j = |C * cross (F.ρ (j - 1)) (F.ρ (j + 1)) / (2 * coef (Dv r q) j)| := by
      simp only [thr, if_pos hDpos]
    rw [h2] at h1
    exact (le_abs_self _).trans (h1.trans hδ')
  have hcoef' : 0 < coef (Dv r q) j := hcoef
  have hpairU : C ≤ pair (Dv r q) (logState (a, b)) := by
    have h1 : C * cross (F.ρ (j - 1)) (F.ρ (j + 1)) ≤ 2 * δ' * coef (Dv r q) j := by
      rw [div_le_iff₀ (by positivity)] at hthr; linarith
    have h2 : C * cross (F.ρ (j - 1)) (F.ρ (j + 1)) ≤
        cross (F.ρ (j - 1)) (F.ρ (j + 1)) * pair (Dv r q) (logState (a, b)) := by
      have := hbound; simp only [coef] at h1; linarith
    nlinarith
  have hq := N.sourceLogProjection_aligned hdisj hc hB hx ha hb hxa hxb hrest q
  have hr := N.sourceLogProjection_aligned hdisj hc hB hx ha hb hxa hxb hrest r
  have hsplit : pair (Dv r q) (logState (a, b)) =
      pair (N.transSource P1 P2 q) (logState (a, b)) -
        pair (N.transSource P1 P2 r) (logState (a, b)) := by
    simp only [Dv, pair, Prod.fst_sub, Prod.snd_sub]; ring
  rw [abs_le] at hq hr
  rw [← hE] at hq hr
  linarith [hq.2, hr.1]

end Network

/-!
## The local codimension-two trap

Composition of `transversal_descent` with the planar trapping polygon: in the chart
`a = ∑_{P1} x`, `b = ∑_{P2} x`, a mass-action trajectory segment that stays aligned, in the box,
with the remaining log-ratios bounded, cannot leave the region above the polygon.
-/

namespace Network

open PlanarZSH

variable {S : Type} [DecidableEq S] [Fintype S]

theorem hasDerivAt_sum_coords {x : ℝ → Concentration S} {v : Concentration S} {t : ℝ}
    (hx : HasDerivAt x v t) (P : Finset S) :
    HasDerivAt (fun τ => ∑ s ∈ P, x τ s) (∑ s ∈ P, v s) t := by
  have h : ∀ s, HasDerivAt (fun τ => x τ s) (v s) t := fun s => (hasDerivAt_pi.mp hx) s
  exact HasDerivAt.fun_sum fun s _ => h s

/-- **Local trap near an aligned codimension-two face.** -/
theorem local_codimTwo_trap (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {P1 P2 : Finset S} (hdisj : Disjoint P1 P2) {c : S → ℝ}
    (hc : ∀ s, s ∈ P1 ∨ s ∈ P2 → 0 < c s) (hc1 : ∑ s ∈ P1, c s = 1) (hc2 : ∑ s ∈ P2, c s = 1)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ b₀ : ℝ, 0 < b₀ → b₀ ≤ β₀ →
      ∃ off : ℕ → ℝ, ∃ e₀ : ℝ, 0 < e₀ ∧
      (∀ j, 1 ≤ j → j ≤ (N.transFan P1 P2).k + 2 → 0 < off j) ∧
      (∀ z : ℝ × ℝ, b₀ ^ K ≤ z.1 → b₀ ≤ z.2 → ∀ j, 1 ≤ j → j ≤ (N.transFan P1 P2).k + 2 →
        off j ≤ pair ((N.transFan P1 P2).ρ j) z) ∧
      (∀ e, 0 < e → e ≤ e₀ → ∀ (x : ℝ → Concentration S) (T : ℝ), 0 ≤ T →
        ContinuousOn (fun t => ((∑ s ∈ P1, x t s), (∑ s ∈ P2, x t s))) (Set.Ici 0) →
        (∀ t, 0 ≤ t → t < T → HasDerivAt x (N.massActionVectorField κ (x t)) t) →
        (∀ t, 0 ≤ t → t ≤ T → (x t).Positive) →
        (∀ t, 0 ≤ t → t ≤ T → (∀ s ∈ P1, x t s = c s * ∑ s' ∈ P1, x t s') ∧
          (∀ s ∈ P2, x t s = c s * ∑ s' ∈ P2, x t s')) →
        (∀ t, 0 ≤ t → t ≤ T → ∀ s, s ∉ P1 → s ∉ P2 →
          |Real.log (x t s) - Real.log (xstar s)| ≤ B) →
        (∀ t, 0 ≤ t → t ≤ T → ∑ s ∈ P1, x t s ≤ Real.exp (-(2 * δ)) ∧
          ∑ s ∈ P2, x t s ≤ Real.exp (-(2 * δ))) →
        (∀ j, 1 ≤ j → j ≤ (N.transFan P1 P2).k + 2 →
          off j + e ≤ pair ((N.transFan P1 P2).ρ j) (∑ s ∈ P1, x 0 s, ∑ s ∈ P2, x 0 s)) →
        ∀ t, 0 ≤ t → t ≤ T → ∀ j, 1 ≤ j → j ≤ (N.transFan P1 P2).k + 2 →
          off j + e ≤ pair ((N.transFan P1 P2).ρ j) (∑ s ∈ P1, x t s, ∑ s ∈ P2, x t s)) := by
  obtain ⟨δ₀, hδ₀, hdesc⟩ := N.transversal_descent κ hxs hcb hdisj hc hB
  set F := N.transFan P1 P2
  refine ⟨2 * δ₀, by positivity, ?_⟩
  obtain ⟨β₀, hβ₀, K, hK, htrap⟩ := F.exists_trapping_polygon (δ := 2 * δ₀) (by positivity)
  refine ⟨β₀, hβ₀, K, hK, fun b₀ hb₀ hbβ => ?_⟩
  obtain ⟨off, e₀, he₀, hP0, hP1, hP2⟩ := htrap b₀ hb₀ hbβ
  refine ⟨off, e₀, he₀, hP0, hP1, ?_⟩
  intro e he hee₀ x T hT hcont hderiv hpos halign hrest hbox hstart
  set γ : ℝ → ℝ × ℝ := fun t => ((∑ s ∈ P1, x t s), (∑ s ∈ P2, x t s)) with hγ
  set v : ℝ → ℝ × ℝ := fun t => ((∑ s ∈ P1, N.massActionVectorField κ (x t) s),
    (∑ s ∈ P2, N.massActionVectorField κ (x t) s)) with hv
  have hP1ne : P1.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; rw [h] at hc1; simp at hc1
  have hP2ne : P2.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; rw [h] at hc2; simp at hc2
  have hγpos : ∀ t, 0 ≤ t → t ≤ T → 0 < (γ t).1 ∧ 0 < (γ t).2 := by
    intro t ht htT
    exact ⟨Finset.sum_pos (fun s _ => hpos t ht htT s) hP1ne,
      Finset.sum_pos (fun s _ => hpos t ht htT s) hP2ne⟩
  refine hP2 e he hee₀ γ v T hT hcont ?_ hstart ?_ ?_
  · intro t ht htT
    exact (hasDerivAt_sum_coords (hderiv t ht htT) P1).prodMk
      (hasDerivAt_sum_coords (hderiv t ht htT) P2)
  · intro t ht htT
    obtain ⟨h1, h2⟩ := hγpos t ht htT
    exact ⟨h1, h2, (hbox t ht htT).1, (hbox t ht htT).2⟩
  · intro t ht htT j hj1 hjk hgood
    obtain ⟨h1, h2⟩ := hγpos t ht htT.le
    have hgood' : Good δ₀ (F.ρ (j - 1)) (F.ρ (j + 1)) (logState (γ t)) := by
      have : 2 * δ₀ / 2 = δ₀ := by ring
      rw [this] at hgood; exact hgood
    have := hdesc δ₀ le_rfl (x t) (hpos t ht htT.le) (γ t).1 (γ t).2 h1 h2
      (halign t ht htT.le).1 (halign t ht htT.le).2 (hrest t ht htT.le) j hj1 hjk hgood'
    simpa [pair, hv] using this

end Network

end CRNT
