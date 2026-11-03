import CRNT.Multistationarity.Concordance

/-!
# Converse to the concordance injectivity theorem

Shinar--Feinberg concordance is not only sufficient for injectivity over weakly monotonic
kinetics: discordance is witnessed by an admissible weakly monotonic kinetics that is
noninjective on a stoichiometric compatibility class.  The constructive proof starts from a
`ConcordanceWitness (α,σ)`, chooses two positive compatible compositions separated by `σ`, and
builds reaction rate functions whose rate displacement is `α` while respecting every source
support sign constraint.

This file isolates that construction so the structural theorem can be stated as an iff.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Positive pair realizing a prescribed nonzero stoichiometric displacement up to a common
positive scalar. -/
structure PositivePairRealizing (N : Network S) (σ : S → ℝ) where
  x : Concentration S
  y : Concentration S
  scale : ℝ
  scale_pos : 0 < scale
  x_pos : x.Positive
  y_pos : y.Positive
  displacement : y - x = scale • σ

/-- Every finite nonzero displacement can be realized between two positive concentrations after
positive rescaling. -/
theorem exists_positivePairRealizing (N : Network S) {σ : S → ℝ} (_hσ : σ ≠ 0) :
    Nonempty (N.PositivePairRealizing σ) := by
  let x : Concentration S := fun s => |σ s| + 1
  let y : Concentration S := fun s => x s + σ s
  refine ⟨{
    x := x
    y := y
    scale := 1
    scale_pos := zero_lt_one
    x_pos := ?_
    y_pos := ?_
    displacement := ?_ }⟩
  · intro s
    dsimp [x]
    linarith [abs_nonneg (σ s)]
  · intro s
    dsimp [y, x]
    have h := neg_abs_le (σ s)
    linarith
  · ext s
    simp [y, x]

/-- A reactionwise rate-interpolation certificate for a concordance witness.  It packages a
globally admissible kinetics whose prescribed rate difference between the two selected states is
exactly `α`. -/
structure ConcordanceKineticsRealization (N : Network S)
    (α : N.R → ℝ) (σ : S → ℝ)
    (W : N.ConcordanceWitness α σ) where
  pair : N.PositivePairRealizing σ
  kinetics : Kinetics N
  weaklyMonotonic : kinetics.WeaklyMonotonic
  rateDifference : ∀ r : N.R,
    kinetics.rate r pair.y - kinetics.rate r pair.x = α r

/-- **Constructive discordance lemma.** Every concordance witness can be realized by a weakly
monotonic kinetics.  The proof uses source-supported monotone interpolation reaction by reaction;
the sign clauses of the witness are precisely the compatibility conditions for this construction. -/
private theorem exists_sourceWeights_for_concordanceWitness
    (N : Network S) {α : N.R → ℝ} {σ : S → ℝ}
    (W : N.ConcordanceWitness α σ) (r : N.R) :
    ∃ w : S → ℝ,
      (∀ s : S, (N.reaction r).source s ≠ 0 → 0 < w s) ∧
      (α r = 0 →
        (∑ s ∈ (N.reaction r).source.support, w s * σ s) = 0) ∧
      (α r ≠ 0 →
        0 < α r * (∑ s ∈ (N.reaction r).source.support, w s * σ s)) := by
  classical
  let T := (N.reaction r).source.support
  let B : ℝ := ∑ s ∈ T, σ s
  by_cases ha : α r = 0
  · rcases W.sign_balance r ha with hzero | hmix
    · refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · intro s _
        exact one_pos
      · intro _
        apply Finset.sum_eq_zero
        intro s hs
        have hsrc : (N.reaction r).source s ≠ 0 := by
          simpa [T, Complex.support] using hs
        simp [hzero s hsrc]
      · exact fun h => (h ha).elim
    · obtain ⟨sneg, spos, hsnegSrc, hsposSrc, hsneg, hspos⟩ := hmix
      have hsnegT : sneg ∈ T := by
        simp [T, Complex.support, hsnegSrc]
      have hsposT : spos ∈ T := by
        simp [T, Complex.support, hsposSrc]
      by_cases hB : 0 ≤ B
      · let w : S → ℝ := fun s =>
          if s = sneg then 1 + B / (-σ sneg) else 1
        refine ⟨w, ?_, ?_, ?_⟩
        · intro s _
          by_cases hsn : s = sneg
          · subst s
            have hden : 0 < -σ sneg := neg_pos.mpr hsneg
            have hquot : 0 ≤ B / (-σ sneg) := div_nonneg hB hden.le
            dsimp [w]
            simp only [if_pos]
            linarith
          · simp [w, hsn]
        · intro _
          have hden : -σ sneg ≠ 0 := (neg_pos.mpr hsneg).ne'
          have hq :
              (∑ s ∈ T, w s * σ s) = B + (B / (-σ sneg)) * σ sneg := by
            calc
              (∑ s ∈ T, w s * σ s)
                  = ∑ s ∈ T, (σ s + if s = sneg then (B / (-σ sneg)) * σ s else 0) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      by_cases hsn : s = sneg
                      · subst s
                        simp [w]
                        ring
                      · simp [w, hsn]
              _ = B + (B / (-σ sneg)) * σ sneg := by
                    simp [B, hsnegT, Finset.sum_add_distrib]
          rw [hq]
          have hcancel : (B / (-σ sneg)) * (-σ sneg) = B :=
            div_mul_cancel₀ B hden
          have hterm : (B / (-σ sneg)) * σ sneg = -B := by
            calc
              (B / (-σ sneg)) * σ sneg
                  = -((B / (-σ sneg)) * (-σ sneg)) := by ring
              _ = -B := by rw [hcancel]
          rw [hterm]
          ring
        · exact fun h => (h ha).elim
      · have hBneg : B < 0 := lt_of_not_ge hB
        let w : S → ℝ := fun s =>
          if s = spos then 1 + (-B) / σ spos else 1
        refine ⟨w, ?_, ?_, ?_⟩
        · intro s _
          by_cases hsp : s = spos
          · subst s
            have hquot : 0 ≤ (-B) / σ spos :=
              div_nonneg (neg_nonneg.mpr hBneg.le) hspos.le
            dsimp [w]
            simp only [if_pos]
            linarith
          · simp [w, hsp]
        · intro _
          have hden : σ spos ≠ 0 := hspos.ne'
          have hq :
              (∑ s ∈ T, w s * σ s) = B + ((-B) / σ spos) * σ spos := by
            calc
              (∑ s ∈ T, w s * σ s)
                  = ∑ s ∈ T, (σ s + if s = spos then ((-B) / σ spos) * σ s else 0) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      by_cases hsp : s = spos
                      · subst s
                        simp [w]
                        ring
                      · simp [w, hsp]
              _ = B + ((-B) / σ spos) * σ spos := by
                    simp [B, hsposT, Finset.sum_add_distrib]
          rw [hq]
          field_simp [hden]
          ring
        · exact fun h => (h ha).elim
  · obtain ⟨s0, hs0Src, hs0Sign⟩ := W.sign_match r ha
    have hs0T : s0 ∈ T := by
      simp [T, Complex.support, hs0Src]
    let A : ℝ := ∑ s ∈ T, |σ s|
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun s _ => abs_nonneg (σ s)
    have hBabs : |B| ≤ A := by
      simpa [A, B] using Finset.abs_sum_le_sum_abs σ T
    let w : S → ℝ := fun s =>
      if s = s0 then 1 + (A + 1) / |σ s0| else 1
    have hapos_or_neg : α r < 0 ∨ 0 < α r := lt_or_gt_of_ne ha
    rcases hapos_or_neg with haneg | hapos
    · have hs0neg : σ s0 < 0 := by
        rw [← sign_eq_neg_one_iff, hs0Sign, sign_neg haneg]
      have habspos : 0 < |σ s0| := abs_pos.mpr hs0neg.ne
      refine ⟨w, ?_, ?_, ?_⟩
      · intro s _
        by_cases hs : s = s0
        · subst s
          have hquot : 0 ≤ (A + 1) / |σ s0| :=
            div_nonneg (by linarith) habspos.le
          simp [w]
          linarith
        · simp [w, hs]
      · exact fun h => (ha h).elim
      · intro _
        have hcorr : ((A + 1) / |σ s0|) * σ s0 = -(A + 1) := by
          rw [abs_of_neg hs0neg]
          have hne : -σ s0 ≠ 0 := (neg_pos.mpr hs0neg).ne'
          have hcancel : ((A + 1) / (-σ s0)) * (-σ s0) = A + 1 :=
            div_mul_cancel₀ (A + 1) hne
          calc
            ((A + 1) / (-σ s0)) * σ s0
                = -(((A + 1) / (-σ s0)) * (-σ s0)) := by ring
            _ = -(A + 1) := by rw [hcancel]
        have hq :
            (∑ s ∈ T, w s * σ s) = B - (A + 1) := by
          calc
            (∑ s ∈ T, w s * σ s)
                = ∑ s ∈ T,
                    (σ s + if s = s0 then ((A + 1) / |σ s0|) * σ s else 0) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      by_cases hse : s = s0
                      · subst s
                        simp [w]
                        ring
                      · simp [w, hse]
            _ = B + ((A + 1) / |σ s0|) * σ s0 := by
                  simp [B, hs0T, Finset.sum_add_distrib]
            _ = B - (A + 1) := by rw [hcorr]; ring
        have hBleA : B ≤ A := le_of_abs_le hBabs
        have hqneg : (∑ s ∈ T, w s * σ s) < 0 := by
          rw [hq]
          linarith
        exact mul_pos_of_neg_of_neg haneg hqneg
    · have hs0pos : 0 < σ s0 := by
        rw [← sign_eq_one_iff, hs0Sign, sign_pos hapos]
      have habspos : 0 < |σ s0| := abs_pos.mpr hs0pos.ne'
      refine ⟨w, ?_, ?_, ?_⟩
      · intro s _
        by_cases hs : s = s0
        · subst s
          have hquot : 0 ≤ (A + 1) / |σ s0| :=
            div_nonneg (by linarith) habspos.le
          simp [w]
          linarith
        · simp [w, hs]
      · exact fun h => (ha h).elim
      · intro _
        have hcorr : ((A + 1) / |σ s0|) * σ s0 = A + 1 := by
          rw [abs_of_pos hs0pos]
          exact div_mul_cancel₀ (A + 1) hs0pos.ne'
        have hq :
            (∑ s ∈ T, w s * σ s) = B + (A + 1) := by
          calc
            (∑ s ∈ T, w s * σ s)
                = ∑ s ∈ T,
                    (σ s + if s = s0 then ((A + 1) / |σ s0|) * σ s else 0) := by
                      apply Finset.sum_congr rfl
                      intro s hs
                      by_cases hse : s = s0
                      · subst s
                        simp [w]
                        ring
                      · simp [w, hse]
            _ = B + ((A + 1) / |σ s0|) * σ s0 := by
                  simp [B, hs0T, Finset.sum_add_distrib]
            _ = B + (A + 1) := by rw [hcorr]
        have hnegAleB : -A ≤ B := neg_le_of_abs_le hBabs
        have hqpos : 0 < (∑ s ∈ T, w s * σ s) := by
          rw [hq]
          linarith
        exact mul_pos hapos hqpos

private def sourceInterior (N : Network S) (r : N.R) (x : Concentration S) : Prop :=
  ∀ s : S, (N.reaction r).source s ≠ 0 → 0 < x s

private noncomputable def sourceLinearForm (N : Network S)
    (w : N.R → S → ℝ) (r : N.R) (x : Concentration S) : ℝ :=
  ∑ s ∈ (N.reaction r).source.support, w r s * x s

private noncomputable def guardedLinearKinetics (N : Network S)
    (w : N.R → S → ℝ) (lam : N.R → ℝ)
    (hw : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → 0 < w r s)
    (hlam : ∀ r : N.R, 0 < lam r) : Kinetics N := by
  classical
  refine {
    rate := fun r x =>
      if N.sourceInterior r x then lam r * N.sourceLinearForm w r x else 0
    rate_nonneg := ?_
    rate_vanishing := ?_
    rate_supportDep := ?_
    rate_mono := ?_ }
  · intro r x hx
    by_cases hi : N.sourceInterior r x
    · simp only [hi, if_pos]
      exact mul_nonneg (hlam r).le (Finset.sum_nonneg fun s hs => by
        have hsrc : (N.reaction r).source s ≠ 0 := by
          simpa [Complex.support] using hs
        exact mul_nonneg (hw r s hsrc).le (hx s))
    · simp only [hi, if_false]
      exact le_rfl
  · intro r x s hsrc hxs
    have hnot : ¬ N.sourceInterior r x := by
      intro hi
      have := hi s hsrc
      linarith
    simp only [hnot, if_false]
  · intro r x y hxy
    have hi : N.sourceInterior r x ↔ N.sourceInterior r y := by
      constructor
      · intro hx s hsrc
        rw [← hxy s hsrc]
        exact hx s hsrc
      · intro hy s hsrc
        rw [hxy s hsrc]
        exact hy s hsrc
    by_cases hx : N.sourceInterior r x
    · have hy : N.sourceInterior r y := hi.mp hx
      simp only [hx, hy, if_pos]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      have hsrc : (N.reaction r).source s ≠ 0 := by
        simpa [Complex.support] using hs
      rw [hxy s hsrc]
    · have hy : ¬ N.sourceInterior r y := fun h => hx (hi.mpr h)
      simp only [hx, hy, if_false]
  · intro r x hx y hy hxy
    by_cases hix : N.sourceInterior r x
    · have hiy : N.sourceInterior r y := by
        intro s hsrc
        exact lt_of_lt_of_le (hix s hsrc) (hxy s)
      simp only [hix, hiy, if_pos]
      apply mul_le_mul_of_nonneg_left _ (hlam r).le
      apply Finset.sum_le_sum
      intro s hs
      have hsrc : (N.reaction r).source s ≠ 0 := by
        simpa [Complex.support] using hs
      exact mul_le_mul_of_nonneg_left (hxy s) (hw r s hsrc).le
    · simp only [hix, if_false]
      by_cases hiy : N.sourceInterior r y
      · simp only [hiy, if_pos]
        exact mul_nonneg (hlam r).le (Finset.sum_nonneg fun s hs => by
          have hsrc : (N.reaction r).source s ≠ 0 := by
            simpa [Complex.support] using hs
          exact mul_nonneg (hw r s hsrc).le (hy s))
      · simp only [hiy, if_false]
        exact le_rfl

private theorem guardedLinearKinetics_weaklyMonotonic
    (N : Network S) (w : N.R → S → ℝ) (lam : N.R → ℝ)
    (hw : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → 0 < w r s)
    (hlam : ∀ r : N.R, 0 < lam r) :
    (N.guardedLinearKinetics w lam hw hlam).WeaklyMonotonic := by
  classical
  intro cs css hcs hcss r hcsg hcssg
  have hics : N.sourceInterior r cs := by
    intro s hsrc
    exact lt_of_le_of_ne (hcs s) (Ne.symm (hcsg s hsrc))
  have hicss : N.sourceInterior r css := by
    intro s hsrc
    exact lt_of_le_of_ne (hcss s) (Ne.symm (hcssg s hsrc))
  have hrate_cs :
      (N.guardedLinearKinetics w lam hw hlam).rate r cs =
        lam r * N.sourceLinearForm w r cs := by
    simp [guardedLinearKinetics, hics]
  have hrate_css :
      (N.guardedLinearKinetics w lam hw hlam).rate r css =
        lam r * N.sourceLinearForm w r css := by
    simp [guardedLinearKinetics, hicss]
  constructor
  · intro hlt
    rw [hrate_cs, hrate_css] at hlt
    have hlin : N.sourceLinearForm w r cs < N.sourceLinearForm w r css := by
      nlinarith [hlam r]
    by_contra hnone
    have hrev : N.sourceLinearForm w r css ≤ N.sourceLinearForm w r cs := by
      apply Finset.sum_le_sum
      intro s hs
      have hsrc : (N.reaction r).source s ≠ 0 := by
        simpa [Complex.support] using hs
      have hsle : css s ≤ cs s := by
        exact not_lt.mp (fun hsc => hnone ⟨s, hsrc, hsc⟩)
      exact mul_le_mul_of_nonneg_left hsle (hw r s hsrc).le
    exact (not_lt_of_ge hrev) hlin
  · intro heq
    rw [hrate_cs, hrate_css] at heq
    have hlinEq : N.sourceLinearForm w r cs = N.sourceLinearForm w r css :=
      (mul_left_cancel₀ (hlam r).ne' heq)
    by_cases hall : ∀ s : S, (N.reaction r).source s ≠ 0 → cs s = css s
    · exact Or.inl hall
    · right
      have hinc : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ cs s < css s := by
        by_contra hno
        have hle : ∀ s : S, (N.reaction r).source s ≠ 0 → css s ≤ cs s := by
          intro s hsrc
          exact not_lt.mp (fun hlt => hno ⟨s, hsrc, hlt⟩)
        push_neg at hall
        obtain ⟨s0, hs0src, hs0ne⟩ := hall
        have hs0lt : css s0 < cs s0 :=
          lt_of_le_of_ne (hle s0 hs0src) (Ne.symm hs0ne)
        have hs0mem : s0 ∈ (N.reaction r).source.support := by
          simp [Complex.support, hs0src]
        have hsumlt : N.sourceLinearForm w r css < N.sourceLinearForm w r cs := by
          apply Finset.sum_lt_sum
          · intro s hs
            have hsrc : (N.reaction r).source s ≠ 0 := by
              simpa [Complex.support] using hs
            exact mul_le_mul_of_nonneg_left (hle s hsrc) (hw r s hsrc).le
          · refine ⟨s0, hs0mem, ?_⟩
            exact mul_lt_mul_of_pos_left hs0lt (hw r s0 hs0src)
        exact (ne_of_lt hsumlt) hlinEq.symm
      have hdec : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ css s < cs s := by
        by_contra hno
        have hle : ∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≤ css s := by
          intro s hsrc
          exact not_lt.mp (fun hlt => hno ⟨s, hsrc, hlt⟩)
        push_neg at hall
        obtain ⟨s0, hs0src, hs0ne⟩ := hall
        have hs0lt : cs s0 < css s0 := lt_of_le_of_ne (hle s0 hs0src) hs0ne
        have hs0mem : s0 ∈ (N.reaction r).source.support := by
          simp [Complex.support, hs0src]
        have hsumlt : N.sourceLinearForm w r cs < N.sourceLinearForm w r css := by
          apply Finset.sum_lt_sum
          · intro s hs
            have hsrc : (N.reaction r).source s ≠ 0 := by
              simpa [Complex.support] using hs
            exact mul_le_mul_of_nonneg_left (hle s hsrc) (hw r s hsrc).le
          · refine ⟨s0, hs0mem, ?_⟩
            exact mul_lt_mul_of_pos_left hs0lt (hw r s0 hs0src)
        exact (ne_of_lt hsumlt) hlinEq
      obtain ⟨si, hsiSrc, hsi⟩ := hinc
      obtain ⟨sd, hsdSrc, hsd⟩ := hdec
      exact ⟨si, sd, hsiSrc, hsdSrc, hsi, hsd⟩

/-- **Constructive discordance lemma.** Every concordance witness can be realized by a weakly
monotonic kinetics.  The proof uses a boundary-guarded positive linear form on each source
support.  The witness sign clauses are exactly what is needed to choose strictly positive source
weights whose displacement has the prescribed reaction-rate sign (or vanishes when `α r = 0`). -/
theorem realize_concordanceWitness
    (N : Network S) {α : N.R → ℝ} {σ : S → ℝ}
    (W : N.ConcordanceWitness α σ) :
    Nonempty (N.ConcordanceKineticsRealization α σ W) := by
  classical
  have hweights : ∀ r : N.R, ∃ w : S → ℝ,
      (∀ s : S, (N.reaction r).source s ≠ 0 → 0 < w s) ∧
      (α r = 0 →
        (∑ s ∈ (N.reaction r).source.support, w s * σ s) = 0) ∧
      (α r ≠ 0 →
        0 < α r * (∑ s ∈ (N.reaction r).source.support, w s * σ s)) :=
    fun r => N.exists_sourceWeights_for_concordanceWitness W r
  let w : N.R → S → ℝ := fun r => Classical.choose (hweights r)
  have hwSpec : ∀ r : N.R,
      (∀ s : S, (N.reaction r).source s ≠ 0 → 0 < w r s) ∧
      (α r = 0 →
        (∑ s ∈ (N.reaction r).source.support, w r s * σ s) = 0) ∧
      (α r ≠ 0 →
        0 < α r * (∑ s ∈ (N.reaction r).source.support, w r s * σ s)) := by
    intro r
    exact Classical.choose_spec (hweights r)
  let q : N.R → ℝ := fun r =>
    ∑ s ∈ (N.reaction r).source.support, w r s * σ s
  let lam : N.R → ℝ := fun r => if h : α r = 0 then 1 else α r / q r
  have hwpos : ∀ r : N.R, ∀ s : S,
      (N.reaction r).source s ≠ 0 → 0 < w r s := fun r => (hwSpec r).1
  have hqzero : ∀ r : N.R, α r = 0 → q r = 0 := by
    intro r hr
    exact (hwSpec r).2.1 hr
  have hqprod : ∀ r : N.R, α r ≠ 0 → 0 < α r * q r := by
    intro r hr
    exact (hwSpec r).2.2 hr
  have hlampos : ∀ r : N.R, 0 < lam r := by
    intro r
    by_cases hr : α r = 0
    · simp [lam, hr]
    · have hp := hqprod r hr
      rcases (mul_pos_iff.mp hp) with hpp | hnn
      · simp [lam, hr, div_pos hpp.1 hpp.2]
      · simp [lam, hr, div_pos_of_neg_of_neg hnn.1 hnn.2]
  let x : Concentration S := fun s => |σ s| + 1
  let y : Concentration S := fun s => x s + σ s
  have hxpos : x.Positive := by
    intro s
    dsimp [x]
    linarith [abs_nonneg (σ s)]
  have hypos : y.Positive := by
    intro s
    dsimp [y, x]
    linarith [neg_abs_le (σ s)]
  have hdisp : y - x = σ := by
    ext s
    simp [y, x]
  let pair : N.PositivePairRealizing σ := {
    x := x
    y := y
    scale := 1
    scale_pos := one_pos
    x_pos := hxpos
    y_pos := hypos
    displacement := by simpa using hdisp }
  let K : Kinetics N := N.guardedLinearKinetics w lam hwpos hlampos
  have hwm : K.WeaklyMonotonic := by
    exact N.guardedLinearKinetics_weaklyMonotonic w lam hwpos hlampos
  refine ⟨{
    pair := pair
    kinetics := K
    weaklyMonotonic := hwm
    rateDifference := ?_ }⟩
  intro r
  have hix : N.sourceInterior r x := by
    intro s _
    exact hxpos s
  have hiy : N.sourceInterior r y := by
    intro s _
    exact hypos s
  have hlinDiff :
      N.sourceLinearForm w r y - N.sourceLinearForm w r x = q r := by
    simp only [sourceLinearForm, q]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hsdisp : y s - x s = σ s := by
      have := congrFun hdisp s
      simpa [Pi.sub_apply] using this
    rw [← mul_sub, hsdisp]
  have hrateDiff : K.rate r y - K.rate r x = lam r * q r := by
    simp only [K, guardedLinearKinetics, hix, hiy, if_pos]
    rw [← mul_sub, hlinDiff]
  rw [hrateDiff]
  by_cases hr : α r = 0
  · rw [hqzero r hr]
    simp [hr]
  · have hqne : q r ≠ 0 := by
      intro hq
      have hp := hqprod r hr
      rw [hq, mul_zero] at hp
      exact (lt_irrefl 0) hp
    simp [lam, hr, hqne]

/-- The realized discordance kinetics has equal vector field at its two distinct compatible
positive states. -/
theorem concordanceKineticsRealization_noninjective
    {α : N.R → ℝ} {σ : S → ℝ} {W : N.ConcordanceWitness α σ}
    (R : N.ConcordanceKineticsRealization α σ W) :
    R.pair.x ≠ R.pair.y ∧
    N.StoichCompatible R.pair.x R.pair.y ∧
    R.kinetics.vectorField R.pair.x = R.kinetics.vectorField R.pair.y := by
  constructor
  · intro hxy
    have hz : R.pair.y - R.pair.x = 0 := sub_eq_zero.mpr hxy.symm
    rw [R.pair.displacement] at hz
    exact W.sigma_ne ((smul_eq_zero.mp hz).resolve_left R.pair.scale_pos.ne')
  constructor
  · have hσS := W.mem_stoich
    rw [Network.StoichCompatible]
    -- `y-x = scale • σ` and the stoichiometric subspace is closed under scaling.
    simpa [R.pair.displacement] using N.stoichSubspace.smul_mem R.pair.scale hσS
  · funext s
    have hker := W.mem_kerL
    have hcoord := N.inKerL_apply hker s
    rw [Kinetics.vectorField_apply, Kinetics.vectorField_apply]
    rw [← sub_eq_zero, ← neg_eq_zero, neg_sub]
    simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
    have hr : ∀ r : N.R,
        (R.kinetics.rate r R.pair.y - R.kinetics.rate r R.pair.x) = α r :=
      R.rateDifference
    simpa [hr] using hcoord

/-- Discordance produces a noninjective weakly monotonic kinetics. -/
theorem exists_noninjective_weaklyMonotonic_of_not_concordant
    (N : Network S) (hN : ¬ N.Concordant) :
    ∃ K : Kinetics N,
      K.WeaklyMonotonic ∧ ¬ K.Injective := by
  rw [Concordant] at hN
  push_neg at hN
  obtain ⟨α, σ, W⟩ := hN
  obtain ⟨R⟩ := N.realize_concordanceWitness W
  refine ⟨R.kinetics, R.weaklyMonotonic, ?_⟩
  intro hinj
  obtain ⟨hne, hcomp, hfield⟩ := concordanceKineticsRealization_noninjective R
  -- Apply injectivity in the compatibility class represented by `R.pair.x`.
  have hx : R.pair.x ∈ N.positiveCompatibilityClass R.pair.x :=
    ⟨Network.StoichCompatible.refl (N := N) _, R.pair.x_pos⟩
  have hy : R.pair.y ∈ N.positiveCompatibilityClass R.pair.x :=
    ⟨hcomp, R.pair.y_pos⟩
  exact hne (hinj R.pair.x hx hy hfield)

/-- **Concordance characterization.** A network is concordant iff every weakly monotonic kinetics
on it is injective on positive stoichiometric compatibility classes. -/
theorem concordant_iff_all_weaklyMonotonic_injective (N : Network S) :
    N.Concordant ↔
      ∀ K : Kinetics N, K.WeaklyMonotonic → K.Injective := by
  constructor
  · intro hN K hK
    exact hN.injective_of_weaklyMonotonic hK
  · intro hall
    by_contra hN
    obtain ⟨K, hwm, hnon⟩ := N.exists_noninjective_weaklyMonotonic_of_not_concordant hN
    exact hnon (hall K hwm)

end Network
end CRNT
