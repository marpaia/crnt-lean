import CRNT.Deficiency.BorosBirchGraph
import CRNT.Deficiency.KineticBlock
import CRNT.Analysis.BorosEdgeSumEstimate
import CRNT.Analysis.BorosZeroSumMax
import CRNT.Theorems.DeficiencyZero.Dissipation

/-!
# The finite single-linkage rate estimate

This file combines the finite path estimate with the reaction-rate bounds in one linkage class.
It proves the strict sign of the mass-action kinetic pairing once a class has a sufficiently
large potential range.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reactions whose source belongs to one fixed linkage class. -/
abbrev BorosClassReaction (N : Network S) (q : Quotient N.linkedSetoid) :=
  {r : N.R // N.classOf (N.sourceIdx r) = q}

/-- If a zero-mean class potential reaches far enough above its nonpositive part, the
single-linkage mass-action pairing is strictly negative. The quantitative budget accounts for
the largest possible source cost from every reaction in the class. -/
theorem WeaklyReversible.boros_classMassActionPairing_neg_of_largeRange
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (rate : N.R → ℝ)
    (q : Quotient N.linkedSetoid) (z : N.ComplexIdx → ℝ)
    {m b kmin kmax : ℝ}
    (hzmax : ∀ c, N.classOf c = q → z c ≤ m)
    (hstart : ∃ a, N.classOf a = q ∧ z a = m)
    (hend : ∃ c, N.classOf c = q ∧ z c ≤ 0)
    (hb : 0 ≤ b) (hkminpos : 0 < kmin)
    (hkmin : ∀ r, N.classOf (N.sourceIdx r) = q → kmin ≤ rate r)
    (hkmax : ∀ r, N.classOf (N.sourceIdx r) = q → rate r ≤ kmax)
    (hbudget : (Fintype.card (N.BorosClassReaction q) : ℝ) * kmax < kmin * b)
    (hrange : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < m) :
    ∑ r : N.BorosClassReaction q,
      rate r.val * Real.exp (z (N.sourceIdx r.val)) *
        (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) < 0 := by
  classical
  let gap : N.ComplexIdx → ℝ := fun c => if N.classOf c = q then m - z c else 0
  have hgap_nonneg : ∀ c, 0 ≤ gap c := by
    intro c
    by_cases hc : N.classOf c = q
    · simp [gap, hc]
      exact hzmax c hc
    · simp [gap, hc]
  obtain ⟨a, haq, haz⟩ := hstart
  obtain ⟨c, hcq, hcz⟩ := hend
  have hclass : N.classOf a = N.classOf c := haq.trans hcq.symm
  have hgap_a : gap a = 0 := by simp [gap, haq, haz]
  have hgap_c : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < gap c := by
    simp [gap, hcq]
    linarith
  obtain ⟨r, hrclass, hrlarge⟩ :=
    WeaklyReversible.exists_reaction_edge_weightedIncrement_gt_with_context
      N hwr b hb a c hclass gap hgap_a hgap_c
  let E := N.BorosClassReaction q
  let src : E → N.ComplexIdx := fun e => N.sourceIdx e.val
  let tgt : E → N.ComplexIdx := fun e => N.targetIdx e.val
  let classRate : E → ℝ := fun e => rate e.val
  have hlarge : ∃ e : E, b < Real.exp (-gap (src e)) * gap (tgt e) := by
    have hrq : N.classOf (N.sourceIdx r) = q := hrclass.trans haq
    exact ⟨⟨r, hrq⟩, by simpa [E, src, tgt] using hrlarge⟩
  have hedgeSum : 0 < ∑ e : E, classRate e * Real.exp (-gap (src e)) *
      (gap (tgt e) - gap (src e)) := by
    apply Analysis.boros_weightedEdgeSum_pos src tgt gap classRate hgap_nonneg hkminpos
    · intro e
      exact hkmin e.val e.property
    · intro e
      exact hkmax e.val e.property
    · exact hlarge
    · simpa [E] using hbudget
  have hterm (e : E) :
      rate e.val * Real.exp (z (N.sourceIdx e.val)) *
          (z (N.targetIdx e.val) - z (N.sourceIdx e.val)) =
        -(Real.exp m * (classRate e * Real.exp (-gap (src e)) *
          (gap (tgt e) - gap (src e)))) := by
    have hs : N.classOf (N.sourceIdx e.val) = q := e.property
    have ht : N.classOf (N.targetIdx e.val) = q := by
      rw [← N.classOf_sourceIdx_eq_targetIdx]
      exact hs
    have hexp : Real.exp (z (N.sourceIdx e.val)) =
        Real.exp m * Real.exp (-gap (src e)) := by
      have hz : z (N.sourceIdx e.val) = m + -gap (src e) := by
        simp [gap, src, hs]
      rw [hz, Real.exp_add]
    have hdiff : z (N.targetIdx e.val) - z (N.sourceIdx e.val) =
        -(gap (tgt e) - gap (src e)) := by
      simp [gap, src, tgt, hs, ht]
    rw [hexp, hdiff]
    simp only [classRate]
    ring
  have hsumrel :
      (∑ e : E, rate e.val * Real.exp (z (N.sourceIdx e.val)) *
        (z (N.targetIdx e.val) - z (N.sourceIdx e.val))) =
        -(Real.exp m * ∑ e : E,
          classRate e * Real.exp (-gap (src e)) * (gap (tgt e) - gap (src e))) := by
    calc
      _ = ∑ e : E, -(Real.exp m *
          (classRate e * Real.exp (-gap (src e)) *
            (gap (tgt e) - gap (src e)))) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hterm e
      _ = -(Real.exp m * ∑ e : E,
          classRate e * Real.exp (-gap (src e)) *
            (gap (tgt e) - gap (src e))) := by
            rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hscaled : -(Real.exp m *
      ∑ e : E, classRate e * Real.exp (-gap (src e)) *
        (gap (tgt e) - gap (src e))) < 0 := by
    calc
      _ = Real.exp m *
          -(∑ e : E, classRate e * Real.exp (-gap (src e)) *
            (gap (tgt e) - gap (src e))) := by ring
      _ < 0 := mul_neg_of_pos_of_neg (Real.exp_pos m) (neg_neg_of_pos hedgeSum)
  rw [hsumrel]
  exact hscaled

/-- Uniform version of the class estimate under a bounded additive perturbation of the log
potential. The perturbation changes each source rate by a factor in `[exp(-rho), exp(rho)]`. -/
theorem WeaklyReversible.boros_classPairing_neg_of_largeRange_boundedPerturbation
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (q : Quotient N.linkedSetoid) (z w : N.ComplexIdx → ℝ)
    {m b kmin kmax rho : ℝ}
    (hzmax : ∀ c, N.classOf c = q → z c ≤ m)
    (hstart : ∃ a, N.classOf a = q ∧ z a = m)
    (hend : ∃ c, N.classOf c = q ∧ z c ≤ 0)
    (hwbound : ∀ c, N.classOf c = q → |w c| ≤ rho)
    (hb : 0 ≤ b)
    (hkminpos : 0 < kmin)
    (hkmin : ∀ r, N.classOf (N.sourceIdx r) = q → kmin ≤ κ.k r)
    (hkmax : ∀ r, N.classOf (N.sourceIdx r) = q → κ.k r ≤ kmax)
    (hbudget : (Fintype.card (N.BorosClassReaction q) : ℝ) *
      (kmax * Real.exp rho) < (kmin * Real.exp (-rho)) * b)
    (hrange : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < m) :
    ∑ r : N.BorosClassReaction q,
      κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
        (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) < 0 := by
  let rate : N.R → ℝ := fun r => κ.k r * Real.exp (w (N.sourceIdx r))
  have hrate_min : ∀ r, N.classOf (N.sourceIdx r) = q →
      kmin * Real.exp (-rho) ≤ rate r := by
    intro r hr
    have hwlo : -rho ≤ w (N.sourceIdx r) := (abs_le.mp (hwbound _ hr)).1
    have hexp : Real.exp (-rho) ≤ Real.exp (w (N.sourceIdx r)) :=
      Real.exp_le_exp.mpr hwlo
    dsimp [rate]
    calc
      kmin * Real.exp (-rho) ≤ κ.k r * Real.exp (-rho) :=
        mul_le_mul_of_nonneg_right (hkmin r hr) (Real.exp_pos _).le
      _ ≤ κ.k r * Real.exp (w (N.sourceIdx r)) :=
        mul_le_mul_of_nonneg_left hexp (κ.positive r).le
  have hrate_max : ∀ r, N.classOf (N.sourceIdx r) = q →
      rate r ≤ kmax * Real.exp rho := by
    intro r hr
    have hwup : w (N.sourceIdx r) ≤ rho := (abs_le.mp (hwbound _ hr)).2
    have hexp : Real.exp (w (N.sourceIdx r)) ≤ Real.exp rho :=
      Real.exp_le_exp.mpr hwup
    dsimp [rate]
    calc
      κ.k r * Real.exp (w (N.sourceIdx r)) ≤ κ.k r * Real.exp rho :=
        mul_le_mul_of_nonneg_left hexp (κ.positive r).le
      _ ≤ kmax * Real.exp rho :=
        mul_le_mul_of_nonneg_right (hkmax r hr) (Real.exp_pos _).le
  have hkmin_mod_pos : 0 < kmin * Real.exp (-rho) :=
    mul_pos hkminpos (Real.exp_pos _)
  have hneg := WeaklyReversible.boros_classMassActionPairing_neg_of_largeRange
    N hwr rate q z
    (m := m) (b := b) (kmin := kmin * Real.exp (-rho))
    (kmax := kmax * Real.exp rho) hzmax hstart hend hb
    hkmin_mod_pos hrate_min hrate_max hbudget hrange
  have hrewrite : ∀ r : N.BorosClassReaction q,
      rate r.val * Real.exp (z (N.sourceIdx r.val)) =
        κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) := by
    intro r
    simp [rate, Real.exp_add]
    ring
  have hsumRewrite :
      (∑ r : N.BorosClassReaction q,
        rate r.val * Real.exp (z (N.sourceIdx r.val)) *
          (z (N.targetIdx r.val) - z (N.sourceIdx r.val))) =
      ∑ r : N.BorosClassReaction q,
        κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
          (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hrewrite r]
  rw [← hsumRewrite]
  exact hneg

/-- The bounded-perturbation estimate follows from the class zero-sum constraint once the
class component has large enough Euclidean norm. -/
theorem WeaklyReversible.boros_classPairing_neg_of_zeroSum_norm_large
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (q : Quotient N.linkedSetoid) (z w : N.ComplexIdx → ℝ)
    (hclassNonempty : ∃ c, N.classOf c = q)
    {threshold b kmin kmax rho : ℝ}
    (hzero : ∑ c : {c : N.ComplexIdx // N.classOf c = q}, z c.val = 0)
    (hnorm : (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) *
      (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) * threshold <
        ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => z c.val)‖)
    (hwbound : ∀ c, N.classOf c = q → |w c| ≤ rho)
    (hb : 0 ≤ b) (hkminpos : 0 < kmin)
    (hkmin : ∀ r, N.classOf (N.sourceIdx r) = q → kmin ≤ κ.k r)
    (hkmax : ∀ r, N.classOf (N.sourceIdx r) = q → κ.k r ≤ kmax)
    (hbudget : (Fintype.card (N.BorosClassReaction q) : ℝ) *
      (kmax * Real.exp rho) < (kmin * Real.exp (-rho)) * b)
    (hthreshold : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength <
      threshold) :
    ∑ r : N.BorosClassReaction q,
      κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
        (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) < 0 := by
  classical
  let C := {c : N.ComplexIdx // N.classOf c = q}
  letI : Nonempty C := by
    obtain ⟨c, hc⟩ := hclassNonempty
    exact ⟨⟨c, hc⟩⟩
  let v : C → ℝ := fun c => z c.val
  obtain ⟨j, hj⟩ := Analysis.exists_coordinate_gt_of_zero_sum_of_norm_large
    v hzero (L := threshold) (by simpa [C, v] using hnorm)
  let values : Finset ℝ := Finset.univ.image v
  have hvalues_nonempty : values.Nonempty := by
    obtain ⟨c⟩ := ‹Nonempty C›
    exact ⟨v c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩⟩
  let m : ℝ := values.max' hvalues_nonempty
  have hvle : ∀ c : C, v c ≤ m := by
    intro c
    exact Finset.le_max' values (v c)
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
  have hm_mem : m ∈ values := Finset.max'_mem values hvalues_nonempty
  obtain ⟨a, ha_mem, ha_eq⟩ := Finset.mem_image.mp hm_mem
  have hmax : v a = m := ha_eq
  have hthreshold_lt_m : threshold < m := lt_of_lt_of_le hj (hvle j)
  have hstart : ∃ c, N.classOf c = q ∧ z c = m :=
    ⟨a.val, a.property, by simpa [v] using hmax⟩
  have hend : ∃ c, N.classOf c = q ∧ z c ≤ 0 := by
    by_contra hnone
    push_neg at hnone
    have hsumpos : 0 < ∑ c : C, v c := by
      obtain ⟨c₀⟩ := ‹Nonempty C›
      apply Finset.sum_pos'
      · intro c _
        exact (hnone c.val c.property).le
      · exact ⟨c₀, Finset.mem_univ c₀, hnone c₀.val c₀.property⟩
    have : (∑ c : C, v c) = 0 := by simpa [C, v] using hzero
    linarith
  have hrange : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < m :=
    lt_trans hthreshold hthreshold_lt_m
  exact WeaklyReversible.boros_classPairing_neg_of_largeRange_boundedPerturbation
    N hwr κ q z w (m := m) (b := b) (kmin := kmin)
    (kmax := kmax) (rho := rho)
    (fun c hc => by
      let ci : C := ⟨c, hc⟩
      exact hvle ci)
    hstart hend hwbound hb hkminpos hkmin hkmax hbudget hrange

/-- A class-constant shift of the exponent multiplies the whole class pairing by a positive
factor, so it does not change its sign. This is the form used for the orthogonal residual of the
Boros selector: orthogonality to the incidence space makes that residual constant on each
linkage class. -/
theorem WeaklyReversible.boros_classPairing_neg_of_zeroSum_norm_large_classShift
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (q : Quotient N.linkedSetoid) (z w : N.ComplexIdx → ℝ)
    (alpha : Quotient N.linkedSetoid → ℝ)
    (hclassNonempty : ∃ c, N.classOf c = q)
    {threshold b kmin kmax rho : ℝ}
    (hzero : ∑ c : {c : N.ComplexIdx // N.classOf c = q}, z c.val = 0)
    (hnorm : (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) *
      (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) * threshold <
        ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => z c.val)‖)
    (hwbound : ∀ c, N.classOf c = q → |w c| ≤ rho)
    (hb : 0 ≤ b) (hkminpos : 0 < kmin)
    (hkmin : ∀ r, N.classOf (N.sourceIdx r) = q → kmin ≤ κ.k r)
    (hkmax : ∀ r, N.classOf (N.sourceIdx r) = q → κ.k r ≤ kmax)
    (hbudget : (Fintype.card (N.BorosClassReaction q) : ℝ) *
      (kmax * Real.exp rho) < (kmin * Real.exp (-rho)) * b)
    (hthreshold : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength <
      threshold) :
    ∑ r : N.BorosClassReaction q,
      κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q) *
        (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) < 0 := by
  have hbase := WeaklyReversible.boros_classPairing_neg_of_zeroSum_norm_large
    N hwr κ q z w hclassNonempty hzero hnorm hwbound hb hkminpos hkmin hkmax
    hbudget hthreshold
  have hfactor : ∀ r : N.BorosClassReaction q,
      κ.k r.val * Real.exp
          (z (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q) *
          (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) =
        Real.exp (alpha q) *
          (κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
            (z (N.targetIdx r.val) - z (N.sourceIdx r.val))) := by
    intro r
    rw [show z (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q =
        alpha q + (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) by ring,
      Real.exp_add]
    ring
  have hsum :
      (∑ r : N.BorosClassReaction q,
        κ.k r.val * Real.exp
          (z (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q) *
          (z (N.targetIdx r.val) - z (N.sourceIdx r.val))) =
      Real.exp (alpha q) *
        ∑ r : N.BorosClassReaction q,
          κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
            (z (N.targetIdx r.val) - z (N.sourceIdx r.val)) := by
    calc
      _ = ∑ r : N.BorosClassReaction q,
          Real.exp (alpha q) *
            (κ.k r.val * Real.exp (z (N.sourceIdx r.val) + w (N.sourceIdx r.val)) *
              (z (N.targetIdx r.val) - z (N.sourceIdx r.val))) := by
                apply Finset.sum_congr rfl
                intro r _
                exact hfactor r
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hbase

end Network
end CRNT
