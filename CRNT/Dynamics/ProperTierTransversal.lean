import CRNT.Dynamics.TierSubsequenceExtraction
import CRNT.Dynamics.SiphonConservation
import CRNT.Kinetics.Generalized
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences

/-!
# Proper tier sequences are transversal

This file formalizes Lemma 4.1 of Anderson--Cappelletti--Kim--Nguyen by a compactness
argument equivalent to the separator argument used in the paper.

Assume a proper tier sequence were not transversal.  Then every reaction joins complexes in the
same tier, so every reaction-vector pairing with `log xₙ` stays bounded.  Set

`vₙ = log xₙ - log x₀`.

Logarithmic escape implies `‖vₙ‖ → ∞`.  Normalize `vₙ` and extract a convergent subsequence on the
unit sphere.  Its nonzero limit `w` is orthogonal to every reaction vector and hence to the whole
stoichiometric subspace.  On the other hand `xₙ-x₀` belongs to that subspace by properness, while
strict monotonicity of `log` makes `xₙ-x₀` and `vₙ` have the same coordinate signs.  For a late
normalized subsequence point those signs agree with every nonzero coordinate of `w`, so
`⟨w,xₙ-x₀⟩>0`, contradicting orthogonality.

This avoids importing the older separator theorem cited in the paper and makes the finite-
dimensional argument explicit in Lean.
-/

open Filter Set
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Log displacement from a fixed positive reference point. -/
noncomputable def tierLogDisplacement (x₀ x : Concentration S) : Concentration S :=
  fun s => Real.log (x s) - Real.log (x₀ s)

/-- Log displacement has the same coordinate sign as ordinary displacement. -/
theorem sameSign_sub_tierLogDisplacement {x₀ x : Concentration S}
    (hx₀ : x₀.Positive) (hx : x.Positive) :
    SameSign (x - x₀) (tierLogDisplacement x₀ x) := by
  exact logRatio_sameSign hx hx₀

/-- The `L1` size of a finite vector is controlled by its Pi norm. -/
theorem sum_abs_le_card_mul_norm (v : S → ℝ) :
    (∑ s : S, |v s|) ≤ (Fintype.card S : ℝ) * ‖v‖ := by
  calc
    (∑ s : S, |v s|) ≤ ∑ _s : S, ‖v‖ := by
      apply Finset.sum_le_sum
      intro s _
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v s
    _ = (Fintype.card S : ℝ) * ‖v‖ := by simp [mul_comm]

/-- Logarithmic escape is unchanged, up to a fixed additive vector, by taking log displacement
from one positive reference point; in particular its Pi norm tends to infinity. -/
theorem norm_tierLogDisplacement_tendsto_atTop
    {xs : ℕ → Concentration S} (hesc : LogEscapes xs) (x₀ : Concentration S) :
    Tendsto (fun n => ‖tierLogDisplacement x₀ (xs n)‖) atTop atTop := by
  classical
  by_cases hS : Nonempty S
  · let C : ℝ := ∑ s : S, |Real.log (x₀ s)|
    have hcard : 0 < (Fintype.card S : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [tendsto_atTop_atTop]
    intro R
    obtain ⟨N, hN⟩ := hesc ((Fintype.card S : ℝ) * max R 0 + C)
    refine ⟨N, ?_⟩
    intro n hn
    have hlarge := hN n hn
    have hsplit :
        (∑ s : S, |Real.log (xs n s)|) ≤
          (∑ s : S, |tierLogDisplacement x₀ (xs n) s|) + C := by
      dsimp [C]
      apply le_trans (Finset.sum_le_sum fun s _ => ?_) (by rw [Finset.sum_add_distrib])
      have heq : Real.log (xs n s) =
          tierLogDisplacement x₀ (xs n) s + Real.log (x₀ s) := by
        simp [tierLogDisplacement]
      rw [heq]
      exact abs_add_le _ _
    have hv := sum_abs_le_card_mul_norm (tierLogDisplacement x₀ (xs n))
    have hmul : (Fintype.card S : ℝ) * max R 0 ≤
        (Fintype.card S : ℝ) * ‖tierLogDisplacement x₀ (xs n)‖ := by
      linarith
    have hmax : max R 0 ≤ ‖tierLogDisplacement x₀ (xs n)‖ :=
      le_of_mul_le_mul_left hmul hcard
    exact (le_max_left R 0).trans hmax
  · haveI : IsEmpty S := not_nonempty_iff.mp hS
    exfalso
    obtain ⟨N, hN⟩ := hesc 1
    have := hN N le_rfl
    exact absurd this (by norm_num)

/-- Normalized log displacement.  It is eventually on the unit sphere because the denominator
escapes to infinity. -/
noncomputable def normalizedTierLogDisplacement (x₀ x : Concentration S) : Concentration S :=
  ‖tierLogDisplacement x₀ x‖⁻¹ • tierLogDisplacement x₀ x

/-- The normalized log displacement eventually has norm exactly one. -/
theorem eventually_norm_normalizedTierLogDisplacement_eq_one
    {xs : ℕ → Concentration S} (hesc : LogEscapes xs) (x₀ : Concentration S) :
    ∀ᶠ n in atTop, ‖normalizedTierLogDisplacement x₀ (xs n)‖ = 1 := by
  have hnorm := norm_tierLogDisplacement_tendsto_atTop hesc x₀
  have hpos : ∀ᶠ n in atTop, 0 < ‖tierLogDisplacement x₀ (xs n)‖ :=
    (tendsto_atTop.1 hnorm 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  filter_upwards [hpos] with n hn
  rw [normalizedTierLogDisplacement, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn.ne']

/-- A non-transversal tier sequence has every reaction source and target in the same tier. -/
theorem tierSame_reaction_of_not_transversal {N : Network S} {xs : ℕ → Concentration S}
    (htier : N.IsTierSequence xs) (hnot : ¬ N.IsTransversalTierSequence xs) (r : N.R) :
    TierSame xs (N.reaction r).source (N.reaction r).target := by
  have hnostrict :
      ¬ (TierStrictBelow xs (N.reaction r).source (N.reaction r).target ∨
        TierStrictBelow xs (N.reaction r).target (N.reaction r).source) := by
    intro h
    exact hnot ⟨htier, ⟨r, h⟩⟩
  rcases htier.2.2 (N.reaction r).source (N.source_mem_complexes r)
      (N.reaction r).target (N.target_mem_complexes r) with hle | hrev
  · rcases hle with hbelow | hsame
    · exact (hnostrict (Or.inl hbelow)).elim
    · exact hsame
  · exact (hnostrict (Or.inr hrev)).elim

/-- Along a non-transversal tier sequence, every reaction-vector pairing with the log displacement
has a finite limit. -/
theorem reactionPairing_logDisplacement_tendsto
    {N : Network S} {xs : ℕ → Concentration S}
    (hproper : N.IsProperTierSequence xs) (hnot : ¬ N.IsTransversalTierSequence xs)
    (r : N.R) :
    ∃ a : ℝ, Tendsto
      (fun n => ∑ s : S, tierLogDisplacement (xs 0) (xs n) s * N.reactionVector r s)
      atTop (𝓝 a) := by
  have hsame := N.tierSame_reaction_of_not_transversal hproper.1 hnot r
  obtain ⟨c, hc, hratio⟩ := hsame
  have hlog : Tendsto
      (fun n => Real.log
        (tierMonomial (xs n) (N.reaction r).source /
          tierMonomial (xs n) (N.reaction r).target))
      atTop (𝓝 (Real.log c)) := hratio.log hc.ne'
  let a0 : ℝ := ∑ s : S, Real.log (xs 0 s) * N.reactionVector r s
  refine ⟨-(Real.log c) - a0, ?_⟩
  have hpair : Tendsto
      (fun n => ∑ s : S, Real.log (xs n s) * N.reactionVector r s)
      atTop (𝓝 (-(Real.log c))) := by
    have hneg := hlog.neg
    apply hneg.congr'
    exact Filter.Eventually.of_forall fun n => by
      have heq := N.log_pair_reactionVector (hproper.1.1 n) r
      dsimp only
      rw [heq]
      have hsrc : 0 < tierMonomial (xs n) (N.reaction r).source := by
        simpa [tierMonomial_eq_massActionMonomial] using
          Complex.massActionMonomial_pos (hproper.1.1 n) (N.reaction r).source
      have htgt : 0 < tierMonomial (xs n) (N.reaction r).target := by
        simpa [tierMonomial_eq_massActionMonomial] using
          Complex.massActionMonomial_pos (hproper.1.1 n) (N.reaction r).target
      rw [← Real.log_inv, inv_div]
  have hsub := hpair.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => a0) atTop (𝓝 a0))
  apply hsub.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp [a0, tierLogDisplacement]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring

/-- If a proper tier sequence were non-transversal, a unit limiting normalized log direction would
belong to the stoichiometric orthogonal complement. -/
theorem exists_unit_orthogonal_logDirection_of_not_transversal
    {N : Network S} {xs : ℕ → Concentration S}
    (hproper : N.IsProperTierSequence xs) (hnot : ¬ N.IsTransversalTierSequence xs) :
    ∃ w : Concentration S, ‖w‖ = 1 ∧ w ∈ orthSum N.stoichSubspace ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => normalizedTierLogDisplacement (xs 0) (xs (φ n))) atTop (𝓝 w) := by
  let wn : ℕ → Concentration S := fun n => normalizedTierLogDisplacement (xs 0) (xs n)
  have hone := eventually_norm_normalizedTierLogDisplacement_eq_one hproper.1.2.1 (xs 0)
  have hball : ∀ n, wn n ∈ Metric.closedBall (0 : Concentration S) 1 := by
    intro n
    by_cases hz : ‖tierLogDisplacement (xs 0) (xs n)‖ = 0
    · simp [wn, normalizedTierLogDisplacement, hz]
    · rw [Metric.mem_closedBall, dist_zero_right]
      simp [wn, normalizedTierLogDisplacement, norm_smul, Real.norm_eq_abs, hz,
        abs_of_nonneg (norm_nonneg _)]
  obtain ⟨w, hwball, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Concentration S) 1).tendsto_subseq hball
  have honeφ : Tendsto (fun n => ‖wn (φ n)‖) atTop (𝓝 1) := by
    have hevent : ∀ᶠ n in atTop, ‖wn (φ n)‖ = 1 :=
      (hφ.tendsto_atTop.eventually hone)
    exact (tendsto_congr' hevent).mpr tendsto_const_nhds
  have hnormw : ‖w‖ = 1 := by
    exact tendsto_nhds_unique hlim.norm honeφ
  have horth : w ∈ orthSum N.stoichSubspace := by
    apply (N.conservationLaw_iff_mem_orthSum w).mp
    intro r
    obtain ⟨a, hpair⟩ := N.reactionPairing_logDisplacement_tendsto hproper hnot r
    have hnorm := norm_tierLogDisplacement_tendsto_atTop hproper.1.2.1 (xs 0)
    have hinv : Tendsto (fun n => ‖tierLogDisplacement (xs 0) (xs n)‖⁻¹)
        atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
    have hscaled : Tendsto
        (fun n => ‖tierLogDisplacement (xs 0) (xs n)‖⁻¹ *
          (∑ s : S, tierLogDisplacement (xs 0) (xs n) s * N.reactionVector r s))
        atTop (𝓝 0) := by
      simpa using hinv.mul hpair
    have hscaledφ := hscaled.comp hφ.tendsto_atTop
    have hinnerlim : Tendsto
        (fun n => ∑ s : S, wn (φ n) s * N.reactionVector r s)
        atTop (𝓝 (∑ s : S, w s * N.reactionVector r s)) := by
      exact tendsto_finset_sum _ fun s _ =>
        ((tendsto_pi_nhds.mp hlim) s).mul tendsto_const_nhds
    have hzlim : Tendsto (fun n => ∑ s : S, wn (φ n) s * N.reactionVector r s)
        atTop (𝓝 0) := by
      apply hscaledφ.congr'
      exact Filter.Eventually.of_forall fun n => by
        simp only [wn, normalizedTierLogDisplacement, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, reactionVector_apply]
        exact Finset.sum_congr rfl fun s _ => by ring
    exact tendsto_nhds_unique hinnerlim hzlim
  exact ⟨w, hnormw, horth, φ, hφ, hlim⟩

/-- A nonzero orthogonal limiting log direction contradicts properness: late ordinary displacement
vectors lie in the stoichiometric subspace but have strictly positive pairing with that direction. -/
theorem false_of_unit_orthogonal_logDirection
    {N : Network S} {xs : ℕ → Concentration S}
    (hproper : N.IsProperTierSequence xs)
    {w : Concentration S} (hnormw : ‖w‖ = 1) (horth : w ∈ orthSum N.stoichSubspace)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun n => normalizedTierLogDisplacement (xs 0) (xs (φ n)))
      atTop (𝓝 w)) : False := by
  classical
  have hwne : w ≠ 0 := by intro hz; simpa [hz] using hnormw
  obtain ⟨s0, hs0⟩ : ∃ s : S, w s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hwne (funext h)
  have hnorm := norm_tierLogDisplacement_tendsto_atTop hproper.1.2.1 (xs 0)
  have hnormφ := hnorm.comp hφ.tendsto_atTop
  have hdenpos : ∀ᶠ n in atTop,
      0 < ‖tierLogDisplacement (xs 0) (xs (φ n))‖ :=
    (tendsto_atTop.1 hnormφ 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  have hsign : ∀ᶠ n in atTop, ∀ s : S,
      w s ≠ 0 →
        ((0 < w s ∧ 0 < normalizedTierLogDisplacement (xs 0) (xs (φ n)) s) ∨
         (w s < 0 ∧ normalizedTierLogDisplacement (xs 0) (xs (φ n)) s < 0)) := by
    have hcoord : ∀ s : S, ∀ᶠ n in atTop,
        w s ≠ 0 →
          ((0 < w s ∧ 0 < normalizedTierLogDisplacement (xs 0) (xs (φ n)) s) ∨
           (w s < 0 ∧ normalizedTierLogDisplacement (xs 0) (xs (φ n)) s < 0)) := by
      intro s
      by_cases hws : 0 < w s
      · have hnhd : Set.Ioi 0 ∈ 𝓝 (w s) := Ioi_mem_nhds hws
        have hev : ∀ᶠ n in atTop,
            normalizedTierLogDisplacement (xs 0) (xs (φ n)) s ∈ Set.Ioi (0 : ℝ) :=
          (tendsto_pi_nhds.mp hlim s) hnhd
        exact hev.mono fun _ hn _ => Or.inl ⟨hws, hn⟩
      · have hwsneg : w s < 0 ∨ w s = 0 := lt_or_eq_of_le (le_of_not_gt hws)
        rcases hwsneg with hwsneg | hws0
        · have hnhd : Set.Iio 0 ∈ 𝓝 (w s) := Iio_mem_nhds hwsneg
          have hev : ∀ᶠ n in atTop,
              normalizedTierLogDisplacement (xs 0) (xs (φ n)) s ∈ Set.Iio (0 : ℝ) :=
            (tendsto_pi_nhds.mp hlim s) hnhd
          exact hev.mono fun _ hn _ => Or.inr ⟨hwsneg, hn⟩
        · exact Filter.Eventually.of_forall fun _ hn => (hn hws0).elim
    exact (Filter.eventually_all_finset (Finset.univ : Finset S)).2
      (fun s _ => hcoord s) |>.mono (fun n hn s => hn s (Finset.mem_univ s))
  -- the goal is `False`, so take one index where both eventual facts hold
  obtain ⟨n, hden, hsignn⟩ := (hdenpos.and hsign).exists
  let x := xs (φ n)
  let u : Concentration S := x - xs 0
  have huS : u ∈ N.stoichSubspace := hproper.2 (φ n) 0
  have hsame : SameSign u (tierLogDisplacement (xs 0) x) :=
    sameSign_sub_tierLogDisplacement (hproper.1.1 0) (hproper.1.1 (φ n))
  have hterm_nonneg : ∀ s : S, 0 ≤ w s * u s := by
    intro s
    by_cases hws : w s = 0
    · simp [hws]
    · rcases hsignn s hws with ⟨hwp, hnp⟩ | ⟨hwn, hnn⟩
      · have hvp : 0 < tierLogDisplacement (xs 0) x s := by
          have hinvpos : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ := inv_pos.mpr hden
          have hmul : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ *
              tierLogDisplacement (xs 0) x s := by
            simpa [normalizedTierLogDisplacement, x, Pi.smul_apply, smul_eq_mul] using hnp
          nlinarith [hinvpos, hmul]
        have hup : 0 < u s := (hsame s).1.mpr hvp
        exact (mul_pos hwp hup).le
      · have hvn : tierLogDisplacement (xs 0) x s < 0 := by
          have hinvpos : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ := inv_pos.mpr hden
          have : ‖tierLogDisplacement (xs 0) x‖⁻¹ * tierLogDisplacement (xs 0) x s < 0 := by
            simpa [normalizedTierLogDisplacement, x, Pi.smul_apply, smul_eq_mul] using hnn
          nlinarith [hinvpos, this]
        have hun : u s < 0 := (hsame s).2.mpr hvn
        exact (mul_pos_of_neg_of_neg hwn hun).le
  have hterm_pos : 0 < w s0 * u s0 := by
    rcases hsignn s0 hs0 with ⟨hwp, hnp⟩ | ⟨hwn, hnn⟩
    · have hinvpos : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ := inv_pos.mpr hden
      have hvp : 0 < tierLogDisplacement (xs 0) x s0 := by
        have : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ *
            tierLogDisplacement (xs 0) x s0 := by
          simpa [normalizedTierLogDisplacement, x, Pi.smul_apply, smul_eq_mul] using hnp
        nlinarith [hinvpos, this]
      exact mul_pos hwp ((hsame s0).1.mpr hvp)
    · have hinvpos : 0 < ‖tierLogDisplacement (xs 0) x‖⁻¹ := inv_pos.mpr hden
      have hvn : tierLogDisplacement (xs 0) x s0 < 0 := by
        have : ‖tierLogDisplacement (xs 0) x‖⁻¹ *
            tierLogDisplacement (xs 0) x s0 < 0 := by
          simpa [normalizedTierLogDisplacement, x, Pi.smul_apply, smul_eq_mul] using hnn
        nlinarith [hinvpos, this]
      exact mul_pos_of_neg_of_neg hwn ((hsame s0).2.mpr hvn)
  have hsumpos : 0 < ∑ s : S, w s * u s := by
    exact Finset.sum_pos' (fun s _ => hterm_nonneg s) ⟨s0, Finset.mem_univ s0, hterm_pos⟩
  have hsumzero := (mem_orthSum.mp horth) u huS
  linarith

/-- **Lemma 4.1.** Every proper tier sequence is transversal. -/
theorem properTierSequence_isTransversal (N : Network S) {xs : ℕ → Concentration S}
    (hproper : N.IsProperTierSequence xs) : N.IsTransversalTierSequence xs := by
  by_contra hnot
  obtain ⟨w, hnormw, horth, φ, hφ, hlim⟩ :=
    N.exists_unit_orthogonal_logDirection_of_not_transversal hproper hnot
  exact N.false_of_unit_orthogonal_logDirection hproper hnormw horth hφ hlim

/-- Public proposition-valued API is discharged unconditionally by Lemma 4.1. -/
theorem properTierSequencesAreTransversal (N : Network S) :
    N.ProperTierSequencesAreTransversal := by
  intro xs hproper
  exact N.properTierSequence_isTransversal hproper

end Network
end CRNT
