import CRNT.Equilibria.DetailedBalanceToric

/-!
# Entropy production for detailed-balanced CRNs

For a reversible pairing, define the pairwise entropy production

`EP(x) = 1/2 Σ_r (v_r-v_rev(r)) (log v_r-log v_rev(r))`.

Every summand is nonnegative because `log` is strictly increasing.  At positive states,
`EP=0` exactly at reactionwise detailed balance.  Relative to a positive detailed-balanced
reference `x*`, entropy production is exactly minus the Horn--Jackson logarithmic
dissipation `⟨log(x/x*), f(x)⟩`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- One oriented reaction-pair entropy-production term. -/
noncomputable def reactionEntropyProduction (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S) (r : N.R) : ℝ :=
  (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) *
    (Real.log (N.massActionRate κ r x) -
      Real.log (N.massActionRate κ (ρ.rev r) x))

/-- Total entropy production; factor `1/2` compensates for the involutive double count. -/
noncomputable def entropyProduction (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S) : ℝ :=
  (1 / 2 : ℝ) * ∑ r : N.R, N.reactionEntropyProduction ρ κ x r

/-- Each pair term is nonnegative at a positive state. -/
theorem reactionEntropyProduction_nonneg (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive) (r : N.R) :
    0 ≤ N.reactionEntropyProduction ρ κ x r := by
  unfold reactionEntropyProduction
  have ha := N.massActionRate_pos κ r hx
  have hb := N.massActionRate_pos κ (ρ.rev r) hx
  rcases le_total (N.massActionRate κ r x) (N.massActionRate κ (ρ.rev r) x) with h | h
  · have hlog := Real.log_le_log ha h
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr hlog)
  · have hlog := Real.log_le_log hb h
    exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hlog)

/-- Entropy production is nonnegative. -/
theorem entropyProduction_nonneg (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive) :
    0 ≤ N.entropyProduction ρ κ x := by
  unfold entropyProduction
  -- `positivity` cannot see inside the sum; use the per-reaction nonnegativity term-wise.
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun r _ => ?_)
  exact N.reactionEntropyProduction_nonneg ρ κ hx r

/-- A pair term vanishes exactly when forward and reverse fluxes agree. -/
theorem reactionEntropyProduction_eq_zero_iff (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Positive) (r : N.R) :
    N.reactionEntropyProduction ρ κ x r = 0 ↔
      N.massActionRate κ r x = N.massActionRate κ (ρ.rev r) x := by
  unfold reactionEntropyProduction
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hrate | hlog
    · exact sub_eq_zero.mp hrate
    · have hleq : Real.log (N.massActionRate κ r x) =
          Real.log (N.massActionRate κ (ρ.rev r) x) := sub_eq_zero.mp hlog
      exact Real.log_injOn_pos (N.massActionRate_pos κ r hx)
        (N.massActionRate_pos κ (ρ.rev r) hx) hleq
  · intro h
    rw [h]
    simp

/-- At positive states, zero entropy production is exactly reactionwise detailed balance. -/
theorem entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Positive) :
    N.entropyProduction ρ κ x = 0 ↔ N.IsReactionwiseDetailedBalanced ρ κ x := by
  unfold entropyProduction
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [mul_eq_zero]
  simp only [hhalf, false_or]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h r
      exact (N.reactionEntropyProduction_eq_zero_iff ρ κ hx r).1
        (h r (Finset.mem_univ r))
    · intro h r _
      exact (N.reactionEntropyProduction_eq_zero_iff ρ κ hx r).2 (h r)
  · exact fun r _ => N.reactionEntropyProduction_nonneg ρ κ hx r

/-- Logarithmic pairing of the vector field against a positive detailed-balance reference. -/
noncomputable def relativeLogDissipation (N : Network S) (κ : RateConstants N)
    (x xstar : Concentration S) : ℝ :=
  ∑ s : S, (Real.log (x s) - Real.log (xstar s)) *
    N.massActionVectorField κ x s

/-- At a positive reactionwise detailed-balanced reference, the logarithmic displacement
paired with one reaction vector is the negative forward/reverse log-rate ratio. -/
theorem logRatio_dot_reactionVector_eq_neg_logRateRatio
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) (r : N.R) :
    (∑ s : S, (Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) =
      -(Real.log (N.massActionRate κ r x) -
        Real.log (N.massActionRate κ (ρ.rev r) x)) := by
  have hstar := congrArg Real.log (hdbs r)
  have hsrcs := Complex.massActionMonomial_pos hxs (N.reaction r).source
  have htgts := Complex.massActionMonomial_pos hxs (N.reaction r).target
  rw [massActionRate, massActionRate, ρ.source_rev,
    Real.log_mul (κ.positive r).ne' hsrcs.ne',
    Real.log_mul (κ.positive (ρ.rev r)).ne' htgts.ne',
    log_massActionMonomial_eq hxs, log_massActionMonomial_eq hxs] at hstar
  have hsrc := Complex.massActionMonomial_pos hx (N.reaction r).source
  have htgt := Complex.massActionMonomial_pos hx (N.reaction r).target
  rw [massActionRate, massActionRate, ρ.source_rev,
    Real.log_mul (κ.positive r).ne' hsrc.ne',
    Real.log_mul (κ.positive (ρ.rev r)).ne' htgt.ne',
    log_massActionMonomial_eq hx, log_massActionMonomial_eq hx]
  simp only [reactionVector_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hstar' :
      Real.log (κ.k r) +
          (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s)) =
        Real.log (κ.k (ρ.rev r)) +
          (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (xstar s)) := hstar
  have hstar'' :
      Real.log (κ.k r) - Real.log (κ.k (ρ.rev r)) =
        (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (xstar s)) -
          (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s)) := by
    linarith [hstar']
  have hmul1 : (∑ s : S, Real.log (x s) * ((N.reaction r).target s : ℝ)) =
      ∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (x s) := by
    apply Finset.sum_congr rfl; intro s _; ring
  have hmul2 : (∑ s : S, Real.log (x s) * ((N.reaction r).source s : ℝ)) =
      ∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (x s) := by
    apply Finset.sum_congr rfl; intro s _; ring
  have hmul3 : (∑ s : S, Real.log (xstar s) * ((N.reaction r).target s : ℝ)) =
      ∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (xstar s) := by
    apply Finset.sum_congr rfl; intro s _; ring
  have hmul4 : (∑ s : S, Real.log (xstar s) * ((N.reaction r).source s : ℝ)) =
      ∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s) := by
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hmul1, hmul2, hmul3, hmul4]
  linarith [hstar'']

/-- **Thermodynamic/Horn--Jackson identity.** -/
theorem relativeLogDissipation_eq_neg_entropyProduction
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    N.relativeLogDissipation κ x xstar = -N.entropyProduction ρ κ x := by
  let a : N.R → ℝ := fun r => N.massActionRate κ r x
  let L : N.R → ℝ := fun r => Real.log (N.massActionRate κ r x) -
    Real.log (N.massActionRate κ (ρ.rev r) x)
  have hD : N.relativeLogDissipation κ x xstar = -∑ r : N.R, a r * L r := by
    unfold relativeLogDissipation
    calc
      (∑ s : S, (Real.log (x s) - Real.log (xstar s)) *
          N.massActionVectorField κ x s)
          = ∑ s : S, ∑ r : N.R,
              (Real.log (x s) - Real.log (xstar s)) *
                (N.massActionRate κ r x * N.reactionVector r s) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [massActionVectorField_apply, Finset.mul_sum]
      _ = ∑ r : N.R, ∑ s : S,
              (Real.log (x s) - Real.log (xstar s)) *
                (N.massActionRate κ r x * N.reactionVector r s) := by
              rw [Finset.sum_comm]
      _ = ∑ r : N.R, N.massActionRate κ r x *
              (∑ s : S, (Real.log (x s) - Real.log (xstar s)) *
                N.reactionVector r s) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = -∑ r : N.R, a r * L r := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro r _
              rw [N.logRatio_dot_reactionVector_eq_neg_logRateRatio ρ κ hxs hx hdbs r]
              simp only [a, L]
              ring
  have hrevsum :
      (∑ r : N.R, N.massActionRate κ (ρ.rev r) x * L r) =
        -(∑ r : N.R, a r * L r) := by
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_equiv ρ.equiv
    intro r
    change N.massActionRate κ (ρ.rev r) x * L r =
      -(a (ρ.rev r) * L (ρ.rev r))
    simp only [L, a, ρ.rev_rev]
    ring
  have hEP : N.entropyProduction ρ κ x = ∑ r : N.R, a r * L r := by
    unfold entropyProduction reactionEntropyProduction
    simp only [a, L]
    have hsplit :
        (∑ r : N.R,
          (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) *
            (Real.log (N.massActionRate κ r x) -
              Real.log (N.massActionRate κ (ρ.rev r) x))) =
          (∑ r : N.R, N.massActionRate κ r x * L r) -
            (∑ r : N.R, N.massActionRate κ (ρ.rev r) x * L r) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      simp only [L]
      ring
    rw [hsplit, hrevsum]
    have hA : (∑ r : N.R, N.massActionRate κ r x * L r) = ∑ r : N.R, a r * L r := by
      simp only [a]
    have hAL :
        (∑ r : N.R, N.massActionRate κ r x *
          (Real.log (N.massActionRate κ r x) -
            Real.log (N.massActionRate κ (ρ.rev r) x))) =
          ∑ r : N.R, a r * L r := by
      simp only [a, L]
    rw [hA, hAL]
    ring
  rw [hD, hEP]

/-- Strict dissipation away from detailed balance. -/
theorem relativeLogDissipation_lt_zero_iff
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    N.relativeLogDissipation κ x xstar < 0 ↔
      ¬ N.IsReactionwiseDetailedBalanced ρ κ x := by
  rw [N.relativeLogDissipation_eq_neg_entropyProduction ρ κ hxs hx hdbs]
  have hnonneg := N.entropyProduction_nonneg ρ κ hx
  rw [neg_lt_zero]
  constructor
  · intro hpos hdb
    have hz := (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).2 hdb
    linarith
  · intro hnot
    exact lt_of_le_of_ne hnonneg
      (Ne.symm (fun hz => hnot
        ((N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz)))

end Network

end CRNT
