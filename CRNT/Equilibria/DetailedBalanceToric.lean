import CRNT.Equilibria.Wegscheider
import CRNT.Equilibria.CompatibilityClass
import CRNT.Theorems.DeficiencyZero.BirchExistence
import CRNT.Kinetics.Generalized

/-!
# Toric geometry of detailed-balanced equilibria

Fix one positive reactionwise detailed-balanced equilibrium `x*`.  Another positive state
`x` is reactionwise detailed-balanced for the same rate constants exactly when

`log x - log x* ∈ S(N)^⊥`.

Thus the detailed-balanced equilibria form the toric manifold
`x* ⊙ exp(S^⊥)`.  Birch existence/uniqueness then gives exactly one detailed-balanced
equilibrium in every positive stoichiometric compatibility class.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Log displacement from a positive reference concentration. -/
noncomputable def logRatio (x xstar : Concentration S) : S → ℝ :=
  fun s => Real.log (x s) - Real.log (xstar s)

/-- Two positive reactionwise detailed-balanced states differ logarithmically by a vector
orthogonal to every reaction vector. -/
theorem logRatio_mem_orthStoich_of_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    logRatio x xstar ∈ orthSum N.stoichSubspace := by
  rw [Network.stoichSubspace]
  apply mem_orthSum_span
  intro g hg
  rcases hg with ⟨r, rfl⟩
  have hlog (z : Concentration S) (hz : z.Positive)
      (hdbz : N.IsReactionwiseDetailedBalanced ρ κ z) :
      N.logEquilibriumConstant ρ κ r =
        ∑ s : S, N.reactionVector r s * Real.log (z s) := by
    have h := congrArg Real.log (hdbz r)
    have hsrcpos := Complex.massActionMonomial_pos hz (N.reaction r).source
    have htgtpos := Complex.massActionMonomial_pos hz (N.reaction r).target
    rw [massActionRate, massActionRate, ρ.source_rev,
      Real.log_mul (κ.positive r).ne' hsrcpos.ne',
      Real.log_mul (κ.positive (ρ.rev r)).ne' htgtpos.ne',
      log_massActionMonomial_eq hz, log_massActionMonomial_eq hz] at h
    rw [logEquilibriumConstant]
    simp only [reactionVector_apply]
    calc
      Real.log (κ.k r) - Real.log (κ.k (ρ.rev r))
          = (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (z s))
            - (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (z s)) := by
              linarith
      _ = ∑ s : S,
          (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) *
            Real.log (z s) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
  have hs := hlog xstar hxs hdbs
  have hx' := hlog x hx hdb
  simp only [logRatio]
  have hdiff :
      (∑ s : S, N.reactionVector r s * Real.log (x s)) -
        (∑ s : S, N.reactionVector r s * Real.log (xstar s)) = 0 := by
    linarith
  rw [← Finset.sum_sub_distrib] at hdiff
  simpa [sub_mul, mul_comm] using hdiff
/-- Conversely, moving a positive detailed-balanced reference in a logarithmic direction
orthogonal to the stoichiometric subspace preserves every reactionwise balance equation. -/
theorem reactionwiseDetailedBalanced_of_logRatio_mem_orthStoich
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (horth : logRatio x xstar ∈ orthSum N.stoichSubspace) :
    N.IsReactionwiseDetailedBalanced ρ κ x := by
  intro r
  have horth_r := (mem_orthSum.mp horth) (N.reactionVector r)
    (N.reactionVector_mem_stoichSubspace r)
  have hlogs : N.logEquilibriumConstant ρ κ r =
      ∑ s : S, N.reactionVector r s * Real.log (xstar s) := by
    have h := congrArg Real.log (hdbs r)
    have hsrcpos := Complex.massActionMonomial_pos hxs (N.reaction r).source
    have htgtpos := Complex.massActionMonomial_pos hxs (N.reaction r).target
    rw [massActionRate, massActionRate, ρ.source_rev,
      Real.log_mul (κ.positive r).ne' hsrcpos.ne',
      Real.log_mul (κ.positive (ρ.rev r)).ne' htgtpos.ne',
      log_massActionMonomial_eq hxs, log_massActionMonomial_eq hxs] at h
    rw [logEquilibriumConstant]
    simp only [reactionVector_apply]
    calc
      Real.log (κ.k r) - Real.log (κ.k (ρ.rev r))
          = (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (xstar s))
            - (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s)) := by
              linarith
      _ = ∑ s : S,
          (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) *
            Real.log (xstar s) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
  have hdot :
      ∑ s : S, N.reactionVector r s * Real.log (x s) =
        ∑ s : S, N.reactionVector r s * Real.log (xstar s) := by
    simp only [logRatio, reactionVector_apply, sub_mul, mul_sub,
      Finset.sum_sub_distrib] at horth_r ⊢
    have horth_r' :
        (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (x s)) -
            (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (xstar s)) -
          ((∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (x s)) -
            (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s))) = 0 := by
      simpa only [mul_comm] using horth_r
    linarith [horth_r']
  have hlogx : N.logEquilibriumConstant ρ κ r =
      ∑ s : S, N.reactionVector r s * Real.log (x s) := by
    linarith
  have hrpos := N.massActionRate_pos κ r hx
  have hrevpos := N.massActionRate_pos κ (ρ.rev r) hx
  apply Real.log_injOn_pos hrpos hrevpos
  rw [massActionRate, massActionRate,
    Real.log_mul (κ.positive r).ne' (Complex.massActionMonomial_pos hx _).ne',
    Real.log_mul (κ.positive (ρ.rev r)).ne' (Complex.massActionMonomial_pos hx _).ne',
    log_massActionMonomial_eq hx, log_massActionMonomial_eq hx,
    ρ.source_rev]
  rw [logEquilibriumConstant] at hlogx
  simp only [reactionVector_apply] at hlogx
  have hsum :
      (∑ s : S,
          (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) * Real.log (x s)) =
        (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (x s)) -
          (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (x s)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum] at hlogx
  linarith
/-- Exact toric characterization relative to one positive detailed-balanced reference. -/
theorem reactionwiseDetailedBalanced_iff_logRatio_orthStoich
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    N.IsReactionwiseDetailedBalanced ρ κ x ↔
      logRatio x xstar ∈ orthSum N.stoichSubspace := by
  constructor
  · exact N.logRatio_mem_orthStoich_of_reactionwiseDetailedBalanced ρ κ hxs hx hdbs
  · exact N.reactionwiseDetailedBalanced_of_logRatio_mem_orthStoich ρ κ hxs hx hdbs

/-- **Existence in every positive compatibility class.** -/
theorem exists_reactionwiseDetailedBalanced_in_positiveClass
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar c : Concentration S} (hxs : xstar.Positive) (hc : c.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    ∃ x : Concentration S,
      x.Positive ∧ N.StoichCompatible c x ∧
      N.IsReactionwiseDetailedBalanced ρ κ x := by
  obtain ⟨x, hx, hxc, horth⟩ := birch_existence N.stoichSubspace hxs hc
  refine ⟨x, hx, ?_, ?_⟩
  · exact hxc
  · apply (N.reactionwiseDetailedBalanced_iff_logRatio_orthStoich ρ κ hxs hx hdbs).2
    simpa [logRatio] using mem_orthSum.mpr horth

/-- **Uniqueness in a positive compatibility class.** -/
theorem reactionwiseDetailedBalanced_unique_in_class
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x y : Concentration S} (hxs : xstar.Positive)
    (hx : x.Positive) (hy : y.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (hdbx : N.IsReactionwiseDetailedBalanced ρ κ x)
    (hdby : N.IsReactionwiseDetailedBalanced ρ κ y)
    (hxy : N.StoichCompatible x y) : x = y := by
  apply birch_uniqueness_of_self N.stoichSubspace hx hy
  · -- `StoichCompatible x y` is `(y - x) ∈ stoichSubspace`; the goal is the negation.
    have hneg := Submodule.neg_mem N.stoichSubspace hxy
    simpa [neg_sub] using hneg
  · have hxorth := N.logRatio_mem_orthStoich_of_reactionwiseDetailedBalanced
      ρ κ hxs hx hdbs hdbx
    have hyorth := N.logRatio_mem_orthStoich_of_reactionwiseDetailedBalanced
      ρ κ hxs hy hdbs hdby
    have hsub := (orthSum N.stoichSubspace).sub_mem hxorth hyorth
    simpa [logRatio, Pi.sub_apply] using hsub

end Network

end CRNT
