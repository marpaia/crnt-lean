import CRNT.Graph.PositiveCirculation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Deficiency-zero theorem, part (i): arbitrary kinetics

**Theorem (Feinberg, Deficiency Zero Theorem (i)).**  Let a reaction network have deficiency
zero.  If it is not weakly reversible then, for *any* kinetics, the induced differential
equations admit neither a positive steady state nor a cyclic composition trajectory along which
all reaction rates are positive.

Kinetics are arbitrary here: the velocity is `∑ r, ρ r x • (y'_r - y_r)` for any rate functions
`ρ r`, positive along the states considered (for physical kinetics, rates are positive at
positive compositions).  The mass-action steady-state case was already in the library
(`no_positiveSteadyState_of_deficiencyZero_not_weaklyReversible`).

**Proof.**  A positive flux `c` with `∑ r, c r • (y'_r - y_r) = 0` lies in the kernel of
`Y ∘ ∂`; at deficiency zero that kernel equals the kernel of `∂`
(`deficiencyZero_iff_stoichCycle_is_graphCycle`), so `c` is a positive circulation of the
reaction graph, which forces weak reversibility (`weaklyReversible_of_positiveGraphCirculation`).
A steady state supplies `c` directly; along a cyclic trajectory of period `T`, integrating the
equations over one period gives `c r = ∫₀ᵀ ρ r (γ t) dt > 0`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A positive stoichiometric cycle at deficiency zero forces weak reversibility.** -/
theorem weaklyReversible_of_deficiencyZero_of_positive_stoichCycle (N : Network S)
    (hδ : N.DeficiencyZero) {c : N.R → ℝ} (hc : ∀ r, 0 < c r) (hcyc : N.stoichMap c = 0) :
    N.WeaklyReversible :=
  N.weaklyReversible_of_positiveGraphCirculation
    ⟨hc, (N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp hδ) c hcyc⟩

/-- **Steady states, arbitrary kinetics.**  At deficiency zero, a steady state with all
reaction rates positive forces weak reversibility. -/
theorem weaklyReversible_of_deficiencyZero_of_positiveRate_steadyState (N : Network S)
    (hδ : N.DeficiencyZero) (ρ : N.R → ℝ) (hρ : ∀ r, 0 < ρ r)
    (hss : ∑ r : N.R, ρ r • N.reactionVector r = 0) :
    N.WeaklyReversible :=
  N.weaklyReversible_of_deficiencyZero_of_positive_stoichCycle hδ hρ hss

/-- **Cyclic trajectories, arbitrary kinetics.**  At deficiency zero, a solution that returns to
its starting point after time `T > 0`, with all reaction rates positive and continuous along it,
forces weak reversibility. -/
theorem weaklyReversible_of_deficiencyZero_of_cyclic_trajectory (N : Network S)
    (hδ : N.DeficiencyZero) (ρ : N.R → Concentration S → ℝ) {γ : ℝ → Concentration S}
    {T : ℝ} (hT : 0 < T)
    (hsol : ∀ t ∈ Set.Icc 0 T, ∀ s : S, HasDerivAt (fun τ => γ τ s)
      (∑ r : N.R, ρ r (γ t) * N.reactionVector r s) t)
    (hcont : ∀ r, ContinuousOn (fun t => ρ r (γ t)) (Set.Icc 0 T))
    (hpos : ∀ t ∈ Set.Icc 0 T, ∀ r, 0 < ρ r (γ t))
    (hper : γ T = γ 0) :
    N.WeaklyReversible := by
  have huIcc : Set.uIcc 0 T = Set.Icc 0 T := Set.uIcc_of_le hT.le
  have hint : ∀ r, IntervalIntegrable (fun t => ρ r (γ t)) MeasureTheory.volume 0 T := by
    intro r; apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hcont r
  set c : N.R → ℝ := fun r => ∫ t in (0 : ℝ)..T, ρ r (γ t) with hc
  have hcpos : ∀ r, 0 < c r := fun r =>
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint r)
      (fun t ht => hpos t (Set.Ioo_subset_Icc_self ht) r) hT
  refine N.weaklyReversible_of_deficiencyZero_of_positive_stoichCycle hδ hcpos ?_
  funext s
  -- integrate the `s`-th equation over one period
  have hftc : ∫ t in (0 : ℝ)..T, (∑ r : N.R, ρ r (γ t) * N.reactionVector r s) =
      γ T s - γ 0 s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht; rw [huIcc] at ht; exact hsol t ht s
    · apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact continuousOn_finset_sum _ fun r _ => (hcont r).mul continuousOn_const
  rw [hper, sub_self, intervalIntegral.integral_finsetSum
    (fun r _ => (hint r).mul_const _)] at hftc
  simp only [intervalIntegral.integral_mul_const] at hftc
  change (∑ r : N.R, c r • N.reactionVector r) s = 0
  rw [Finset.sum_apply]
  simpa [hc, smul_eq_mul] using hftc

/-- **Deficiency Zero Theorem (i).**  A deficiency-zero network that is not weakly reversible
admits, for any kinetics, no steady state with all rates positive and no cyclic trajectory along
which all rates are positive. -/
theorem deficiencyZero_not_weaklyReversible_no_positive_steadyState_or_cycle (N : Network S)
    (hδ : N.DeficiencyZero) (hnwr : ¬ N.WeaklyReversible) (ρ : N.R → Concentration S → ℝ) :
    (¬ ∃ x : Concentration S, (∀ r, 0 < ρ r x) ∧
        ∑ r : N.R, ρ r x • N.reactionVector r = 0) ∧
    (∀ (γ : ℝ → Concentration S) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Icc 0 T, ∀ s : S, HasDerivAt (fun τ => γ τ s)
        (∑ r : N.R, ρ r (γ t) * N.reactionVector r s) t) →
      (∀ r, ContinuousOn (fun t => ρ r (γ t)) (Set.Icc 0 T)) →
      (∀ t ∈ Set.Icc 0 T, ∀ r, 0 < ρ r (γ t)) → γ T ≠ γ 0) := by
  refine ⟨fun ⟨x, hx, hss⟩ => hnwr
    (N.weaklyReversible_of_deficiencyZero_of_positiveRate_steadyState hδ (fun r => ρ r x) hx hss),
    fun γ T hT hsol hcont hpos hper => hnwr
      (N.weaklyReversible_of_deficiencyZero_of_cyclic_trajectory hδ ρ hT hsol hcont hpos hper)⟩

end Network
end CRNT
