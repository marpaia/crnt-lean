import CRNT.Multistationarity.Capacity
import CRNT.Kinetics.SignVectorCriterion

/-!
# Exact characterization of the capacity for multiple steady states

A mass-action network has the capacity for multiple positive steady states in one compatibility
class iff there are

* a strictly positive flux vector `α` with `∑_r α_r (y'_r − y_r) = 0`,
* a vector `μ ∈ ℝ^S` and a nonzero `σ` in the stoichiometric subspace with the same sign pattern,

such that `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`. Given two steady states `x ≠ y`, take
`α_r = κ_r x^{y_r}`, `μ = log y − log x`, `σ = y − x`; conversely, from `(α, μ, σ)` put
`x_s = σ_s/(e^{μ_s} − 1)` (or `1` where `σ_s = 0`), `y = x e^{μ}` and `κ_r = α_r / x^{y_r}`.
This is the reformulation underlying the Deficiency One Algorithm and the sign-condition tests
(Feinberg 1995b; Conradi–Feliu–Mincheva–Wiuf 2017; Müller et al. 2016).

Main result: `CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Pairing of a complex with a log-vector. -/
def complexPairing (y : Complex S) (μ : S → ℝ) : ℝ := ∑ s, (y s : ℝ) * μ s

omit [DecidableEq S] in
theorem massActionMonomial_mul_exp (y : Complex S) (x μ : S → ℝ) :
    y.massActionMonomial (fun s => x s * Real.exp (μ s)) =
      y.massActionMonomial x * Real.exp (complexPairing y μ) := by
  unfold Complex.massActionMonomial complexPairing
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [mul_pow, ← Real.exp_nat_mul]

/-- **Capacity iff a sign-compatible flux certificate exists.** -/
theorem hasMultistationarityCapacity_iff_flux_sign (N : Network S) :
    N.HasMultistationarityCapacity ↔
      ∃ (α : N.R → ℝ) (μ σ : S → ℝ), (∀ r, 0 < α r) ∧ σ ∈ N.stoichSubspace ∧ σ ≠ 0 ∧
        (∀ s, SignType.sign (σ s) = SignType.sign (μ s)) ∧
        (∀ s, ∑ r, α r * N.reactionVector r s = 0) ∧
        (∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s = 0) := by
  constructor
  · rintro ⟨κ, x₀, x, y, hx, hy, hxs, hys, hne⟩
    have hxp := hx.2
    have hyp := hy.2
    refine ⟨fun r => κ.k r * (N.reaction r).source.massActionMonomial x,
      fun s => Real.log (y s) - Real.log (x s), y - x, fun r =>
        mul_pos (κ.positive r) (Complex.massActionMonomial_pos hxp _), ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : x - x₀ ∈ N.stoichSubspace := hx.1
      have h2 : y - x₀ ∈ N.stoichSubspace := hy.1
      have : y - x = (y - x₀) - (x - x₀) := by abel
      rw [this]; exact N.stoichSubspace.sub_mem h2 h1
    · intro h; exact hne (sub_eq_zero.mp h).symm
    · intro s
      exact sign_sub_eq_sign_logDiff (hyp s) (hxp s)
    · intro s
      have := hxs s
      rw [isMassActionSteadyState_iff] at hxs
      simpa [massActionRate] using hxs s
    · intro s
      have hyx : y = fun s => x s * Real.exp (Real.log (y s) - Real.log (x s)) := by
        funext s
        rw [Real.exp_sub, Real.exp_log (hyp s), Real.exp_log (hxp s)]
        field_simp [(hxp s).ne']
      have hss := hys s
      rw [isMassActionSteadyState_iff] at hys
      have h := hys s
      rw [hyx] at h
      simp only [massActionRate, massActionMonomial_mul_exp] at h
      rw [← h]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
  · rintro ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩
    -- construct `x`
    let x : Concentration S := fun s => if σ s = 0 then 1 else σ s / (Real.exp (μ s) - 1)
    have hcoord : ∀ s, 0 < x s ∧ x s * (Real.exp (μ s) - 1) = σ s := by
      intro s
      have hs := hsign s
      by_cases h0 : σ s = 0
      · have hμ0 : μ s = 0 := by
          rw [h0, sign_zero] at hs; exact sign_eq_zero_iff.mp hs.symm
        simp [x, h0, hμ0]
      · have hμ0 : μ s ≠ 0 := fun e => h0 (by
          rw [e, sign_zero] at hs; exact sign_eq_zero_iff.mp hs)
        have hden : Real.exp (μ s) - 1 ≠ 0 := by
          intro e
          have : Real.exp (μ s) = Real.exp 0 := by rw [Real.exp_zero]; linarith
          exact hμ0 (Real.exp_injective this)
        have hpos : 0 < σ s / (Real.exp (μ s) - 1) := by
          rcases lt_or_gt_of_ne h0 with hneg | hposσ
          · rw [sign_neg hneg] at hs
            have : μ s < 0 := sign_eq_neg_one_iff.mp hs.symm
            exact div_pos_of_neg_of_neg hneg (by linarith [Real.exp_lt_one_iff.mpr this])
          · rw [sign_pos hposσ] at hs
            have : 0 < μ s := sign_eq_one_iff.mp hs.symm
            exact div_pos hposσ (by linarith [Real.one_lt_exp_iff.mpr this])
        refine ⟨by simpa [x, h0] using hpos, ?_⟩
        simp only [x, h0, ite_false]
        field_simp
    have hxp : x.Positive := fun s => (hcoord s).1
    let y : Concentration S := fun s => x s * Real.exp (μ s)
    have hyp : y.Positive := fun s => mul_pos (hxp s) (Real.exp_pos _)
    have hyx : y - x = σ := by
      funext s
      have := (hcoord s).2
      simp only [y, Pi.sub_apply]
      linarith
    let κ : RateConstants N := ⟨fun r => α r / (N.reaction r).source.massActionMonomial x,
      fun r => div_pos (hα r) (Complex.massActionMonomial_pos hxp _)⟩
    have hrate : ∀ r, κ.k r * (N.reaction r).source.massActionMonomial x = α r := fun r =>
      div_mul_cancel₀ _ (Complex.massActionMonomial_pos hxp _).ne'
    refine ⟨κ, x, x, y, ⟨StoichCompatible.refl N x, hxp⟩, ⟨?_, hyp⟩, ?_, ?_, ?_⟩
    · show y - x ∈ N.stoichSubspace
      rw [hyx]; exact hσS
    · intro s
      rw [massActionVectorField_apply]
      simp only [massActionRate]
      simp_rw [hrate]
      exact hflux s
    · intro s
      rw [massActionVectorField_apply]
      simp only [massActionRate]
      rw [← hflux' s]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [y]
      rw [massActionMonomial_mul_exp, ← mul_assoc, hrate]
    · intro h
      apply hσ0
      rw [← hyx, ← h, sub_self]

end Network

end CRNT
