import CRNT.Design.MaxRPAIntegrator
import CRNT.Stochastic.FosterLyapunov

/-!
# Stochastic maxRPA from the CTMC generator

For a maxRPA charge observable, the stochastic generator sees exactly the same distinguished
reaction combination as the deterministic vector field.  Under the stochastic source-pair
condition the drift is affine in the output copy number,

`L Q(n) = gain * k_ref - k_sense * n_out`.

Consequently every stationary law with a finite first moment has the robust mean setpoint
`E[N_out] = gain*k_ref/k_sense`.  The theorem is stated against an abstract summable
stationary moment functional so it is independent of a particular measure encoding.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Count-space version of a maxRPA charge. -/
def stochasticChargeObservable (q : S → ℝ) (n : S → ℕ) : ℝ :=
  linearObservable q n

/-- The generator drift of the charge leaves only the distinguished propensities. -/
theorem observableGenerator_maxRPA_charge
    (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {gain : ℝ} {q : S → ℝ}
    (hq : N.IsMaxRPACharge rRef rSense gain q) (n : S → ℕ) :
    N.observableGenerator κ (stochasticChargeObservable q) n =
      gain * N.stochasticMassActionRate κ n rRef -
        N.stochasticMassActionRate κ n rSense := by
  change N.observableGenerator κ (linearObservable q) n = _
  rw [N.observableGenerator_linear κ q n]
  -- Collapse the finite reaction sum using the charge witness.
  change (∑ r : N.R, N.stochasticMassActionRate κ n r * N.chargeIncrement q r) = _
  have hrewrite :
      (∑ r : N.R, N.stochasticMassActionRate κ n r * N.chargeIncrement q r) =
        ∑ r : N.R, N.stochasticMassActionRate κ n r *
          ((if r = rRef then gain else 0) - (if r = rSense then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hq r]
  rw [hrewrite]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp [mul_comm]

/-- A zeroth-order stochastic mass-action reaction has constant propensity `k`. -/
theorem stochasticRate_eq_rateConstant_of_zeroSource
    (N : Network S) (κ : N.RateConstants) (r : N.R)
    (hzero : ∀ s, (N.reaction r).source s = 0) (n : S → ℕ) :
    N.stochasticMassActionRate κ n r = κ.k r := by
  unfold stochasticMassActionRate
  simp [hzero]

/-- A reaction consuming exactly one output molecule and no other reactants has propensity
`k * n_out`. -/
theorem stochasticRate_eq_linear_output_of_unitSource
    (N : Network S) (κ : N.RateConstants) (r : N.R) (out : S)
    (hone : (N.reaction r).source out = 1)
    (hother : ∀ s, s ≠ out → (N.reaction r).source s = 0)
    (n : S → ℕ) :
    N.stochasticMassActionRate κ n r = κ.k r * n out := by
  unfold stochasticMassActionRate
  -- All falling-factorial factors are one except `out`, where `n.descFactorial 1 = n`.
  have hp :
      (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = n out := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ out)]
    rw [hone, Nat.descFactorial_one]
    have hrest :
        (∏ s ∈ (Finset.univ \ {out}),
          ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro s hs
      have hne : s ≠ out := by
        simpa using hs
      rw [hother s hne]
      simp
    rw [hrest, mul_one]
  rw [hp]

/-- **Exact stochastic integral-control identity.** -/
theorem stochasticMaxRPA_generator_charge_eq_error
    (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hpair : N.StochasticMaxRPASourcePair rRef rSense out)
    (n : S → ℕ) :
    N.observableGenerator κ (stochasticChargeObservable C.charge) n =
      C.gain * κ.k rRef - κ.k rSense * n out := by
  rw [N.observableGenerator_maxRPA_charge κ C.identity n,
    N.stochasticRate_eq_rateConstant_of_zeroSource κ rRef hpair.1 n,
    N.stochasticRate_eq_linear_output_of_unitSource κ rSense out hpair.2.1 hpair.2.2 n]

/-- Abstract stationary expectation functional.  This is enough for moment identities and
avoids committing the theorem to finite-state, countable-measure, or normalized-PMF APIs. -/
structure StationaryExpectation (N : Network S) (κ : N.RateConstants) where
  mean : ((S → ℕ) → ℝ) → ℝ
  map_add : ∀ f g, mean (fun n => f n + g n) = mean f + mean g
  map_smul : ∀ a f, mean (fun n => a * f n) = a * mean f
  map_const : ∀ a, mean (fun _ => a) = a
  generator_zero : ∀ f, mean (fun n => N.observableGenerator κ f n) = 0

/-- Expected copy number under a stationary expectation functional. -/
def StationaryExpectation.expectedCount {N : Network S} {κ : N.RateConstants}
    (E : N.StationaryExpectation κ) (s : S) : ℝ :=
  E.mean (fun n => n s)

/-- Stationarity turns the stochastic maxRPA generator identity into a robust mean setpoint. -/
theorem stationary_mean_output_maxRPA
    (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hpair : N.StochasticMaxRPASourcePair rRef rSense out)
    (E : N.StationaryExpectation κ) :
    E.expectedCount out = C.gain * κ.k rRef / κ.k rSense := by
  have hgen := E.generator_zero (stochasticChargeObservable C.charge)
  have hid :
      E.mean (fun n => C.gain * κ.k rRef - κ.k rSense * n out) = 0 := by
    simpa [N.stochasticMaxRPA_generator_charge_eq_error κ C hpair] using hgen
  have hlin :
      E.mean (fun n => C.gain * κ.k rRef - κ.k rSense * n out) =
        C.gain * κ.k rRef - κ.k rSense * E.expectedCount out := by
    -- Follows from linearity and preservation of constants.
    have hfun :
        (fun n : S → ℕ => C.gain * κ.k rRef - κ.k rSense * n out) =
          (fun n : S → ℕ => C.gain * κ.k rRef + (-κ.k rSense) * (n out : ℝ)) := by
      funext n
      ring
    rw [hfun, E.map_add, E.map_const, E.map_smul]
    simp [StationaryExpectation.expectedCount]
    ring
  rw [hlin] at hid
  have hk : κ.k rSense ≠ 0 := (κ.positive rSense).ne'
  field_simp [hk]
  linarith

/-- Therefore the stationary mean output is invariant under arbitrary changes to all rate
constants except the two distinguished controller rates, provided the maxRPA charge and
source-pair structure are retained. -/
theorem stationary_mean_output_eq_between_rate_vectors
    (N : Network S)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hpair : N.StochasticMaxRPASourcePair rRef rSense out)
    (κ₁ κ₂ : N.RateConstants)
    (href : κ₁.k rRef = κ₂.k rRef)
    (hsense : κ₁.k rSense = κ₂.k rSense)
    (E₁ : N.StationaryExpectation κ₁) (E₂ : N.StationaryExpectation κ₂) :
    E₁.expectedCount out = E₂.expectedCount out := by
  rw [N.stationary_mean_output_maxRPA κ₁ C hpair E₁,
    N.stationary_mean_output_maxRPA κ₂ C hpair E₂, href, hsense]

end Network
end CRNT
