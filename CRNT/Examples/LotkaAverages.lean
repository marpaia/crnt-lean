import CRNT.Examples.Lotka
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Time averages along periodic orbits; Volterra's law of averages

Along a periodic mass-action orbit of period `T` the field integrates to zero over a period, so the
time-averaged reaction rates `ρ̄_r = (1/T) ∫_0^T κ_r x(t)^{y_r} dt` form a stoichiometric cycle:
`∑_r ρ̄_r (y'_r − y_r) = 0` (`PositivePeriodicOrbit.integral_field_eq_zero`,
`PositivePeriodicOrbit.averageRates_stoich_eq_zero`).

For the Lotka network (`A → 2A`, `A + B → 2B`, `B → 0`), integrating `d/dt log x_B = k₁ x_A − k₂`
and `d/dt log x_A = k₀ − k₁ x_B` over a period gives **Volterra's law of averages** (Volterra 1926):
the time averages of `x_A` and `x_B` over any positive periodic orbit equal the coordinates of the
positive equilibrium, `k₂/k₁` and `k₀/k₁` (`Lotka.average_A`, `Lotka.average_B`).
-/

namespace CRNT

open MeasureTheory intervalIntegral

namespace Network

namespace PositivePeriodicOrbit

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {κ : N.RateConstants}

theorem continuous_coord (P : N.PositivePeriodicOrbit κ) (s : S) :
    Continuous fun t => P.orbit t s :=
  continuous_iff_continuousAt.2 fun t => (P.solution t s).continuousAt

theorem continuous_orbit (P : N.PositivePeriodicOrbit κ) : Continuous P.orbit :=
  continuous_pi fun s => P.continuous_coord s

theorem continuous_rate (P : N.PositivePeriodicOrbit κ) (r : N.R) :
    Continuous fun t => N.massActionRate κ r (P.orbit t) := by
  unfold massActionRate Complex.massActionMonomial
  exact continuous_const.mul (continuous_finsetProd _ fun s _ => (P.continuous_coord s).pow _)

/-- **The field integrates to zero over a period.** -/
theorem integral_field_eq_zero (P : N.PositivePeriodicOrbit κ) (s : S) :
    ∫ t in (0 : ℝ)..P.period, N.massActionVectorField κ (P.orbit t) s = 0 := by
  have hcont : Continuous fun t => N.massActionVectorField κ (P.orbit t) s := by
    have : (fun t => N.massActionVectorField κ (P.orbit t) s) =
        fun t => ∑ r : N.R, N.massActionRate κ r (P.orbit t) * N.reactionVector r s := by
      funext t; rw [massActionVectorField_apply]
    rw [this]
    exact continuous_finsetSum _ fun r _ => (P.continuous_rate r).mul continuous_const
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => P.solution t s)
    (hcont.intervalIntegrable _ _), P.closes, sub_self]

/-- The time-averaged reaction rates over one period. -/
noncomputable def averageRates (P : N.PositivePeriodicOrbit κ) (r : N.R) : ℝ :=
  (∫ t in (0 : ℝ)..P.period, N.massActionRate κ r (P.orbit t)) / P.period

/-- **Averaged fluxes are a stoichiometric cycle:** `∑_r ρ̄_r (y'_r − y_r) = 0`. -/
theorem averageRates_stoich_eq_zero (P : N.PositivePeriodicOrbit κ) (s : S) :
    ∑ r : N.R, P.averageRates r * N.reactionVector r s = 0 := by
  have h := P.integral_field_eq_zero s
  have hsplit : (∫ t in (0 : ℝ)..P.period, N.massActionVectorField κ (P.orbit t) s) =
      ∑ r : N.R, (∫ t in (0 : ℝ)..P.period, N.massActionRate κ r (P.orbit t)) *
        N.reactionVector r s := by
    simp_rw [massActionVectorField_apply]
    rw [intervalIntegral.integral_finsetSum
      (f := fun r t => N.massActionRate κ r (P.orbit t) * N.reactionVector r s) fun r _ =>
      ((P.continuous_rate r).mul continuous_const).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun r _ => intervalIntegral.integral_mul_const _ _
  rw [hsplit] at h
  simp only [averageRates, div_mul_eq_mul_div, ← Finset.sum_div, h, zero_div]

/-- The average of a coordinate over one period. -/
noncomputable def average (P : N.PositivePeriodicOrbit κ) (s : S) : ℝ :=
  (∫ t in (0 : ℝ)..P.period, P.orbit t s) / P.period

/-- **Logarithmic derivatives integrate to zero over a period.** -/
theorem integral_logDeriv_eq_zero (P : N.PositivePeriodicOrbit κ) (s : S) :
    ∫ t in (0 : ℝ)..P.period, N.massActionVectorField κ (P.orbit t) s / P.orbit t s = 0 := by
  have hder : ∀ t, HasDerivAt (fun τ => Real.log (P.orbit τ s))
      (N.massActionVectorField κ (P.orbit t) s / P.orbit t s) t :=
    fun t => (P.solution t s).log (P.positive t s).ne'
  have hcont : Continuous fun t => N.massActionVectorField κ (P.orbit t) s / P.orbit t s := by
    have : (fun t => N.massActionVectorField κ (P.orbit t) s) =
        fun t => ∑ r : N.R, N.massActionRate κ r (P.orbit t) * N.reactionVector r s := by
      funext t; rw [massActionVectorField_apply]
    refine Continuous.div ?_ (P.continuous_coord s) fun t => (P.positive t s).ne'
    rw [this]
    exact continuous_finsetSum _ fun r _ => (P.continuous_rate r).mul continuous_const
  rw [integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hcont.intervalIntegrable _ _), P.closes,
    sub_self]

end PositivePeriodicOrbit

end Network

namespace Examples

namespace Lotka

open Network

/-- **Volterra's law of averages, predator equation.** The time average of `x_A` over any positive
periodic orbit equals `k₂/k₁`, the `A`-coordinate of the positive equilibrium. -/
theorem average_A (κ : Network.RateConstants N) (P : N.PositivePeriodicOrbit κ) :
    P.average A = κ.k decay / κ.k prey := by
  have h := P.integral_logDeriv_eq_zero B
  have hT := P.period_pos
  have hcA := P.continuous_coord A
  have hrw : (fun t => N.massActionVectorField κ (P.orbit t) B / P.orbit t B) =
      fun t => κ.k prey * P.orbit t A - κ.k decay := by
    funext t
    rw [field_B]
    have := (P.positive t B).ne'
    field_simp
  rw [hrw, intervalIntegral.integral_sub ((hcA.const_mul _).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at h
  have hk := (κ.positive prey).ne'
  rw [PositivePeriodicOrbit.average]
  field_simp
  linarith

/-- **Volterra's law of averages, prey equation.** The time average of `x_B` over any positive
periodic orbit equals `k₀/k₁`, the `B`-coordinate of the positive equilibrium. -/
theorem average_B (κ : Network.RateConstants N) (P : N.PositivePeriodicOrbit κ) :
    P.average B = κ.k grow / κ.k prey := by
  have h := P.integral_logDeriv_eq_zero A
  have hT := P.period_pos
  have hcB := P.continuous_coord B
  have hrw : (fun t => N.massActionVectorField κ (P.orbit t) A / P.orbit t A) =
      fun t => κ.k grow - κ.k prey * P.orbit t B := by
    funext t
    rw [field_A]
    have := (P.positive t A).ne'
    field_simp
  rw [hrw, intervalIntegral.integral_sub intervalIntegrable_const
    ((hcB.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  have hk := (κ.positive prey).ne'
  rw [PositivePeriodicOrbit.average]
  field_simp
  linarith

end Lotka

end Examples

end CRNT
