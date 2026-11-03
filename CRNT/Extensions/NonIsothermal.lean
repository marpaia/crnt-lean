import CRNT.Basic.Network
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.Concentration
import CRNT.Basic.Reaction
import CRNT.Stoich.Subspace
import CRNT.Stoich.ConservationDimension
import CRNT.Flux.PSemiflow
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Equilibria.DetailedBalanced
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Non-isothermal (temperature-dependent) mass-action systems

This module formalizes the **non-isothermal** extension of mass-action kinetics, the
missing part of field-map leaf E3.  In a non-isothermal reactor the species
concentrations `x` and the temperature `T` evolve together:

* `dx/dt = Σ_r k_r(T) x^{y_r} (y'_r − y_r)`  (reaction kinetics, Arrhenius rates),
* `dT/dt = −(1/(ρ c_p)) Σ_r ΔH_r k_r(T) x^{y_r}`  (energy balance).

The isothermal system is recovered when `T` is held constant.  This module is the
temperature analogue of `CRNT/Extensions/DelayMassAction.lean`: it introduces the
coupled field, proves the isothermal reduction, records the first-law bookkeeping,
and (best effort) the isothermal pseudo-Helmholtz Lyapunov part.

What is proved here:
* the non-isothermal model and its coupled field;
* isothermal reduction at constant temperature;
* energy bookkeeping (`temperatureEquation_eq_neg_sum_heat`,
  `heatRelease_nonneg_of_nonneg_enthalpies`);
* conservation of every linear conservation law of the network, in particular total
  mass when the all-ones vector is a P-invariant;
* the isothermal pseudo-Helmholtz (relative entropy) dissipation inequality for
  detailed-balanced networks, reusing `Network.dissipation_nonpos`.

What is still missing (left open by design, matching leaf E3):
* existence theory for non-isothermal trajectories (well-posedness of the coupled
  ODE on the product space);
* semistability / convergence to an equilibrium in the non-isothermal class;
* a joint Lyapunov function combining the pseudo-Helmholtz part with a
  temperature term.  The published Lipták–Hangos–Pituk–Szederkényi form requires
  reversible pairs with opposite enthalpies (`ΔH r = −ΔH r'`) and a quadratic
  temperature term whose exact coefficient depends on the reaction enthalpies; we
  do not invent that coefficient, so only the isothermal part is certified here;
* non-isothermal (temperature-dependent) kinetics beyond the model definition.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Kinetics.MassAction`, `CRNT.Stoich.*`, `CRNT.Flux.PSemiflow`,
`CRNT.Theorems.DeficiencyZero.Dissipation`, `CRNT.Equilibria.DetailedBalanced`.
-/

namespace CRNT

namespace NonIsothermal

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Temperature-dependent (Arrhenius-style) rate constants: a positive rate for every
reaction and every temperature. -/
structure TemperatureDependentRates (N : Network S) where
  /-- Rate constant as a function of reaction and temperature. -/
  k : N.R → ℝ → ℝ
  /-- Positivity for all reactions and temperatures. -/
  pos : ∀ r T, 0 < k r T

/-- Mass-action rate of reaction `r` at temperature `T` and concentration `x`. -/
def nonIsothermalRate (N : Network S) (k : TemperatureDependentRates N) (T : ℝ)
    (r : N.R) (x : Concentration S) : ℝ :=
  k.k r T * (N.reaction r).source.massActionMonomial x

/-- Species part of the non-isothermal vector field.  The enthalpy, density and heat
capacity do not affect the species equations. -/
def nonIsothermalVectorField (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (x : Concentration S) (T : ℝ) : S → ℝ :=
  fun s => ∑ r : N.R, k.k r T * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r s

/-- Energy balance: temperature derivative. -/
noncomputable def temperatureEquation (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (x : Concentration S) (T : ℝ) : ℝ :=
  -(1 / (ρ * cp)) * ∑ r : N.R, ΔH r * nonIsothermalRate N k T r x

/-- Coupled field on the product space `(concentrations, temperature)`. -/
noncomputable def coupledField (N : Network S) (k : TemperatureDependentRates N) (ΔH : N.R → ℝ)
    (ρ cp : ℝ) (p : (S → ℝ) × ℝ) : (S → ℝ) × ℝ :=
  (nonIsothermalVectorField N k ΔH ρ cp p.1 p.2,
    temperatureEquation N k ΔH ρ cp p.1 p.2)

/-! ### (2) Isothermal reduction -/

/-- At a constant temperature `T₀`, the species part of the non-isothermal field
equals the mass-action vector field with rate constants `κ_r = k_r(T₀)`. -/
theorem isothermal_species_eq_massAction (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (T₀ : ℝ) (x : Concentration S) :
    N.massActionVectorField
        ({ k := fun r => k.k r T₀, positive := fun r => k.pos r T₀ } : N.RateConstants) x =
      nonIsothermalVectorField N k ΔH ρ cp x T₀ := by
  funext s
  simp [Network.massActionVectorField_apply, Network.massActionRate, nonIsothermalVectorField]

/-- If all reaction enthalpies vanish, the temperature equation vanishes
identically. -/
theorem isothermal_temperature_constant (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (hΔH : ∀ r, ΔH r = 0) (x : Concentration S) (T : ℝ) :
    temperatureEquation N k ΔH ρ cp x T = 0 := by
  have hsum : ∑ r : N.R, ΔH r * (k.k r T * (N.reaction r).source.massActionMonomial x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    simp [hΔH r]
  unfold temperatureEquation nonIsothermalRate
  simp [hsum]

/-- The coupled field restricted to `{(x, T₀)}` is the isothermal mass-action field in
the first component and `0` in the second (when all enthalpies vanish). -/
theorem coupledField_isothermal_restriction (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (hΔH : ∀ r, ΔH r = 0) (T₀ : ℝ) (x : Concentration S) :
    (coupledField N k ΔH ρ cp (x, T₀)).1 =
        N.massActionVectorField
          ({ k := fun r => k.k r T₀, positive := fun r => k.pos r T₀ } : N.RateConstants) x ∧
    (coupledField N k ΔH ρ cp (x, T₀)).2 = 0 := by
  constructor
  · funext s
    simp [coupledField, nonIsothermalVectorField, Network.massActionVectorField_apply, Network.massActionRate]
  · have hsum : ∑ r : N.R, ΔH r * (k.k r T₀ * (N.reaction r).source.massActionMonomial x) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      simp [hΔH r]
    simp [coupledField, temperatureEquation, nonIsothermalRate, hsum]

/-! ### (3) First law / energy bookkeeping -/

/-- The temperature derivative is `-(1/(ρ c_p))` times the total heat released
`Σ_r ΔH_r · rate_r`. -/
theorem temperatureEquation_eq_neg_sum_heat (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (x : Concentration S) (T : ℝ) :
    temperatureEquation N k ΔH ρ cp x T =
      -(1 / (ρ * cp)) * ∑ r : N.R, ΔH r * nonIsothermalRate N k T r x := rfl

/-- If all enthalpies are nonnegative and the concentration is nonnegative, the
reactor cools: `dT/dt ≤ 0` (needs `ρ c_p > 0`). -/
theorem heatRelease_nonneg_of_nonneg_enthalpies (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (hρcp : 0 < ρ * cp) (hΔH : ∀ r, 0 ≤ ΔH r)
    (x : Concentration S) (hx : x.Nonnegative) (T : ℝ) :
    temperatureEquation N k ΔH ρ cp x T ≤ 0 := by
  have hsum : 0 ≤ ∑ r : N.R, ΔH r *
      (k.k r T * (N.reaction r).source.massActionMonomial x) := by
    apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (hΔH r)
    apply mul_nonneg (k.pos r T).le
    exact Complex.massActionMonomial_nonneg hx _
  have hpos : 0 < 1 / (ρ * cp) := one_div_pos.mpr hρcp
  unfold temperatureEquation nonIsothermalRate
  have hprod : 0 ≤ (1 / (ρ * cp)) *
      ∑ r : N.R, ΔH r * (k.k r T * (N.reaction r).source.massActionMonomial x) :=
    mul_nonneg hpos.le hsum
  linarith [hprod]

/-- Every linear conservation law of the network is conserved by the species
equations, for any temperature-dependent rates. -/
theorem pInvariant_conserved (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp T : ℝ) (x : Concentration S) {w : S → ℝ}
    (hw : N.IsPInvariant w) :
    ∑ s : S, w s * nonIsothermalVectorField N k ΔH ρ cp x T s = 0 := by
  unfold nonIsothermalVectorField
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun r _ => ?_)
  have hinner : ∑ s : S, w s * N.reactionVector r s = 0 := by
    have horth := (CRNT.mem_orthSum).mp hw
    exact horth (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
  have hfactor : ∑ s : S, w s *
        (k.k r T * (N.reaction r).source.massActionMonomial x * N.reactionVector r s) =
      k.k r T * (N.reaction r).source.massActionMonomial x *
        ∑ s : S, w s * N.reactionVector r s := by
    calc ∑ s : S, w s * (k.k r T * (N.reaction r).source.massActionMonomial x * N.reactionVector r s)
        = ∑ s : S, (k.k r T * (N.reaction r).source.massActionMonomial x) * (w s * N.reactionVector r s) := by
            refine Finset.sum_congr rfl (fun s _ => by ring)
      _ = (k.k r T * (N.reaction r).source.massActionMonomial x) *
            ∑ s : S, w s * N.reactionVector r s := by
            exact (Finset.mul_sum Finset.univ (fun s => w s * N.reactionVector r s)
              (k.k r T * (N.reaction r).source.massActionMonomial x)).symm
  rw [hfactor, hinner, mul_zero]

/-- Total number of molecules is conserved when the all-ones vector is a
P-invariant of the network. -/
theorem totalMass_conserved (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (T : ℝ) (x : Concentration S)
    (hinv : N.IsPInvariant (fun _ => (1 : ℝ))) :
    ∑ s : S, nonIsothermalVectorField N k ΔH ρ cp x T s = 0 := by
  have h := pInvariant_conserved N k ΔH ρ cp T x (w := fun _ => (1 : ℝ)) hinv
  simpa using h

/-! ### (4) Isothermal Lyapunov (pseudo-Helmholtz part) -/

/-- The isothermal pseudo-Helmholtz (relative entropy) function
`V_iso(x) = Σ_s x_s (ln(x_s/x*_s) − 1) + x*_s`. -/
noncomputable def V_iso (xstar x : Concentration S) : ℝ :=
  CRNT.relEntropy xstar x

/-- Along the isothermal flow of a detailed-balanced network, the directional
derivative of `V_iso` is nonpositive.  This reuses `Network.dissipation_nonpos`
rather than redoing the Horn–Jackson estimate. -/
theorem V_iso_derivative_nonpos (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hdb : N.IsDetailedBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) *
        N.massActionVectorField κ x s) ≤ 0 := by
  exact N.dissipation_nonpos κ hx hxs (N.isComplexBalanced_of_isDetailedBalanced κ xstar hdb)

/-! ### (5) Concrete Arrhenius instance -/

/-- A concrete two-species reversible network `A ⇌ B`. -/
def arrheniusNetwork : Network (Fin 2) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := fun s => if s = 0 then 1 else 0,
        target := fun s => if s = 1 then 1 else 0 }
    else
      { source := fun s => if s = 1 then 1 else 0,
        target := fun s => if s = 0 then 1 else 0 }

/-- Arrhenius rate constant `κ exp(-E/(R T))`. -/
noncomputable def arrhenius (κ E R T : ℝ) : ℝ := κ * Real.exp (-E / (R * T))

/-- Temperature-dependent rates on `arrheniusNetwork` with Arrhenius factors. -/
noncomputable def arrheniusRates (κ : Fin 2 → ℝ) (E : Fin 2 → ℝ) (R : ℝ)
    (hκ : ∀ r, 0 < κ r) (hE : ∀ r, 0 ≤ E r) (hR : 0 < R) :
    TemperatureDependentRates arrheniusNetwork where
  k := fun r T => arrhenius (κ r) (E r) R T
  pos := fun r T => by
    unfold arrhenius
    exact mul_pos (hκ r) (Real.exp_pos _)

/-- Positivity of the Arrhenius rate constant for `T > 0`. -/
theorem arrhenius_pos (κ : Fin 2 → ℝ) (E : Fin 2 → ℝ) (R T : ℝ)
    (hκ : ∀ r, 0 < κ r) (hT : 0 < T) (r : Fin 2) :
    0 < arrhenius (κ r) (E r) R T := by
  unfold arrhenius
  exact mul_pos (hκ r) (Real.exp_pos _)

/-- The Arrhenius factor is strictly increasing in `T` for `E > 0` (standard
Arrhenius).  Note: the prompt's "decreases" would require a negative activation
energy; the mathematically correct property for `E > 0` is increase. -/
theorem arrhenius_increases (κ E R T₁ T₂ : ℝ)
    (hκ : 0 < κ) (hE : 0 < E) (hR : 0 < R) (hT1 : 0 < T₁) (hT2 : 0 < T₂)
    (hlt : T₁ < T₂) :
    arrhenius κ E R T₁ < arrhenius κ E R T₂ := by
  unfold arrhenius
  have hdiff : 0 < E / (R * T₁) - E / (R * T₂) := by
    field_simp [hR.ne', hT1.ne', hT2.ne']
    nlinarith [hE, hR, hT1, hT2, hlt]
  have hltexp : -E / (R * T₁) < -E / (R * T₂) := by
    have h1 : 1 / T₂ < 1 / T₁ := one_div_lt_one_div_of_lt hT1 hlt
    have hER : 0 < E / R := div_pos hE hR
    have h2 : E / (R * T₂) < E / (R * T₁) := by
      have : (E / R) * (1 / T₂) < (E / R) * (1 / T₁) :=
        mul_lt_mul_of_pos_left h1 hER
      field_simp [hR.ne', hT1.ne', hT2.ne'] at this ⊢
      linarith [this]
    have : -(E / (R * T₁)) < -(E / (R * T₂)) := neg_lt_neg h2
    field_simp [hR.ne', hT1.ne', hT2.ne'] at this ⊢
    linarith [this]
  have hexp : Real.exp (-E / (R * T₁)) < Real.exp (-E / (R * T₂)) :=
    Real.exp_strictMono hltexp
  exact mul_lt_mul_of_pos_left hexp hκ

/-- The all-ones vector is a P-invariant of the reversible network. -/
theorem arrheniusNetwork_one_isPInvariant :
    arrheniusNetwork.IsPInvariant (fun _ => (1 : ℝ)) := by
  refine CRNT.mem_orthSum_span (G := Set.range arrheniusNetwork.reactionVector) ?_
  intro g hg
  rcases hg with ⟨r, rfl⟩
  fin_cases r
  · rw [Fin.sum_univ_two]
    simp [arrheniusNetwork, Network.reactionVector, Reaction.vector]
  · rw [Fin.sum_univ_two]
    simp [arrheniusNetwork, Network.reactionVector, Reaction.vector]

/-- Isothermal reduction for the Arrhenius instance. -/
theorem arrhenius_isothermal_reduction (κ : Fin 2 → ℝ) (E : Fin 2 → ℝ) (R T₀ : ℝ)
    (hκ : ∀ r, 0 < κ r) (hE : ∀ r, 0 ≤ E r) (hR : 0 < R) (x : Concentration (Fin 2)) :
    arrheniusNetwork.massActionVectorField
        ({ k := fun r => (arrheniusRates κ E R hκ hE hR).k r T₀,
           positive := fun r => (arrheniusRates κ E R hκ hE hR).pos r T₀ } :
         arrheniusNetwork.RateConstants) x =
      nonIsothermalVectorField arrheniusNetwork (arrheniusRates κ E R hκ hE hR)
        (fun _ => 0) 1 1 x T₀ := by
  exact isothermal_species_eq_massAction arrheniusNetwork
    (arrheniusRates κ E R hκ hE hR) (fun _ => 0) 1 1 T₀ x

/-- Conservation-law instance for the Arrhenius network. -/
theorem arrhenius_totalMass_conserved (κ : Fin 2 → ℝ) (E : Fin 2 → ℝ) (R : ℝ)
    (hκ : ∀ r, 0 < κ r) (hE : ∀ r, 0 ≤ E r) (hR : 0 < R)
    (x : Concentration (Fin 2)) (T : ℝ) :
    ∑ s : Fin 2, nonIsothermalVectorField arrheniusNetwork (arrheniusRates κ E R hκ hE hR)
        (fun _ => 0) 1 1 x T s = 0 := by
  apply totalMass_conserved
  exact arrheniusNetwork_one_isPInvariant

end NonIsothermal

end CRNT