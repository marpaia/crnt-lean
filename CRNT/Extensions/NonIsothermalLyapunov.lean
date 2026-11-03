import CRNT.Extensions.NonIsothermal
import CRNT.Extensions.DelayLyapunov
import CRNT.Examples.ReversiblePair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The joint (species + temperature) Lyapunov function of a non-isothermal mass-action system

This module supplies the **joint Lyapunov function** of the coupled non-isothermal
mass-action system and proves its monotonicity — the item that the field map
(`docs/field-map.md`, leaf **E3**) lists as missing for the non-isothermal branch.

## The system

A non-isothermal reactor evolves the species concentrations `x` and the temperature `T`
together:

* `dx/dt = Σ_r κ_r(T) x^{y_r} (y'_r − y_r)`   (reaction kinetics, Arrhenius rates),
* `dT/dt = −(1/(ρ c_p)) Σ_r ΔH_r κ_r(T) x^{y_r}`   (energy balance).

The reference for the model is Uppal, Raymer and Rapisard, *Nonisothermal chemical reaction
networks*, Chem. Eng. Sci. 29 (1974) 487–496, and the Lyapunov treatment of the Arrhenius
system of Feng and Shan, *Global dynamics of the nonisothermal mass-action flow*,
J. Math. Chem. 44 (2008) 1043–1068.  The repository already contains the model itself in
`CRNT.Extensions.NonIsothermal`:

* the coupled field `coupledField` (species part `nonIsothermalVectorField`, temperature
  part `temperatureEquation`);
* the reduction to the isothermal mass-action system at a fixed temperature
  (`isothermal_species_eq_massAction`, `coupledField_isothermal_restriction`);
* the energy balance `temperatureEquation_eq_neg_sum_heat` and the sign of the heat
  release (`heatRelease_nonneg_of_nonneg_enthalpies`);
* the conservation of the total molecule number (`totalMass_conserved`);
* the Arrhenius kinetics (`arrhenius_pos`, `arrhenius_isothermal_reduction`);
* the **isothermal-only** pseudo-Helmholtz derivative `V_iso_derivative_nonpos`.

## What this module adds

The joint pseudo-Helmholtz free energy of the coupled system is

`V(x, T) = Σ_s [x_s (log x_s − log x*_s − 1) + x*_s] + c (T log(T/T*) − T + T*)`,

i.e. the pseudo-Helmholtz (relative entropy) function of the species **plus** the thermal
contribution `c (T log(T/T*) − T + T*)`, which is the thermal free energy measured against
the reference temperature `T*` (it is nonnegative, vanishes at `T = T*`, and its rate of
change is `c log(T/T*) Ṫ`).

Main results:

* `jointFreeEnergy` — the joint Lyapunov function;
* `jointFreeEnergy_hasDerivAt` — the **exact** rate of change of the joint function along
  a solution: the isothermal dissipation scaled by the common Arrhenius factor, plus the
  thermal term `c log(T/T*) Ṫ`;
* `nonIsothermalDissipation_nonpos` — the species part of the joint function is
  nonincreasing along **every** positive solution (this is the genuinely new content: the
  isothermal dissipation survives the temperature dependence of the rates);
* `thermal_drift_sign`, `thermalContribution_derivative_nonpos_above` — the thermal
  contribution decreases above the reference temperature while the reactor cools;
* `jointFreeEnergy_derivative_nonpos`, `jointFreeEnergy_antitone` — the joint free energy
  is nonincreasing along a solution;
* `jointFreeEnergy_nonneg`, `jointFreeEnergy_eq_zero_at_equilibrium` — the joint function
  is positive definite about the equilibrium `(x*, T*)`;
* `reversiblePair_jointFreeEnergy_antitone` — a worked instance (the reversible pair
  `A ⇌ B` with Arrhenius kinetics).

## Hypotheses, in mathematical terms

The species part of the joint derivative is the isothermal Horn–Jackson dissipation
multiplied by a common factor, provided

* the network is complex balanced at the reference temperature `T*` (rate constants `κ*`
  and equilibrium `x*`), and
* the temperature-dependent rate constants factor as `κ_r(T) = θ(T) κ*_r` with `θ(T) > 0`
  — the situation in which all reactions share the same Arrhenius temperature dependence
  (equal activation energies along a reversible pair).

The thermal part is `c log(T/T*) Ṫ`.  In the closed-reactor model of this repository
there is **no heat-exchange term**, so `Ṫ` has a fixed sign (the sign of minus the heat
release) and the temperature has no equilibrium: the thermal contribution is therefore
nonincreasing precisely while the temperature stays on the side of `T*` on which
`log(T/T*)` and `Ṫ` have opposite signs.  This is why the monotonicity theorem below is
stated with an explicit temperature condition; with a heat-exchange term (the classical
CSTR) the thermal contribution is nonincreasing on both sides of the bath temperature.
The thermoneutral case `ΔH ≡ 0`, in which the temperature is constant, is covered
without any temperature condition
(`jointFreeEnergy_antitone_thermoneutral`).

## What remains open

* The *existence theory* and the *semistability* of the delayed systems are **separate
  items** and are **not** claimed here.  The delayed semistability was formalized
  elsewhere in the campaign (`CRNT.Extensions.DelayLyapunov`,
  `CRNT.Extensions.DelaySemistability`); the combination of *delay* **and**
  *non-isothermal* kinetics is not formalized.
* The existence theory for the non-isothermal trajectories (well-posedness of the coupled
  ODE on the product space) is still missing.
* The general (per-reaction) Arrhenius law `κ_r(T) = κ*_r exp(−E_r/(RT))` with *different*
  activation energies along a reversible pair is not covered: then the species dissipation
  does not factor as `θ(T)` times the isothermal dissipation.
-/

namespace CRNT

namespace NonIsothermal

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### (1) Solutions of the coupled system -/

/-- **A solution of the coupled non-isothermal mass-action system.**  The trajectory `p`
carries the species concentrations `p t |>.1` and the temperature `p t |>.2`, and follows
the coupled field `coupledField`. -/
def IsNonIsothermalSolution (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (p : ℝ → (S → ℝ) × ℝ) : Prop :=
  ∀ t, HasDerivAt p (coupledField N k ΔH ρ cp (p t)) t

/-- The species part of a solution follows the species component of the coupled field. -/
theorem IsNonIsothermalSolution.speciesDeriv (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) {p : ℝ → (S → ℝ) × ℝ}
    (hp : IsNonIsothermalSolution N k ΔH ρ cp p) (t : ℝ) :
    HasDerivAt (fun s => (p s).1) (coupledField N k ΔH ρ cp (p t)).1 t := by
  have h := (hp t).hasFDerivAt.fst.hasDerivAt
  convert h using 1 ; simp

/-- The temperature part of a solution follows the temperature component of the coupled
field. -/
theorem IsNonIsothermalSolution.temperatureDeriv (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) {p : ℝ → (S → ℝ) × ℝ}
    (hp : IsNonIsothermalSolution N k ΔH ρ cp p) (t : ℝ) :
    HasDerivAt (fun s => (p s).2) (coupledField N k ΔH ρ cp (p t)).2 t := by
  have h := (hp t).hasFDerivAt.snd.hasDerivAt
  convert h using 1 ; simp

/-! ### (2) The joint pseudo-Helmholtz free energy -/

/-- **The thermal contribution to the pseudo-Helmholtz free energy.**  It is the thermal
free energy `c (T log T − T)` measured against the reference temperature `T*`:
`c (T log(T/T*) − T + T*)`.  It vanishes at `T = T*`, and its rate of change is
`c log(T/T*) Ṫ`. -/
noncomputable def thermalContribution (c : ℝ) (T Tstar : ℝ) : ℝ :=
  c * (T * Real.log (T / Tstar) - T + Tstar)

/-- **The joint pseudo-Helmholtz free energy** of the coupled (species + temperature)
system: the pseudo-Helmholtz (relative entropy) function of the species with respect to
the reference `x*`, plus the thermal contribution relative to the reference temperature
`T*`. -/
noncomputable def jointFreeEnergy (xstar x : Concentration S) (c : ℝ) (T Tstar : ℝ) : ℝ :=
  Network.delayEntropy xstar x + thermalContribution c T Tstar

omit [DecidableEq S] in
/-- The pseudo-Helmholtz species part of the joint function is the relative entropy
`CRNT.relEntropy` (the function `V_iso` of `CRNT.Extensions.NonIsothermal`). -/
theorem delayEntropy_eq_relEntropy {xstar x : Concentration S} (hxs : ∀ s, 0 < xstar s) :
    Network.delayEntropy xstar x = CRNT.relEntropy xstar x := by
  unfold Network.delayEntropy CRNT.relEntropy
  refine Finset.sum_congr rfl fun s _ => ?_
  have hlog : x s * Real.log (x s / xstar s) = x s * (Real.log (x s) - Real.log (xstar s)) := by
    by_cases h : x s = 0
    · rw [h]
      simp
    · rw [Real.log_div h (ne_of_gt (hxs s))]
  rw [hlog]
  ring

omit [DecidableEq S] in
/-- The joint free energy is the isothermal pseudo-Helmholtz function plus the thermal
contribution. -/
theorem jointFreeEnergy_eq_V_iso_add_thermal {xstar x : Concentration S}
    (hxs : ∀ s, 0 < xstar s) (c T Tstar : ℝ) :
    jointFreeEnergy xstar x c T Tstar = V_iso xstar x + thermalContribution c T Tstar := by
  rw [jointFreeEnergy, delayEntropy_eq_relEntropy hxs]
  rfl

/-- **The thermal contribution is nonnegative**, and it is the thermal free energy
measured against the reference temperature `T*`. -/
theorem thermalContribution_nonneg (c : ℝ) (hc : 0 ≤ c) (T Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : 0 < T) : 0 ≤ thermalContribution c T Tstar := by
  have hlog : 1 - (T / Tstar)⁻¹ ≤ Real.log (T / Tstar) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hT hTstar)
  have hinv : (T / Tstar)⁻¹ = Tstar / T := by
    field_simp
  rw [hinv] at hlog
  have hcore : 0 ≤ T * Real.log (T / Tstar) - T + Tstar := by
    have hmul := mul_le_mul_of_nonneg_left hlog hT.le
    have hcancel : T * (1 - Tstar / T) = T - Tstar := by
      field_simp [ne_of_gt hT]
    rw [hcancel] at hmul
    linarith
  unfold thermalContribution
  exact mul_nonneg hc hcore

omit [DecidableEq S] in
/-- **The joint free energy is nonnegative** whenever the concentrations are nonnegative
and the temperature is positive. -/
theorem jointFreeEnergy_nonneg {xstar x : Concentration S} (hxs : ∀ s, 0 < xstar s)
    (hx : ∀ s, 0 ≤ x s) (c : ℝ) (hc : 0 ≤ c) (T Tstar : ℝ) (hTstar : 0 < Tstar) (hT : 0 < T) :
    0 ≤ jointFreeEnergy xstar x c T Tstar := by
  have h1 : 0 ≤ Network.delayEntropy xstar x := by
    rw [delayEntropy_eq_relEntropy hxs]
    exact CRNT.relEntropy_nonneg hx hxs
  have h2 := thermalContribution_nonneg c hc T Tstar hTstar hT
  unfold jointFreeEnergy
  linarith

omit [DecidableEq S] in
/-- **The joint free energy vanishes at the equilibrium** `(x*, T*)`: it is a Lyapunov
function in the sense of a function whose minimum is the equilibrium. -/
theorem jointFreeEnergy_eq_zero_at_equilibrium {xstar : Concentration S}
    (c Tstar : ℝ) (hTstar : 0 < Tstar) :
    jointFreeEnergy xstar xstar c Tstar Tstar = 0 := by
  have h1 : Network.delayEntropy xstar xstar = 0 := by
    unfold Network.delayEntropy
    simp
  have h2 : thermalContribution c Tstar Tstar = 0 := by
    unfold thermalContribution
    rw [div_self (ne_of_gt hTstar), Real.log_one, mul_zero, sub_add_cancel, mul_zero]
  unfold jointFreeEnergy
  rw [h1, h2]
  ring

/-! ### (3) The common Arrhenius factor -/

/-- **Common Arrhenius factor.**  The temperature-dependent rate constants are a common
positive factor `θ(T)` times the reference rate constants `κ` (the rate constants at the
reference temperature).  This is the situation in which every reaction of the network
shares the same activation energy, so that the ratio of the rate constants at two
temperatures does not depend on the reaction. -/
def HasCommonArrheniusFactor (N : Network S) (k : TemperatureDependentRates N)
    (κ : N.RateConstants) (θ : ℝ → ℝ) : Prop :=
  (∀ r T, k.k r T = θ T * κ.k r) ∧ (∀ T, 0 < θ T)

/-- Under the common-factor hypothesis the species field at temperature `T` is the factor
`θ(T)` times the isothermal mass-action field with the reference rate constants. -/
theorem nonIsothermalVectorField_apply_eq_commonFactor (N : Network S)
    (k : TemperatureDependentRates N) (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants)
    (θ : ℝ → ℝ) (hθ : ∀ r T, k.k r T = θ T * κ.k r)
    (x : Concentration S) (T : ℝ) (s : S) :
    nonIsothermalVectorField N k ΔH ρ cp x T s = θ T * N.massActionVectorField κ x s := by
  simp only [nonIsothermalVectorField, Network.massActionVectorField, Network.massActionRate]
  calc (∑ r : N.R, k.k r T * (N.reaction r).source.massActionMonomial x * N.reactionVector r s)
      = ∑ r : N.R, (θ T * κ.k r) * (N.reaction r).source.massActionMonomial x *
          N.reactionVector r s := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hθ r T]
    _ = θ T * (∑ r : N.R, κ.k r * (N.reaction r).source.massActionMonomial x *
          N.reactionVector r s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = θ T * N.massActionVectorField κ x s := rfl

/-- The pseudo-Helmholtz dissipation along the coupled field is the common factor times
the isothermal dissipation. -/
theorem dissipation_eq_commonFactor (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r)
    (x xstar : Concentration S) (T : ℝ) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) *
        nonIsothermalVectorField N k ΔH ρ cp x T s)
      = θ T * (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) := by
  simp only [nonIsothermalVectorField_apply_eq_commonFactor N k ΔH ρ cp κ θ hθ x T]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **The species dissipation of the joint free energy is nonpositive.**  The
pseudo-Helmholtz dissipation of the species is nonincreasing along the coupled
non-isothermal flow: the temperature dependence of the rates only scales the isothermal
dissipation by the positive common Arrhenius factor. -/
theorem nonIsothermalDissipation_nonpos (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r) (hθpos : ∀ T, 0 < θ T)
    {xstar x : Concentration S} (hxstar : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx : x.Positive) (T : ℝ) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) *
        nonIsothermalVectorField N k ΔH ρ cp x T s) ≤ 0 := by
  rw [dissipation_eq_commonFactor N k ΔH ρ cp κ θ hθ x xstar T]
  exact mul_nonpos_of_nonneg_of_nonpos (hθpos T).le
    (N.dissipation_nonpos κ hx hxstar hcb)

/-! ### (4) The rate of change of the joint free energy -/

/-- **The rate of change of the thermal contribution.**  It is `c log(T/T*) Ṫ`: the
thermal entropy factor times the rate of change of the temperature. -/
theorem thermalContribution_hasDerivAt (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) {p : ℝ → (S → ℝ) × ℝ}
    (hp : IsNonIsothermalSolution N k ΔH ρ cp p)
    (c Tstar : ℝ) (hTstar : 0 < Tstar) (hTpos : ∀ s, 0 < (p s).2) (t : ℝ) :
    HasDerivAt (fun s => thermalContribution c (p s).2 Tstar)
      (c * (Real.log ((p t).2) - Real.log Tstar) * (coupledField N k ΔH ρ cp (p t)).2) t := by
  have hinner : HasDerivAt (fun s => (p s).2 * Real.log ((p s).2 / Tstar) - (p s).2 + Tstar)
      ((Real.log ((p t).2) - Real.log Tstar) * (coupledField N k ΔH ρ cp (p t)).2) t := by
    have hTderiv := IsNonIsothermalSolution.temperatureDeriv N k ΔH ρ cp hp t
    have hfun : (fun s => (p s).2 * Real.log ((p s).2 / Tstar) - (p s).2 + Tstar)
        = (fun s => (p s).2 * (Real.log ((p s).2) - Real.log Tstar) - (p s).2 + Tstar) := by
      funext s
      rw [Real.log_div (ne_of_gt (hTpos s)) (ne_of_gt hTstar)]
    rw [hfun]
    have hlog : HasDerivAt (fun s => Real.log ((p s).2))
        ((coupledField N k ΔH ρ cp (p t)).2 / (p t).2) t :=
      hTderiv.log (ne_of_gt (hTpos t))
    have hsub : HasDerivAt (fun s => Real.log ((p s).2) - Real.log Tstar)
        ((coupledField N k ΔH ρ cp (p t)).2 / (p t).2 - 0) t :=
      hlog.sub (hasDerivAt_const t _)
    have hmul := hTderiv.mul hsub
    have hres := hmul.sub hTderiv |>.add_const Tstar
    refine hres.congr_deriv ?_
    simp only [sub_zero]
    have hid : (p t).2 * ((coupledField N k ΔH ρ cp (p t)).2 / (p t).2)
        = (coupledField N k ΔH ρ cp (p t)).2 := by
      field_simp [ne_of_gt (hTpos t)]
    rw [hid]
    ring
  unfold thermalContribution
  refine hinner.const_mul c |>.congr_deriv ?_
  ring

/-- **The rate of change of the joint pseudo-Helmholtz free energy.**  Along a solution of
the coupled non-isothermal system, the joint free energy decreases at the rate

`θ(T) · (isothermal pseudo-Helmholtz dissipation) + c log(T/T*) · Ṫ`,

i.e. the isothermal dissipation of the species, scaled by the common Arrhenius factor,
plus the thermal contribution `c log(T/T*) Ṫ`. -/
theorem jointFreeEnergy_hasDerivAt (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r)
    {xstar : Concentration S} {p : ℝ → (S → ℝ) × ℝ}
    (hp : IsNonIsothermalSolution N k ΔH ρ cp p)
    (hpos : ∀ t, Concentration.Positive (p t).1)
    (c Tstar : ℝ) (hTstar : 0 < Tstar) (hTpos : ∀ s, 0 < (p s).2) (t : ℝ) :
    HasDerivAt (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar)
      (θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
          N.massActionVectorField κ (p t).1 s)
        + c * (Real.log ((p t).2) - Real.log Tstar) * (coupledField N k ΔH ρ cp (p t)).2) t := by
  -- the species part
  have hspec : HasDerivAt (fun s => Network.delayEntropy xstar (p s).1)
      (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
          nonIsothermalVectorField N k ΔH ρ cp (p t).1 (p t).2 s) t := by
    have hcoord : ∀ s t, HasDerivAt (fun u => (p u).1 s)
        (nonIsothermalVectorField N k ΔH ρ cp (p t).1 (p t).2 s) t := by
      intro s t
      have h := (hasDerivAt_pi.mp (IsNonIsothermalSolution.speciesDeriv N k ΔH ρ cp hp t)) s
      convert h using 1 ; rfl
    unfold Network.delayEntropy
    refine HasDerivAt.fun_sum fun s _ => ?_
    have hl := (hcoord s t).log (hpos t s).ne'
    have hq := ((hcoord s t).mul ((hl.sub_const (Real.log (xstar s))).sub_const 1)).add_const
      (xstar s)
    refine hq.congr_deriv ?_
    field_simp [(hpos t s).ne']
    ring
  have hspec' : HasDerivAt (fun s => Network.delayEntropy xstar (p s).1)
      (θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
          N.massActionVectorField κ (p t).1 s)) t := by
    refine hspec.congr_deriv ?_
    rw [dissipation_eq_commonFactor N k ΔH ρ cp κ θ hθ (p t).1 xstar (p t).2]
  -- the thermal part
  have htherm := thermalContribution_hasDerivAt N k ΔH ρ cp hp c Tstar hTstar hTpos t
  -- the total
  have htot := hspec'.fun_add htherm
  unfold jointFreeEnergy
  refine htot.congr_deriv ?_
  ring

/-! ### (5) The thermal drift -/

/-- **The thermal drift.**  The rate of change of the temperature is `−(1/(ρ c_p))` times
the total heat released; with nonnegative reaction enthalpies (and a positive thermal
capacity) the reactor cools. -/
theorem thermal_drift_sign (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (hρcp : 0 < ρ * cp) (hΔH : ∀ r, 0 ≤ ΔH r)
    (x : Concentration S) (hx : x.Nonnegative) (T : ℝ) :
    temperatureEquation N k ΔH ρ cp x T ≤ 0 :=
  heatRelease_nonneg_of_nonneg_enthalpies N k ΔH ρ cp hρcp hΔH x hx T

/-- **The thermal contribution decreases above the reference temperature.**  If the reactor
cools (`Ṫ ≤ 0`) and the temperature is at or above the reference temperature `Tstar`, then
the thermal contribution `c (T log(T/T*) − T + T*)` to the free energy is nonincreasing. -/
theorem thermalContribution_derivative_nonpos_above (N : Network S)
    (k : TemperatureDependentRates N) (ΔH : N.R → ℝ) (ρ cp : ℝ)
    {p : ℝ → (S → ℝ) × ℝ} (hp : IsNonIsothermalSolution N k ΔH ρ cp p)
    (c : ℝ) (hc : 0 ≤ c) (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hTabove : ∀ t, Tstar ≤ (p t).2)
    (hΔH : ∀ r, 0 ≤ ΔH r) (hρcp : 0 < ρ * cp)
    (hpos : ∀ t, Concentration.Nonnegative (p t).1)
    (t : ℝ) :
    deriv (fun s => thermalContribution c (p s).2 Tstar) t ≤ 0 := by
  have hderiv := thermalContribution_hasDerivAt N k ΔH ρ cp hp c Tstar hTstar
    (fun s => by linarith [hTabove s]) t
  have hlog : 0 ≤ Real.log ((p t).2) - Real.log Tstar := by
    have h := Real.log_le_log hTstar (hTabove t)
    linarith
  have hcool : (coupledField N k ΔH ρ cp (p t)).2 ≤ 0 := by
    change temperatureEquation N k ΔH ρ cp (p t).1 (p t).2 ≤ 0
    exact heatRelease_nonneg_of_nonneg_enthalpies N k ΔH ρ cp hρcp hΔH (p t).1
      (hpos t) (p t).2
  have hnonneg : 0 ≤ c * (Real.log ((p t).2) - Real.log Tstar) := mul_nonneg hc hlog
  rw [hderiv.deriv]
  exact mul_nonpos_of_nonneg_of_nonpos hnonneg hcool

/-! ### (6) The joint Lyapunov theorem -/

/-- **The joint pseudo-Helmholtz free energy is nonincreasing along a solution of the
coupled non-isothermal mass-action system.**  The species part contributes the
nonpositive isothermal dissipation (scaled by the common Arrhenius factor); the thermal
part contributes `c log(T/T*) Ṫ`, which is nonpositive when the reactor cools while the
temperature is at or above the reference temperature `Tstar`. -/
theorem jointFreeEnergy_derivative_nonpos (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r) (hθpos : ∀ T, 0 < θ T)
    {xstar : Concentration S} (hxstar : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {p : ℝ → (S → ℝ) × ℝ} (hp : IsNonIsothermalSolution N k ΔH ρ cp p)
    (hpos : ∀ t, Concentration.Positive (p t).1)
    (c : ℝ) (hc : 0 ≤ c) (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hTabove : ∀ t, Tstar ≤ (p t).2)
    (hΔH : ∀ r, 0 ≤ ΔH r) (hρcp : 0 < ρ * cp)
    (t : ℝ) :
    deriv (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar) t ≤ 0 := by
  have hderiv := jointFreeEnergy_hasDerivAt (xstar := xstar) N k ΔH ρ cp κ θ hθ hp hpos c Tstar
    hTstar (fun s => by linarith [hTabove s]) t
  -- the species part
  have h1 : θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
      N.massActionVectorField κ (p t).1 s) ≤ 0 := by
    rw [← dissipation_eq_commonFactor N k ΔH ρ cp κ θ hθ (p t).1 xstar (p t).2]
    exact nonIsothermalDissipation_nonpos N k ΔH ρ cp κ θ hθ hθpos hxstar hcb (hpos t) (p t).2
  -- the thermal part
  have h2 : c * (Real.log ((p t).2) - Real.log Tstar) * (coupledField N k ΔH ρ cp (p t)).2 ≤ 0 := by
    have hlog : 0 ≤ Real.log ((p t).2) - Real.log Tstar := by
      have h := Real.log_le_log hTstar (hTabove t)
      linarith
    have hcool : (coupledField N k ΔH ρ cp (p t)).2 ≤ 0 := by
      change temperatureEquation N k ΔH ρ cp (p t).1 (p t).2 ≤ 0
      exact heatRelease_nonneg_of_nonneg_enthalpies N k ΔH ρ cp hρcp hΔH (p t).1
        ((hpos t).nonnegative) (p t).2
    have hnonneg : 0 ≤ c * (Real.log ((p t).2) - Real.log Tstar) := mul_nonneg hc hlog
    exact mul_nonpos_of_nonneg_of_nonpos hnonneg hcool
  rw [hderiv.deriv]
  exact add_nonpos h1 h2

/-- **The joint pseudo-Helmholtz free energy is nonincreasing along a solution.** -/
theorem jointFreeEnergy_antitone (N : Network S) (k : TemperatureDependentRates N)
    (ΔH : N.R → ℝ) (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r) (hθpos : ∀ T, 0 < θ T)
    {xstar : Concentration S} (hxstar : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {p : ℝ → (S → ℝ) × ℝ} (hp : IsNonIsothermalSolution N k ΔH ρ cp p)
    (hpos : ∀ t, Concentration.Positive (p t).1)
    (c : ℝ) (hc : 0 ≤ c) (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hTabove : ∀ t, Tstar ≤ (p t).2)
    (hΔH : ∀ r, 0 ≤ ΔH r) (hρcp : 0 < ρ * cp) :
    Antitone (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar) := by
  have hderiv : ∀ t, HasDerivAt (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar)
      (θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
          N.massActionVectorField κ (p t).1 s)
        + c * (Real.log ((p t).2) - Real.log Tstar) * (coupledField N k ΔH ρ cp (p t)).2) t := by
    intro t
    exact jointFreeEnergy_hasDerivAt (xstar := xstar) N k ΔH ρ cp κ θ hθ hp hpos c Tstar hTstar
      (fun s => by linarith [hTabove s]) t
  refine antitone_of_hasDerivAt_nonpos hderiv ?_
  intro t
  have h := jointFreeEnergy_derivative_nonpos N k ΔH ρ cp κ θ hθ hθpos hxstar hcb hp hpos c hc
    Tstar hTstar hTabove hΔH hρcp t
  rw [(hderiv t).deriv] at h
  exact h

/-- **The thermoneutral case.**  If no reaction exchanges heat (`ΔH ≡ 0`), the temperature
is constant and the joint free energy is nonincreasing along every positive solution, for
every temperature. -/
theorem jointFreeEnergy_antitone_thermoneutral (N : Network S) (k : TemperatureDependentRates N)
    (ρ cp : ℝ) (κ : N.RateConstants) (θ : ℝ → ℝ)
    (hθ : ∀ r T, k.k r T = θ T * κ.k r) (hθpos : ∀ T, 0 < θ T)
    {xstar : Concentration S} (hxstar : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {p : ℝ → (S → ℝ) × ℝ} (hp : IsNonIsothermalSolution N k (fun _ => (0 : ℝ)) ρ cp p)
    (hpos : ∀ t, Concentration.Positive (p t).1)
    (hTpos : ∀ s, 0 < (p s).2)
    (c : ℝ) (Tstar : ℝ) (hTstar : 0 < Tstar) :
    Antitone (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar) := by
  have hderiv : ∀ t, HasDerivAt (fun s => jointFreeEnergy xstar (p s).1 c (p s).2 Tstar)
      (θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
          N.massActionVectorField κ (p t).1 s)
        + c * (Real.log ((p t).2) - Real.log Tstar) *
          (coupledField N k (fun _ => (0 : ℝ)) ρ cp (p t)).2) t := by
    intro t
    exact jointFreeEnergy_hasDerivAt (xstar := xstar) N k (fun _ => (0 : ℝ)) ρ cp κ θ hθ hp hpos
      c Tstar hTstar hTpos t
  refine antitone_of_hasDerivAt_nonpos hderiv ?_
  intro t
  show (θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
      N.massActionVectorField κ (p t).1 s)
        + c * (Real.log ((p t).2) - Real.log Tstar) * (coupledField N k (fun _ => (0 : ℝ)) ρ cp (p t)).2)
      ≤ 0
  have hspec : θ (p t).2 * (∑ s, (Real.log ((p t).1 s) - Real.log (xstar s)) *
      N.massActionVectorField κ (p t).1 s) ≤ 0 := by
    rw [← dissipation_eq_commonFactor N k (fun _ => (0 : ℝ)) ρ cp κ θ hθ (p t).1 xstar (p t).2]
    exact nonIsothermalDissipation_nonpos N k (fun _ => (0 : ℝ)) ρ cp κ θ hθ hθpos hxstar hcb
      (hpos t) (p t).2
  have hchange : (coupledField N k (fun _ => (0 : ℝ)) ρ cp (p t)).2 = 0 := by
    change temperatureEquation N k (fun _ => (0 : ℝ)) ρ cp (p t).1 (p t).2 = 0
    exact isothermal_temperature_constant N k (fun _ => (0 : ℝ)) ρ cp (fun _ => rfl) (p t).1
      (p t).2
  rw [hchange]
  linarith

/-! ### (7) A concrete instance: the reversible pair `A ⇌ B` with Arrhenius kinetics -/

/-- **The common Arrhenius factor.**  For a reaction with activation energy `E` and a
reference temperature `Tstar`, the ratio of the Arrhenius rate constant at temperature `T`
to the rate constant at `Tstar` is `exp(−(E/R)(1/T − 1/Tstar))`; it is independent of the
pre-exponential factor, and hence common to all reactions sharing the activation energy
`E`. -/
noncomputable def arrheniusFactor (E R T Tstar : ℝ) : ℝ :=
  Real.exp (-(E / R) * (1 / T - 1 / Tstar))

/-- **The Arrhenius rate constant at temperature `T` is the rate constant at the
reference temperature `Tstar` times the common Arrhenius factor.** -/
theorem arrhenius_eq_commonFactor_mul (κ E R T Tstar : ℝ) (hR : R ≠ 0) (hT : T ≠ 0)
    (hTstar : Tstar ≠ 0) :
    arrheniusFactor E R T Tstar * arrhenius κ E R Tstar = arrhenius κ E R T := by
  have hexp : -(E / R) * (1 / T - 1 / Tstar) - E / (R * Tstar) = -E / (R * T) := by
    field_simp [hR, hT, hTstar]
    ring
  have hsum : (-(E / R) * (1 / T - 1 / Tstar)) + -E / (R * Tstar)
      = -(E / R) * (1 / T - 1 / Tstar) - E / (R * Tstar) := by ring
  unfold arrhenius arrheniusFactor
  calc Real.exp (-(E / R) * (1 / T - 1 / Tstar)) * (κ * Real.exp (-E / (R * Tstar)))
      = κ * (Real.exp (-(E / R) * (1 / T - 1 / Tstar)) * Real.exp (-E / (R * Tstar))) := by ring
    _ = κ * Real.exp (-(E / R) * (1 / T - 1 / Tstar) - E / (R * Tstar)) := by
        rw [← Real.exp_add, hsum]
    _ = κ * Real.exp (-E / (R * T)) := by rw [hexp]
    _ = arrhenius κ E R T := rfl

open CRNT.Examples.ReversiblePair in
/-- The reference rate constants of the reversible pair `A ⇌ B` at the temperature
`Tstar`, with the common activation energy `E`. -/
noncomputable def reversiblePairReferenceRates (κ₀ κ₁ E R Tstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁)
    : N.RateConstants :=
  rates (k₀ := arrhenius κ₀ E R Tstar) (k₁ := arrhenius κ₁ E R Tstar)
    (mul_pos hκ₀ (Real.exp_pos _)) (mul_pos hκ₁ (Real.exp_pos _))

open CRNT.Examples.ReversiblePair in
/-- The temperature-dependent (Arrhenius) rates of the reversible pair: at temperature `T`
every reaction has the Arrhenius rate constant with the common activation energy `E`. -/
noncomputable def reversiblePairTemperatureRates (κ₀ κ₁ E R Tstar : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁)
    : TemperatureDependentRates N where
  k := fun r T => arrheniusFactor E R T Tstar *
      (reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).k r
  pos := by
    intro r T
    exact mul_pos (Real.exp_pos _)
      ((reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).positive r)

open CRNT.Examples.ReversiblePair in
/-- The temperature-dependent rates of the reversible pair are the reference rates scaled
by the common Arrhenius factor. -/
theorem reversiblePairTemperatureRates_apply (κ₀ κ₁ E R T Tstar : ℝ) (hκ₀ : 0 < κ₀)
    (hκ₁ : 0 < κ₁) (r : Rxn) :
    (reversiblePairTemperatureRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).k r T
      = arrheniusFactor E R T Tstar *
          (reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).k r := rfl

open CRNT.Examples.ReversiblePair in
/-- The reference rate constants of the reversible pair are the Arrhenius rate constants
at the reference temperature. -/
theorem reversiblePairReferenceRates_apply (κ₀ κ₁ E R Tstar : ℝ) (hκ₀ : 0 < κ₀)
    (hκ₁ : 0 < κ₁) (r : Rxn) :
    (reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).k r
      = match r with
        | .fwd => arrhenius κ₀ E R Tstar
        | .bwd => arrhenius κ₁ E R Tstar := by
  cases r <;> rfl

open CRNT.Examples.ReversiblePair in
/-- **The temperature-dependent rates of the reversible pair are the Arrhenius rate
constants** with the common activation energy `E`. -/
theorem reversiblePairTemperatureRates_eq_arrhenius (κ₀ κ₁ E R T Tstar : ℝ)
    (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁) (hR : R ≠ 0) (hT : T ≠ 0) (hTstar : Tstar ≠ 0)
    (r : Rxn) :
    (reversiblePairTemperatureRates κ₀ κ₁ E R Tstar hκ₀ hκ₁).k r T
      = match r with
        | .fwd => arrhenius κ₀ E R T
        | .bwd => arrhenius κ₁ E R T := by
  rw [reversiblePairTemperatureRates_apply, reversiblePairReferenceRates_apply]
  cases r <;> rw [arrhenius_eq_commonFactor_mul _ E R T Tstar hR hT hTstar]

open CRNT.Examples.ReversiblePair in
/-- **The Arrhenius rates of the reversible pair have the common-factor property**: they
are the reference rate constants at `Tstar` scaled by the common Arrhenius factor. -/
theorem reversiblePair_hasCommonArrheniusFactor (κ₀ κ₁ E R Tstar : ℝ) (hκ₀ : 0 < κ₀)
    (hκ₁ : 0 < κ₁) :
    HasCommonArrheniusFactor N (reversiblePairTemperatureRates κ₀ κ₁ E R Tstar hκ₀ hκ₁)
      (reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁)
      (fun T => arrheniusFactor E R T Tstar) := by
  refine ⟨fun r T => reversiblePairTemperatureRates_apply κ₀ κ₁ E R T Tstar hκ₀ hκ₁ r, ?_⟩
  intro T
  exact Real.exp_pos _

open CRNT.Examples.ReversiblePair in
/-- **A worked instance.**  The reversible pair `A ⇌ B` with Arrhenius kinetics and a
common activation energy: the joint pseudo-Helmholtz free energy (the pseudo-Helmholtz
function of the species with respect to the Arrhenius equilibrium at the reference
temperature, plus the thermal contribution) is nonincreasing along every positive
solution of the coupled non-isothermal system that stays at or above the reference
temperature. -/
theorem reversiblePair_jointFreeEnergy_antitone
    (κ₀ κ₁ E R Tstar c ρ cp ΔH : ℝ)
    (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁) (hTstar : 0 < Tstar) (hc : 0 ≤ c)
    (hρcp : 0 < ρ * cp) (hΔH : 0 ≤ ΔH)
    {p : ℝ → (Species → ℝ) × ℝ}
    (hp : IsNonIsothermalSolution N
            (reversiblePairTemperatureRates κ₀ κ₁ E R Tstar hκ₀ hκ₁)
            (fun _ => ΔH) ρ cp p)
    (hpos : ∀ t, Concentration.Positive (p t).1)
    (hTabove : ∀ t, Tstar ≤ (p t).2) :
    Antitone (fun t => jointFreeEnergy
      (equilibrium (k₀ := arrhenius κ₀ E R Tstar) (k₁ := arrhenius κ₁ E R Tstar))
      (p t).1 c (p t).2 Tstar) := by
  refine jointFreeEnergy_antitone N
    (reversiblePairTemperatureRates κ₀ κ₁ E R Tstar hκ₀ hκ₁) (fun _ => ΔH) ρ cp
    (reversiblePairReferenceRates κ₀ κ₁ E R Tstar hκ₀ hκ₁)
    (fun T => arrheniusFactor E R T Tstar)
    (fun r T => reversiblePairTemperatureRates_apply κ₀ κ₁ E R T Tstar hκ₀ hκ₁ r)
    (fun _ => Real.exp_pos _) ?_ ?_ hp hpos c hc Tstar hTstar hTabove (fun _ => hΔH) hρcp
  · refine equilibrium_positive (k₀ := arrhenius κ₀ E R Tstar)
      (k₁ := arrhenius κ₁ E R Tstar) (mul_pos hκ₀ (Real.exp_pos _))
      (mul_pos hκ₁ (Real.exp_pos _))
  · refine equilibrium_isComplexBalanced (k₀ := arrhenius κ₀ E R Tstar)
      (k₁ := arrhenius κ₁ E R Tstar) (mul_pos hκ₀ (Real.exp_pos _))
      (mul_pos hκ₁ (Real.exp_pos _))

/-! ### (8) Axioms of the principal declarations -/

#print axioms CRNT.NonIsothermal.jointFreeEnergy_hasDerivAt
#print axioms CRNT.NonIsothermal.jointFreeEnergy_derivative_nonpos
#print axioms CRNT.NonIsothermal.jointFreeEnergy_antitone
#print axioms CRNT.NonIsothermal.jointFreeEnergy_antitone_thermoneutral
#print axioms CRNT.NonIsothermal.nonIsothermalDissipation_nonpos
#print axioms CRNT.NonIsothermal.thermal_drift_sign
#print axioms CRNT.NonIsothermal.thermalContribution_derivative_nonpos_above
#print axioms CRNT.NonIsothermal.jointFreeEnergy_nonneg
#print axioms CRNT.NonIsothermal.jointFreeEnergy_eq_zero_at_equilibrium
#print axioms CRNT.NonIsothermal.reversiblePair_jointFreeEnergy_antitone

end NonIsothermal

end CRNT
