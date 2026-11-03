import CRNT.Design.MaxRPA
import CRNT.Stochastic.FosterLyapunov
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FinCases

/-!
# Antithetic integral feedback: deterministic and stochastic setpoints

The antithetic integral controller of Briat, Gupta and Khammash (*Antithetic integral
feedback ensures robust perfect adaptation in noisy biomolecular networks*, Cell Systems 2
(2016)) consists of a reference reaction `∅ → Z₁` (rate `μ`), a sensing reaction
`X → X + Z₂` (rate `θ`), annihilation `Z₁ + Z₂ → ∅`, and actuation of the plant by `Z₁`.
The charge `q = e_{Z₁} - e_{Z₂}` is changed only by the reference (`+1`) and the sensing
(`-1`) reactions, which is exactly a maxRPA charge certificate of `CRNT.Design.MaxRPA`.

This module adds the **stochastic** counterpart of the maxRPA setpoint theorem:
* `CRNT.Network.observableGenerator_maxRPACharge`: the stochastic generator maps the charge
  observable to `gain · λ_ref(n) - λ_sense(n)` (stochastic internal-model identity).
* `CRNT.Network.stochastic_maxRPA_mean`: for any stationary law `π` satisfying the
  first-moment stationarity identity `E_π[A q] = 0` (the identity that Briat–Gupta–Khammash
  obtain from ergodicity and finite first moments), when the reference source is the zero
  complex and the sensing source is one output molecule, the stationary mean output is
  `E_π[X] = gain · κ_ref / κ_sense`, independently of every other rate constant.
* `CRNT.Antithetic.closedLoop`: the antithetic controller closed around a
  production–degradation plant, with its charge certificate, the deterministic setpoint
  `x_X = μ/θ` (`closedLoop_deterministic_setpoint`) and the stochastic setpoint
  `E_π[X] = μ/θ` (`closedLoop_stochastic_setpoint`).
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Stochastic internal-model identity.** -/
theorem observableGenerator_maxRPACharge (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {gain : ℝ} {q : S → ℝ} (hq : N.IsMaxRPACharge rRef rSense gain q)
    (n : S → ℕ) :
    N.observableGenerator κ (linearObservable q) n =
      gain * N.stochasticMassActionRate κ n rRef - N.stochasticMassActionRate κ n rSense := by
  rw [observableGenerator_linear]
  have : ∀ r, (∑ s : S, q s * N.reactionVector r s) =
      (if r = rRef then gain else 0) - (if r = rSense then 1 else 0) := fun r => hq r
  simp_rw [this, mul_sub, Finset.sum_sub_distrib]
  simp [mul_comm]

/-- Propensity of a reaction whose source is the zero complex. -/
theorem stochasticMassActionRate_of_source_zero (N : Network S) (κ : N.RateConstants)
    {r : N.R} (h : ∀ s, (N.reaction r).source s = 0) (n : S → ℕ) :
    N.stochasticMassActionRate κ n r = κ.k r := by
  unfold stochasticMassActionRate
  simp [h]

/-- Propensity of a reaction whose source is a single molecule of `out`. -/
theorem stochasticMassActionRate_of_source_unit (N : Network S) (κ : N.RateConstants)
    {r : N.R} {out : S} (h1 : (N.reaction r).source out = 1)
    (h0 : ∀ s, s ≠ out → (N.reaction r).source s = 0) (n : S → ℕ) :
    N.stochasticMassActionRate κ n r = κ.k r * n out := by
  unfold stochasticMassActionRate
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ out), h1,
    Finset.prod_eq_one (fun s hs => by rw [h0 s (Finset.ne_of_mem_erase hs)]; simp)]
  simp

/-- **Stochastic maxRPA / antithetic setpoint.** If the reference reaction has the zero
complex as source and the sensing reaction consumes one output molecule (and nothing else),
then every law `π` on counts with total mass one, finite first output moment and the
first-moment stationarity identity for the charge observable has stationary mean output
`gain · κ_ref / κ_sense`. -/
theorem stochastic_maxRPA_mean (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S} (C : N.MaxRPAChargeCertificate rRef rSense)
    (hgap : N.UnitOutputGap rRef rSense out) (href : ∀ s, (N.reaction rRef).source s = 0)
    (π : (S → ℕ) → ℝ) (hsum : Summable π) (hmass : ∑' n, π n = 1)
    (hsumOut : Summable (fun n => π n * (n out : ℝ)))
    (hstat : ∑' n, π n * N.observableGenerator κ (linearObservable C.charge) n = 0) :
    ∑' n, π n * (n out : ℝ) = C.gain * κ.k rRef / κ.k rSense := by
  have h1 : (N.reaction rSense).source out = 1 := by rw [hgap.1, href]
  have h0 : ∀ s, s ≠ out → (N.reaction rSense).source s = 0 := fun s hs => by
    rw [hgap.2 s hs, href]
  have hpt : ∀ n, π n * N.observableGenerator κ (linearObservable C.charge) n =
      C.gain * κ.k rRef * π n - κ.k rSense * (π n * (n out : ℝ)) := by
    intro n
    rw [N.observableGenerator_maxRPACharge κ C.identity n,
      N.stochasticMassActionRate_of_source_zero κ href,
      N.stochasticMassActionRate_of_source_unit κ h1 h0]
    ring
  simp_rw [hpt] at hstat
  rw [(hsum.mul_left _).tsum_sub (hsumOut.mul_left _), tsum_mul_left, tsum_mul_left,
    hmass, mul_one, sub_eq_zero] at hstat
  have hks : κ.k rSense ≠ 0 := (κ.positive rSense).ne'
  field_simp
  linarith

end Network

namespace Antithetic

open Network

/-! Species `0 = Z₁`, `1 = Z₂`, `2 = X`; reactions `0` reference `∅ → Z₁`,
`1` annihilation `Z₁ + Z₂ → ∅`, `2` actuation `Z₁ → Z₁ + X`, `3` degradation `X → ∅`,
`4` sensing `X → X + Z₂`. -/

/-- The reaction table. -/
def rxn : Fin 5 → Reaction (Fin 3)
  | 0 => ⟨![0, 0, 0], ![1, 0, 0]⟩
  | 1 => ⟨![1, 1, 0], ![0, 0, 0]⟩
  | 2 => ⟨![1, 0, 0], ![1, 0, 1]⟩
  | 3 => ⟨![0, 0, 1], ![0, 0, 0]⟩
  | 4 => ⟨![0, 0, 1], ![0, 1, 1]⟩

/-- The antithetic controller closed around a production–degradation plant. -/
def closedLoop : Network (Fin 3) := ⟨Fin 5, inferInstance, inferInstance, rxn⟩

/-- The reference reaction `∅ → Z₁`. -/
def rRef : closedLoop.R := (0 : Fin 5)
/-- The sensing reaction `X → X + Z₂`. -/
def rSense : closedLoop.R := (4 : Fin 5)

/-- The antithetic charge `e_{Z₁} - e_{Z₂}`. -/
def charge : Fin 3 → ℝ := ![1, -1, 0]

theorem charge_isMaxRPACharge : closedLoop.IsMaxRPACharge rRef rSense 1 charge := by
  intro r
  fin_cases r <;>
    simp [chargeIncrement, closedLoop, rxn, charge, rRef, rSense, Fin.sum_univ_three]

/-- The antithetic charge certificate (gain one). -/
def certificate : closedLoop.MaxRPAChargeCertificate rRef rSense :=
  ⟨1, one_pos, charge, charge_isMaxRPACharge⟩

theorem unitOutputGap : closedLoop.UnitOutputGap rRef rSense 2 := by
  refine ⟨by decide, fun s hs => ?_⟩
  fin_cases s <;> simp_all [closedLoop, rxn, rRef, rSense]

theorem ref_source_zero : ∀ s, (closedLoop.reaction rRef).source s = 0 := by
  intro s; fin_cases s <;> rfl

/-- **Deterministic robust perfect adaptation.** Every positive steady state of the closed
loop has `x_X = μ / θ`, for all values of the annihilation, actuation and degradation
rates. -/
theorem closedLoop_deterministic_setpoint (κ : closedLoop.RateConstants)
    {x : Concentration (Fin 3)} (hx : x.Positive) (hss : closedLoop.IsMassActionSteadyState κ x) :
    x 2 = κ.k rRef / κ.k rSense := by
  have := closedLoop.maxRPA_setpoint κ certificate unitOutputGap hx hss
  simpa [certificate] using this

/-- **Stochastic robust perfect adaptation** (Briat–Gupta–Khammash 2016). Every law on
counts of total mass one, with finite mean output and satisfying the first-moment
stationarity identity for the antithetic charge, has mean output `μ / θ`. -/
theorem closedLoop_stochastic_setpoint (κ : closedLoop.RateConstants)
    (π : (Fin 3 → ℕ) → ℝ) (hsum : Summable π) (hmass : ∑' n, π n = 1)
    (hsumOut : Summable (fun n => π n * (n 2 : ℝ)))
    (hstat : ∑' n, π n * closedLoop.observableGenerator κ (linearObservable charge) n = 0) :
    ∑' n, π n * (n 2 : ℝ) = κ.k rRef / κ.k rSense := by
  have := closedLoop.stochastic_maxRPA_mean κ certificate unitOutputGap ref_source_zero π hsum
    hmass hsumOut hstat
  simpa [certificate] using this

end Antithetic

end CRNT
