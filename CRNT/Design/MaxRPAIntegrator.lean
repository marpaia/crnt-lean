import CRNT.Design.MaxRPA
import CRNT.Stochastic.Generator

/-!
# Internal-model integrators for maxRPA

The maxRPA charge witness is not merely a steady-state certificate.  Along trajectories it
provides an internal-model coordinate.  Under the source-pattern condition,

`d⟨q,x⟩/dt = -k_sense m(x) (x_out - x_set)`

where `m(x)` is the common background reactant monomial.  In the stochastic/maximal special
case the background monomial is one, so the charge itself is an exact linear integral
controller for the output error.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The common background monomial of a unit-output-gap pair. -/
def maxRPABackgroundMonomial (N : Network S) (rRef : N.R)
    (x : Concentration S) : ℝ :=
  (N.reaction rRef).source.massActionMonomial x

/-- Setpoint encoded by the two distinguished rate constants and the charge gain. -/
noncomputable def maxRPASetpoint {N : Network S} {rRef rSense : N.R}
    (κ : N.RateConstants) (C : N.MaxRPAChargeCertificate rRef rSense) : ℝ :=
  C.gain * κ.k rRef / κ.k rSense

/-- **Internal-model error identity.** -/
theorem maxRPA_charge_derivative_eq_weighted_error
    (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hgap : N.UnitOutputGap rRef rSense out)
    (x : Concentration S) :
    ∑ s : S, C.charge s * N.massActionVectorField κ x s =
      -κ.k rSense * N.maxRPABackgroundMonomial rRef x *
        (x out - N.maxRPASetpoint κ C) := by
  rw [N.charge_vectorField_identity κ C.identity x]
  unfold maxRPABackgroundMonomial maxRPASetpoint massActionRate
  rw [N.massActionMonomial_unitOutputGap hgap x]
  field_simp [(κ.positive rSense).ne']
  ring

/-- A stochastic-maxRPA source pair: the reference reaction has no reactants and the
sensing reaction consumes exactly one molecule of the output species and nothing else. -/
def StochasticMaxRPASourcePair (N : Network S)
    (rRef rSense : N.R) (out : S) : Prop :=
  (∀ s, (N.reaction rRef).source s = 0) ∧
  (N.reaction rSense).source out = 1 ∧
  (∀ s, s ≠ out → (N.reaction rSense).source s = 0)

/-- Stochastic source pairs imply the deterministic unit-gap condition. -/
theorem StochasticMaxRPASourcePair.unitOutputGap
    {N : Network S} {rRef rSense : N.R} {out : S}
    (h : N.StochasticMaxRPASourcePair rRef rSense out) :
    N.UnitOutputGap rRef rSense out := by
  constructor
  · rw [h.1 out, h.2.1]
  · intro s hs
    rw [h.1 s, h.2.2 s hs]

/-- The background monomial of a stochastic-maxRPA pair is identically one. -/
theorem backgroundMonomial_eq_one_of_stochasticPair
    (N : Network S) {rRef rSense : N.R} {out : S}
    (h : N.StochasticMaxRPASourcePair rRef rSense out)
    (x : Concentration S) :
    N.maxRPABackgroundMonomial rRef x = 1 := by
  unfold maxRPABackgroundMonomial Complex.massActionMonomial
  simp [h.1]

/-- **Exact linear integral-control identity in the stochastic/maximal case.** -/
theorem stochasticMaxRPA_charge_derivative_eq_error
    (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hpair : N.StochasticMaxRPASourcePair rRef rSense out)
    (x : Concentration S) :
    ∑ s : S, C.charge s * N.massActionVectorField κ x s =
      -κ.k rSense * (x out - N.maxRPASetpoint κ C) := by
  rw [N.maxRPA_charge_derivative_eq_weighted_error κ C hpair.unitOutputGap x,
    N.backgroundMonomial_eq_one_of_stochasticPair hpair x, mul_one]

/-- Antithetic charge pattern: the integrator uses both positive and negative charges. -/
def IsAntitheticCharge {N : Network S} {rRef rSense : N.R}
    (C : N.MaxRPAChargeCertificate rRef rSense) : Prop :=
  (∃ s, 0 < C.charge s) ∧ ∃ t, C.charge t < 0

/-- Homothetic charge pattern: after an overall sign choice all nonzero charges have the
same sign. -/
def IsHomotheticCharge {N : Network S} {rRef rSense : N.R}
    (C : N.MaxRPAChargeCertificate rRef rSense) : Prop :=
  (∀ s, 0 ≤ C.charge s) ∨ (∀ s, C.charge s ≤ 0)

/-- Antithetic and homothetic charge patterns are mutually exclusive. -/
theorem not_homothetic_of_antitheticCharge
    {N : Network S} {rRef rSense : N.R}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hanti : IsAntitheticCharge C) : ¬ IsHomotheticCharge C := by
  rintro (hpos | hneg)
  · obtain ⟨t, ht⟩ := hanti.2
    linarith [hpos t]
  · obtain ⟨s, hs⟩ := hanti.1
    linarith [hneg s]

/-- Any charge vector that is not homothetic has an antithetic sign pattern. -/
theorem antithetic_of_not_homotheticCharge
    {N : Network S} {rRef rSense : N.R}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (h : ¬ IsHomotheticCharge C) : IsAntitheticCharge C := by
  unfold IsHomotheticCharge at h
  push_neg at h
  rcases h with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  exact ⟨⟨t, ht⟩, ⟨s, hs⟩⟩

end Network
end CRNT
