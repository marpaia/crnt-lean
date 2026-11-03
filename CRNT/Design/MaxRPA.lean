import CRNT.Equilibria.SteadyState
import CRNT.Deficiency.KernelDimension

/-!
# Structural maxRPA certificates

The deterministic maxRPA criterion can be separated into two exact algebraic pieces:

1. a **charge witness** `q` with `qᵀS = gain·e_ref - e_sense`, yielding the internal-model
   identity `d⟨q,x⟩/dt = gain·v_ref-v_sense`;
2. a source-pattern condition making the two distinguished mass-action monomials differ
   only by one power of the output species.

At steady state the first identity forces `gain·v_ref=v_sense`; the second cancels all
background reactants, pinning the output to `gain*k_ref/k_sense` independently of all
other reactions and rate constants.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Pairing of a species weight with a reaction vector. -/
def chargeIncrement (N : Network S) (q : S → ℝ) (r : N.R) : ℝ :=
  ∑ s : S, q s * N.reactionVector r s

/-- Charge witness for the two distinguished reactions. -/
def IsMaxRPACharge (N : Network S) (rRef rSense : N.R) (gain : ℝ)
    (q : S → ℝ) : Prop :=
  ∀ r : N.R,
    N.chargeIncrement q r =
      (if r = rRef then gain else 0) - (if r = rSense then 1 else 0)

/-- Existence of a positive-gain maxRPA charge witness. -/
structure MaxRPAChargeCertificate (N : Network S) (rRef rSense : N.R) where
  gain : ℝ
  gain_pos : 0 < gain
  charge : S → ℝ
  identity : N.IsMaxRPACharge rRef rSense gain charge

/-- Linear charge observable on concentration space. -/
def concentrationCharge (q : S → ℝ) (x : Concentration S) : ℝ :=
  ∑ s : S, q s * x s

/-- **Internal-model identity.** Pairing the vector field with a maxRPA charge leaves
only the two distinguished reaction fluxes. -/
theorem charge_vectorField_identity (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {gain : ℝ} {q : S → ℝ}
    (hq : N.IsMaxRPACharge rRef rSense gain q) (x : Concentration S) :
    ∑ s : S, q s * N.massActionVectorField κ x s =
      gain * N.massActionRate κ rRef x - N.massActionRate κ rSense x := by
  simp only [Network.massActionVectorField_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ r : N.R, ∑ s : S,
        q s * (N.massActionRate κ r x * N.reactionVector r s))
        = ∑ r : N.R, N.massActionRate κ r x * N.chargeIncrement q r := by
            apply Finset.sum_congr rfl
            intro r _
            unfold chargeIncrement
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
    _ = gain * N.massActionRate κ rRef x - N.massActionRate κ rSense x := by
          have hrewrite :
              (∑ r : N.R, N.massActionRate κ r x * N.chargeIncrement q r) =
                ∑ r : N.R, N.massActionRate κ r x *
                  ((if r = rRef then gain else 0) - (if r = rSense then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hq r]
          rw [hrewrite]
          simp only [mul_sub, Finset.sum_sub_distrib]
          simp [mul_comm]

/-- At every mass-action steady state the distinguished reaction fluxes obey the maxRPA
balance relation. -/
theorem maxRPA_flux_balance_at_steadyState (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} (C : N.MaxRPAChargeCertificate rRef rSense)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    C.gain * N.massActionRate κ rRef x = N.massActionRate κ rSense x := by
  have hcharge := N.charge_vectorField_identity κ C.identity x
  have hzero : (∑ s : S, C.charge s * N.massActionVectorField κ x s) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [hss s, mul_zero]
  linarith

/-- The two distinguished sources have a unit kinetic-order gap in the output species and
are identical on every other species. -/
def UnitOutputGap (N : Network S) (rRef rSense : N.R) (out : S) : Prop :=
  (N.reaction rSense).source out = (N.reaction rRef).source out + 1 ∧
  ∀ s, s ≠ out →
    (N.reaction rSense).source s = (N.reaction rRef).source s

/-- Under the unit-gap condition, the sensing source monomial is output concentration
times the reference source monomial. -/
theorem massActionMonomial_unitOutputGap (N : Network S)
    {rRef rSense : N.R} {out : S} (hgap : N.UnitOutputGap rRef rSense out)
    (x : Concentration S) :
    (N.reaction rSense).source.massActionMonomial x =
      x out * (N.reaction rRef).source.massActionMonomial x := by
  classical
  unfold Complex.massActionMonomial
  have hprod :
      (∏ s ∈ (Finset.univ.erase out), x s ^ (N.reaction rSense).source s) =
        ∏ s ∈ (Finset.univ.erase out), x s ^ (N.reaction rRef).source s := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [hgap.2 s (Finset.ne_of_mem_erase hs)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun s => x s ^ (N.reaction rSense).source s) (Finset.mem_univ out)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun s => x s ^ (N.reaction rRef).source s) (Finset.mem_univ out)]
  rw [hprod, hgap.1, pow_succ]
  ring

/-- **Generic deterministic maxRPA setpoint theorem.** -/
theorem maxRPA_setpoint (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hgap : N.UnitOutputGap rRef rSense out)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x) :
    x out = C.gain * κ.k rRef / κ.k rSense := by
  have hflux := N.maxRPA_flux_balance_at_steadyState κ C hss
  unfold massActionRate at hflux
  rw [N.massActionMonomial_unitOutputGap hgap x] at hflux
  have hmono : 0 < (N.reaction rRef).source.massActionMonomial x :=
    Complex.massActionMonomial_pos hx _
  have hks : κ.k rSense ≠ 0 := (κ.positive rSense).ne'
  field_simp
  nlinarith

/-- Two positive steady states at the same distinguished rate constants have the same
maxRPA output, regardless of all other network coordinates. -/
theorem maxRPA_output_eq_between_steadyStates (N : Network S) (κ : N.RateConstants)
    {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense)
    (hgap : N.UnitOutputGap rRef rSense out)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hxs : N.IsMassActionSteadyState κ x) (hys : N.IsMassActionSteadyState κ y) :
    x out = y out := by
  rw [N.maxRPA_setpoint κ C hgap hx hxs,
    N.maxRPA_setpoint κ C hgap hy hys]

end Network

end CRNT
