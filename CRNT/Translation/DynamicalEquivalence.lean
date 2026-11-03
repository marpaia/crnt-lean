import CRNT.Equilibria.SteadyState

/-!
# Dynamical equivalence of mass-action realizations

Two mass-action CRNs on the same species set are *dynamically equivalent at chosen rate
constants* when they induce exactly the same polynomial vector field.  This is the minimal
mathematical relation underlying alternative CRN realizations and network-translation methods:
the reaction graphs may differ, but the ODE is identical.

This file deliberately contains no realization-search algorithm.  It only formalizes the
mathematical equivalence relation and its immediate consequences for steady states.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two rate-parametrized mass-action networks are dynamically equivalent when their vector
fields agree at every concentration. -/
def MassActionDynamicallyEquivalent (N M : Network S)
    (κN : RateConstants N) (κM : RateConstants M) : Prop :=
  ∀ x : Concentration S, N.massActionVectorField κN x = M.massActionVectorField κM x

@[refl] theorem massActionDynamicallyEquivalent_refl (N : Network S)
    (κ : RateConstants N) :
    N.MassActionDynamicallyEquivalent N κ κ := by
  intro x
  rfl

@[symm] theorem MassActionDynamicallyEquivalent.symm {N M : Network S}
    {κN : RateConstants N} {κM : RateConstants M}
    (h : N.MassActionDynamicallyEquivalent M κN κM) :
    M.MassActionDynamicallyEquivalent N κM κN := by
  intro x
  exact (h x).symm

@[trans] theorem MassActionDynamicallyEquivalent.trans {N M L : Network S}
    {κN : RateConstants N} {κM : RateConstants M} {κL : RateConstants L}
    (hNM : N.MassActionDynamicallyEquivalent M κN κM)
    (hML : M.MassActionDynamicallyEquivalent L κM κL) :
    N.MassActionDynamicallyEquivalent L κN κL := by
  intro x
  exact (hNM x).trans (hML x)

/-- Dynamically equivalent realizations have exactly the same mass-action steady states. -/
theorem MassActionDynamicallyEquivalent.steadyState_iff {N M : Network S}
    {κN : RateConstants N} {κM : RateConstants M}
    (h : N.MassActionDynamicallyEquivalent M κN κM) (x : Concentration S) :
    N.IsMassActionSteadyState κN x ↔ M.IsMassActionSteadyState κM x := by
  unfold IsMassActionSteadyState IsSteadyState
  constructor <;> intro hx s
  · have hs := hx s
    rw [h x] at hs
    exact hs
  · have hs := hx s
    rw [h x]
    exact hs

/-- Equality of the mass-action vector fields as functions is equivalent to dynamical
 equivalence.  This is useful when a symbolic realization argument proves function equality. -/
theorem massActionDynamicallyEquivalent_iff_field_eq (N M : Network S)
    (κN : RateConstants N) (κM : RateConstants M) :
    N.MassActionDynamicallyEquivalent M κN κM ↔
      N.massActionVectorField κN = M.massActionVectorField κM := by
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

/-- A packaged alternative realization of a fixed mass-action system. -/
structure MassActionRealization (N : Network S) (κN : RateConstants N) where
  network : Network S
  rates : RateConstants network
  equivalent : N.MassActionDynamicallyEquivalent network κN rates

namespace MassActionRealization

variable {N : Network S} {κN : RateConstants N}

/-- The original network is itself a realization. -/
def self (N : Network S) (κN : RateConstants N) : MassActionRealization N κN where
  network := N
  rates := κN
  equivalent := N.massActionDynamicallyEquivalent_refl κN

/-- Every alternative realization has the same steady-state predicate as the original one. -/
theorem steadyState_iff (R : MassActionRealization N κN) (x : Concentration S) :
    N.IsMassActionSteadyState κN x ↔ R.network.IsMassActionSteadyState R.rates x :=
  R.equivalent.steadyState_iff x

end MassActionRealization

end Network
end CRNT
