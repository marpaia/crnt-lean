import CRNT.Kinetics.MassAction
import CRNT.Stoich.Subspace
import CRNT.Equilibria.SteadyState

/-!
# General kinetics

The mass-action vector field is `∑ r, rate r x · reactionVector r s`; only the *rate*
is specific to mass action. A `Kinetics N` makes that rate a parameter: a map
`rate : N.R → Concentration S → ℝ` carrying Feinberg's admissibility hypotheses —
nonnegativity, vanishing when a source species is absent, dependence on the source
support only, and weak monotonicity (nondecreasing in each source species on the
nonnegative orthant). Mass action is recovered as `massActionKinetics`, whose induced
field is definitionally `massActionVectorField`.

The stoichiometry of the induced field — boundary non-attraction of the nonnegative
orthant and membership in the stoichiometric subspace — is kinetics-agnostic and is
proved here for every `Kinetics`. The mass-action-specific results (smoothness, the
toric/complex-balanced chain) stay in their own modules.

This module depends on: `CRNT.Kinetics.MassAction`, `CRNT.Stoich.Subspace`,
`CRNT.Equilibria.SteadyState`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- A **kinetics** for a network: a rate law `rate r x` for each reaction `r` at each
concentration `x`, subject to the standard admissibility hypotheses. Mass action is the
instance `massActionKinetics`; this is also the class over which the injectivity and
concordance theory is stated. -/
structure Kinetics (N : Network S) where
  /-- The rate of reaction `r` at concentration `x`. -/
  rate : N.R → Concentration S → ℝ
  /-- At a nonnegative concentration every rate is nonnegative. -/
  rate_nonneg : ∀ (r : N.R) {x : Concentration S}, x.Nonnegative → 0 ≤ rate r x
  /-- The rate vanishes when a species required by the source complex is absent. -/
  rate_vanishing : ∀ (r : N.R) {x : Concentration S} {s : S},
    (N.reaction r).source s ≠ 0 → x s = 0 → rate r x = 0
  /-- The rate depends only on the concentrations of the source species: if `x` and `y`
  agree on every species occurring in the source complex, the rates agree. -/
  rate_supportDep : ∀ (r : N.R) {x y : Concentration S},
    (∀ s : S, (N.reaction r).source s ≠ 0 → x s = y s) → rate r x = rate r y
  /-- Weak monotonicity: each rate is nondecreasing in the species concentrations on the
  nonnegative orthant. -/
  rate_mono : ∀ r : N.R, MonotoneOn (rate r) {x : Concentration S | x.Nonnegative}

namespace Kinetics

/-- The vector field induced by a kinetics: for each species, the net rate of change is
the sum over reactions of the rate times the species' entry in the reaction vector. This
is the right-hand side of the induced ODE `ẋ = f(x)`. -/
def vectorField (K : Kinetics N) (x : Concentration S) : S → ℝ :=
  fun s => ∑ r : N.R, K.rate r x * N.reactionVector r s

@[simp] theorem vectorField_apply (K : Kinetics N) (x : Concentration S) (s : S) :
    K.vectorField x s = ∑ r : N.R, K.rate r x * N.reactionVector r s :=
  rfl

/-- **Boundary non-attraction.** At a nonnegative concentration with `x_s = 0`, the
`s`-component of the induced field is nonnegative: every reaction that would decrease
`x_s` consumes `s`, so its rate vanishes there. The orthant face `{x_s = 0}` is
non-attracting for any admissible kinetics. -/
theorem vectorField_nonneg_of_zero (K : Kinetics N) {x : Concentration S}
    (hx : x.Nonnegative) {s : S} (hs : x s = 0) : 0 ≤ K.vectorField x s := by
  rw [vectorField_apply]
  refine Finset.sum_nonneg fun r _ => ?_
  by_cases hle : (N.reaction r).source s ≤ (N.reaction r).target s
  · -- the reaction does not consume `s`, so its reaction-vector entry is `≥ 0`
    refine mul_nonneg (K.rate_nonneg r hx) ?_
    rw [reactionVector_apply]
    have : ((N.reaction r).source s : ℝ) ≤ ((N.reaction r).target s : ℝ) := by exact_mod_cast hle
    linarith
  · -- the reaction consumes `s`, so its rate carries the vanishing factor at `s`
    have hsrc : (N.reaction r).source s ≠ 0 := by omega
    rw [K.rate_vanishing r hsrc hs, zero_mul]

/-- **Conservation.** The induced field always lies in the stoichiometric subspace: it is
a linear combination of reaction vectors. Hence every solution stays in the compatibility
class of its initial condition. -/
theorem vectorField_mem_stoichSubspace (K : Kinetics N) (x : Concentration S) :
    K.vectorField x ∈ N.stoichSubspace := by
  have hsum : K.vectorField x = ∑ r : N.R, (K.rate r x) • (N.reactionVector r) := by
    funext s
    rw [vectorField_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

end Kinetics

/-- A concentration is a **steady state** of a kinetics when the induced field vanishes
componentwise. -/
def IsKineticSteadyState (K : Kinetics N) (x : Concentration S) : Prop :=
  IsSteadyState K.vectorField x

theorem isKineticSteadyState_iff (K : Kinetics N) (x : Concentration S) :
    N.IsKineticSteadyState K x ↔
      ∀ s : S, (∑ r : N.R, K.rate r x * N.reactionVector r s) = 0 :=
  Iff.rfl

/-! ## Mass action as a kinetics

Mass action is the instance whose rate is `massActionRate`. Its admissibility is the
content of the existing mass-action lemmas; the induced field is `massActionVectorField`
definitionally, so the stable API is untouched. -/

/-- **Mass action as a `Kinetics`.** The rate is `massActionRate κ`; the four
admissibility hypotheses hold. -/
def massActionKinetics (N : Network S) (κ : RateConstants N) : Kinetics N where
  rate := N.massActionRate κ
  rate_nonneg := by intro r x hx; exact N.massActionRate_nonneg κ r hx
  rate_vanishing := by
    intro r x s hsrc hs
    show κ.k r * (N.reaction r).source.massActionMonomial x = 0
    have hmon : (N.reaction r).source.massActionMonomial x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, zero_pow hsrc])
    rw [hmon, mul_zero]
  rate_supportDep := by
    intro r x y hxy
    show κ.k r * (N.reaction r).source.massActionMonomial x
        = κ.k r * (N.reaction r).source.massActionMonomial y
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    by_cases hs : (N.reaction r).source s = 0
    · rw [hs, pow_zero, pow_zero]
    · rw [hxy s hs]
  rate_mono := by
    intro r x hx y _ hxy
    show κ.k r * (N.reaction r).source.massActionMonomial x
        ≤ κ.k r * (N.reaction r).source.massActionMonomial y
    refine mul_le_mul_of_nonneg_left ?_ (κ.positive r).le
    refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg (hx s) _) (fun s _ => ?_)
    exact pow_le_pow_left₀ (hx s) (hxy s) _

@[simp] theorem massActionKinetics_rate (N : Network S) (κ : RateConstants N) :
    (N.massActionKinetics κ).rate = N.massActionRate κ := rfl

/-- The field induced by `massActionKinetics` is the mass-action vector field — the stable
definition is a definitional alias. -/
theorem massActionKinetics_vectorField (N : Network S) (κ : RateConstants N) :
    (N.massActionKinetics κ).vectorField = N.massActionVectorField κ := rfl

/-- Mass-action steady states are exactly the steady states of `massActionKinetics`. -/
theorem isMassActionSteadyState_iff_kinetic (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔ N.IsKineticSteadyState (N.massActionKinetics κ) x :=
  Iff.rfl

end Network

end CRNT
