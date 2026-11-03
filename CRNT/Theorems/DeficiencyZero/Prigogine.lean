import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.Stability
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Equilibria.QuasiThermostatic
import CRNT.Thermo.FreeEnergyMinimization
import CRNT.Examples.ReversiblePair

/-!
# The Prigogine principle: the complex-balanced equilibrium is a local minimum of the free
# energy

**Prigogine's minimum-entropy principle** says that a chemical system at equilibrium sits at a
*minimum* of its free energy: close to a complex-balanced equilibrium the pseudo-Helmholtz
free energy

```text
V(x) = Σ_s x_s (log(x_s / x*_s) − 1) + x*_s
```

is *larger* than its value at the equilibrium.  This is the thermodynamic reading of the
deficiency-zero theorem.

Literature: I. Prigogine, *Introduction to the Study of Chemical Reaction Dynamics* (1973);
F. Horn and R. Jackson, *Generalized mass action laws*, Bull. Math. Biol. **34** (1972),
473–496 (the pseudo-Helmholtz function and its class-wise minimization); G. Craciun,
*Chemical Reaction Network Theory*, Chapter 8 (the minimum-entropy principle).

## What the repository already contains

* the pseudo-Helmholtz function itself, `CRNT.relEntropy`
  `= ∑_s (x_s log(x_s / x*_s) − x_s + x*_s)`, together with Gibbs' inequality
  (`CRNT.relEntropyTerm_nonneg`, `CRNT.relEntropyTerm_pos`) and the consequences
  `CRNT.relEntropy_nonneg`, `CRNT.relEntropy_eq_zero_iff`, `CRNT.relEntropy_pos_of_ne`
  (`CRNT/Theorems/DeficiencyZero/Lyapunov.lean`);
* the **global** statement `CRNT.Network.relEntropy_ge_at_complexBalanced` and
  `CRNT.Network.exists_unique_freeEnergy_minimizer`
  (`CRNT/Thermo/FreeEnergyMinimization.lean`): on each stoichiometric compatibility class the
  free energy is *uniquely* minimized at the complex-balanced equilibrium of that class;
* the **dissipation identity** `CRNT.Network.dissipation_nonpos` and its rigidity consequence
  `CRNT.Network.complexBalanced_of_dissipation_eq_zero`
  (`CRNT/Theorems/DeficiencyZero/Dissipation.lean`), together with the Lyapunov descent
  `CRNT.Network.relEntropy_antitone_along_solution`
  (`CRNT/Theorems/DeficiencyZero/Stability.lean`);
* the **asymptotic-stability theorem** for the complex-balanced equilibrium
  (`CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean`);
* the quasi-thermostatic property `CRNT.Network.positiveSteadyState_iff_logRatio_mem_orthStoich`
  and `CRNT.Network.positiveSteadyState_iff_complexBalanced`
  (`CRNT/Equilibria/QuasiThermostatic.lean`): a positive state is a mass-action steady state
  exactly when `log x − log x*` is orthogonal to the stoichiometric subspace.

## What this module adds: the *local* statement

The global inequality and the dissipation identity were formalized; the *local* form of the
Prigogine principle was not.  This module adds it:

* `CRNT.Network.relEntropy_isLocalMin_of_pos` — the free energy is a local minimum at *every*
  positive reference (the purely thermodynamic statement);
* `CRNT.Network.relEntropy_isLocalMin_of_complexBalanced` — the free energy has a **local
  minimum** at a positive complex-balanced equilibrium;
* `CRNT.Network.relEntropy_isStrictLocalMin_of_complexBalanced` — the minimum is **strict**:
  on a neighbourhood of `x*` the free energy is strictly larger at every other positive
  point;
* `CRNT.Network.relEntropy_isLocalMinOn_of_complexBalanced` — the same statement relative to
  the stoichiometric compatibility class of `x*`, obtained from the global theorem;
* `CRNT.Network.relEntropyGradient_eq_zero_of_isLocalMin` and
  `CRNT.Network.relEntropy_eq_of_isLocalMin` — **Fermat's theorem** for the free energy: at a
  positive local minimum the gradient of the free energy vanishes, so the local minimum *is*
  the reference point;
* `CRNT.Network.relEntropyGradient_orthogonal_of_isLocalMinOn` — Fermat's theorem along the
  compatibility class: at a local minimum of the free energy *on its class* the gradient is
  orthogonal to the stoichiometric subspace;
* `CRNT.Network.steadyState_of_relEntropy_gradient_zero` and
  `CRNT.Network.complexBalanced_of_relEntropy_gradient_zero` — **the critical points of the
  free energy are the mass-action steady states**, and they are complex balanced;
* `CRNT.Network.complexBalanced_of_relEntropy_isLocalMinOn` — the converse of the Prigogine
  principle: a positive local minimum of the free energy on a compatibility class is a
  complex-balanced equilibrium;
* `CRNT.Examples.ReversiblePair.relEntropy_equilibrium_isLocalMin` (and the strict version,
  the uniqueness statement and a concrete value) — the worked instance `A ⇌ B`.

## Hypotheses, statement by statement

* `relEntropy_isLocalMin_of_complexBalanced`, `relEntropy_isStrictLocalMin_of_complexBalanced`:
  the reference `x*` must be **positive**; the complex-balance hypothesis is what makes `x*`
  *the equilibrium* of the dynamics, but the local-minimum property itself is the purely
  thermodynamic inequality (Gibbs) and holds at every positive reference — the hypothesis is
  recorded because the statement is the classical Prigogine principle.  No weak reversibility
  is needed.
* `relEntropy_isLocalMinOn_of_complexBalanced`: needs a **weakly reversible** network, a
  positive complex-balanced `x*`, and the comparison is restricted to the compatibility class
  of `x*` (this is where the global theorem of `CRNT/Thermo/FreeEnergyMinimization.lean`
  enters).
* `relEntropyGradient_eq_zero_of_isLocalMin`, `relEntropy_eq_of_isLocalMin`: `x*` and `x`
  positive; the local minimum is taken in the whole concentration space.  Since the positive
  orthant is open (`isOpen_positiveOrthant`), a local minimum *inside* the orthant is a local
  minimum in the whole space, so this is the strongest (most restrictive) form of the
  hypothesis.
* `relEntropyGradient_orthogonal_of_isLocalMinOn`, `complexBalanced_of_relEntropy_isLocalMinOn`:
  `x*` positive and complex balanced, `x` positive, and `x` a local minimum of the free
  energy relative to its compatibility class.  The complex-balance hypothesis of `x*` already
  forces weak reversibility of the network
  (`CRNT.Network.weaklyReversible_of_positive_complexBalanced`), so no separate
  weak-reversibility hypothesis is needed; conversely, the conclusion "a local minimum is
  complex balanced" does *not* hold for an arbitrary reference: if the reference `x*` is not
  complex balanced then `x*` is itself a local minimum of the free energy
  (`relEntropy_isLocalMin_of_pos`) although it need not be a complex-balanced equilibrium.
* `steadyState_of_relEntropy_gradient_zero`, `complexBalanced_of_relEntropy_gradient_zero`:
  `x*` positive and complex balanced, `x` positive, and the gradient `log x − log x*`
  orthogonal to the stoichiometric subspace (i.e. `x` is a critical point of the free energy
  restricted to its class).

-/

namespace CRNT

namespace Network

open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The **positive orthant** in the concentration space: the (open) domain on which the
pseudo-Helmholtz free energy is classically defined. -/
def positiveOrthant (S : Type) : Set (Concentration S) := {x | x.Positive}

/-- The positive orthant is open. -/
theorem isOpen_positiveOrthant (S : Type) [Fintype S] :
    IsOpen (positiveOrthant S) := by
  have hset : positiveOrthant S = ⋂ s : S, {x : Concentration S | 0 < x s} := by
    ext x
    constructor
    · intro h
      rw [Set.mem_iInter]
      intro s
      exact h s
    · intro h
      rw [Set.mem_iInter] at h
      exact h
  rw [hset]
  exact isOpen_iInter_of_finite fun s => isOpen_Ioi.preimage (continuous_apply s)

/-- The **gradient** of the pseudo-Helmholtz free energy `relEntropy xstar ·` at `x`:
`log x_s − log x*_s`.  This is the vector that appears in the dissipation identity
`CRNT.Network.dissipation_nonpos` and in the chain rule `CRNT.Network.relEntropy_hasDerivAt`. -/
noncomputable def relEntropyGradient {ι : Type*} (xstar x : ι → ℝ) : ι → ℝ :=
  fun s => Real.log (x s) - Real.log (xstar s)

/-- The free energy vanishes at its reference. -/
theorem relEntropy_self_eq_zero {ι : Type*} [Fintype ι] {xstar : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) : relEntropy xstar xstar = 0 := by
  unfold relEntropy
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [div_self (hxs i).ne', Real.log_one, mul_zero]
  ring

omit [DecidableEq S] in
/-- **The free energy is a local minimum at its reference.**  This is the purely
thermodynamic content of the Prigogine principle: Gibbs' inequality makes `relEntropy xstar ·`
nonnegative, with equality only at `xstar`.  No complex-balance hypothesis is needed. -/
theorem relEntropy_isLocalMin_of_pos {xstar : Concentration S} (hxs : xstar.Positive) :
    IsLocalMin (fun x : Concentration S => relEntropy xstar x) xstar := by
  have hopen : IsOpen (positiveOrthant S) := isOpen_positiveOrthant S
  have hnhds : (positiveOrthant S : Set (Concentration S)) ∈ 𝓝 xstar := hopen.mem_nhds hxs
  refine (isMinOn_iff.mpr ?_).isLocalMin hnhds
  intro x hx
  have hzero : relEntropy xstar xstar = 0 := relEntropy_self_eq_zero hxs
  have hnn : 0 ≤ relEntropy xstar x := relEntropy_nonneg (fun s => (hx s).le) hxs
  linarith

/-- **The Prigogine principle.**  If `x*` is a positive complex-balanced equilibrium of the
mass-action system, then the pseudo-Helmholtz free energy
`V(x) = ∑_s x_s (log(x_s / x*_s) − 1) + x*_s` is a **local minimum** at `x*`: there is a
neighbourhood of `x*` on which `V(x) ≥ V(x*)`.

The complex-balance hypothesis identifies `x*` as *the equilibrium* of the dynamics; the
local-minimum property itself is Gibbs' inequality (`relEntropy_isLocalMin_of_pos`). -/
theorem relEntropy_isLocalMin_of_complexBalanced (N : Network S) (κ : RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (_hcb : N.IsComplexBalanced κ xstar) :
    IsLocalMin (fun x : Concentration S => relEntropy xstar x) xstar :=
  relEntropy_isLocalMin_of_pos hxs

/-- **The strict Prigogine principle.**  The local minimum of the free energy at a positive
complex-balanced equilibrium is strict: on a neighbourhood of `x*` the free energy is
*strictly* larger at every other positive point. -/
theorem relEntropy_isStrictLocalMin_of_complexBalanced (N : Network S) (κ : RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (_hcb : N.IsComplexBalanced κ xstar) :
    ∃ U ∈ 𝓝 xstar, ∀ x ∈ U, x ≠ xstar → relEntropy xstar xstar < relEntropy xstar x := by
  have hopen : IsOpen (positiveOrthant S) := isOpen_positiveOrthant S
  refine ⟨(positiveOrthant S : Set (Concentration S)), hopen.mem_nhds hxs, ?_⟩
  intro x hx hne
  have hzero : relEntropy xstar xstar = 0 := relEntropy_self_eq_zero hxs
  have hpos : 0 < relEntropy xstar x :=
    relEntropy_pos_of_ne (fun s => (hx s).le) hxs hne
  linarith

/-- **The local form of the class-wise minimization.**  If the network is weakly reversible and
`x*` is a positive complex-balanced equilibrium, then the free energy has a local minimum at
`x*` relative to the stoichiometric compatibility class of `x*`.  This is the local
counterpart of the global theorem `CRNT.Network.relEntropy_ge_at_complexBalanced`. -/
theorem relEntropy_isLocalMinOn_of_complexBalanced (N : Network S) (hwr : N.WeaklyReversible)
    (κ : RateConstants N) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    ∃ U ∈ 𝓝 xstar, ∀ y ∈ U, y - xstar ∈ N.stoichSubspace →
      relEntropy xstar xstar ≤ relEntropy xstar y := by
  refine ⟨(positiveOrthant S : Set (Concentration S)),
    (isOpen_positiveOrthant S).mem_nhds hxs, ?_⟩
  intro y hy hclass
  have h := N.relEntropy_ge_at_complexBalanced hwr κ hxs hxs hcb hcb (fun s => (hy s).le) hclass
  exact h.1

omit [DecidableEq S] in
/-- **Fermat's theorem for the pseudo-Helmholtz free energy.**  At a local minimum of the
free energy the gradient vanishes.  (The proof differentiates the free energy along the
lines `x + t • v` and applies Fermat's theorem to the resulting one-variable function.) -/
theorem relEntropyGradient_eq_zero_of_isLocalMin {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Positive)
    (hmin : IsLocalMin (fun y : Concentration S => relEntropy xstar y) x) :
    relEntropyGradient xstar x = 0 := by
  have hdir : ∀ v : Concentration S,
      ∑ u, (Real.log (x u) - Real.log (xstar u)) * v u = 0 := by
    intro v
    set φ : ℝ → Concentration S := fun t => x + t • v with hφ
    have hφ0 : φ 0 = x := by simp [hφ]
    have hmin' : ∀ᶠ y in 𝓝 x, relEntropy xstar x ≤ relEntropy xstar y := hmin
    obtain ⟨U, hU, hUy⟩ := Filter.Eventually.exists_mem hmin'
    have hU' : U ∈ 𝓝 (φ 0) := by rw [hφ0]; exact hU
    have hcont : ContinuousAt φ 0 := by
      rw [continuousAt_pi]
      intro u
      simp only [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact continuousAt_const.add (continuousAt_id.mul_const (v u))
    have hpre : φ ⁻¹' U ∈ 𝓝 0 := hcont.preimage_mem_nhds hU'
    have hloc : ∀ᶠ t in 𝓝 0, relEntropy xstar (φ 0) ≤ relEntropy xstar (φ t) := by
      filter_upwards [hpre] with t ht
      rw [hφ0]
      exact hUy (φ t) ht
    have hderiv : HasDerivAt (fun t : ℝ => relEntropy xstar (φ t))
        (∑ u, (Real.log (φ 0 u) - Real.log (xstar u)) * v u) 0 := by
      have hpos0 : Concentration.Positive (φ 0) := by rw [hφ0]; exact hx
      refine relEntropy_hasDerivAt hxs hpos0 ?_
      intro u
      have h1 : HasDerivAt (fun τ : ℝ => τ * v u) (1 * v u) 0 :=
        (hasDerivAt_id 0).mul_const (v u)
      have h2 : HasDerivAt (fun τ : ℝ => x u + τ * v u) (1 * v u) 0 :=
        h1.const_add (x u)
      have h3 : HasDerivAt (fun τ : ℝ => φ τ u) (v u) 0 := by
        rw [show (fun τ : ℝ => φ τ u) = fun τ => x u + τ * v u by
          funext τ; simp [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
        simpa using h2
      exact h3
    have hz : (∑ u, (Real.log (φ 0 u) - Real.log (xstar u)) * v u) = 0 :=
      (show IsLocalMin (fun t : ℝ => relEntropy xstar (φ t)) 0 from hloc).hasDerivAt_eq_zero hderiv
    rw [hφ0] at hz
    exact hz
  have hsq : ∑ u, (Real.log (x u) - Real.log (xstar u)) *
      (Real.log (x u) - Real.log (xstar u)) = 0 :=
    hdir (fun u => Real.log (x u) - Real.log (xstar u))
  have hnn : ∀ u ∈ (Finset.univ : Finset S),
      0 ≤ (Real.log (x u) - Real.log (xstar u)) * (Real.log (x u) - Real.log (xstar u)) :=
    fun u _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq
  funext u
  have h1 : (Real.log (x u) - Real.log (xstar u)) * (Real.log (x u) - Real.log (xstar u)) = 0 :=
    hz u (Finset.mem_univ u)
  have h2 : Real.log (x u) - Real.log (xstar u) = 0 := mul_self_eq_zero.mp h1
  simpa [relEntropyGradient] using h2

omit [DecidableEq S] in
/-- **The unique local minimum of the free energy.**  A positive local minimum of the
pseudo-Helmholtz free energy is its reference point. -/
theorem relEntropy_eq_of_isLocalMin {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Positive)
    (hmin : IsLocalMin (fun y : Concentration S => relEntropy xstar y) x) : x = xstar := by
  have hgrad : relEntropyGradient xstar x = 0 :=
    relEntropyGradient_eq_zero_of_isLocalMin hxs hx hmin
  funext u
  have h1 : Real.log (x u) - Real.log (xstar u) = 0 := by
    have h4 := congrFun hgrad u
    simpa [relEntropyGradient] using h4
  have h2 : Real.log (x u) = Real.log (xstar u) := by linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hx u)) (Set.mem_Ioi.mpr (hxs u)) h2

/-- **Fermat's theorem on a compatibility class.**  If the free energy has a local minimum at
`x` relative to the stoichiometric compatibility class of `x`, then the gradient of the free
energy is orthogonal to the stoichiometric subspace. -/
theorem relEntropyGradient_orthogonal_of_isLocalMinOn (N : Network S)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hmin : ∃ U ∈ 𝓝 x, ∀ y ∈ U, y - x ∈ N.stoichSubspace →
      relEntropy xstar x ≤ relEntropy xstar y) :
    relEntropyGradient xstar x ∈ orthSum N.stoichSubspace := by
  refine mem_orthSum.mpr ?_
  intro v hv
  set φ : ℝ → Concentration S := fun t => x + t • v with hφ
  have hφ0 : φ 0 = x := by simp [hφ]
  have hφmem : ∀ t, φ t - x ∈ N.stoichSubspace := by
    intro t
    have heq : φ t - x = t • v := by
      funext u
      simp only [hφ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_sub_cancel_left]
    rw [heq]
    exact N.stoichSubspace.smul_mem t hv
  obtain ⟨U, hU, hUy⟩ := hmin
  have hU' : U ∈ 𝓝 (φ 0) := by rw [hφ0]; exact hU
  have hcont : ContinuousAt φ 0 := by
    rw [continuousAt_pi]
    intro u
    simp only [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact continuousAt_const.add (continuousAt_id.mul_const (v u))
  have hpre : φ ⁻¹' U ∈ 𝓝 0 := hcont.preimage_mem_nhds hU'
  have hloc : ∀ᶠ t in 𝓝 0, relEntropy xstar (φ 0) ≤ relEntropy xstar (φ t) := by
    filter_upwards [hpre] with t ht
    rw [hφ0]
    exact hUy (φ t) ht (hφmem t)
  have hderiv : HasDerivAt (fun t : ℝ => relEntropy xstar (φ t))
      (∑ u, (Real.log (φ 0 u) - Real.log (xstar u)) * v u) 0 := by
    have hpos0 : Concentration.Positive (φ 0) := by rw [hφ0]; exact hx
    refine relEntropy_hasDerivAt hxs hpos0 ?_
    intro u
    have h1 : HasDerivAt (fun τ : ℝ => τ * v u) (1 * v u) 0 :=
      (hasDerivAt_id 0).mul_const (v u)
    have h2 : HasDerivAt (fun τ : ℝ => x u + τ * v u) (1 * v u) 0 :=
      h1.const_add (x u)
    have h3 : HasDerivAt (fun τ : ℝ => φ τ u) (v u) 0 := by
      rw [show (fun τ : ℝ => φ τ u) = fun τ => x u + τ * v u by
        funext τ; simp [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
      simpa using h2
    exact h3
  have hz : (∑ u, (Real.log (φ 0 u) - Real.log (xstar u)) * v u) = 0 :=
    (show IsLocalMin (fun t : ℝ => relEntropy xstar (φ t)) 0 from hloc).hasDerivAt_eq_zero hderiv
  rw [hφ0] at hz
  exact hz

/-- **The critical points of the free energy are the mass-action steady states.**  A positive
concentration at which the gradient of the pseudo-Helmholtz free energy is orthogonal to the
stoichiometric subspace — i.e. at which the free energy restricted to its compatibility
class has a critical point — is a mass-action steady state. -/
theorem steadyState_of_relEntropy_gradient_zero (N : Network S) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx : x.Positive)
    (hgrad : relEntropyGradient xstar x ∈ orthSum N.stoichSubspace) :
    N.IsMassActionSteadyState κ x :=
  (N.positiveSteadyState_iff_logRatio_mem_orthStoich κ hxs hcb hx).mpr hgrad

/-- **The critical points of the free energy are complex balanced.** -/
theorem complexBalanced_of_relEntropy_gradient_zero (N : Network S) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx : x.Positive)
    (hgrad : relEntropyGradient xstar x ∈ orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ x :=
  N.isComplexBalanced_of_positive_steadyState κ hx hxs hcb
    (steadyState_of_relEntropy_gradient_zero N κ hxs hcb hx hgrad)

/-- **The converse of the Prigogine principle.**  A positive local minimum of the free energy
on a compatibility class is a complex-balanced equilibrium. -/
theorem complexBalanced_of_relEntropy_isLocalMinOn (N : Network S) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx : x.Positive)
    (hmin : ∃ U ∈ 𝓝 x, ∀ y ∈ U, y - x ∈ N.stoichSubspace →
      relEntropy xstar x ≤ relEntropy xstar y) :
    N.IsComplexBalanced κ x :=
  complexBalanced_of_relEntropy_gradient_zero N κ hxs hcb hx
    (relEntropyGradient_orthogonal_of_isLocalMinOn N hxs hx hmin)

end Network

end CRNT

/-! ## A concrete instance: the reversible pair `A ⇌ B`

For the reversible pair `A ⇌ B` with forward rate constant `k₀` and backward rate constant
`k₁` the detailed-balanced equilibrium is `(k₁, k₀)`: the forward flux `k₀ k₁` and the
backward flux `k₁ k₀` agree, so the equilibrium is complex balanced
(`CRNT.Examples.ReversiblePair.equilibrium_isComplexBalanced`).  The free energy relative to
that equilibrium has its unique minimum there, and the minimum is strict. -/

namespace CRNT.Examples.ReversiblePair

open CRNT
open Species
open scoped BigOperators Topology

/-- **The unique minimizer of the free energy.**  For the reversible pair `A ⇌ B` the
detailed-balanced equilibrium `(k₁, k₀)` is the unique minimizer of the pseudo-Helmholtz free
energy: the free energy vanishes there and only there. -/
theorem relEntropy_equilibrium_eq_zero_iff {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    {x : Concentration Species} (hx : x.Nonnegative) :
    relEntropy (equilibrium k₀ k₁) x = 0 ↔ x = equilibrium k₀ k₁ :=
  relEntropy_eq_zero_iff hx (equilibrium_positive h₀ h₁)

/-- **The Prigogine principle for the reversible pair.**  The free energy has a local minimum
at the detailed-balanced equilibrium. -/
theorem relEntropy_equilibrium_isLocalMin {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    IsLocalMin (fun x : Concentration Species => relEntropy (equilibrium k₀ k₁) x)
      (equilibrium k₀ k₁) :=
  Network.relEntropy_isLocalMin_of_complexBalanced N (rates h₀ h₁)
    (equilibrium_positive h₀ h₁) (equilibrium_isComplexBalanced h₀ h₁)

/-- **The local minimum at the detailed-balanced equilibrium is strict.** -/
theorem relEntropy_equilibrium_isStrictLocalMin {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    ∃ U ∈ 𝓝 (equilibrium k₀ k₁), ∀ x ∈ U, x ≠ equilibrium k₀ k₁ →
      relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁)
        < relEntropy (equilibrium k₀ k₁) x :=
  Network.relEntropy_isStrictLocalMin_of_complexBalanced N (rates h₀ h₁)
    (equilibrium_positive h₀ h₁) (equilibrium_isComplexBalanced h₀ h₁)

/-- **A concrete value.**  For `A ⇌ B` with forward rate `1` and backward rate `2` the
complex-balanced equilibrium is `(2, 1)`; at the state `(4, 1)` the free energy relative to
the equilibrium is `log 16 − 2`, which is positive: the free energy is strictly larger away
from the equilibrium. -/
theorem relEntropy_at_state :
    relEntropy (equilibrium 1 2) (fun s => match s with | A => 4 | B => 1) = Real.log 16 - 2 := by
  unfold relEntropy
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [equilibrium]
  norm_num [Real.log_div_self]
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  linarith

end CRNT.Examples.ReversiblePair

/-! ## Axiom audit (informational) -/

#print axioms CRNT.Network.relEntropy_isLocalMin_of_complexBalanced
#print axioms CRNT.Network.relEntropy_isStrictLocalMin_of_complexBalanced
#print axioms CRNT.Network.relEntropy_isLocalMinOn_of_complexBalanced
#print axioms CRNT.Network.relEntropyGradient_eq_zero_of_isLocalMin
#print axioms CRNT.Network.relEntropy_eq_of_isLocalMin
#print axioms CRNT.Network.relEntropyGradient_orthogonal_of_isLocalMinOn
#print axioms CRNT.Network.steadyState_of_relEntropy_gradient_zero
#print axioms CRNT.Network.complexBalanced_of_relEntropy_gradient_zero
#print axioms CRNT.Network.complexBalanced_of_relEntropy_isLocalMinOn
#print axioms CRNT.Examples.ReversiblePair.relEntropy_equilibrium_isLocalMin
#print axioms CRNT.Examples.ReversiblePair.relEntropy_equilibrium_isStrictLocalMin
#print axioms CRNT.Examples.ReversiblePair.relEntropy_equilibrium_eq_zero_iff
#print axioms CRNT.Examples.ReversiblePair.relEntropy_at_state
