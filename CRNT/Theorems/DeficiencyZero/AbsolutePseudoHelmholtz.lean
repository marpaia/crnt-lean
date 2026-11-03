import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Dynamics.MassActionAlgebra
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Examples.ReversiblePair

/-!
# The absolute pseudo-Helmholtz function and its class-wise minimization

## The two pseudo-Helmholtz functions

Horn and Jackson (1972, *General mass action laws*, Bull. Math. Biol. **34**, 473–496)
attach to a mass-action network the *pseudo-Helmholtz* function.  In its **relative** form —
the one used throughout this repository — it is the entropy of `x` with respect to a
reference `x*`:

```text
G_{x*}(x) = relEntropy xstar x = ∑_s ( x_s log(x_s / x*_s) − x_s + x*_s ).
```

In its **absolute** form the reference disappears and the *complex* part of the network
enters:

```text
V(x) = absolutePseudoHelmholtz N κ x
     = ∑_s ( x_s log x_s − x_s )  +  ∑_c ( A_κ x )_c ,
```

where `A_κ` is the kinetic map of the network (the `κ`-weighted Laplacian of the reaction
graph, `CRNT.Network.kineticMap`) acting on the monomial vector `Ψ(x)`
(`CRNT.Network.complexMonomialVector`), and the second sum runs over the complexes
(`CRNT.Network.ComplexIdx`).  This module supplies the absolute form
(`CRNT.Network.absolutePseudoHelmholtz`) and the class-wise minimization statement.

## What the repository already contains

* the relative pseudo-Helmholtz function `CRNT.relEntropy` together with Gibbs' inequality
  (`CRNT.relEntropyTerm_nonneg`, `CRNT.relEntropyTerm_pos`) and its consequences
  `CRNT.relEntropy_nonneg`, `CRNT.relEntropy_eq_zero_iff`, `CRNT.relEntropy_pos_of_ne`
  (`CRNT/Theorems/DeficiencyZero/Lyapunov.lean`);
* the **global** class-wise minimization `CRNT.Network.relEntropy_ge_at_complexBalanced` and
  `CRNT.Network.exists_unique_freeEnergy_minimizer`
  (`CRNT/Thermo/FreeEnergyMinimization.lean`): on each stoichiometric compatibility class
  the *relative* free energy is uniquely minimized at the complex-balanced equilibrium of that
  class;
* the **local** form of the Prigogine principle — `relEntropy_isLocalMin_of_complexBalanced`,
  `relEntropy_isStrictLocalMin_of_complexBalanced`, Fermat's theorem
  `relEntropyGradient_eq_zero_of_isLocalMin` and its class-wise version
  `relEntropyGradient_orthogonal_of_isLocalMinOn`, and the converse
  `complexBalanced_of_relEntropy_isLocalMinOn` (`CRNT/Theorems/DeficiencyZero/Prigogine.lean`);
* the toric parametrization of the complex-balanced equilibria: the monomial vector scales
  torically about a reference, `complexBalanced_of_logRatio_orthogonal`, and the converse
  inclusion `logRatio_orthogonal_of_complexBalanced` (`CRNT/Theorems/DeficiencyZero/Toric.lean`);
* the algebraic factorization `ẋ = Y A_κ Ψ(x)` and the criterion
  `N.isComplexBalanced_iff_kineticMap` (`CRNT/Dynamics/MassActionAlgebra.lean`).

## What this module adds

* `CRNT.Network.absolutePseudoHelmholtz` — the absolute pseudo-Helmholtz function;
* `CRNT.Network.absolutePseudoHelmholtz_eq_speciesSum` — **the complex part vanishes
  identically**: the kinetic map has zero total (`CRNT.Network.kineticMap_sum_eq_zero`), so
  `V(x) = ∑_s (x_s log x_s − x_s)`;
* `CRNT.Network.absolutePseudoHelmholtz_sub_relEntropy` — the *exact* difference between the
  absolute and the relative function,
  `V(x) − V(x*) = G_{x*}(x) + ∑_s (x_s − x*_s) log x*_s`;
* `CRNT.Network.absolutePseudoHelmholtz_sub_relEntropy_of_orth` — on a compatibility class of
  a *logarithmically balanced* reference `x*` (i.e. `log x* ⊥ S`) the extra term vanishes and
  the two functions differ exactly by the relative entropy;
* `CRNT.Network.IsLogarithmicallyBalanced` — the condition `log x ⊥ S`
  (`⟨log x, target r − source r⟩ = 0` for every reaction, i.e. `x^{target r} = x^{source r}`);
* `CRNT.Network.absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced` — the **class-wise
  minimization**: for a logarithmically balanced positive `x*`, the absolute
  pseudo-Helmholtz function is *uniquely* minimized on the compatibility class of `x*`, at
  `x*` (Gibbs' inequality);
* `CRNT.Network.absolutePseudoHelmholtz_ge_at_complexBalanced` — the same statement with the
  complex-balanced equilibrium recorded as the reference (the weak-reversibility and
  complex-balance hypotheses record the classical setting; the conclusion is the purely
  thermodynamic one);
* `CRNT.Network.absolutePseudoHelmholtz_hasDerivAt` — the directional derivative of `V`;
* `CRNT.Network.absolutePseudoHelmholtz_log_orthogonal_of_isLocalMinOn` — **Fermat's theorem
  for the absolute function on a class**: a class-wise local minimum of `V` is logarithmically
  balanced;
* `CRNT.Network.absolutePseudoHelmholtz_isClassMinimizer_iff` — hence the class-wise local
  minimizers of the absolute pseudo-Helmholtz function are *exactly* the logarithmically
  balanced states.

## The obstruction: the absolute minimizer is not the complex-balanced state

The classical slogan attached to the absolute pseudo-Helmholtz function — that *its
minimizers in a compatibility class are the complex-balanced states of that class* — is
**false for the function `V` above**, and this module records the counterexample rather than
the slogan.

The reason is visible in `absolutePseudoHelmholtz_sub_relEntropy`: the absolute function and
the relative function differ, on a compatibility class, by the term
`∑_s (x_s − x*_s) log x*_s`, which is constant on the class **iff** `log x* ⊥ S`.  Complex
balance does *not* imply logarithmic balance, so the two functions have different class-wise
minimizers in general.  Concretely, for the reversible pair `A ⇌ B` with rate constants
`k₀ ≠ k₁`:

* the complex-balanced equilibrium is `x* = (k₁, k₀)`;
* the class-wise minimizer of `V` is the *logarithmically balanced* point
  `((k₀+k₁)/2, (k₀+k₁)/2)` (`CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_minimized_at_balanced`);
* `CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_equilibrium_not_minimizer` proves
  `V( ((k₀+k₁)/2, (k₀+k₁)/2) ) < V( (k₁, k₀) )`, i.e. the complex-balanced equilibrium is
  *not* the class-wise minimizer of the absolute pseudo-Helmholtz function;
* `CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_sub_relEntropy_not_constant` shows
  that the difference `V(x) − G_{x*}(x)` is *not* constant on that class.

The "complex-coordinate route" (rewriting `V` in the coordinates `y` with `x = Ψ(y)` and
minimizing the resulting linear problem) does not repair this: the complex part `∑_c (A_κ x)_c`
is identically zero, so `V` restricted to a class is the strictly convex species sum
`∑_s (x_s log x_s − x_s)`, whose class-wise critical point is characterized by `log x ⊥ S`
(logarithmic balance, i.e. Wegscheider's condition), *not* by complex balance.

## Hypotheses, statement by statement

* `absolutePseudoHelmholtz_eq_speciesSum` needs no hypotheses: the complex part of `V` is
  zero for every concentration.
* `absolutePseudoHelmholtz_sub_relEntropy` assumes only that the reference `x*` is positive
  (so that `log x*_s` is the logarithmic reference); the comparison point `x` is arbitrary.
* `absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced` assumes that the reference `x*` is
  positive and logarithmically balanced, that the comparison point `x` is nonnegative, and
  that `x` lies in the compatibility class of `x*` (`x − x* ∈ S`).  Gibbs' inequality then
  gives `V(x*) ≤ V(x)`, with equality only at `x = x*`.
* `absolutePseudoHelmholtz_ge_at_complexBalanced` adds the classical hypotheses (weak
  reversibility, complex balance of `x*`); they are *not* needed for the conclusion, which
  is the purely thermodynamic one — exactly as in
  `CRNT.Network.relEntropy_isLocalMin_of_complexBalanced`.
* `absolutePseudoHelmholtz_log_orthogonal_of_isLocalMinOn` assumes that `x*` is positive and
  a local minimum of `V` *relative to its compatibility class*; the conclusion is
  `log x* ⊥ S`, the classical Wegscheider (logarithmic balance) condition.
* the reversible-pair statements assume positive rate constants; `balanced k₀ k₁` is the
  logarithmically balanced point of the class of the equilibrium `(k₁, k₀)`.

## What is *not* claimed here

* it is **not** claimed that the complex-balanced states are the class-wise minimizers of the
  absolute pseudo-Helmholtz function — they are not, except when they happen to be
  logarithmically balanced (e.g. `A ⇌ B` with equal rate constants,
  `CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_equilibrium_isMinimizer`);
* it is **not** claimed that the absolute and the relative pseudo-Helmholtz functions differ
  by a constant on a compatibility class; the extra term
  `∑_s (x_s − x*_s) log x*_s` is present in general and vanishes only under logarithmic
  balance;
* the *toric* (monomial) compatibility classes of Horn–Jackson are not used: all statements
  here are about the stoichiometric compatibility classes `x* + S` of this repository;
* the absolute *entropy* of the literature (which normalizes the complex part differently and
  studies the suprema of `V` over classes) is not addressed.

-/

namespace CRNT

namespace Network

open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The absolute pseudo-Helmholtz function** (Horn–Jackson 1972): the species part
`∑_s (x_s log x_s − x_s)` plus the complex part `∑_c (A_κ x)_c`, where `A_κ` is the kinetic
map of the network acting on the monomial vector `Ψ(x)` and the sum runs over the complexes
of the network. -/
noncomputable def absolutePseudoHelmholtz (N : Network S) (κ : RateConstants N)
    (x : Concentration S) : ℝ :=
  ∑ s, (x s * Real.log (x s) - x s) +
    ∑ c : N.ComplexIdx, N.kineticMap κ (N.complexMonomialVector x) c

/-- **The complex part of the absolute pseudo-Helmholtz function vanishes identically.**
The kinetic map has zero total (`CRNT.Network.kineticMap_sum_eq_zero`), so the absolute
pseudo-Helmholtz function is the species sum `∑_s (x_s log x_s − x_s)`. -/
theorem absolutePseudoHelmholtz_eq_speciesSum (N : Network S) (κ : RateConstants N)
    (x : Concentration S) :
    absolutePseudoHelmholtz N κ x = ∑ s, (x s * Real.log (x s) - x s) := by
  unfold absolutePseudoHelmholtz
  rw [N.kineticMap_sum_eq_zero κ (N.complexMonomialVector x)]
  ring

/-- **The exact difference between the absolute and the relative pseudo-Helmholtz
function.**  For a positive reference `x*`,

```text
V(x) − V(x*) = G_{x*}(x) + ∑_s (x_s − x*_s) log x*_s .
```

The additional term is the obstruction to the two functions having the same class-wise
minimizers: it is constant on the compatibility class of `x*` exactly when `x*` is
logarithmically balanced. -/
theorem absolutePseudoHelmholtz_sub_relEntropy (N : Network S) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) :
    absolutePseudoHelmholtz N κ x - absolutePseudoHelmholtz N κ xstar
      = relEntropy xstar x + ∑ s, (x s - xstar s) * Real.log (xstar s) := by
  rw [absolutePseudoHelmholtz_eq_speciesSum, absolutePseudoHelmholtz_eq_speciesSum]
  have hlog : ∀ s, x s * Real.log (x s / xstar s)
      = x s * Real.log (x s) - x s * Real.log (xstar s) := by
    intro s
    by_cases h0 : x s = 0
    · rw [h0]
      simp
    · rw [Real.log_div (fun h => h0 h) (hxs s).ne']
      ring
  have key : ∀ s,
      (x s * Real.log (x s) - x s) - (xstar s * Real.log (xstar s) - xstar s)
        = (x s * Real.log (x s / xstar s) - x s + xstar s)
          + (x s - xstar s) * Real.log (xstar s) := by
    intro s
    rw [hlog s]
    ring
  unfold relEntropy
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [key s]

/-- **Logarithmic balance.**  A concentration `x` is *logarithmically balanced* when
`log x` is orthogonal to the stoichiometric subspace `S`, i.e. when
`⟨log x, target r − source r⟩ = 0` for every reaction `r` — equivalently, when
`x^{target r} = x^{source r}` for every reaction `r` (Wegscheider's logarithmic condition). -/
def IsLogarithmicallyBalanced (N : Network S) (x : Concentration S) : Prop :=
  (fun s => Real.log (x s)) ∈ orthSum N.stoichSubspace

/-- **On a compatibility class of a logarithmically balanced reference the absolute and the
relative pseudo-Helmholtz functions differ exactly by the relative entropy.** -/
theorem absolutePseudoHelmholtz_sub_relEntropy_of_orth (N : Network S) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (horth : (fun s => Real.log (xstar s)) ∈ orthSum N.stoichSubspace)
    (hclass : x - xstar ∈ N.stoichSubspace) :
    absolutePseudoHelmholtz N κ x - absolutePseudoHelmholtz N κ xstar = relEntropy xstar x := by
  rw [absolutePseudoHelmholtz_sub_relEntropy N κ hxs]
  have hz : ∑ s, (x s - xstar s) * Real.log (xstar s) = 0 := by
    have h := (mem_orthSum.mp horth) (x - xstar) hclass
    have h2 : ∑ s, Real.log (xstar s) * (x s - xstar s) = 0 := by
      simpa only [Pi.sub_apply] using h
    have h3 : ∑ s, (x s - xstar s) * Real.log (xstar s)
        = ∑ s, Real.log (xstar s) * (x s - xstar s) := by
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h3]
    exact h2
  rw [hz, add_zero]

/-- **Class-wise minimization of the absolute pseudo-Helmholtz function.**  If `x*` is a
positive logarithmically balanced concentration, then the absolute pseudo-Helmholtz function
is *uniquely* minimized on the compatibility class of `x*`, at `x*` itself.  This is the
class-wise minimization statement for the absolute form; the reference is required to be
logarithmically balanced (complex balance alone does not suffice). -/
theorem absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced (N : Network S)
    (κ : RateConstants N) {xstar x : Concentration S} (hxs : xstar.Positive)
    (horth : IsLogarithmicallyBalanced N xstar)
    (hx : x.Nonnegative) (hclass : x - xstar ∈ N.stoichSubspace) :
    absolutePseudoHelmholtz N κ xstar ≤ absolutePseudoHelmholtz N κ x ∧
      (absolutePseudoHelmholtz N κ x = absolutePseudoHelmholtz N κ xstar → x = xstar) := by
  have hid := absolutePseudoHelmholtz_sub_relEntropy_of_orth N κ hxs horth hclass
  have hnn : 0 ≤ relEntropy xstar x := relEntropy_nonneg hx hxs
  have hzero : relEntropy xstar x = 0 ↔ x = xstar := relEntropy_eq_zero_iff hx hxs
  refine ⟨by linarith, fun heq => ?_⟩
  have hz : relEntropy xstar x = 0 := by linarith
  exact hzero.mp hz

/-- **Class-wise minimization at a complex-balanced equilibrium.**  The classical setting of
the statement: the network is weakly reversible and `x*` is a positive complex-balanced
equilibrium, so that `x*` is *the* equilibrium of the dynamics.  The class-wise
minimization property itself is the purely thermodynamic one and requires the reference to be
logarithmically balanced; the weak-reversibility and complex-balance hypotheses are recorded
for the classical statement and are not used in the proof (compare
`CRNT.Network.relEntropy_isLocalMin_of_complexBalanced`). -/
theorem absolutePseudoHelmholtz_ge_at_complexBalanced (N : Network S) (_hwr : N.WeaklyReversible)
    (κ : RateConstants N) {xstar x : Concentration S} (hxs : xstar.Positive)
    (_hcb : N.IsComplexBalanced κ xstar)
    (horth : IsLogarithmicallyBalanced N xstar)
    (hx : x.Nonnegative) (hclass : x - xstar ∈ N.stoichSubspace) :
    absolutePseudoHelmholtz N κ xstar ≤ absolutePseudoHelmholtz N κ x ∧
      (absolutePseudoHelmholtz N κ x = absolutePseudoHelmholtz N κ xstar → x = xstar) :=
  absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced N κ hxs horth hx hclass

/-- **The derivative of the absolute pseudo-Helmholtz function** along a differentiable
curve `γ`: it is `∑_s log(γ_s t) · γ'_s`.  (The `− x_s` part of the species sum cancels the
`+1` of the derivative of `x log x`.) -/
theorem absolutePseudoHelmholtz_hasDerivAt (N : Network S) (κ : RateConstants N)
    {γ : ℝ → Concentration S} {γ' : S → ℝ} {t : ℝ} (hpos : (γ t).Positive)
    (hγ : ∀ s, HasDerivAt (fun τ => γ τ s) (γ' s) t) :
    HasDerivAt (fun τ => absolutePseudoHelmholtz N κ (γ τ))
      (∑ s, Real.log (γ t s) * γ' s) t := by
  have hconv : (fun τ : ℝ => absolutePseudoHelmholtz N κ (γ τ))
      = (fun τ : ℝ => ∑ s, ((γ τ) s * Real.log ((γ τ) s) - (γ τ) s)) := by
    funext τ
    rw [absolutePseudoHelmholtz_eq_speciesSum]
  rw [hconv]
  rw [show (fun τ : ℝ => ∑ s, ((γ τ) s * Real.log ((γ τ) s) - (γ τ) s))
      = ∑ s, fun τ : ℝ => (γ τ) s * Real.log ((γ τ) s) - (γ τ) s from by
        funext τ; simp only [Finset.sum_apply]]
  apply HasDerivAt.sum
  intro s _
  have hmul : HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log (γ t s) + 1) (γ t s) :=
    Real.hasDerivAt_mul_log (hpos s).ne'
  have hraw := (hmul.comp t (hγ s)).sub (hγ s)
  have hsub : HasDerivAt (fun τ : ℝ => (γ τ) s * Real.log ((γ τ) s) - (γ τ) s)
      ((Real.log (γ t s) + 1) * γ' s - γ' s) t := by
    refine HasDerivAt.congr_of_eventuallyEq hraw ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  convert hsub using 1 ; ring

/-- **Fermat's theorem for the absolute pseudo-Helmholtz function on a class.**  A local
minimum of the absolute pseudo-Helmholtz function relative to its compatibility class is
*logarithmically balanced*: `log x*` is orthogonal to the stoichiometric subspace.  This is
the precise characterization of the class-wise critical points of the absolute function, and
it shows that they are the logarithmically balanced states rather than the complex-balanced
ones. -/
theorem absolutePseudoHelmholtz_log_orthogonal_of_isLocalMinOn (N : Network S)
    (κ : RateConstants N) {xstar : Concentration S} (hxs : xstar.Positive)
    (hmin : ∃ U ∈ 𝓝 xstar, ∀ y ∈ U, y - xstar ∈ N.stoichSubspace →
      absolutePseudoHelmholtz N κ xstar ≤ absolutePseudoHelmholtz N κ y) :
    (fun s => Real.log (xstar s)) ∈ orthSum N.stoichSubspace := by
  refine mem_orthSum.mpr ?_
  intro v hv
  set φ : ℝ → Concentration S := fun t => xstar + t • v with hφ
  have hφ0 : φ 0 = xstar := by simp [hφ]
  have hφmem : ∀ t, φ t - xstar ∈ N.stoichSubspace := by
    intro t
    have heq : φ t - xstar = t • v := by
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
  have hloc : ∀ᶠ t in 𝓝 0,
      absolutePseudoHelmholtz N κ (φ 0) ≤ absolutePseudoHelmholtz N κ (φ t) := by
    filter_upwards [hpre] with t ht
    rw [hφ0]
    exact hUy (φ t) ht (hφmem t)
  have hγ : ∀ s, HasDerivAt (fun τ => φ τ s) (v s) 0 := by
    intro s
    have h1 : HasDerivAt (fun τ : ℝ => τ * v s) (1 * v s) 0 :=
      (hasDerivAt_id 0).mul_const (v s)
    have h2 : HasDerivAt (fun τ : ℝ => xstar s + τ * v s) (1 * v s) 0 := h1.const_add (xstar s)
    have h3 : HasDerivAt (fun τ : ℝ => (xstar + τ • v) s) (v s) 0 := by
      rw [show (fun τ : ℝ => (xstar + τ • v) s) = fun τ => xstar s + τ * v s by
        funext τ; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
      simpa using h2
    simpa [hφ] using h3
  have hderiv : HasDerivAt (fun t : ℝ => absolutePseudoHelmholtz N κ (φ t))
      (∑ s, Real.log (xstar s) * v s) 0 := by
    have hpos : (φ 0).Positive := by rw [hφ0]; exact hxs
    have hderiv' := absolutePseudoHelmholtz_hasDerivAt N κ hpos hγ
    rw [hφ0] at hderiv'
    exact hderiv'
  have hz : (∑ s, Real.log (xstar s) * v s) = 0 :=
    (show IsLocalMin (fun t : ℝ => absolutePseudoHelmholtz N κ (φ t)) 0 from hloc).hasDerivAt_eq_zero
      hderiv
  exact hz

/-- **The class-wise local minimizers of the absolute pseudo-Helmholtz function are exactly
the logarithmically balanced states.**  This is the class-wise minimization statement for the
absolute form: it is *not* the complex-balanced states, unless they happen to be
logarithmically balanced. -/
theorem absolutePseudoHelmholtz_isClassMinimizer_iff (N : Network S) (κ : RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive) :
    (∃ U ∈ 𝓝 xstar, ∀ y ∈ U, y - xstar ∈ N.stoichSubspace →
        absolutePseudoHelmholtz N κ xstar ≤ absolutePseudoHelmholtz N κ y)
      ↔ IsLogarithmicallyBalanced N xstar := by
  constructor
  · rintro ⟨U, hU, hUy⟩
    exact absolutePseudoHelmholtz_log_orthogonal_of_isLocalMinOn N κ hxs ⟨U, hU, hUy⟩
  · intro horth
    refine ⟨{y : Concentration S | ∀ s, 0 < y s}, ?_, ?_⟩
    · have hset : {y : Concentration S | ∀ s, 0 < y s}
          = ⋂ s : S, {y : Concentration S | 0 < y s} := by
        ext y
        constructor
        · intro h
          rw [Set.mem_iInter]
          exact h
        · intro h
          rw [Set.mem_iInter] at h
          exact h
      rw [hset]
      have hmem : xstar ∈ ⋂ s : S, {y : Concentration S | 0 < y s} := by
        rw [Set.mem_iInter]
        intro s
        exact hxs s
      exact (isOpen_iInter_of_finite fun s => isOpen_Ioi.preimage (continuous_apply s)).mem_nhds hmem
    · intro y hy hclass
      have h1 := (absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced N κ hxs horth
        (fun s => (hy s).le) hclass).1
      exact h1

end Network

end CRNT

/-! ## A worked instance: the reversible pair `A ⇌ B`

For the reversible pair `A ⇌ B` with forward rate `k₀` and backward rate `k₁` the
complex-balanced (detailed-balanced) equilibrium is `x* = (k₁, k₀)`, and its compatibility
class is `{(a, b) : a + b = k₀ + k₁}`.  The *logarithmically balanced* point of that class is
the midpoint `((k₀+k₁)/2, (k₀+k₁)/2)`, and this is the class-wise minimizer of the absolute
pseudo-Helmholtz function.  The two coincide exactly when `k₀ = k₁`. -/

namespace CRNT.Examples.ReversiblePair

open CRNT
open Species
open scoped BigOperators

/-- The **logarithmically balanced point** of the compatibility class of the
detailed-balanced equilibrium `(k₁, k₀)`: the midpoint `((k₀ + k₁)/2, (k₀ + k₁)/2)`. -/
noncomputable def balanced (k₀ k₁ : ℝ) : Concentration Species :=
  fun s => match s with | A => (k₀ + k₁) / 2 | B => (k₀ + k₁) / 2

/-- The backward reaction vector is the negative of the forward one. -/
theorem reactionVector_bwd : N.reactionVector Rxn.bwd = -N.reactionVector Rxn.fwd := by
  funext s
  cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]

/-- The balanced point is positive. -/
theorem balanced_positive {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    (balanced k₀ k₁).Positive := by
  intro s
  cases s <;> simp [balanced] <;> linarith

/-- **The balanced point is logarithmically balanced**: its two coordinates coincide, so
`log` of it is orthogonal to the stoichiometric subspace. -/
theorem balanced_isLogarithmicallyBalanced {k₀ k₁ : ℝ} (_h₀ : 0 < k₀) (_h₁ : 0 < k₁) :
    Network.IsLogarithmicallyBalanced N (balanced k₀ k₁) := by
  show (fun s => Real.log (balanced k₀ k₁ s)) ∈
    orthSum (Submodule.span ℝ N.reactionVectors)
  refine mem_orthSum_span ?_
  rintro g ⟨r, rfl⟩
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  cases r
  · rw [reactionVector_fwd, huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [balanced]
  · rw [reactionVector_bwd, reactionVector_fwd, huniv, Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp [balanced]

/-- The difference between the balanced point and the equilibrium is a multiple of the
forward reaction vector. -/
theorem balanced_sub_equilibrium (k₀ k₁ : ℝ) :
    balanced k₀ k₁ - equilibrium k₀ k₁ = ((k₁ - k₀) / 2) • N.reactionVector Rxn.fwd := by
  funext s
  cases s <;>
    simp [balanced, equilibrium, reactionVector_fwd, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The balanced point lies in the class of the equilibrium. -/
theorem balanced_sub_equilibrium_mem (k₀ k₁ : ℝ) :
    balanced k₀ k₁ - equilibrium k₀ k₁ ∈ N.stoichSubspace := by
  rw [balanced_sub_equilibrium]
  exact N.stoichSubspace.smul_mem _ (N.reactionVector_mem_stoichSubspace Rxn.fwd)

/-- Every point of the class of the equilibrium lies in the class of the balanced point. -/
theorem sub_balanced_mem {k₀ k₁ : ℝ} {x : Concentration Species}
    (h : x - equilibrium k₀ k₁ ∈ N.stoichSubspace) :
    x - balanced k₀ k₁ ∈ N.stoichSubspace := by
  have h2 : balanced k₀ k₁ - equilibrium k₀ k₁ ∈ N.stoichSubspace :=
    balanced_sub_equilibrium_mem _ _
  have heq : x - balanced k₀ k₁
      = (x - equilibrium k₀ k₁) - (balanced k₀ k₁ - equilibrium k₀ k₁) := by abel
  rw [heq]
  exact N.stoichSubspace.sub_mem h h2

/-- **The class-wise minimizer of the absolute pseudo-Helmholtz function for `A ⇌ B`.**  On
the compatibility class of the detailed-balanced equilibrium `(k₁, k₀)` the absolute
pseudo-Helmholtz function is uniquely minimized at the logarithmically balanced point
`((k₀+k₁)/2, (k₀+k₁)/2)`. -/
theorem absolutePseudoHelmholtz_minimized_at_balanced {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    {x : Concentration Species} (hx : x.Nonnegative)
    (hclass : x - equilibrium k₀ k₁ ∈ N.stoichSubspace) :
    Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
        ≤ Network.absolutePseudoHelmholtz N (rates h₀ h₁) x ∧
      (Network.absolutePseudoHelmholtz N (rates h₀ h₁) x
          = Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁) →
        x = balanced k₀ k₁) := by
  refine Network.absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced N (rates h₀ h₁)
    (balanced_positive h₀ h₁) (balanced_isLogarithmicallyBalanced h₀ h₁) hx ?_
  exact sub_balanced_mem hclass

/-- **The complex-balanced equilibrium is not the class-wise minimizer of the absolute
pseudo-Helmholtz function when the two rate constants differ.**  This is the counterexample
to the naive form of the class-wise minimization statement for the absolute function: the
complex-balanced equilibrium `(k₁, k₀)` of `A ⇌ B` has a *larger* value of `V` than the
logarithmically balanced point `((k₀+k₁)/2, (k₀+k₁)/2)` of the same class. -/
theorem absolutePseudoHelmholtz_equilibrium_not_minimizer {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (hne : k₀ ≠ k₁) :
    Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
      < Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁) := by
  have hmem : equilibrium k₀ k₁ - equilibrium k₀ k₁ ∈ N.stoichSubspace := by
    have hz : equilibrium k₀ k₁ - equilibrium k₀ k₁ = 0 := sub_self _
    rw [hz]
    exact Submodule.zero_mem _
  obtain ⟨h1, h2⟩ := absolutePseudoHelmholtz_minimized_at_balanced h₀ h₁
    (equilibrium_positive h₀ h₁).nonnegative hmem
  have hne' : equilibrium k₀ k₁ ≠ balanced k₀ k₁ := by
    intro heq
    have hh := congrFun heq Species.A
    simp [equilibrium, balanced] at hh
    have hh2 : k₀ = k₁ := by
      have h3 := congrArg (fun t : ℝ => 2 * t) hh
      have h4 : 2 * ((k₀ + k₁) / 2) = k₀ + k₁ := by field_simp
      linarith
    exact hne hh2
  have hlt : Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
      < Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁) := by
    by_contra hcon
    have heq : Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
        = Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁) :=
      (le_antisymm (le_of_not_gt hcon) h1)
    exact hne' (h2 heq)
  exact hlt

/-- **The worked instance.** For the reversible pair with *equal* rate constants the
complex-balanced equilibrium `(k, k)` is exactly the minimizer of the absolute
pseudo-Helmholtz function on its compatibility class: here the complex-balanced state is
logarithmically balanced as well. -/
theorem absolutePseudoHelmholtz_equilibrium_isMinimizer {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (heq : k₀ = k₁) {x : Concentration Species} (hx : x.Nonnegative)
    (hclass : x - equilibrium k₀ k₁ ∈ N.stoichSubspace) :
    Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
        ≤ Network.absolutePseudoHelmholtz N (rates h₀ h₁) x ∧
      (Network.absolutePseudoHelmholtz N (rates h₀ h₁) x
          = Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁) →
        x = equilibrium k₀ k₁) := by
  have hbal : balanced k₀ k₁ = equilibrium k₀ k₁ := by
    funext s
    cases s <;> simp [balanced, equilibrium, heq]
  rw [← hbal]
  exact absolutePseudoHelmholtz_minimized_at_balanced h₀ h₁ hx hclass

/-- **The absolute and the relative pseudo-Helmholtz function do not differ by a constant on
a compatibility class.**  For `A ⇌ B` with two different rate constants the difference
`V(x) − G_{x*}(x)` takes different values at two points of the *same* class, namely at the
complex-balanced equilibrium `(k₁, k₀)` and at the logarithmically balanced point
`((k₀+k₁)/2, (k₀+k₁)/2)`. -/
theorem absolutePseudoHelmholtz_sub_relEntropy_not_constant {k₀ k₁ : ℝ} (h₀ : 0 < k₀)
    (h₁ : 0 < k₁) (hne : k₀ ≠ k₁) :
    Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁)
      ≠ Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁) := by
  have hxs : (equilibrium k₀ k₁).Positive := equilibrium_positive h₀ h₁
  have h1 := Network.absolutePseudoHelmholtz_sub_relEntropy N (rates h₀ h₁) hxs
    (x := balanced k₀ k₁)
  have h2 := Network.absolutePseudoHelmholtz_sub_relEntropy N (rates h₀ h₁) hxs
    (x := equilibrium k₀ k₁)
  have hself : relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁) = 0 := by
    have hz : ∑ s, (equilibrium k₀ k₁ s - equilibrium k₀ k₁ s) * Real.log (equilibrium k₀ k₁ s) = 0 := by
      simp
    linarith
  have hdiff : (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁))
      - (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁))
      = ∑ s, (balanced k₀ k₁ s - equilibrium k₀ k₁ s) * Real.log (equilibrium k₀ k₁ s) := by
    calc
      (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
          - relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁))
          - (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
            - relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁))
          = (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
              - Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁))
            - (relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁)
              - relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁)) := by abel
      _ = (relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁)
            + ∑ s, (balanced k₀ k₁ s - equilibrium k₀ k₁ s) * Real.log (equilibrium k₀ k₁ s))
            - (relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁) - 0) := by rw [h1, hself]
      _ = ∑ s, (balanced k₀ k₁ s - equilibrium k₀ k₁ s) * Real.log (equilibrium k₀ k₁ s) := by
        ring
  have hS : (∑ s, (balanced k₀ k₁ s - equilibrium k₀ k₁ s) * Real.log (equilibrium k₀ k₁ s))
      = ((k₁ - k₀) / 2) * (Real.log k₀ - Real.log k₁) := by
    have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [balanced, equilibrium]
    ring
  intro hcon
  have hz : (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (balanced k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (balanced k₀ k₁))
      - (Network.absolutePseudoHelmholtz N (rates h₀ h₁) (equilibrium k₀ k₁)
        - relEntropy (equilibrium k₀ k₁) (equilibrium k₀ k₁)) = 0 := by linarith
  rw [hdiff, hS] at hz
  have hlogne : Real.log k₀ ≠ Real.log k₁ := by
    intro hcon2
    have hh : k₀ = k₁ := Real.log_injOn_pos (Set.mem_Ioi.mpr h₀) (Set.mem_Ioi.mpr h₁) hcon2
    exact hne hh
  have hfactor : (k₁ - k₀) / 2 ≠ 0 := by
    intro hz2
    have hh : k₁ = k₀ := by linarith
    exact hne hh.symm
  exact (mul_ne_zero hfactor (sub_ne_zero.mpr hlogne)) hz

/-- The rate constants `1` (forward) and `1` (backward) of `A ⇌ B`. -/
def unitRates : Network.RateConstants N :=
  rates (k₀ := 1) (k₁ := 1) (by norm_num) (by norm_num)

/-- **A concrete value.** For `A ⇌ B` with rates `1` and `1`, the absolute pseudo-Helmholtz
function takes the value `-2` at the complex-balanced equilibrium `(1, 1)`. -/
theorem absolutePseudoHelmholtz_at_equilibrium :
    Network.absolutePseudoHelmholtz N unitRates (equilibrium 1 1) = -2 := by
  rw [Network.absolutePseudoHelmholtz_eq_speciesSum]
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [equilibrium]; ring

/-- **A concrete value off the equilibrium.** At the state `(2, 0)` the absolute
pseudo-Helmholtz function of `A ⇌ B` with rates `1` and `1` takes the value `2 log 2 - 2`,
which is strictly larger than its value `-2` at the equilibrium. -/
theorem absolutePseudoHelmholtz_at_state :
    Network.absolutePseudoHelmholtz N unitRates (fun s => match s with | A => 2 | B => 0)
      = 2 * Real.log 2 - 2 := by
  rw [Network.absolutePseudoHelmholtz_eq_speciesSum]
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

/-- The value at the state `(2, 0)` is strictly larger than the value at the equilibrium. -/
theorem absolutePseudoHelmholtz_at_state_gt_equilibrium :
    Network.absolutePseudoHelmholtz N unitRates (equilibrium 1 1)
      < Network.absolutePseudoHelmholtz N unitRates (fun s => match s with | A => 2 | B => 0) := by
  rw [absolutePseudoHelmholtz_at_equilibrium, absolutePseudoHelmholtz_at_state]
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end CRNT.Examples.ReversiblePair

/-! ## Axiom audit (informational) -/

#print axioms CRNT.Network.absolutePseudoHelmholtz
#print axioms CRNT.Network.absolutePseudoHelmholtz_eq_speciesSum
#print axioms CRNT.Network.absolutePseudoHelmholtz_sub_relEntropy
#print axioms CRNT.Network.absolutePseudoHelmholtz_sub_relEntropy_of_orth
#print axioms CRNT.Network.absolutePseudoHelmholtz_ge_at_logarithmicallyBalanced
#print axioms CRNT.Network.absolutePseudoHelmholtz_ge_at_complexBalanced
#print axioms CRNT.Network.absolutePseudoHelmholtz_hasDerivAt
#print axioms CRNT.Network.absolutePseudoHelmholtz_log_orthogonal_of_isLocalMinOn
#print axioms CRNT.Network.absolutePseudoHelmholtz_isClassMinimizer_iff
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_minimized_at_balanced
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_equilibrium_not_minimizer
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_equilibrium_isMinimizer
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_sub_relEntropy_not_constant
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_at_equilibrium
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_at_state
#print axioms CRNT.Examples.ReversiblePair.absolutePseudoHelmholtz_at_state_gt_equilibrium
