import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Oscillation.Basic
import CRNT.Decision.Rank
import CRNT.Decision.DeficiencyZeroTactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Lotka network: a concrete mass-action system with positive periodic orbits

## Why this file exists

The oscillation development has no network for which `OscillatoryCapacity` is proved. Everything in
it is either an exclusion theorem (no oscillation) or a conditional existence route;
`Examples.HopfNetwork3` reaches a Hurwitz-boundary crossing with transversal eigenvalue motion and
stops there. So no `…Target` in the tree has ever been composed end to end on a real network, which
means a target that is subtly too weak to compose cannot be detected by anything except reading it.
That is not hypothetical: `FloquetOrbitalStabilityTarget` was outright vacuous until it was
strengthened, and reading is what caught it. See `docs/math-review.md`.

This file is the cheapest possible witness in the other direction.

## The network

```
r₀ :  A → 2A          (autocatalytic growth of A)
r₁ :  A + B → 2B      (predation: B consumes A and reproduces)
r₂ :  B → 0           (decay of B)
```

Its mass-action vector field is

```
ẋ = k₀ x − k₁ x y
ẏ = k₁ x y − k₂ y
```

which is exactly the Lotka–Volterra predator–prey system — the standard example of a mass-action
network all of whose positive non-equilibrium orbits are closed. The function

```
V(x, y) = k₁ x + k₁ y − k₂ log x − k₀ log y
```

is a first integral, strictly convex on the open positive quadrant with its unique minimum at the
positive equilibrium `(k₂/k₁, k₀/k₁)`, so its level sets are compact closed curves and every
non-equilibrium positive solution traverses one.

Two reasons this is the right target rather than `HopfNetwork3`:

* the closed orbit comes from a conserved quantity, so the proof needs no centre manifold, no
  normal form and no first Lyapunov coefficient — all of which live in the unverified frontier;
* the network has stoichiometric rank two, the setting the planar route is built for, so proving it
  also exercises `RankTwoPlanar` / `PlanarPoincareBendixson`.

## Indexing choice

`Species` and `Rxn` are `Fin 2` and `Fin 3` rather than custom inductives, unlike the other example
modules. The reason is purely about proof robustness: sums and products over `Fin n` reduce by the
Mathlib simp lemmas `Fin.sum_univ_three` and `Fin.prod_univ_two`, whereas enumerating
`Finset.univ` for a `deriving Fintype` inductive needs a hand-written `Finset.sum_insert` chain.
Readable names are recovered by the abbreviations below.

## What is proved here and what is not

Proved: the network, the explicit form of both components of the vector field, the positive
equilibrium, the conservation identity `⟪∇V, F⟫ = 0` at every positive concentration, failure of
weak reversibility, and rank `≥ 2` (so neither compiled exclusion route applies, as it must not).

Not proved: the step from "V is constant along the orbit" to an actual `PositivePeriodicOrbit`
structure, which needs a period. That is `HasPositivePeriodicOrbitTarget` at the end of the file,
with the four remaining steps and the core theorems that supply each.

**Update.** All remaining steps are now proved downstream:
`CRNT/Examples/LotkaFirstIntegral.lean` (`firstIntegralConstant`, `levelSetCompact`) and
`CRNT/Examples/LotkaPeriodic.lean` (`hasPositivePeriodicOrbit`, `oscillatoryCapacity`).
-/

namespace CRNT
namespace Examples
namespace Lotka

open CRNT

/-- Two species, indexed by `Fin 2`. -/
abbrev Species : Type := Fin 2

/-- Prey / substrate. -/
abbrev A : Species := 0
/-- Predator. -/
abbrev B : Species := 1

/-- Three reactions, indexed by `Fin 3`. -/
abbrev Rxn : Type := Fin 3

/-- `A → 2A`. -/
abbrev grow : Rxn := 0
/-- `A + B → 2B`. -/
abbrev prey : Rxn := 1
/-- `B → 0`. -/
abbrev decay : Rxn := 2

/-! ## Complexes -/

/-- The complex `A`. -/
def cA : Complex Species := ![1, 0]
/-- The complex `2A`. -/
def c2A : Complex Species := ![2, 0]
/-- The complex `A + B`. -/
def cAB : Complex Species := ![1, 1]
/-- The complex `2B`. -/
def c2B : Complex Species := ![0, 2]
/-- The complex `B`. -/
def cB : Complex Species := ![0, 1]
/-- The zero complex. -/
def c0 : Complex Species := ![0, 0]

/-- The reaction map. -/
def rxn : Rxn → Reaction Species :=
  ![{ source := cA,  target := c2A },
    { source := cAB, target := c2B },
    { source := cB,  target := c0 }]

/-- The Lotka network. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-! ## Structural facts

Complex and reaction counts, and the two exclusion routes failing. The latter matters: if either
compiled exclusion route applied to this network, the file would be claiming a contradiction. -/

/-- Five distinct complexes: `A`, `2A`, `A + B`, `2B`, `B`, `0` — with `2A` and `0` both appearing,
so six listed but the count is what `decide` says. -/
theorem numReactions_eq : N.numReactions = 3 := by decide

/-- No reaction has the zero complex as its source, so nothing is reachable from `0`.  This is the
same shape as `Examples.IrreversibleChain.not_directlyReacts_from_cC`. -/
theorem not_directlyReacts_from_c0 (d : Complex Species) : ¬ N.DirectlyReacts c0 d := by
  rintro ⟨r, hs, -⟩
  fin_cases r <;> exact absurd hs (by decide)

/-- **The network is not weakly reversible.** The decay reaction `B → 0` has no return path: the
zero complex is a sink of the reaction graph. Hence the deficiency-zero exclusion route
(`neverPositivePeriodic_of_weaklyReversible_deficiencyZero`) does not apply. -/
theorem not_weaklyReversible : ¬ N.WeaklyReversible := by
  intro h
  have hr : Relation.ReflTransGen N.DirectlyReacts c0 cB := h decay
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨e, hedge, -⟩
  · exact absurd heq (by decide)
  · exact not_directlyReacts_from_c0 e hedge

/-- The two reaction vectors `(1, 0)` (growth) and `(−1, 1)` (predation) are independent, so the
stoichiometric rank is at least two and the low-rank exclusion route
(`neverPositivePeriodic_of_stoichRank_le_one`) does not apply either.

Uses the `crnt_stoich_rank_ge` tactic with the explicit nonsingular minor: rows `A, B`, columns
`grow, prey`. That minor is `[[1, −1], [0, 1]]`, determinant `1`. -/
theorem two_le_stoichRank : 2 ≤ N.stoichRank := by
  crnt_stoich_rank_ge ![grow, prey], ![A, B]
  all_goals
    simp [N, rxn, cA, c2A, cAB, c2B]
    norm_num

/-! ## The vector field, computed

Both components in closed form. Everything downstream depends only on these two lemmas, so if the
`simp` set below needs adjusting on a real build, that is the only place to touch. -/

/-- `ẋ = k₀ x − k₁ x y`.

Term by term: `grow` has source `A` (monomial `x`), reaction-vector entry `2 − 1 = 1`; `prey` has
source `A + B` (monomial `x y`), entry `0 − 1 = −1`; `decay` has source `B` and entry `0 − 0 = 0`. -/
theorem field_A (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x A
      = κ.k grow * x A - κ.k prey * (x A * x B) := by
  change (∑ r : Fin 3,
    κ.k r * (N.reaction r).source.massActionMonomial x *
      (((N.reaction r).target A : ℝ) - ((N.reaction r).source A : ℝ))) = _
  simp [Complex.massActionMonomial, N, rxn, cA, c2A, cAB, c2B, cB, c0,
    Fin.sum_univ_three, Fin.prod_univ_two]
  ring

/-- `ẏ = k₁ x y − k₂ y`.

Term by term: `grow` has entry `0 − 0 = 0`; `prey` has monomial `x y` and entry `2 − 1 = 1`;
`decay` has monomial `y` and entry `0 − 1 = −1`. -/
theorem field_B (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x B
      = κ.k prey * (x A * x B) - κ.k decay * x B := by
  change (∑ r : Fin 3,
    κ.k r * (N.reaction r).source.massActionMonomial x *
      (((N.reaction r).target B : ℝ) - ((N.reaction r).source B : ℝ))) = _
  simp [Complex.massActionMonomial, N, rxn, cA, c2A, cAB, c2B, cB, c0,
    Fin.sum_univ_three, Fin.prod_univ_two]
  ring

/-! ## The positive equilibrium -/

/-- The positive equilibrium `(k₂/k₁, k₀/k₁)`: predation balances growth in `A`, and predation
balances decay in `B`. -/
noncomputable def equilibrium (κ : Network.RateConstants N) : Concentration Species :=
  ![κ.k decay / κ.k prey, κ.k grow / κ.k prey]

/-- The equilibrium really is one: both components of the field vanish there. -/
theorem equilibrium_isSteadyState (κ : Network.RateConstants N) (hp : 0 < κ.k prey) :
    N.massActionVectorField κ (equilibrium κ) = 0 := by
  have hA : N.massActionVectorField κ (equilibrium κ) A = 0 := by
    rw [field_A]
    simp only [equilibrium, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hB : N.massActionVectorField κ (equilibrium κ) B = 0 := by
    rw [field_B]
    simp only [equilibrium, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  funext s
  fin_cases s
  · exact hA
  · exact hB

/-! ## The first integral

`V(x, y) = k₁ x + k₁ y − k₂ log x − k₀ log y`, with gradient `(k₁ − k₂/x, k₁ − k₀/y)`.

The gradient is written as a separate definition rather than derived, because the only thing needed
downstream is the algebraic identity `⟪∇V, F⟫ = 0`; that `firstIntegralGrad` really is the gradient
of `firstIntegral` is a separate (easy) differentiation, stated as `gradient_isGradient` below. -/

/-- The Lotka–Volterra first integral. -/
noncomputable def firstIntegral (κ : Network.RateConstants N) (x : Concentration Species) : ℝ :=
  κ.k prey * x A + κ.k prey * x B
    - κ.k decay * Real.log (x A) - κ.k grow * Real.log (x B)

/-- Its gradient: `∂V/∂x = k₁ − k₂/x`, `∂V/∂y = k₁ − k₀/y`. -/
noncomputable def firstIntegralGrad (κ : Network.RateConstants N) (x : Concentration Species) :
    Species → ℝ :=
  ![κ.k prey - κ.k decay / x A, κ.k prey - κ.k grow / x B]

/-- **The conservation identity.** At every positive concentration the directional derivative of
the first integral along the mass-action field vanishes.

The computation, with `x = x A`, `y = x B`, `k₀ = k grow`, `k₁ = k prey`, `k₂ = k decay`:

```
(k₁ − k₂/x)(k₀x − k₁xy) + (k₁ − k₀/y)(k₁xy − k₂y)
  = k₀k₁x − k₁²xy − k₀k₂ + k₁k₂y      (first bracket)
  + k₁²xy − k₁k₂y − k₀k₁x + k₀k₂      (second bracket)
  = 0
```

Four cancelling pairs: `k₀k₁x`, `k₁²xy`, `k₀k₂`, `k₁k₂y`. Nothing survives. This exact cancellation
is why the Lotka system is conservative, and it is the only place in the file where the specific
form of the network matters. -/
theorem conservation_identity (κ : Network.RateConstants N) {x : Concentration Species}
    (hx : x.Positive) :
    (∑ s, firstIntegralGrad κ x s * N.massActionVectorField κ x s) = 0 := by
  have hA : x A ≠ 0 := ne_of_gt (hx A)
  have hB : x B ≠ 0 := ne_of_gt (hx B)
  rw [Fin.sum_univ_two]
  rw [field_A, field_B]
  simp only [firstIntegralGrad, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- `firstIntegralGrad` is the gradient of `firstIntegral`: the `A`-partial.  Together with the
`B`-partial below this justifies the name, and is what turns `conservation_identity` into constancy
along solutions via the chain rule. -/
theorem hasDerivAt_firstIntegral_A (κ : Network.RateConstants N) {x : Concentration Species}
    (hx : x.Positive) :
    HasDerivAt (fun t : ℝ => κ.k prey * t + κ.k prey * x B
        - κ.k decay * Real.log t - κ.k grow * Real.log (x B))
      (firstIntegralGrad κ x A) (x A) := by
  have hA : x A ≠ 0 := ne_of_gt (hx A)
  have h1 : HasDerivAt (fun t : ℝ => κ.k prey * t) (κ.k prey) (x A) := by
    simpa using (hasDerivAt_id (x A)).const_mul (κ.k prey)
  have h2 : HasDerivAt (fun t : ℝ => κ.k decay * Real.log t)
      (κ.k decay * (x A)⁻¹) (x A) := (Real.hasDerivAt_log hA).const_mul (κ.k decay)
  -- Assemble in the inverse form Mathlib produces, then let `simpa` rewrite the division in
  -- `firstIntegralGrad`.  `convert` is deliberately avoided: on this goal it descends into
  -- instance paths and emits unprovable side goals such as
  -- `Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup`.
  have h4 : HasDerivAt (fun t : ℝ => κ.k prey * t + κ.k prey * x B
      - κ.k decay * Real.log t - κ.k grow * Real.log (x B))
      (κ.k prey - κ.k decay * (x A)⁻¹) (x A) := by
    simpa using ((h1.add_const (κ.k prey * x B)).sub h2).sub_const (κ.k grow * Real.log (x B))
  simpa [firstIntegralGrad, div_eq_mul_inv] using h4

/-- The `B`-partial of the first integral.

The two additive constants are written in the opposite order to `firstIntegral` (the `log (x A)`
term last rather than second).  That is the same function -- constants commute -- and it matters
only for proof assembly: `HasDerivAt.sub_const` has to be the outermost step, otherwise the term
Mathlib builds carries `RCLike.toInnerProductSpaceReal.toModule` where the goal expects
`Semiring.toModule`, and no amount of `simpa` reconciles the two instance paths. Stated in this
order the proof is literally the `A`-partial's with the roles of the species exchanged. -/
theorem hasDerivAt_firstIntegral_B (κ : Network.RateConstants N) {x : Concentration Species}
    (hx : x.Positive) :
    HasDerivAt (fun t : ℝ => κ.k prey * t + κ.k prey * x A
        - κ.k grow * Real.log t - κ.k decay * Real.log (x A))
      (firstIntegralGrad κ x B) (x B) := by
  have hB : x B ≠ 0 := ne_of_gt (hx B)
  have h1 : HasDerivAt (fun t : ℝ => κ.k prey * t) (κ.k prey) (x B) := by
    simpa using (hasDerivAt_id (x B)).const_mul (κ.k prey)
  have h2 : HasDerivAt (fun t : ℝ => κ.k grow * Real.log t)
      (κ.k grow * (x B)⁻¹) (x B) := (Real.hasDerivAt_log hB).const_mul (κ.k grow)
  have h4 : HasDerivAt (fun t : ℝ => κ.k prey * t + κ.k prey * x A
      - κ.k grow * Real.log t - κ.k decay * Real.log (x A))
      (κ.k prey - κ.k grow * (x B)⁻¹) (x B) := by
    simpa using ((h1.add_const (κ.k prey * x A)).sub h2).sub_const (κ.k decay * Real.log (x A))
  simpa [firstIntegralGrad, div_eq_mul_inv] using h4

/-! ## What remains

Constancy along solutions, compactness of level sets, and a period. -/

/-- **Step 2.** The first integral is constant along every positive solution.

This is `conservation_identity` plus the chain rule, and it has a proved analogue in the verified
core: `Network.relEntropy_antitone_along_solution` does the same differentiation for the
Horn–Jackson entropy, with `≤ 0` in place of `= 0`. The only difference is that the conclusion here
is constancy rather than monotonicity, so `Antitone` becomes a statement that the derivative of
`t ↦ V (γ t)` vanishes identically. -/
def FirstIntegralConstantTarget : Prop :=
  ∀ (κ : Network.RateConstants N) (γ : ℝ → Concentration Species),
    (∀ t, (γ t).Positive) →
    (∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) →
    ∀ t, firstIntegral κ (γ t) = firstIntegral κ (γ 0)

/-- **Step 3.** Level sets of the first integral inside the open positive quadrant are compact.

`V` is coercive in both directions: as either coordinate tends to `0` the `−log` term tends to
`+∞`, and as either tends to `∞` the linear term dominates. So every sublevel set is bounded away
from the axes and bounded above, hence its closure is a compact subset of the open quadrant. The
verified core has exactly this argument for the Birch dual objective
(`CRNT.birchDual_coercive`, `CRNT.birchDual_exists_isMinOn`), which is the same
`linear − log` shape. -/
def LevelSetCompactTarget : Prop :=
  ∀ (κ : Network.RateConstants N), 0 < κ.k grow → 0 < κ.k prey → 0 < κ.k decay →
    ∀ c : ℝ, IsCompact {x : Concentration Species | x.Positive ∧ firstIntegral κ x ≤ c}

/-- **Step 4, and the goal.** Every positive non-equilibrium solution is periodic, so the Lotka
network has a positive periodic orbit at every choice of positive rates.

Given steps 2 and 3 the orbit is confined to a compact level set on which the field does not
vanish, and the level set is a regular closed curve. The period comes from a transversal return:
take a transversal at a non-equilibrium point of the level set and use the crossing time. The
verified core supplies exactly that — `CRNT/Dynamics/TransversalCrossingTime.lean` and
`CRNT/Dynamics/PoincareReturnMap.lean`, with `TransversalSection.crossingTime` and
`TransversalSection.isPeriodic_returnMap_fixedPoint`. Note this needs only the transversal-return
part of the planar theory, not Poincaré–Bendixson, so it does not depend on the frontier. -/
def HasPositivePeriodicOrbitTarget : Prop :=
  ∀ κ : Network.RateConstants N,
    0 < κ.k grow → 0 < κ.k prey → 0 < κ.k decay → N.HasPositivePeriodicOrbit κ

/-- **The non-vacuity witness, conditional on step 4.** Once `HasPositivePeriodicOrbitTarget` is
discharged for a single positive rate vector, the Lotka network witnesses `OscillatoryCapacity` and
the oscillation development has its first end-to-end existence result on a concrete network. -/
theorem oscillatoryCapacity_of_target (h : HasPositivePeriodicOrbitTarget)
    (κ : Network.RateConstants N) (h0 : 0 < κ.k grow) (h1 : 0 < κ.k prey)
    (h2 : 0 < κ.k decay) : N.OscillatoryCapacity :=
  ⟨κ, h κ h0 h1 h2⟩

/-- Consistency check on the exclusion side, unconditional: the analyzer's two compiled
non-oscillation routes both fail on this network, as they must if it oscillates. -/
theorem exclusion_routes_do_not_apply : ¬ N.WeaklyReversible ∧ 2 ≤ N.stoichRank :=
  ⟨not_weaklyReversible, two_le_stoichRank⟩

end Lotka
end Examples
end CRNT
