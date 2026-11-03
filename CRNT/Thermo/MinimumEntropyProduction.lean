import CRNT.Equilibria.DetailedBalanceToric
import CRNT.Thermo.GibbsFreeEnergy
import CRNT.Theorems.DeficiencyZero.Existence

/-!
# Prigogine's minimum entropy production principle

**The principle.**  I. Prigogine, *Étude thermodynamique des réactions chimiques*,
Bull. Soc. Chim. Belg. **56** (1947) 930–939; S. R. de Groot & P. Mazur,
*Non-Equilibrium Thermodynamics* (North-Holland, 1952), Ch. III ("the minimum entropy
production principle"); F. Horn & R. Jackson (1972), *Generalized Mass Action Laws*,
§5.

For a mass-action network with a reverse pairing `ρ` and positive rate constants `κ`, the
**entropy production** of the repository (leaf E1) is

```text
σ(x) = ½ ∑_r (v_r(x) − v_ρ(r)(x)) (log v_r(x) − log v_ρ(r)(x)) ,
```

the total entropy production rate of the system, in units where the thermal energy is one.
Prigogine's principle is the *minimization* statement about this functional:

* `σ` is nonnegative, and `σ = 0` **exactly** at the *reactionwise detailed-balanced*
  states, i.e. the states at which every forward flux is matched by its reverse flux
  (`Network.IsReactionwiseDetailedBalanced`);
* the states at which `σ` vanishes are the **global minimizers** of `σ` among the
  positive concentrations;
* within a *stoichiometric compatibility class* (de Groot–Mazur's "reaction class") the
  minimizer is **unique**: it is the reactionwise detailed-balanced state of that class.

The third bullet is the form in which the principle is usually quoted ("in a fixed
reaction class the entropy production is minimal at the equilibrium").  The second bullet
is the global form: the set of global minimizers is the set of detailed-balanced states.
The *global* uniqueness of the minimizer is **false** in general — the detailed-balanced
states form the toric manifold `x* ⊙ exp(S^⊥)`, one (or a continuum) per reaction class —
so the uniqueness is a class-wise statement, and that is what this module proves.

## What the repository already contained

* **The nonnegativity of the entropy production** (leaf E1):
  `CRNT.Network.entropyProduction_nonneg`, and the **equality case**
  `CRNT.Network.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced`.
* **The free-energy minimizer** (leaf E1, the "Tikhonov reading" of the same principle):
  `CRNT.Network.relEntropy_ge_at_complexBalanced` and
  `CRNT.Network.exists_unique_freeEnergy_minimizer` in `CRNT.Thermo.FreeEnergyMinimization`.
* **The Gibbs free energy machinery** in `CRNT.Thermo.GibbsFreeEnergy`: the rate of change
  `Network.gibbsFreeEnergy_rateOfChange`, the chemical affinity
  `Network.chemicalAffinity`, De Donder's identity
  `Network.gibbsFreeEnergy_dissipation_eq_affinity_netCurrent`, the sum-of-squares form
  `Network.gibbsFreeEnergy_dissipation_eq_sum_squares`, and the identification of the
  dissipation with the entropy production
  `Network.gibbsFreeEnergy_dissipation_eq_tau_entropyProduction`.
* The toric theory of the detailed-balanced states
  (`CRNT.Equilibria.DetailedBalanceToric`): the reactionwise detailed-balanced states
  form a toric manifold, and there is **exactly one** of them in each positive
  compatibility class (`Network.reactionwiseDetailedBalanced_unique_in_class`).
* The Horn--Jackson/De Donder identity in the log-potential form
  (`CRNT.Equilibria.DetailedBalanceEntropy`): relative to a positive detailed-balanced
  reference `x*`, the logarithmic dissipation `⟨log x − log x*, f(x)⟩` is *minus* the
  entropy production (`Network.relativeLogDissipation_eq_neg_entropyProduction`).
* The deficiency-zero theory (`CRNT.Theorems.DeficiencyZero.Existence`): a weakly
  reversible network of deficiency zero has a **unique** complex-balanced equilibrium in
  each positive compatibility class.

## What this module adds

This module adds the **minimization reading** of Prigogine's principle, in the entropy
production (rather than the free energy) language:

* `Network.entropyProduction_eq_zero_iff_detailedBalanced` — the equality case, phrased
  with both the reactionwise and the aggregate notions of detailed balance;
* `Network.entropyProduction_minimized_at_detailedBalanced` — the **global form**: a
  detailed-balanced state minimizes `σ` among *all* positive concentrations, and the
  minimizers are exactly the detailed-balanced states;
* `Network.entropyProduction_globalMinimizer_iff_detailedBalanced` — the
  characterization of the set of global minimizers;
* `Network.entropyProduction_uniqueMinimizer_inClass` — the **class-wise uniqueness**:
  the unique minimizer of `σ` on a stoichiometric compatibility class;
* `Network.massActionVectorField_eq_zero_of_reactionwiseDetailedBalanced` — the minimizer
  is a stationary state of the dynamics (the mass-action vector field vanishes there);
* `Network.deficiencyZero_entropyProduction_minimizer` — the deficiency-zero assembly:
  the class contains a unique complex-balanced equilibrium, and if that equilibrium is
  detailed balanced then it is the unique entropy-production minimizer of the class;
* `Network.exists_entropyProduction_minimizer_of_hasWegscheiderPotential` — existence of
  the minimizer from a Wegscheider potential (the classical "the rate constants are
  thermodynamically consistent" hypothesis);
* `Network.gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction` and
  `Network.gibbsFreeEnergy_rateOfChange_eq_zero_iff_detailedBalanced` — **De Donder's
  identity** in the entropy-production form: the rate of change of the Gibbs free energy
  is *minus* the entropy production, and the free energy is stationary exactly at the
  detailed-balanced states.

## What is *not* formalized here

The **local** (Onsager) form of the principle — the *linear-response* statement that
near equilibrium the entropy production is a positive-definite quadratic form in the
affinities, `σ ≈ ½ Aᵀ L A` with `L` positive definite — is **not** formalized.  It
requires the positive-definite matrix theory of Onsager's reciprocal relations, which
Mathlib has only partially; the repository's related content is the *global* Lyapunov
statement of `CRNT.Theorems.DeficiencyZero.Lyapunov` and the linear-stability statements
of `CRNT.Equilibria.ComplexBalanceLinearStability`, which are different statements.

Depends on: `CRNT.Equilibria.DetailedBalanceToric`, `CRNT.Thermo.GibbsFreeEnergy`,
`CRNT.Theorems.DeficiencyZero.Existence`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The minimizer predicates -/

/-- `x` is a **global minimizer** of the entropy production: it is a positive
concentration and no positive concentration has a smaller entropy production. -/
def IsEntropyProductionMinimizer (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S) : Prop :=
  x.Positive ∧
    ∀ y : Concentration S, y.Positive →
      N.entropyProduction ρ κ x ≤ N.entropyProduction ρ κ y

/-- `x` minimizes the entropy production **on its stoichiometric compatibility class**:
this is the form in which Prigogine's principle is quoted in de Groot--Mazur, Ch. III
(the "reaction class" of the system). -/
def IsEntropyProductionMinimizerInClass (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S) : Prop :=
  x.Positive ∧
    ∀ y : Concentration S, y.Positive → N.StoichCompatible x y →
      N.entropyProduction ρ κ x ≤ N.entropyProduction ρ κ y

/-! ## The equality case -/

/-- **The entropy production vanishes exactly at the detailed-balanced states.**

At a positive concentration, `σ = 0` if and only if the state is *reactionwise*
detailed balanced with respect to the reverse pairing `ρ` (every forward flux is matched
by the flux of its paired reverse channel) — and then it is also detailed balanced in the
aggregate sense of `Network.IsDetailedBalanced` (the total flux between two complexes is
the same in both directions), hence complex balanced.

This is the equality case of leaf E1, restated with the two notions of detailed balance
available in the library. -/
theorem entropyProduction_eq_zero_iff_detailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Positive) :
    N.entropyProduction ρ κ x = 0 ↔
      (N.IsReactionwiseDetailedBalanced ρ κ x ∧ N.IsDetailedBalanced κ x) := by
  constructor
  · intro hz
    have hdb : N.IsReactionwiseDetailedBalanced ρ κ x :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz
    exact ⟨hdb, N.isDetailedBalanced_of_reactionwiseDetailedBalanced ρ κ x hdb⟩
  · rintro ⟨hdb, _⟩
    exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).2 hdb

/-! ## The global form of the principle -/

/-- **Prigogine's minimum entropy production principle, global form.**

Let `x*` be a positive *reactionwise* detailed-balanced state of the network with respect
to a reverse pairing `ρ`.  Then the entropy production
`σ(x) = ½ ∑_r (v_r(x) − v_ρ(r)(x)) (log v_r(x) − log v_ρ(r)(x))` is nonnegative for
every positive `x`, `σ(x*) = 0`, and `σ(x) = σ(x*)` **exactly** at the reactionwise
detailed-balanced states.  In other words `x*` is a global minimizer of the entropy
production, and the global minimizers are precisely the detailed-balanced states.

Note that the global minimizer is *not* unique in general: the detailed-balanced states
form the toric manifold `x* ⊙ exp(S^⊥)`, one per reaction class.  The class-wise
uniqueness is `Network.entropyProduction_uniqueMinimizer_inClass` below. -/
theorem entropyProduction_minimized_at_detailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    N.entropyProduction ρ κ xstar ≤ N.entropyProduction ρ κ x ∧
      (N.entropyProduction ρ κ x = N.entropyProduction ρ κ xstar ↔
        N.IsReactionwiseDetailedBalanced ρ κ x) := by
  have hzstar : N.entropyProduction ρ κ xstar = 0 :=
    (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hxs).2 hdbs
  have hn : 0 ≤ N.entropyProduction ρ κ x := N.entropyProduction_nonneg ρ κ hx
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have hz : N.entropyProduction ρ κ x = 0 := by linarith
    exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz
  · intro hdb
    have hz : N.entropyProduction ρ κ x = 0 :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).2 hdb
    linarith

/-- **The global minimizers of the entropy production are exactly the detailed-balanced
states.**  If the network admits a positive reactionwise detailed-balanced state, then a
positive concentration is a global minimizer of `σ` if and only if it is reactionwise
detailed balanced. -/
theorem entropyProduction_globalMinimizer_iff_detailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar) (hx : x.Positive) :
    (∀ y : Concentration S, y.Positive →
        N.entropyProduction ρ κ x ≤ N.entropyProduction ρ κ y) ↔
      N.IsReactionwiseDetailedBalanced ρ κ x := by
  constructor
  · intro hglob
    have hzstar : N.entropyProduction ρ κ xstar = 0 :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hxs).2 hdbs
    have hle := hglob xstar hxs
    have hn := N.entropyProduction_nonneg ρ κ hx
    have hz : N.entropyProduction ρ κ x = 0 := by linarith
    exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz
  · intro hdb
    have hz : N.entropyProduction ρ κ x = 0 :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).2 hdb
    intro y hy
    have hn := N.entropyProduction_nonneg ρ κ hy
    linarith

/-! ## The class-wise form of the principle -/

/-- **The unique minimizer of the entropy production on a compatibility class.**

Let `x*` be a positive reactionwise detailed-balanced state and let `x` be a positive
concentration in the *same* stoichiometric compatibility class.  Then `σ(x*) ≤ σ(x)`,
with equality only for `x = x*`.  This is the form of Prigogine's principle quoted in
de Groot--Mazur, Ch. III: within a reaction class, the entropy production is minimized,
uniquely, at the equilibrium.

The uniqueness is the toric fact that the reactionwise detailed-balanced states form a
toric manifold with exactly one point in each positive compatibility class
(`Network.reactionwiseDetailedBalanced_unique_in_class`). -/
theorem entropyProduction_uniqueMinimizer_inClass
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hdbs : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (hclass : N.StoichCompatible xstar x) :
    N.IsEntropyProductionMinimizerInClass ρ κ xstar ∧
      (N.entropyProduction ρ κ x = N.entropyProduction ρ κ xstar → x = xstar) := by
  have hzstar : N.entropyProduction ρ κ xstar = 0 :=
    (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hxs).2 hdbs
  have hn : 0 ≤ N.entropyProduction ρ κ x := N.entropyProduction_nonneg ρ κ hx
  refine ⟨⟨hxs, ?_⟩, ?_⟩
  · intro y hy hcompat
    have hny : 0 ≤ N.entropyProduction ρ κ y := N.entropyProduction_nonneg ρ κ hy
    linarith
  · intro heq
    have hz : N.entropyProduction ρ κ x = 0 := by linarith
    have hdb : N.IsReactionwiseDetailedBalanced ρ κ x :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz
    exact (N.reactionwiseDetailedBalanced_unique_in_class ρ κ hxs hxs hx hdbs hdbs hdb
      hclass).symm

/-- **The minimizer of the entropy production is a stationary state.**  At a reactionwise
detailed-balanced state the mass-action vector field vanishes: every forward flux is
matched by its reverse, so the two cancel.  Hence the minimizer of the entropy production
is an equilibrium of the dynamics. -/
theorem massActionVectorField_eq_zero_of_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    {x : Concentration S} (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    ∀ s, N.massActionVectorField κ x s = 0 := by
  have hagg := N.isDetailedBalanced_of_reactionwiseDetailedBalanced ρ κ x hdb
  have hcb := N.isComplexBalanced_of_isDetailedBalanced κ x hagg
  exact hcb.isMassActionSteadyState N κ

/-! ## Existence of the minimizer -/

/-- **Existence of the entropy-production minimizer.**  If the rate constants admit a
Wegscheider potential — the classical hypothesis that the rate constants are
thermodynamically consistent, so that the log-affinities are stoichiometric potential
differences — then the network admits a positive reactionwise detailed-balanced state,
which is the unique minimizer of the entropy production on its compatibility class. -/
theorem exists_entropyProduction_minimizer_of_hasWegscheiderPotential
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    (hpot : N.HasWegscheiderPotential ρ κ) :
    ∃ xstar : Concentration S, xstar.Positive ∧
      N.IsReactionwiseDetailedBalanced ρ κ xstar ∧
      N.IsEntropyProductionMinimizerInClass ρ κ xstar ∧
      (∀ x : Concentration S, x.Positive → N.StoichCompatible xstar x →
        N.entropyProduction ρ κ x = N.entropyProduction ρ κ xstar → x = xstar) := by
  obtain ⟨xstar, hxs, hdbs⟩ :=
    N.exists_positive_reactionwiseDetailedBalanced_of_hasWegscheiderPotential ρ κ hpot
  have hzstar : N.entropyProduction ρ κ xstar = 0 :=
    (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hxs).2 hdbs
  refine ⟨xstar, hxs, hdbs, ⟨hxs, ?_⟩, ?_⟩
  · intro y hy hcompat
    have hny : 0 ≤ N.entropyProduction ρ κ y := N.entropyProduction_nonneg ρ κ hy
    linarith
  · intro x hx hcompat hz
    have hz' : N.entropyProduction ρ κ x = 0 := by linarith [hzstar]
    have hdbx : N.IsReactionwiseDetailedBalanced ρ κ x :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz'
    exact (N.reactionwiseDetailedBalanced_unique_in_class ρ κ hxs hxs hx hdbs hdbs hdbx
      hcompat).symm

/-! ## De Donder's identity: the Gibbs free energy and the entropy production -/

/-- **De Donder's identity in the entropy-production form.**  If the standard chemical
potentials `μ` are thermodynamically consistent with the rate constants (the affinity of
each reaction pair is `τ` times the logarithmic flux ratio), then the rate of change of
the Gibbs free energy along the mass-action flow is `−τ · σ`: the free energy decreases
at the rate given by the entropy production. -/
theorem gibbsFreeEnergy_rateOfChange_eq_neg_tau_entropyProduction
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) {τ : ℝ}
    {x : Concentration S} (hcons : N.HasConsistentChemicalPotentials ρ κ μ τ x) :
    (∑ s, μ s * N.massActionVectorField κ x s) = -τ * N.entropyProduction ρ κ x := by
  have h := N.gibbsFreeEnergy_rateOfChange κ μ x
  have hd := N.gibbsFreeEnergy_dissipation_eq_tau_entropyProduction ρ κ μ hcons
  unfold gibbsFreeEnergyDissipation at hd
  linarith

/-- **The rate of change of the Gibbs free energy is minus the entropy production.**  In
units where the thermal energy is one (`τ = 1`), `dG/dt = −σ` along a mass-action
solution: the Gibbs free energy decreases at the rate given by the entropy production. -/
theorem gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ)
    {x : Concentration S} (hcons : N.HasConsistentChemicalPotentials ρ κ μ 1 x) :
    (∑ s, μ s * N.massActionVectorField κ x s) = -N.entropyProduction ρ κ x := by
  have h := N.gibbsFreeEnergy_rateOfChange_eq_neg_tau_entropyProduction ρ κ μ hcons
  simpa using h

/-- **The Gibbs free energy is stationary exactly at the detailed-balanced states.**
With thermodynamically consistent standard chemical potentials, the rate of change of the
Gibbs free energy vanishes exactly at the reactionwise detailed-balanced states: it is
`−σ(x)`, nonpositive everywhere, and strictly negative at every positive concentration
which is not reactionwise detailed balanced. -/
theorem gibbsFreeEnergy_rateOfChange_eq_zero_iff_detailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ)
    {x : Concentration S} (hx : x.Positive)
    (hcons : N.HasConsistentChemicalPotentials ρ κ μ 1 x) :
    (∑ s, μ s * N.massActionVectorField κ x s) = 0 ↔
      N.IsReactionwiseDetailedBalanced ρ κ x := by
  have h := N.gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction ρ κ μ hcons
  constructor
  · intro hz
    have hσ : N.entropyProduction ρ κ x = 0 := by linarith
    exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hσ
  · intro hdb
    have hσ : N.entropyProduction ρ κ x = 0 :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).2 hdb
    linarith

/-- **The Gibbs free energy is stationary at the detailed-balanced states.**  At a
reactionwise detailed-balanced state the mass-action vector field vanishes, so the
Gibbs free energy is stationary there for *every* choice of standard chemical potentials
— no consistency hypothesis is needed. -/
theorem gibbsFreeEnergy_stationary_at_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ)
    {x : Concentration S} (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    (∑ s, μ s * N.massActionVectorField κ x s) = 0 := by
  have hzero := N.massActionVectorField_eq_zero_of_reactionwiseDetailedBalanced ρ κ hdb
  rw [Finset.sum_eq_zero]
  intro s _
  rw [hzero s]
  ring

/-- **The Gibbs free energy does not increase along the flow.**  With thermodynamically
consistent standard chemical potentials, the rate of change of the Gibbs free energy is
nonpositive at every positive concentration. -/
theorem gibbsFreeEnergy_rateOfChange_nonpos
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ)
    {x : Concentration S} (hx : x.Positive)
    (hcons : N.HasConsistentChemicalPotentials ρ κ μ 1 x) :
    (∑ s, μ s * N.massActionVectorField κ x s) ≤ 0 := by
  have h := N.gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction ρ κ μ hcons
  have hn := N.entropyProduction_nonneg ρ κ hx
  linarith

/-! ## The deficiency-zero assembly -/

/-- **Prigogine's principle, deficiency-zero form.**

Let `N` be weakly reversible with deficiency zero and `κ` its rate constants.  Then every
positive compatibility class contains a unique complex-balanced equilibrium (the
deficiency-zero theorem).  If that equilibrium is *reactionwise detailed balanced* for a
reverse pairing `ρ` — the classical detailed-balance hypothesis of Prigogine — then it
is the **unique minimizer of the entropy production** on its class, and the entropy
production vanishes there. -/
theorem deficiencyZero_entropyProduction_minimizer
    (N : Network S) (hyp : N.SatisfiesDeficiencyZeroHypotheses) (κ : RateConstants N)
    (ρ : ReversiblePairing N) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ xstar : Concentration S, xstar ∈ N.positiveCompatibilityClass x₀ ∧
      N.IsComplexBalanced κ xstar ∧
      (∀ y : Concentration S, y ∈ N.positiveCompatibilityClass x₀ →
        N.IsComplexBalanced κ y → y = xstar) ∧
      (N.IsReactionwiseDetailedBalanced ρ κ xstar →
        N.IsEntropyProductionMinimizerInClass ρ κ xstar ∧
          (∀ x : Concentration S, x.Positive → N.StoichCompatible xstar x →
            N.entropyProduction ρ κ x = N.entropyProduction ρ κ xstar → x = xstar)) := by
  obtain ⟨xstar, hxstar, huniq⟩ := N.deficiencyZeroTheorem hyp κ x₀ hx₀
  refine ⟨xstar, hxstar.1, hxstar.2, ?_, ?_⟩
  · intro y hy hcb
    exact huniq y ⟨hy, hcb⟩
  · intro hdbs
    have hzstar : N.entropyProduction ρ κ xstar = 0 :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hxstar.1.2).2 hdbs
    refine ⟨⟨hxstar.1.2, ?_⟩, ?_⟩
    · intro y hy hcompat
      have hny : 0 ≤ N.entropyProduction ρ κ y := N.entropyProduction_nonneg ρ κ hy
      linarith
    · intro x hx hcompat hz
      have hz' : N.entropyProduction ρ κ x = 0 := by linarith [hzstar]
      have hdbx : N.IsReactionwiseDetailedBalanced ρ κ x :=
        (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced ρ κ hx).1 hz'
      exact (N.reactionwiseDetailedBalanced_unique_in_class ρ κ hxstar.1.2 hxstar.1.2 hx hdbs
        hdbs hdbx hcompat).symm

end Network

end CRNT

/-! ## A concrete instance: the reversible pair `A ⇌ B`

The smallest system with a non-trivial entropy production is the isomerization `A ⇌ B`
with unit rate constants (the network of `CRNT.Examples.GibbsIsomerization`).  Its forward
flux is `x_A` and its backward flux is `x_B`, so the state is reactionwise detailed
balanced exactly when `x_A = x_B`, and

```text
σ(x) = ½ [(x_A − x_B)(log x_A − log x_B) + (x_B − x_A)(log x_B − log x_A)]
     = (x_A − x_B)(log x_A − log x_B) ,
```

which vanishes exactly at the detailed-balanced states `(t, t)` and is strictly positive
elsewhere.  We check every hypothesis explicitly and evaluate the entropy production at
the equilibrium `(1, 1)` and at the off-equilibrium state `(2, 1)`. -/

namespace CRNT.Examples.MinimumEntropyProduction

open CRNT
open CRNT.Examples.GibbsIsomerization
open CRNT.Examples.GibbsIsomerization.Species
open scoped BigOperators

/-- The off-equilibrium state `(2, 1)`: twice as much `A` as `B`. -/
def state2 : Concentration Species := fun s => match s with | A => 2 | B => 1

/-- The forward mass-action rate at an arbitrary state is the concentration of `A`. -/
theorem massActionRate_fwd (x : Concentration Species) :
    N.massActionRate rates .fwd x = x A := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, cA,
    prod_univ_species]

/-- The backward mass-action rate at an arbitrary state is the concentration of `B`. -/
theorem massActionRate_bwd (x : Concentration Species) :
    N.massActionRate rates .bwd x = x B := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, cB,
    prod_univ_species]

/-- The forward mass-action rate at `(2, 1)` is `2`. -/
theorem massActionRate_fwd_state2 : N.massActionRate rates .fwd state2 = 2 := by
  rw [massActionRate_fwd]
  simp [state2]

/-- The backward mass-action rate at `(2, 1)` is `1`. -/
theorem massActionRate_bwd_state2 : N.massActionRate rates .bwd state2 = 1 := by
  rw [massActionRate_bwd]
  simp [state2]

/-- **The equilibrium `(1, 1)` is reactionwise detailed balanced**: the forward flux `1`
is matched by the backward flux `1`. -/
theorem equilibrium_reactionwiseDetailedBalanced :
    N.IsReactionwiseDetailedBalanced revStruct rates equilibrium := by
  intro r
  cases r with
  | fwd => simp [revStruct, equilibrium, massActionRate_fwd, massActionRate_bwd]
  | bwd => simp [revStruct, equilibrium, massActionRate_fwd, massActionRate_bwd]

/-- **The entropy production vanishes at the detailed-balanced concentration `(1, 1)`.** -/
theorem entropyProduction_at_equilibrium :
    N.entropyProduction revStruct rates equilibrium = 0 := by
  have hx : equilibrium.Positive := by
    intro s
    simp [equilibrium]
  exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced revStruct rates hx).2
    equilibrium_reactionwiseDetailedBalanced

/-- **The entropy production at the off-equilibrium state `(2, 1)` is `log 2`.** -/
theorem entropyProduction_at_state2 :
    N.entropyProduction revStruct rates state2 = Real.log 2 := by
  unfold Network.entropyProduction Network.reactionEntropyProduction
  change (1 / 2 : ℝ) * ∑ r : Rxn,
      (N.massActionRate rates r state2 - N.massActionRate rates (revStruct.rev r) state2) *
        (Real.log (N.massActionRate rates r state2) -
          Real.log (N.massActionRate rates (revStruct.rev r) state2)) = Real.log 2
  rw [sum_univ_rxn]
  simp only [revStruct, massActionRate_fwd_state2, massActionRate_bwd_state2]
  simp [Real.log_one]
  ring

/-- **The entropy production vanishes exactly at the detailed-balanced states** of the
isomerization, i.e. at the states `(t, t)` with `t > 0`. -/
theorem entropyProduction_eq_zero_iff_equilibrium (x : Concentration Species)
    (hx : x.Positive) :
    N.entropyProduction revStruct rates x = 0 ↔ x A = x B := by
  constructor
  · intro hz
    have hdb :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced revStruct rates hx).1 hz
    have h := hdb .fwd
    simp [revStruct, massActionRate_fwd, massActionRate_bwd] at h
    exact h
  · intro h
    have hdb : N.IsReactionwiseDetailedBalanced revStruct rates x := by
      intro r
      cases r with
      | fwd => simp [revStruct, massActionRate_fwd, massActionRate_bwd, h]
      | bwd => simp [revStruct, massActionRate_fwd, massActionRate_bwd, h]
    exact (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced revStruct rates hx).2 hdb

/-- **The entropy production is strictly positive away from the detailed-balanced
states.** -/
theorem entropyProduction_pos_of_not_equilibrium (x : Concentration Species) (hx : x.Positive)
    (hne : x A ≠ x B) : 0 < N.entropyProduction revStruct rates x := by
  have hn := N.entropyProduction_nonneg revStruct rates hx
  have hne' : N.entropyProduction revStruct rates x ≠ 0 := by
    intro hz
    exact hne ((entropyProduction_eq_zero_iff_equilibrium x hx).1 hz)
  exact lt_of_le_of_ne hn (Ne.symm hne')

/-- **Prigogine's principle for the isomerization.**  The equilibrium `(1, 1)` is the
unique minimizer of the entropy production on its stoichiometric compatibility class, and
the entropy production vanishes there. -/
theorem minimumEntropyProduction_at_equilibrium :
    N.IsEntropyProductionMinimizerInClass revStruct rates equilibrium ∧
      (∀ x : Concentration Species, x.Positive → N.StoichCompatible equilibrium x →
        N.entropyProduction revStruct rates x = N.entropyProduction revStruct rates equilibrium →
          x = equilibrium) := by
  have hpos : equilibrium.Positive := by
    intro s
    simp [equilibrium]
  have hdb := equilibrium_reactionwiseDetailedBalanced
  have hz : N.entropyProduction revStruct rates equilibrium = 0 :=
    entropyProduction_at_equilibrium
  refine ⟨⟨hpos, ?_⟩, ?_⟩
  · intro y hy hcompat
    have hny := N.entropyProduction_nonneg revStruct rates hy
    linarith
  · intro x hx hcompat heq
    have hzx : N.entropyProduction revStruct rates x = 0 := by linarith
    have hdbx :=
      (N.entropyProduction_eq_zero_iff_reactionwiseDetailedBalanced revStruct rates hx).1 hzx
    exact (N.reactionwiseDetailedBalanced_unique_in_class revStruct rates hpos hpos hx hdb
      hdb hdbx hcompat).symm

end CRNT.Examples.MinimumEntropyProduction

/-! ## Axiom audit -/

#print axioms CRNT.Network.entropyProduction_eq_zero_iff_detailedBalanced
#print axioms CRNT.Network.entropyProduction_minimized_at_detailedBalanced
#print axioms CRNT.Network.entropyProduction_globalMinimizer_iff_detailedBalanced
#print axioms CRNT.Network.entropyProduction_uniqueMinimizer_inClass
#print axioms CRNT.Network.massActionVectorField_eq_zero_of_reactionwiseDetailedBalanced
#print axioms CRNT.Network.exists_entropyProduction_minimizer_of_hasWegscheiderPotential
#print axioms CRNT.Network.gibbsFreeEnergy_rateOfChange_eq_neg_tau_entropyProduction
#print axioms CRNT.Network.gibbsFreeEnergy_rateOfChange_eq_neg_entropyProduction
#print axioms CRNT.Network.gibbsFreeEnergy_rateOfChange_eq_zero_iff_detailedBalanced
#print axioms CRNT.Network.gibbsFreeEnergy_stationary_at_reactionwiseDetailedBalanced
#print axioms CRNT.Network.gibbsFreeEnergy_rateOfChange_nonpos
#print axioms CRNT.Network.deficiencyZero_entropyProduction_minimizer
#print axioms CRNT.Examples.MinimumEntropyProduction.minimumEntropyProduction_at_equilibrium
