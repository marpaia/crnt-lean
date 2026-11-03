import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Graph.WeakReversibility
import CRNT.Stochastic.CountWitnessPath
import CRNT.Stochastic.RegionStronglyConnected

/-!
# A concrete reversible pair against the embedded-jump convergence interface

The geometric-convergence theorems on the embedded jump chain of a reaction network
(`CRNT.Stochastic.RegionStronglyConnected`, `CRNT.Stochastic.CountWitnessPath`) take a finite
`ClosedEnabledRegion` together with an *aperiodicity self-loop*: a region count `n` and a reaction
`r` that both **holds** (`jumpNextCount n r = n`) and has **positive jump probability**
(`0 < jumpProb κ n r`). This module instantiates that interface on the smallest weakly reversible
network, the reversible pair `A ⇌ B`, and records exactly where a fully hypothesis-discharged,
unconditional convergence instance meets the count lattice.

## The reversible pair

`A ⇌ B` has species `{A, B}`, complexes `A = (1,0)` and `B = (0,1)`, and the two reactions
`fwd : A → B`, `bwd : B → A`. It is weakly reversible (`weaklyReversible`). On the count lattice the
firings are the truncated shifts `jumpNextCount n fwd = (n_A − 1, n_B + 1)` and
`jumpNextCount n bwd = (n_A + 1, n_B − 1)`; mass `n_A + n_B` is conserved on enabled firings.

## Two structural obstructions to an unconditional instance

The convergence interface cannot be fired unconditionally on this (or any genuine)
network, for two independent reasons proved here.

* **No aperiodicity self-loop.** A reaction with positive jump probability is enabled
  (`stochasticMassActionRate` forces every falling factorial positive, i.e. `source ≤ n`), so its
  firing is the exact untruncated shift `n − source + target`; that equals `n` only when
  `target = source`, impossible for a reaction between distinct complexes. The aperiodicity
  hypothesis `jumpNextCount n r = n ∧ 0 < jumpProb κ n r` is therefore unsatisfiable for *every*
  network whose reactions have distinct source and target complexes — recorded generically as
  `no_aperiodic_self_loop` and specialized to the pair as `pair_no_aperiodic_self_loop`. The
  finite-state Perron–Frobenius argument supplies aperiodicity through such a holding
  self-loop, which the mass-action jump chain on `S → ℕ` never has.

* **No finite closed enabled region.** A `ClosedEnabledRegion` demands every reaction enabled at
  every member (`enabled`) and the post-firing count to stay inside (`forward`). For `A ⇌ B`,
  `enabled` forces `1 ≤ n_A` and `1 ≤ n_B` at every member, yet firing `fwd` from a member with
  `n_A = 1` lands on `n_A = 0`, which `forward` requires to be a member too — contradicting
  `enabled`. So a closed enabled region of the pair contains no count with `n_A = 1`: the simplex
  boundary, where the `A → B` propensity vanishes, breaks closure. Recorded as `pair_not_closed_of_mem`.

These are the structural facts a non-vacuity witness must confront: the embedded-jump convergence
theorems are sound but their finite-region-plus-self-loop hypotheses are jointly unsatisfiable on the
genuine count lattice of a mass-action network. The picture is Anderson, Craciun & Kurtz,
"Product-form stationary distributions for deficiency zero chemical reaction networks": the recurrent
class of the embedded chain is a single positive-recurrent communicating class, but on `S → ℕ` it is
infinite (a full conservation class with no boundary-free interior) and aperiodic only through the
truncated boundary dynamics, neither of which the finite-state holding-self-loop interface of Norris,
"Markov Chains", §1.8 captures.

## Main results

* `N` — the reversible pair `A ⇌ B` as a `Network`.
* `weaklyReversible` — the network is weakly reversible.
* `enabled_of_jumpProb_pos` — a positive-probability reaction is enabled.
* `no_aperiodic_self_loop` — for any network with all source ≠ target, no count carries a
  positive-probability holding reaction.
* `pair_no_aperiodic_self_loop` — the aperiodicity hypothesis of the convergence theorems is
  unsatisfiable for the pair.
* `pair_not_closed_of_mem` — a closed enabled region of the pair contains no count with `n_A = 1`,
  so no nonempty conservation window is closed.

Depends on:
`CRNT.Basic.Network`, `CRNT.Graph.WeakReversibility`, `CRNT.Stochastic.CountWitnessPath`,
`CRNT.Stochastic.RegionStronglyConnected`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **A positive-probability reaction is enabled.** A strictly positive jump probability forces a
strictly positive mass-action propensity, hence every falling factorial `(n s).descFactorial
(source s)` is nonzero, which means the count dominates the source complex species by species. -/
theorem enabled_of_jumpProb_pos (N : Network S) (κ : RateConstants N) {n : S → ℕ} {r : N.R}
    (h : 0 < N.jumpProb κ n r) : N.Enabled n r := by
  intro s
  -- a positive ratio has a positive numerator: the propensity is positive.
  have hsmar : 0 < N.stochasticMassActionRate κ n r := by
    by_contra hle
    rw [not_lt] at hle
    have hz : N.stochasticMassActionRate κ n r = 0 :=
      le_antisymm hle (N.stochasticMassActionRate_nonneg κ n r)
    rw [jumpProb, hz, zero_div] at h
    exact lt_irrefl _ h
  -- a positive product of nonnegative factors has every factor positive.
  have hfac : (0 : ℝ) < ((n s).descFactorial ((N.reaction r).source s) : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    have hz : ((n s).descFactorial ((N.reaction r).source s) : ℝ) = 0 :=
      le_antisymm hle (by exact_mod_cast Nat.zero_le _)
    have : N.stochasticMassActionRate κ n r = 0 := by
      rw [stochasticMassActionRate, Finset.prod_eq_zero (Finset.mem_univ s) hz, mul_zero]
    rw [this] at hsmar
    exact lt_irrefl _ hsmar
  have hpos : (0 : ℕ) < (n s).descFactorial ((N.reaction r).source s) := by exact_mod_cast hfac
  exact Nat.descFactorial_pos.mp hpos

/-- **No aperiodicity self-loop on a network of genuine reactions.** A holding reaction at a count
(`jumpNextCount n r = n`) with positive jump probability is impossible whenever every reaction has
distinct source and target complexes: positive probability makes the firing the untruncated shift
`n − source + target` (`enabled_of_jumpProb_pos`), so `jumpNextCount n r = n` forces `target = source`
species by species, contradicting distinctness. This is the structural obstruction to the aperiodicity
hypothesis of the finite-state convergence theorems
(`jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec` and its complex-shift specialization): the
mass-action embedded jump chain carries no holding self-loop at any enabled count. -/
theorem no_aperiodic_self_loop (N : Network S) (κ : RateConstants N)
    (hgen : ∀ r : N.R, (N.reaction r).source ≠ (N.reaction r).target)
    {n : S → ℕ} {r : N.R} (hr : N.jumpNextCount n r = n) :
    ¬ 0 < N.jumpProb κ n r := by
  intro hprob
  have henabled : N.Enabled n r := N.enabled_of_jumpProb_pos κ hprob
  apply hgen r
  funext s
  -- enabled ⇒ untruncated: `jumpNextCount n r s = n s − source s + target s` with `source s ≤ n s`.
  have hns : N.jumpNextCount n r s = n s := congrFun hr s
  rw [jumpNextCount] at hns
  have hle : (N.reaction r).source s ≤ n s := henabled s
  omega

end CRNT.Network

namespace CRNT.Examples.StochasticConvergenceExample

open CRNT CRNT.Network

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A = (1, 0)`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex `B = (0, 1)`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- Two reaction channels: forward `A → B` and backward `B → A`. -/
inductive Rxn
  | fwd
  | bwd
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.fwd, Rxn.bwd}
  complete := by intro r; cases r <;> simp

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

/-- The reversible pair `A ⇌ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- **The pair is weakly reversible:** each reaction has its reverse as a single-step return. -/
theorem weaklyReversible : N.WeaklyReversible := by
  intro r
  cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩

/-- Every reaction of the pair has distinct source and target complexes. -/
theorem source_ne_target (r : N.R) : (N.reaction r).source ≠ (N.reaction r).target := by
  cases r
  · intro h; have := congrFun h A; simp [N, rxn, cA, cB] at this
  · intro h; have := congrFun h A; simp [N, rxn, cA, cB] at this

/-- **The aperiodicity hypothesis of the convergence theorems is unsatisfiable for the pair.** No
count of `A ⇌ B` carries a holding reaction with positive jump probability, so the self-loop the
finite-state Perron–Frobenius argument uses for aperiodicity is never available on this network's count
lattice. -/
theorem pair_no_aperiodic_self_loop (κ : RateConstants N) {n : Species → ℕ} {r : N.R}
    (hr : N.jumpNextCount n r = n) : ¬ 0 < N.jumpProb κ n r :=
  N.no_aperiodic_self_loop κ source_ne_target hr

/-- **A closed enabled region of the pair contains no count with `n A = 1`.** Firing `fwd` from such
a count stays in the region by `forward` and lands on a count with first coordinate `0`; but every
member is enabled for `fwd`, whose source is `A = (1,0)`, forcing `1 ≤ ·` at `A` — contradicting the
`0`. The simplex boundary, where the `A → B` propensity vanishes, is reachable from every count with
`n A = 1`, so no nonempty conservation window of the pair is a closed enabled region. -/
theorem pair_not_closed_of_mem (κ : RateConstants N) {T : Set (Species → ℕ)}
    (hT : N.ClosedEnabledRegion κ T) {n : Species → ℕ} (hn : n ∈ T) (hnA : n A = 1) : False := by
  -- firing `fwd` from `n` stays in `T` by closure, and lands on a count with first coordinate `0`.
  have hmem : N.jumpNextCount n Rxn.fwd ∈ T := hT.forward n hn Rxn.fwd
  have hzero : N.jumpNextCount n Rxn.fwd A = 0 := by
    simp [jumpNextCount, N, rxn, cA, cB, hnA]
  -- but every member is enabled for `fwd`, whose source is `A = (1,0)`, forcing `1 ≤ ·` at `A`.
  have henabled : N.Enabled (N.jumpNextCount n Rxn.fwd) Rxn.fwd := hT.enabled _ hmem Rxn.fwd
  have hge : (1 : ℕ) ≤ N.jumpNextCount n Rxn.fwd A := by
    have h := henabled A
    simpa [N, rxn, cA] using h
  omega

end CRNT.Examples.StochasticConvergenceExample
