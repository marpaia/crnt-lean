import CRNT.Dynamics.EscapeDirection
import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Dynamics.GenuineConfinement
import CRNT.Persistence.VariableRateFloor

/-!
# The bounded case of the persistence conjecture, in the strong and omega-limit forms

## The conjectures

Craciun's **Persistence Conjecture** (_Persistence and positivity of the solutions of a chemical
reaction network_, arXiv:1501.02860) asserts that for a weakly reversible mass-action system,
every solution that starts in the strictly positive orthant stays uniformly away from the
boundary of the orthant:

* for every species `s` there is an `ε > 0` with `x t s ≥ ε` for all forward times `t`.

The **strong (compact-confinement) form** asks more: there is a *compact* set of strictly
positive concentrations that absorbs every forward solution from a given positive state.  This is
the repository's certificate `N.PersistentFrom κ x₀` (`CRNT/Dynamics/SingleLinkageGAC.lean`).

The **Extended (tempered) form** (Craciun–Nazarov–Pantea, _Persistence and positivity of the
solutions of a chemical reaction network in unbounded domains_, 2013; Craciun 2015) allows the
rate constants to vary with time, as long as they stay inside a compact set of the positive
orthant.

## What the repository already covers

* **Conservative networks**: a strictly positive conservation law bounds every forward solution,
  so the strong form holds (`CRNT.Network.persistenceConjectureStrong_of_conservative`,
  `CRNT.Network.weaklyReversible_conservative_persistentFrom`).
* **Two species**, **one linkage class**, **stoichiometric rank one**, **strongly endotactic**
  networks: permanence and persistence at the standard level
  (`CRNT.Dynamics.KnownGlobalPersistenceClasses`, `CRNT.Persistence.StronglyEndotacticConsequences`).
* **No critical siphon**: the omega-limit form of persistence
  (`CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon`).
* **No drainable siphon** and **no self-replicable siphon**: bounded-orbit omega persistence
  (`CRNT.Network.structurallyBoundaryOmegaExcludedStd_of_hasNoDrainableSiphon`,
  `CRNT.Network.structurallyBoundaryOmegaExcludedStd_of_weaklyReversible_hasNoSelfReplicableSiphon`).
* The **bounded case of the ordinary persistence conjecture** at the trajectory level:
  `CRNT.Network.weaklyReversible_forward_floor` and
  `CRNT.Network.weaklyReversible_forward_floor_uniform` say that a bounded forward solution of a
  weakly reversible network that starts positive stays uniformly above a positive constant that
  depends only on the initial state and the bound.

## What this module adds

This module *packages* the bounded case of leaf **D12** into the repository's global-predicate
API.  It adds

* `N.BoundedPositiveSolutions`: the hypothesis that every forward solution from a positive state
  is bounded above (the "bounded case" hypothesis, at the level of solutions rather than of
  flows);
* `N.weaklyReversible_bounded_confined`: the **bounded case, trajectory form** — a bounded
  forward solution stays in the compact box `[η, M]^S` of strictly positive concentrations;
* `N.weaklyReversible_persistentFrom_of_bounded`: the **strong (compact-confinement) bounded
  case** — the compact-interior certificate `N.PersistentFrom κ x₀` follows from the boundedness
  hypothesis alone, with the compact set being the box `[η, M]^S`;
* `N.weaklyReversible_persistentFrom_of_boundedSolution`: the same conclusion from the
  boundedness of a *single* trajectory, using the uniqueness of genuine mass-action solutions
  (`CRNT.Network.genuineOrbit_unique`);
* `N.persistenceConjectureStrong_of_weaklyReversible_of_bounded`: the **strong persistence
  conjecture in the bounded case** for weakly reversible networks;
* `N.boundaryOmegaExcluded_of_weaklyReversible`: the **omega-limit form without the
  critical-siphon hypothesis** — every omega-limit point of a bounded genuine mass-action orbit
  of a weakly reversible network is strictly positive;
* `N.positiveOmegaPointForRates_of_weaklyReversible_of_bounded`: the same conclusion in the
  repository's repaired omega-point API `N.PositiveOmegaPointForRates`;
* `N.weaklyReversible_forward_floor_varK_of_bounded` and
  `N.weaklyReversible_confined_varK_of_bounded`: the **tempered-rate (Extended) bounded case**,
  including the compact-confinement certificate for a time-varying rate vector;
* `CRNT.Network.BoundedPersistenceFakeFlow`: a self-contained counterexample showing that the
  orbit hypothesis of the omega-limit theorem cannot be dropped.

## A remark on `N.BoundaryOmegaExcluded`

The omega-limit theorem of this module carries the hypothesis that the orbit through `x₀` is a
genuine mass-action solution.  That hypothesis is *essential*: a contracting flow that is not a
mass-action solution can send a positive state to a boundary steady state.  The repository's own
counterexample (`CRNT.Examples.OmegaPointFakeFlow.gacN_not_boundaryOmegaExcluded`, on the weakly
reversible, complex-balanced network `2A ⇌ A + B`) refutes the unrestricted predicate
`N.BoundaryOmegaExcluded`; this module reproduces the phenomenon on the one-species network
`A ⇌ 2A` in `CRNT.Network.BoundedPersistenceFakeFlow`, where the weak reversibility of the
network is machine-checked.  The repaired predicate `N.PositiveOmegaPointForRates`
(`CRNT/Dynamics/GlobalAttractorTheorem.lean`) carries the same orbit premise, and this module
proves it for weakly reversible networks in the bounded case.

## What remains open

The **unbounded case** of the persistence conjecture for weakly reversible networks with three or
more species and no strictly positive conservation law is **open in the literature** (Craciun's
Persistence Conjecture) and is **not** claimed here.  What is proved here is the bounded case,
in its strong (compact-confinement) form, its omega-limit form, and its tempered-rate form.

Note also that the *unrestricted* strong conjecture `N.PersistenceConjectureStrong` for arbitrary
weakly reversible networks is at least as strong as the classical (open) persistence conjecture,
because `N.PersistentFrom` implies the classical uniform positivity; the version proved here
therefore carries the boundedness hypothesis `N.BoundedPositiveSolutions`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators NNReal ENNReal Topology Classical
open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The bounded-case hypothesis -/

/-- **Bounded positive solutions.**  Every forward mass-action solution that starts at a strictly
positive state is bounded above by a constant that depends only on the initial state and on the
rate constants.  This is the "bounded case" hypothesis of the persistence conjecture, stated at
the level of *solutions* (the repository's flow-level version is
`N.StructurallyBoundedPositiveTrajectories`). -/
def BoundedPositiveSolutions (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ x₀ : Concentration S, x₀.Positive → ∃ M : ℝ,
    ∀ (Γ : ℝ → Concentration S), Γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ M

omit [DecidableEq S] in
/-- A compact set of concentrations is bounded above, coordinate by coordinate. -/
theorem compact_concentration_bddAbove {K : Set (Concentration S)} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ y ∈ K, ∀ s, y s ≤ M := by
  have hb : ∀ s : S, ∃ M : ℝ, ∀ y ∈ K, y s ≤ M := fun s => by
    obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_apply s).continuousOn
    exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
  choose Mf hMf using hb
  by_cases hS : Nonempty S
  · refine ⟨Finset.univ.sup' Finset.univ_nonempty Mf, fun y hy s => ?_⟩
    exact (hMf s y hy).trans (Finset.le_sup' Mf (Finset.mem_univ s))
  · exact ⟨0, fun y _ s => absurd ⟨s⟩ hS⟩

/-! ### The bounded case: a trajectory is confined to a compact positive box -/

/-- **The bounded case, trajectory form.**  A bounded forward solution of a weakly reversible
network that starts positive stays in the compact box `[η, M]^S` of strictly positive
concentrations, where `η > 0` depends only on the initial state and on the bound `M`.  This is
the compact-confinement content of the bounded case of leaf D12. -/
theorem weaklyReversible_bounded_confined (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {γ : ℝ → Concentration S} {M : ℝ}
    (hγ0 : γ 0 = x₀)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hbdd : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ η : ℝ, 0 < η ∧ ∀ t, 0 ≤ t → γ t ∈ Set.univ.pi (fun _ => Set.Icc η M) := by
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ M
  refine ⟨η, hη, fun t ht => ?_⟩
  exact Set.mem_pi.2 fun s _ => ⟨hfloor γ hγ0 hsol hbdd t ht s, hbdd t ht s⟩

/-! ### The bounded case: the strong (compact-confinement) certificate -/

/-- **The strong (compact-confinement) bounded case.**  If every forward solution of a weakly
reversible network that starts at the positive state `x₀` is bounded above, then the network is
*persistently attracting* from `x₀` in the repository's strong sense: there is a compact box
`[η, M]^S` of strictly positive concentrations that contains every such solution for all forward
times, and whose lower face `η` stays away from the boundary of the orthant.  The box is the one
built in `CRNT.Network.weaklyReversible_conservative_persistentFrom`, with the conservation-law
upper bound replaced by the boundedness hypothesis. -/
theorem weaklyReversible_persistentFrom_of_bounded (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hbdd : N.BoundedPositiveSolutions κ) : N.PersistentFrom κ x₀ := by
  obtain ⟨M, hM⟩ := hbdd x₀ hx₀
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ M
  refine ⟨Set.univ.pi fun _ => Set.Icc η M, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1,
    fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hM Γ hΓ0 hΓd) t ht s, hM Γ hΓ0 hΓd t ht s⟩

/-- **The strong (compact-confinement) bounded case, from one bounded trajectory.**  Suppose the
network has a positive complex-balanced reference `x*`, so that all genuine mass-action solutions
from a given positive start coincide (`CRNT.Network.genuineOrbit_unique`), and suppose that *one*
forward solution from `x₀` is bounded above by `M`.  Then every forward solution from `x₀` is that
solution, hence bounded, and the compact-confinement certificate `N.PersistentFrom κ x₀` follows.

The uniqueness input is needed because `N.PersistentFrom` quantifies over *all* solutions from
`x₀`; the boundedness of a single trajectory does not by itself bound the others.  For a
deficiency-zero weakly reversible network the reference `x*` exists
(`CRNT.Network.exists_isComplexBalanced`). -/
theorem weaklyReversible_persistentFrom_of_boundedSolution (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx₀ : x₀.Positive)
    {γ : ℝ → Concentration S} {M : ℝ}
    (hγ0 : γ 0 = x₀)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hbdd : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M) :
    N.PersistentFrom κ x₀ := by
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ M
  refine ⟨Set.univ.pi fun _ => Set.Icc η M, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1,
    fun Γ hΓ0 hΓd t ht => ?_⟩
  have heq : Γ t = γ t :=
    N.genuineOrbit_unique κ hxs hcb hx₀ hΓ0 hγ0 hΓd hsol t ht
  intro s _
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hfloor γ hγ0 hsol hbdd t ht s
  · rw [heq]
    exact hbdd t ht s

/-- **The strong persistence conjecture in the bounded case.**  A weakly reversible network whose
positive solutions are all bounded above is persistently attracting in the compact-confinement
sense: for every rate vector and every positive initial state there is a compact set of strictly
positive concentrations absorbing every forward solution.  This is the strong (compact-interior)
form of Craciun's Persistence Conjecture, restricted to the bounded case. -/
theorem persistenceConjectureStrong_of_weaklyReversible_of_bounded (N : Network S)
    (hwr : N.WeaklyReversible)
    (hbdd : ∀ κ : N.RateConstants, N.BoundedPositiveSolutions κ) :
    N.PersistenceConjectureStrong := by
  intro _ κ x₀ hx₀
  exact N.weaklyReversible_persistentFrom_of_bounded (x₀ := x₀) κ hwr hx₀ (hbdd κ)

/-! ### The bounded case: the omega-limit form, without the critical-siphon hypothesis -/

/-- **The bounded case of the persistence conjecture at the omega-limit level, for weakly
reversible networks.**  The omega-limit set of a bounded *genuine* mass-action trajectory of a
weakly reversible network that starts positive stays in the strictly positive orthant, *without*
the hypothesis that the network has no critical siphon: the weakly reversible floor
(`CRNT.Network.weaklyReversible_forward_floor_uniform`) gives a uniform positive lower bound on
the trajectory, the bound survives in its closure, and `CRNT.Network.PersistentOrbit.omegaLimit_positive`
then makes every omega-limit point positive.

The hypothesis `horbit` — that the orbit through `x₀` solves the mass-action ODE — is essential
and cannot be dropped: the repository's counterexample
`CRNT.Examples.OmegaPointFakeFlow.gacN_not_boundaryOmegaExcluded` refutes the unrestricted
predicate `N.BoundaryOmegaExcluded` for a weakly reversible network.  The three omega-limit
hypotheses `hωnn`, `hgenω`, `hωaff` are kept for compatibility with `N.BoundaryOmegaExcluded`
and `N.PositiveOmegaPointForRates`; they are not needed for the conclusion. -/
theorem boundaryOmegaExcluded_of_weaklyReversible (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (horbit : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hbounded : ∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (_hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (_hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (_hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive := by
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  obtain ⟨M, hM⟩ := compact_concentration_bddAbove hKcpt
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    symm
    simpa [Flow.map_zero_apply] using h
  have hγx₀ : ∀ t : ℝ, 0 ≤ t → γ x₀ t = ϕ (Real.toNNReal t) x₀ := by
    intro t ht
    have h1 := hϕγ x₀ (Real.toNNReal t)
    rw [h1, Real.coe_toNNReal t ht]
  have hbd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ M := by
    intro t ht s
    have hmem : γ x₀ t ∈ K := by
      rw [hγx₀ t ht]
      exact hmaps (Real.toNNReal t)
    exact hM _ hmem s
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_uniform κ hwr hx₀ M
  have hpers : PersistentOrbit ϕ x₀ := by
    intro s
    refine ⟨η, hη, fun t => ?_⟩
    rw [hϕγ x₀ t]
    exact hfloor (γ x₀) hγ0 (fun τ hτ => horbit τ hτ) hbd (t : ℝ) (NNReal.coe_nonneg t) s
  exact PersistentOrbit.omegaLimit_positive hpers

/-- **The omega-limit form without the critical-siphon hypothesis, in the repository's repaired
API.**  `N.PositiveOmegaPointForRates` is the omega-point predicate with the orbit-ODE premise
that the unrestricted `N.BoundaryOmegaExcluded` lacks; for a weakly reversible network the
bounded case produces a positive omega-limit point (in fact all of them are positive). -/
theorem positiveOmegaPointForRates_of_weaklyReversible_of_bounded (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) : N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ horbit hbounded hωnn hgenω hωaff hx₀
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hbounded' : ∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K :=
    ⟨K, hKcpt, hmaps⟩
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hKcpt habs (Set.singleton_nonempty x₀)
  have hpos := N.boundaryOmegaExcluded_of_weaklyReversible κ hwr hϕγ horbit hbounded' hωnn hgenω
    hωaff hx₀ p hp
  exact ⟨p, hp, hpos⟩

/-! ### The orbit hypothesis is essential: a counterexample -/

/-
A self-contained counterexample showing that the orbit-ODE hypothesis of
`N.boundaryOmegaExcluded_of_weaklyReversible` cannot be dropped.

The network is `A ⇌ 2A` (one species, two reaction channels), which is weakly reversible: the
target of each reaction reaches its source.  The flow `ϕ t x = e^{-t} x` is a genuine
`Flow ℝ≥0`; its orbit through the positive state `x₀ = 1` is bounded, its omega-limit set is
`{0}`, the origin is a steady state of the mass-action field (so the omega-limit point does
generate a mass-action solution), and `0 - x₀` lies in the stoichiometric subspace.  All the
hypotheses of `N.BoundaryOmegaExcluded` therefore hold, while the conclusion fails: `0` is not
strictly positive.

What blocks the construction is precisely the orbit hypothesis: the fake orbit solves
`x' = -x`, not `x' = f(x)`.  The repository's own counterexample for the network `2A ⇌ A + B`
is `CRNT.Examples.OmegaPointFakeFlow.gacN_not_boundaryOmegaExcluded`.
-/
namespace BoundedPersistenceFakeFlow

open CRNT CRNT.Network

/-- The single species `A`. -/
abbrev Sp := Fin 1

instance : Fintype Sp := inferInstance
instance : DecidableEq Sp := inferInstance

/-- The complex `A`. -/
def cA : Complex Sp := fun _ => 1

/-- The complex `2A`. -/
def c2A : Complex Sp := fun _ => 2

/-- The two reaction channels: `A → 2A` and `2A → A`. -/
def rxn : Fin 2 → Reaction Sp
  | 0 => { source := cA, target := c2A }
  | 1 => { source := c2A, target := cA }

/-- The network `A ⇌ 2A`. -/
abbrev Net : Network Sp :=
  { R := Fin 2, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- Unit rate constants. -/
def kap : Net.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- **The network `A ⇌ 2A` is weakly reversible**: each reaction's target reaches its source. -/
theorem net_weaklyReversible : Net.WeaklyReversible := by
  intro r
  fin_cases r
  · exact Net.reaches_of_reaction 1
  · exact Net.reaches_of_reaction 0

/-- The mass-action field vanishes at the origin. -/
theorem field_zero : Net.massActionVectorField kap (0 : Concentration Sp) = 0 := by
  funext s
  fin_cases s
  simp [massActionVectorField_apply, massActionRate, Complex.massActionMonomial, kap,
    Net, rxn, cA, c2A, Fin.sum_univ_two]

/-- The positive initial state `x₀ = 1`. -/
def xz : Concentration Sp := fun _ => 1

/-- The contracting (fake) flow `ϕ t x = e^{-t} x`. -/
noncomputable def fakeFlow : Flow ℝ≥0 (Concentration Sp) where
  toFun := fun t x => fun s => Real.exp (-(t : ℝ)) * x s
  cont' := by
    apply continuous_pi
    intro s
    have h1 : Continuous fun a : ℝ≥0 × Concentration Sp => Real.exp (-(a.1 : ℝ)) :=
      Real.continuous_exp.comp (continuous_neg.comp (NNReal.continuous_coe.comp continuous_fst))
    have h2 : Continuous fun a : ℝ≥0 × Concentration Sp => a.2 s :=
      (continuous_apply s).comp continuous_snd
    exact h1.mul h2
  map_add' := by
    intro t₁ t₂ x
    funext s
    simp [NNReal.coe_add, Real.exp_add, mul_left_comm, mul_comm]
  map_zero' := by
    intro x
    funext s
    simp

theorem fakeFlow_apply (t : ℝ≥0) (x : Concentration Sp) : fakeFlow t x = fun s =>
    Real.exp (-(t : ℝ)) * x s := rfl

/-- The trajectory map of the fake flow. -/
noncomputable def gam : Concentration Sp → ℝ → Concentration Sp :=
  fun x t s => Real.exp (-t) * x s

private theorem coe_atTop : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
  NNReal.tendsto_coe_atTop.mpr tendsto_id

/-- The fake orbit converges to the origin. -/
theorem fake_tendsto : Tendsto (fun t : ℝ≥0 => fakeFlow t xz) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro s
  fin_cases s
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp coe_atTop
  have hm : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ)) * (xz 0)) atTop (𝓝 0) := by
    simpa using hexp.mul_const (xz 0)
  simpa [fakeFlow_apply, xz] using hm

/-- The fake orbit is bounded. -/
theorem fake_bounded :
    ∃ K : Set (Concentration Sp), IsCompact K ∧ ∀ t : ℝ≥0, fakeFlow t xz ∈ K := by
  refine ⟨(fun r : ℝ => (fun _ => r : Concentration Sp)) '' Set.Icc (0 : ℝ) 1, ?_, ?_⟩
  · refine isCompact_Icc.image ?_
    apply continuous_pi
    intro s
    exact continuous_id
  · intro t
    refine ⟨Real.exp (-(t : ℝ)), ⟨(Real.exp_pos _).le, ?_⟩, ?_⟩
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.coe_nonneg)
    · simp [fakeFlow_apply, xz]

/-- The omega-limit set of the fake orbit is `{0}`. -/
theorem fake_omega : omegaLimit atTop fakeFlow {xz} = {0} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hle : 𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop ≤ 𝓝 y ⊓ 𝓝 0 :=
      inf_le_inf_left _ fake_tendsto
    have hne : (𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop).NeBot := hy
    exact Set.mem_singleton_iff.mpr (eq_of_nhds_neBot (hne.mono hle))
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt]
    exact fake_tendsto.mapClusterPt

/-- The omega-limit point is nonnegative. -/
theorem hyp_nn : ∀ y ∈ omegaLimit atTop fakeFlow {xz}, (y : Concentration Sp).Nonnegative := by
  intro y hy
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  intro s
  fin_cases s
  simp

/-- The omega-limit point generates a mass-action solution. -/
theorem hyp_gen : ∀ y ∈ omegaLimit atTop fakeFlow {xz}, ∀ t : ℝ, 0 ≤ t →
    HasDerivAt (gam y) (Net.massActionVectorField kap (gam y t)) t := by
  intro y hy t _
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  have hconst : gam (0 : Concentration Sp) = fun _ => 0 := by
    funext u s; simp [gam]
  rw [hconst, field_zero]
  exact hasDerivAt_const t 0

/-- The omega-limit point stays in the stoichiometric class of `x₀`. -/
theorem hyp_aff : ∀ z ∈ omegaLimit atTop fakeFlow {xz},
    (z - xz : Concentration Sp) ∈ Net.stoichSubspace := by
  intro z hz
  rw [fake_omega, Set.mem_singleton_iff] at hz
  subst hz
  have hb : (0 - xz : Concentration Sp) = (-1 : ℝ) • Net.reactionVector 0 := by
    funext s
    fin_cases s
    simp [xz, rxn, cA, c2A, Network.reactionVector, Reaction.vector]
    norm_num
  rw [hb]
  exact Submodule.smul_mem _ _ (Net.reactionVector_mem_stoichSubspace 0)

/-- The initial state is positive. -/
theorem hyp_x0 : xz.Positive := by
  intro s
  fin_cases s
  simp [xz]

/-- **The unrestricted `N.BoundaryOmegaExcluded` fails for a weakly reversible network.** -/
theorem not_boundaryOmegaExcluded : ¬ Net.BoundaryOmegaExcluded kap := by
  intro h
  have hb : (0 : Concentration Sp) ∈ omegaLimit atTop fakeFlow {xz} := by
    rw [fake_omega]; exact Set.mem_singleton _
  have hpos := h (ϕ := fakeFlow) (γ := gam) (x₀ := xz) (fun _ _ => rfl) fake_bounded
    hyp_nn hyp_gen hyp_aff hyp_x0 (0 : Concentration Sp) hb
  exact absurd (hpos 0) (by simp)

/-- The refutation, with the weak reversibility of the counterexample network spelled out. -/
theorem not_boundaryOmegaExcluded_of_weaklyReversible :
    ¬ (Net.WeaklyReversible → Net.BoundaryOmegaExcluded kap) := by
  intro h
  exact not_boundaryOmegaExcluded (h net_weaklyReversible)

end BoundedPersistenceFakeFlow

/-! ### The bounded case: the tempered (variable-rate) form -/

/-- **The tempered-rate (Extended) persistence conjecture in the bounded case.**  With rate
constants varying in time but staying in `[ε, 1/ε]`, a bounded positive trajectory of a weakly
reversible network stays uniformly away from the boundary of the orthant.  This is the
variable-rate floor `CRNT.Network.weaklyReversible_forward_floor_varK`, applied to one
trajectory. -/
theorem weaklyReversible_forward_floor_varK_of_bounded (N : Network S) (κ : ℝ → N.RateConstants)
    (hwr : N.WeaklyReversible) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {γ : ℝ → Concentration S} {M : ℝ}
    (hγ0 : γ 0 = x₀)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t)
    (hbdd : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ η : ℝ, 0 < η ∧ ∀ t, 0 ≤ t → ∀ s, η ≤ γ t s := by
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_varK κ hwr hε hκ hx₀ M
  exact ⟨η, hη, fun t ht s => hfloor γ hγ0 hsol hbdd t ht s⟩

/-- **The tempered-rate bounded case in the strong (compact-confinement) form.**  With rate
constants varying in time inside `[ε, 1/ε]`, a weakly reversible network whose positive
solutions are all bounded above is persistently attracting: there is a compact box of strictly
positive concentrations containing every forward solution from `x₀`.  This is the
variable-rate analogue of `N.weaklyReversible_persistentFrom_of_bounded` and the counterpart of
`CRNT.Network.weaklyReversible_conservative_confined_varK`. -/
theorem weaklyReversible_confined_varK_of_bounded (N : Network S) (κ : ℝ → N.RateConstants)
    (hwr : N.WeaklyReversible) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) {M : ℝ}
    (hbdd : ∀ (Γ : ℝ → Concentration S), Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
      ∀ t, 0 ≤ t → ∀ s, Γ t s ≤ M) :
    ∃ K₀ : Set (Concentration S), IsCompact K₀ ∧ (∀ y ∈ K₀, y.Positive) ∧
      (∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∀ t, 0 ≤ t → Γ t ∈ K₀) := by
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_varK κ hwr hε hκ hx₀ M
  refine ⟨Set.univ.pi fun _ => Set.Icc η M, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1,
    fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hbdd Γ hΓ0 hΓd) t ht s, hbdd Γ hΓ0 hΓd t ht s⟩

end Network
end CRNT

/-! ### An instance: the reversible pair `A ⇌ B` -/

namespace CRNT.Examples.ReversiblePair

open CRNT CRNT.Network

/-- **The reversible pair `A ⇌ B` has bounded positive solutions.**  The strictly positive
conservation law `A + B` bounds every forward solution, so the bounded-case theorems of
`CRNT.Persistence.BoundedPersistence` apply to this network. -/
theorem boundedPositiveSolutions (κ : N.RateConstants) : N.BoundedPositiveSolutions κ := by
  intro x₀ hx₀
  have hwsp : N.IsStrictPSemiflow (fun _ => (1 : ℝ)) :=
    ⟨totalMass_conservationLaw, fun _ => one_pos⟩
  obtain ⟨B, hB⟩ := N.conservative_forward_bound (x₀ := x₀) κ hwsp hx₀
  exact ⟨B, hB⟩

/-- **The strong persistence conjecture in the bounded case holds for the reversible pair
`A ⇌ B`.**  The conservation law bounds every forward solution, so the compact-confinement
certificate of `CRNT.Network.weaklyReversible_persistentFrom_of_bounded` applies. -/
theorem persistenceConjectureStrong_of_bounded : N.PersistenceConjectureStrong :=
  fun _hwr κ x₀ hx₀ =>
    N.weaklyReversible_persistentFrom_of_bounded (x₀ := x₀) κ weaklyReversible hx₀
      (boundedPositiveSolutions κ)

end CRNT.Examples.ReversiblePair

/-! ### Axiom audit -/

#print axioms CRNT.Network.weaklyReversible_bounded_confined
#print axioms CRNT.Network.weaklyReversible_persistentFrom_of_bounded
#print axioms CRNT.Network.weaklyReversible_persistentFrom_of_boundedSolution
#print axioms CRNT.Network.persistenceConjectureStrong_of_weaklyReversible_of_bounded
#print axioms CRNT.Network.boundaryOmegaExcluded_of_weaklyReversible
#print axioms CRNT.Network.positiveOmegaPointForRates_of_weaklyReversible_of_bounded
#print axioms CRNT.Network.weaklyReversible_forward_floor_varK_of_bounded
#print axioms CRNT.Network.weaklyReversible_confined_varK_of_bounded
#print axioms CRNT.Network.BoundedPersistenceFakeFlow.not_boundaryOmegaExcluded
#print axioms CRNT.Network.BoundedPersistenceFakeFlow.not_boundaryOmegaExcluded_of_weaklyReversible
#print axioms CRNT.Examples.ReversiblePair.boundedPositiveSolutions
#print axioms CRNT.Examples.ReversiblePair.persistenceConjectureStrong_of_bounded
