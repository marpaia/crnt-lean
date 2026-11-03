import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Dynamics.NoCriticalSiphonPersistence
import CRNT.Dynamics.GACSeparatingWitness
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Dynamics.GlobalPermanence

/-!
# Global persistence predicates

The original persistence API in `SingleLinkageGAC` deliberately packages a strong,
pointwise certificate:

`N.PersistentFrom κ x₀`

fixes one rate vector and one initial concentration.  Global CRNT statements quantify
above that level.  This module adds those quantifier layers without changing the existing
certificate, so downstream theorems can state honestly whether they apply to one orbit,
one kinetic parameterization, or the network structure itself.

The hierarchy is

* `PersistentForRates N κ`: every positive initial condition has `PersistentFrom κ`;
* `StructurallyPersistent N`: the previous property holds for every positive rate vector;
* `BoundaryOmegaExcluded N κ`: under the standard bounded/genuine-flow hypotheses used by
  the siphon machinery, every omega-limit point of every positive orbit is positive.

`BoundaryOmegaExcluded` is intentionally weaker than `PersistentForRates`: it captures the
standard no-boundary-omega-limit formulation of persistence and is exactly what the existing
critical-siphon theorem proves.  `PersistentFrom` additionally carries a compact positive
confining set and is the stronger certificate consumed by the existing GAC reduction.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Uniform persistence of one orbit.** Every species coordinate has a strictly positive
uniform lower bound for all forward time.  This is stronger than the omega-boundary formulation
of persistence used elsewhere in CRNT; the historical `PersistentOrbit` name is retained for
backward compatibility. -/
def PersistentOrbit (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) : Prop :=
  ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, ε ≤ ϕ t x₀ s

/-- Uniform persistence for one genuine mass-action flow.  The `Std` suffix is retained for
backward compatibility with the first global-persistence API. -/
def PersistentForFlowStd (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ →
    ∀ x₀ : Concentration S, x₀.Positive → PersistentOrbit ϕ x₀

/-- Uniform persistence for fixed rates, independent of the particular genuine flow construction. -/
def PersistentForRatesStd (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
    N.PersistentForFlowStd κ ϕ γ

/-- Structural **uniform** persistence: every positive rate vector gives a mass-action system
whose positive orbits have coordinate-wise positive lower bounds for all forward time. -/
def StructurallyPersistentStd (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.PersistentForRatesStd κ

/-- Preferred explicit name for `PersistentOrbit`. -/
abbrev UniformlyPersistentOrbit (S : Type) [DecidableEq S] [Fintype S] :=
  @PersistentOrbit S

/-- Preferred explicit name for `PersistentForFlowStd`. -/
abbrev UniformlyPersistentForFlow (N : Network S) := N.PersistentForFlowStd

/-- Preferred explicit name for `PersistentForRatesStd`. -/
abbrev UniformlyPersistentForRates (N : Network S) := N.PersistentForRatesStd

/-- Preferred explicit name for the stronger coordinate-lower-bound structural property. -/
abbrev StructurallyUniformlyPersistent (N : Network S) := N.StructurallyPersistentStd

/-- A compact positive set containing the whole genuine orbit gives standard persistence.  This
bridges the repository's strong `PersistentFrom` certificate to the usual CRNT predicate. -/
theorem persistentOrbit_of_persistentFrom (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hpf : N.PersistentFrom κ x₀) : PersistentOrbit ϕ x₀ := by
  obtain ⟨hγ0, hϕγ, hγd⟩ := hflow
  obtain ⟨K, hKcpt, hKpos, hconf⟩ := hpf
  have hx₀K : x₀ ∈ K := by
    have hmem := hconf (γ x₀) (hγ0 x₀) (hγd x₀) 0 le_rfl
    simpa [hγ0 x₀] using hmem
  have hKne : K.Nonempty := ⟨x₀, hx₀K⟩
  intro s
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcpt.exists_isMinOn hKne (continuous_apply s).continuousOn
  refine ⟨p s, hKpos p hpK s, ?_⟩
  intro t
  have hmem : γ x₀ (t : ℝ) ∈ K := hconf (γ x₀) (hγ0 x₀) (hγd x₀) (t : ℝ) t.coe_nonneg
  rw [hϕγ x₀ t]
  exact isMinOn_iff.mp hpmin _ hmem

/-- Orbit-level permanence plus genuine mass-action dynamics implies standard persistence of that
orbit.  The absorbing compact set supplies the tail lower bound; positivity and continuity of the
genuine trajectory on the finite initial interval supply the pre-tail lower bound. -/
theorem persistentOrbit_of_permanent (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hperm : Permanent ϕ x₀) : PersistentOrbit ϕ x₀ := by
  obtain ⟨hγ0, hϕγ, hγd⟩ := hflow
  obtain ⟨K, hKcpt, hKpos, v, hv, hvK⟩ := hperm
  obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hv
  have hatK : ϕ a x₀ ∈ K := by
    apply hvK
    exact subset_closure (Set.mem_image2_of_mem (ha a le_rfl) (Set.mem_singleton x₀))
  have hKne : K.Nonempty := ⟨ϕ a x₀, hatK⟩
  have hγpos : ∀ u : ℝ, 0 ≤ u → (γ x₀ u).Positive := by
    apply N.genuineOrbit_pos κ
    · simpa [hγ0 x₀] using hx₀
    · exact hγd x₀
  intro s
  -- Positive floor on the eventual compact absorbing set.
  obtain ⟨pK, hpKK, hpKmin⟩ :=
    hKcpt.exists_isMinOn hKne (continuous_apply s).continuousOn
  have heKpos : 0 < pK s := hKpos pK hpKK s
  -- Positive floor on the finite initial segment `[0,a]`.
  have hIne : (Set.Icc (0 : ℝ) (a : ℝ)).Nonempty :=
    ⟨0, le_rfl, a.coe_nonneg⟩
  have hγcont : ContinuousOn (γ x₀) (Set.Icc (0 : ℝ) (a : ℝ)) :=
    fun u hu => (hγd x₀ u hu.1).continuousAt.continuousWithinAt
  have hscont : ContinuousOn (fun u : ℝ => γ x₀ u s) (Set.Icc (0 : ℝ) (a : ℝ)) :=
    (continuous_apply s).comp_continuousOn hγcont
  obtain ⟨pI, hpII, hpImin⟩ := isCompact_Icc.exists_isMinOn hIne hscont
  have heIpos : 0 < γ x₀ pI s := hγpos pI hpII.1 s
  refine ⟨min (γ x₀ pI s) (pK s), lt_min heIpos heKpos, ?_⟩
  intro t
  by_cases hta : t ≤ a
  · have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) (a : ℝ) := by
      refine ⟨t.coe_nonneg, ?_⟩
      exact_mod_cast hta
    have hminI : γ x₀ pI s ≤ γ x₀ (t : ℝ) s :=
      isMinOn_iff.mp hpImin _ htI
    rw [hϕγ x₀ t]
    exact (min_le_left _ _).trans hminI
  · have hat : a ≤ t := le_of_lt (lt_of_not_ge hta)
    have htK : ϕ t x₀ ∈ K := by
      apply hvK
      exact subset_closure (Set.mem_image2_of_mem (ha t hat) (Set.mem_singleton x₀))
    exact (min_le_right _ _).trans (isMinOn_iff.mp hpKmin _ htK)

/-- Standard structural permanence implies standard structural persistence. -/
theorem StructurallyPermanent.toPersistentStd {N : Network S} (h : N.StructurallyPermanent) :
    N.StructurallyPersistentStd := by
  intro κ ϕ γ hflow x₀ hx₀
  exact N.persistentOrbit_of_permanent κ hflow hx₀
    (h.permanent_selfClass κ hflow hx₀)


/-- **Standard persistence excludes boundary omega-limit points.**  This direction needs no
boundedness or reaction-network structure: if every coordinate of an orbit is uniformly bounded
below by a positive constant, every point in the closure of every forward tail has the same lower
bound, hence every omega-limit point is positive. -/
theorem PersistentOrbit.omegaLimit_positive
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    (hpers : PersistentOrbit ϕ x₀) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive := by
  intro w hw s
  obtain ⟨ε, hεpos, hε⟩ := hpers s
  let A : Set (Concentration S) := {x | ε ≤ x s}
  have hAclosed : IsClosed A := by
    dsimp [A]
    exact isClosed_Ici.preimage (continuous_apply s)
  have horbitA : Set.image2 ϕ Set.univ {x₀} ⊆ A := by
    rintro y ⟨t, _ht, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact hε t
  have hclosureA : closure (Set.image2 ϕ Set.univ {x₀}) ⊆ A :=
    closure_minimal horbitA hAclosed
  have hwclosure : w ∈ closure (Set.image2 ϕ Set.univ {x₀}) :=
    omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem hw
  exact lt_of_lt_of_le hεpos (hclosureA hwclosure)


/-- A clean flow-level omega-boundary formulation aligned with the standard persistence API.
Unlike the older technical `BoundaryOmegaExcluded` interface below, this predicate assumes the
same genuine mass-action flow object as `PersistentForFlowStd` and carries only the precompactness
needed to talk usefully about omega limits. -/
def BoundaryOmegaExcludedForFlow (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ →
    ∀ x₀ : Concentration S, x₀.Positive →
      (∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
      ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive

/-- Standard persistence immediately implies omega-boundary exclusion for the same genuine flow. -/
theorem PersistentForFlowStd.toBoundaryOmegaExcludedForFlow {N : Network S}
    {κ : N.RateConstants} {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S}
    (h : N.PersistentForFlowStd κ ϕ γ) : N.BoundaryOmegaExcludedForFlow κ ϕ γ := by
  intro hflow x₀ hx₀ _hbounded w hw
  exact (h hflow x₀ hx₀).omegaLimit_positive w hw

/-- The clean omega-boundary property for every genuine flow at fixed rates. -/
def BoundaryOmegaExcludedForRatesStd (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
    N.BoundaryOmegaExcludedForFlow κ ϕ γ

/-- Structural clean omega-boundary exclusion, quantified over all positive rate vectors. -/
def StructurallyBoundaryOmegaExcludedStd (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.BoundaryOmegaExcludedForRatesStd κ

/-- Preferred CRNT-facing name for bounded-orbit omega persistence of one genuine flow. -/
abbrev OmegaPersistentForFlow (N : Network S) := N.BoundaryOmegaExcludedForFlow

/-- Preferred CRNT-facing name for bounded-orbit omega persistence at fixed rates. -/
abbrev OmegaPersistentForRates (N : Network S) := N.BoundaryOmegaExcludedForRatesStd

/-- Preferred CRNT-facing name for structural bounded-orbit omega persistence. -/
abbrev StructurallyOmegaPersistent (N : Network S) := N.StructurallyBoundaryOmegaExcludedStd

/-- Standard structural persistence implies the clean structural omega-boundary statement. -/
theorem StructurallyPersistentStd.toBoundaryOmegaExcludedStd {N : Network S}
    (h : N.StructurallyPersistentStd) : N.StructurallyBoundaryOmegaExcludedStd := by
  intro κ ϕ γ
  exact (h κ ϕ γ).toBoundaryOmegaExcludedForFlow

/-- Every positive initial condition is equipped with the existing strong persistence
certificate for the fixed rate vector `κ`. -/
def PersistentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ x₀ : Concentration S, x₀.Positive → N.PersistentFrom κ x₀

/-- A pointwise certificate follows immediately from persistence for fixed rates. -/
theorem PersistentForRates.persistentFrom {N : Network S} {κ : N.RateConstants}
    (h : N.PersistentForRates κ) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    N.PersistentFrom κ x₀ :=
  h x₀ hx₀

/-- Structural persistence at the level of `PersistentFrom`: every positive rate vector
and every positive initial condition has the existing compact-interior certificate. -/
def StructurallyPersistent (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.PersistentForRates κ

/-- A structural certificate specializes to any rate vector. -/
theorem StructurallyPersistent.forRates {N : Network S} (h : N.StructurallyPersistent)
    (κ : N.RateConstants) : N.PersistentForRates κ :=
  h κ

/-- A structural certificate specializes all the way to one positive initial condition. -/
theorem StructurallyPersistent.persistentFrom {N : Network S} (h : N.StructurallyPersistent)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    N.PersistentFrom κ x₀ :=
  h κ x₀ hx₀

/-- **Global GAC reduction from structural persistence.**  This is the existing
`gac_of_persistent` theorem with the pointwise certificate supplied by the new structural
quantifier layer. -/
theorem gac_of_structurallyPersistent (N : Network S) (hwr : N.WeaklyReversible)
    (hpers : N.StructurallyPersistent) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_persistent hwr κ hxs hcb hx0 hx0compat (hpers.persistentFrom κ hx0)


/-- **A fully structural strong-persistence theorem already available from the repository's
proved ingredients.**  Weak reversibility and deficiency zero produce, for every positive rate
vector and every positive initial condition, a positive complex-balanced equilibrium in the same
stoichiometric class.  The no-critical-siphon GAC/separating-witness theorem then upgrades that
orbit to the strong `PersistentFrom` certificate. -/
theorem structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (hncs : N.HasNoCriticalSiphon) :
    N.StructurallyPersistent := by
  intro κ x₀ hx₀
  obtain ⟨xref, hxrefpos, hxrefcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  obtain ⟨xstar, hxstarmem, hxstarcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxrefpos hxrefcb hx₀
  obtain ⟨hxstarcompat, hxstarpos⟩ := hxstarmem
  exact N.persistentFrom_of_hasNoCriticalSiphon hwr κ hncs hxstarpos hxstarcb hx₀ hxstarcompat

/-- The standard bounded-orbit/no-boundary-omega-limit claim, quantified over all flow data
that satisfy the hypotheses already used by `omegaLimit_positive_of_hasNoCriticalSiphon`.

This definition is deliberately explicit about boundedness, nonnegativity, genuine mass-action
omega-orbits, and stoichiometric affine invariance.  It therefore does not smuggle global
existence or dissipativity into the word "persistence". -/
def BoundaryOmegaExcluded (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive

/-- **No critical siphon gives a genuinely global boundary-exclusion theorem.**  The result
quantifies over every positive bounded mass-action orbit satisfying the standard flow facts;
there is no orbit-specific persistence assumption. -/
theorem boundaryOmegaExcluded_of_hasNoCriticalSiphon (N : Network S) (κ : N.RateConstants)
    (hncs : N.HasNoCriticalSiphon) : N.BoundaryOmegaExcluded κ := by
  intro ϕ γ x₀ hϕγ hbounded hωnn hgenω hωaff hx0 w hw
  obtain ⟨K, hK, hmaps⟩ := hbounded
  exact N.omegaLimit_positive_of_hasNoCriticalSiphon κ hϕγ hK hmaps hωnn hgenω hωaff
    hx0 hncs hw

/-- Structural boundary exclusion: the standard omega-limit persistence statement holds for
every positive rate vector. -/
def StructurallyBoundaryOmegaExcluded (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.BoundaryOmegaExcluded κ

/-- Networks with no critical siphon satisfy structural boundary exclusion for all rates. -/
theorem structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon (N : Network S)
    (hncs : N.HasNoCriticalSiphon) : N.StructurallyBoundaryOmegaExcluded :=
  fun κ => N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs

/-- The repository's strong structural certificate implies standard structural persistence. -/
theorem StructurallyPersistent.toStd {N : Network S} (h : N.StructurallyPersistent) :
    N.StructurallyPersistentStd := by
  intro κ ϕ γ hflow x₀ hx₀
  exact N.persistentOrbit_of_persistentFrom κ hflow hx₀ (h.persistentFrom κ hx₀)


end Network
end CRNT
