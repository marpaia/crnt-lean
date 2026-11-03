import CRNT.Oscillation.PlanarPoincareBendixson
import CRNT.Oscillation.TrappingRegion
import CRNT.Oscillation.RankTwoPlanar
import CRNT.Dynamics.MinimalInvariant

/-!
# Conditional classification of minimal planar omega-limit subsets

Given a `PoincareBendixsonKernelBundle`, suitable trapping/regularity data, and
exclusion of equilibria, compact minimal invariant subsets are periodic orbit
sets. The kernel bundle is an explicit hypothesis and is not constructed here.
`IsNonregularMinimalSet` means failure of the local equilibrium/periodic-set
classification; it is not a definition of entropy, Devaney chaos, or horseshoes.
The Lotka instances remain conditional on the bundle when they invoke it.
The independent explicit Lotka periodic-orbit construction is elsewhere.
-/

namespace CRNT

namespace Planar

open Set Filter Topology
open scoped BigOperators NNReal Topology

variable {field : Phase2 → Phase2}

/-! ## Equilibrium and periodic minimal-set predicates -/

/-- **An equilibrium of the planar field.** -/
def IsEquilibrium (field : Phase2 → Phase2) (x : Phase2) : Prop :=
  field x = 0

/-- **A point of a periodic orbit.**  The point lies on the geometric image of a nonconstant
periodic trajectory of `field`. -/
def LiesOnPeriodicOrbit (field : Phase2 → Phase2) (x : Phase2) : Prop :=
  ∃ P : PeriodicTrajectory field, x ∈ P.orbitSet

/-- **A periodic orbit, as a set.** -/
def IsPeriodicOrbitSet (field : Phase2 → Phase2) (C : Set Phase2) : Prop :=
  ∃ P : PeriodicTrajectory field, C = P.orbitSet

/-- **An equilibrium, as a set.** -/
def IsEquilibriumSet (field : Phase2 → Phase2) (C : Set Phase2) : Prop :=
  ∃ x : Phase2, C = {x} ∧ field x = 0

/-- **A regular minimal invariant set.**

Such a set is either a single equilibrium or the geometric image of a periodic orbit: the two
kinds of set which the Poincaré–Bendixson classification allows for a *minimal* compact
invariant set of a planar flow. -/
def IsRegularMinimalSet (field : Phase2 → Phase2) (C : Set Phase2) : Prop :=
  IsEquilibriumSet field C ∨ IsPeriodicOrbitSet field C

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
def IsNonregularMinimalSet (field : Phase2 → Phase2) (C : Set Phase2) : Prop :=
  ¬ IsRegularMinimalSet field C

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
def HasNonregularMinimalSubset (field : Phase2 → Phase2) (ϕ : Flow ℝ≥0 Phase2) (Ω : Set Phase2) : Prop :=
  ∃ C ⊆ Ω, C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C ∧
    Minimal (fun E => E.Nonempty ∧ IsCompact E ∧ IsClosed E ∧ IsInvariant ϕ E) C ∧
    IsNonregularMinimalSet field C

/-- **A regular ω-limit set, pointwise.**  Every ω-limit point is an equilibrium of the field or
lies on a periodic orbit.  This is the pointwise reading of the Poincaré–Bendixson
classification. -/
def IsRegularOmegaSet (field : Phase2 → Phase2) (Ω : Set Phase2) : Prop :=
  ∀ x ∈ Ω, IsEquilibrium field x ∨ LiesOnPeriodicOrbit field x

/-! ## Elementary facts about periodic orbits -/

/-- **The geometric image of a periodic trajectory is the image of one period.**

The orbit of a periodic trajectory visits the same points in every period, so the range of the
trajectory is the image of the closed interval `[0, period]`. -/
theorem orbitSet_eq_image_Icc (P : PeriodicTrajectory field) :
    P.orbitSet = P.orbit '' Set.Icc 0 P.period := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨u, hu, k, hk⟩ :=
      Oscillation.exists_eq_add_int_mul P.period t P.period_pos
    have hshift := Oscillation.periodic_eq_int_mul (f := P.orbit) P.periodic u k
    refine ⟨u, hu, ?_⟩
    rw [hk]
    exact hshift.symm
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩

/-- **The geometric image of a periodic trajectory is compact.** -/
theorem isCompact_orbitSet (P : PeriodicTrajectory field) : IsCompact P.orbitSet := by
  rw [orbitSet_eq_image_Icc]
  exact IsCompact.image (isCompact_Icc) P.continuous_orbit

/-- **The geometric image of a periodic trajectory is closed.** -/
theorem isClosed_orbitSet (P : PeriodicTrajectory field) : IsClosed P.orbitSet :=
  isCompact_orbitSet P |>.isClosed

/-- **A closed interval of the real line is connected.** -/
theorem isConnected_Icc_real {a b : ℝ} (hab : a ≤ b) : IsConnected (Set.Icc a b) :=
  ⟨⟨a, left_mem_Icc.2 hab⟩, isPreconnected_Icc⟩

/-- **The geometric image of a periodic trajectory is connected.**  It is the continuous image of
the interval `[0, period]`. -/
theorem isConnected_orbitSet (P : PeriodicTrajectory field) : IsConnected P.orbitSet := by
  rw [orbitSet_eq_image_Icc]
  exact (isConnected_Icc_real P.period_pos.le).image P.orbit P.continuous_orbit.continuousOn

/-- **A connected set with two distinct points is infinite.**

This is the standard fact that a finite subset of a `T₁` space is discrete, so a finite
connected set cannot have two distinct points: the two points would separate it. -/
theorem IsPreconnected.not_finite_of_two_distinct {α : Type*} [TopologicalSpace α] [T1Space α]
    {s : Set α} (h : IsPreconnected s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
    ¬ s.Finite := by
  intro hf
  have hsa_fin : (s \ {a}).Finite := Set.Finite.subset hf Set.sdiff_subset
  have huopen : IsOpen ((s \ {a})ᶜ : Set α) := hsa_fin.isClosed.isOpen_compl
  have hvopen : IsOpen ({a}ᶜ : Set α) := isClosed_singleton.isOpen_compl
  have ha_mem : a ∈ (s \ {a})ᶜ := by
    refine (Set.mem_compl_iff (s \ {a}) a).mpr ?_
    intro hmem
    exact hmem.2 (Set.mem_singleton_iff.2 rfl)
  have hb_mem : b ∈ ({a} : Set α)ᶜ := by
    refine (Set.mem_compl_iff ({a} : Set α) b).mpr ?_
    intro hmem
    exact hne hmem.symm
  have hsub : s ⊆ (s \ {a})ᶜ ∪ {a}ᶜ := by
    intro z hz
    by_cases hza : z = a
    · refine Or.inl ?_
      refine (Set.mem_compl_iff (s \ {a}) z).mpr ?_
      intro hmem
      exact hmem.2 hza
    · refine Or.inr ?_
      refine (Set.mem_compl_iff ({a} : Set α) z).mpr ?_
      intro hmem
      exact hza hmem
  have hempty : s ∩ ((s \ {a})ᶜ ∩ {a}ᶜ) = ∅ := by
    ext z
    constructor
    · rintro ⟨hz, hz2, hz3⟩
      have hza : z = a := by
        by_contra hcon
        exact (Set.mem_compl_iff (s \ {a}) z).mp hz2 (Set.mem_sdiff_of_mem hz hcon)
      have hne' : z ≠ a := fun h =>
        (Set.mem_compl_iff ({a} : Set α) z).mp hz3 (Set.mem_singleton_iff.2 h)
      exact hne' hza
    · rintro hz
      exact absurd hz (by simp)
  have hne : (s ∩ ((s \ {a})ᶜ ∩ {a}ᶜ)).Nonempty :=
    h _ _ huopen hvopen hsub ⟨a, ha, ha_mem⟩ ⟨b, hb, hb_mem⟩
  rw [hempty] at hne
  exact Set.not_nonempty_empty hne

/-- **A nonconstant periodic trajectory has infinitely many distinct points.**

The geometric image of a periodic trajectory is connected (it is the image of an interval) and
it has two distinct points (the trajectory is nonconstant); a connected set with two distinct
points cannot be finite. -/
theorem orbitSet_infinite_of_nonconstant (P : PeriodicTrajectory field) : P.orbitSet.Infinite := by
  obtain ⟨t, ht⟩ := P.nonconstant
  exact IsPreconnected.not_finite_of_two_distinct (isConnected_orbitSet P).2
    ⟨t, rfl⟩ ⟨0, rfl⟩ ht

/-! ## The flow through a point of a periodic orbit -/

/-- **The flow through a point of a periodic orbit runs along the orbit.**

The periodic trajectory `P.orbit` and the trajectory of the *flow* through the point `P.orbit s`
solve the same autonomous equation with the same initial value; by uniqueness of solutions
(`globalSolutionUnique_of_locallyLipschitz`, the `C¹` hypothesis) they coincide.  Hence the
forward orbit of `P.orbit s` is contained in the geometric image of the periodic trajectory. -/
theorem flow_eq_orbitShift_of_mem_orbitSet
    {D : FlowTrappingData field} (hsmooth : ContDiff ℝ 1 field)
    (P : PeriodicTrajectory field) (s : ℝ) (q : Phase2) (hq : q = P.orbit s) :
    ∀ t : ℝ≥0, D.flow t q = P.orbit (s + (t : ℝ)) := by
  intro t
  have huniq : GlobalSolutionUnique field :=
    globalSolutionUnique_of_locallyLipschitz hsmooth.locallyLipschitz
  have hshift : ∀ u : ℝ, HasDerivAt (fun v : ℝ => P.orbit (s + v)) (field (P.orbit (s + u))) u := by
    intro u
    have h := P.solution (s + u)
    have hsh : HasDerivAt (fun v : ℝ => s + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add s
    simpa [Function.comp_def, add_comm, mul_one] using h.scomp u hsh
  have hinit : D.trajectory q 0 = P.orbit (s + 0) := by
    rw [D.trajectory_zero, hq]
    simp
  have heq : D.trajectory q = fun u : ℝ => P.orbit (s + u) :=
    huniq (D.trajectory q) (fun u => P.orbit (s + u)) (D.trajectory_solution q) hshift hinit
  rw [D.flow_eq_trajectory q t]
  exact congrFun heq (t : ℝ)

/-! ## The core theorem: minimal invariant sets in the plane are periodic orbits -/

/-- **A minimal compact invariant subset of a planar ω-limit set is a periodic orbit.**

This is the "minimal set" form of the Poincaré–Bendixson theorem, and it is the sharpest form
which the repository's universal kernel yields.  The hypotheses are

* `K` — the universal planar kernel bundle
  (`CRNT.Planar.PoincareBendixsonKernelBundle`); this is where the *universal* inputs of
  leaf D18 live: the `C¹` dependence of the flow on the initial point, the Jordan separation
  theorem and the straight-edge local-side lemma;
* `D` — trapping data for the planar field: a genuine forward flow, a compact trapping region
  and an equilibrium-free region (so that the ω-limit set contains no equilibrium);
* `hsmooth` — the `C¹` regularity of the field;
* `C` — a nonempty compact closed invariant subset of the ω-limit set, minimal among such
  subsets.

The conclusion is that `C` is *exactly* the geometric image of a nonconstant periodic
trajectory of the field.  (The repository's `PoincareBendixsonOmegaClassificationTarget` only
produces a periodic orbit *inside* `C`; minimality is what identifies the two.) -/
theorem eq_orbitSet_of_minimal_invariant_subset
    (K : PoincareBendixsonKernelBundle) {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) {C : Set Phase2}
    (hCne : C.Nonempty) (hCcpt : IsCompact C) (hCcl : IsClosed C) (hCinv : IsInvariant D.flow C)
    (hCsub : C ⊆ D.omegaSet)
    (hCmin : Minimal (fun E => E.Nonempty ∧ IsCompact E ∧ IsClosed E ∧ IsInvariant D.flow E) C) :
    ∃ P : PeriodicTrajectory field, C = P.orbitSet := by
  -- The nonemptiness and compactness of `C` are the first two components of the minimality
  -- predicate; they are recorded as explicit hypotheses for readability.
  have _hne : C.Nonempty := hCne
  have _hcpt : IsCompact C := hCcpt
  -- The kernel produces a periodic orbit contained in `C`.
  let M : MinimalOmegaData D := ⟨C, hCsub, hCmin⟩
  obtain ⟨P, hP⟩ := K.minimalPeriodicOrbit field D M hsmooth
  have hP' : P.orbitSet ⊆ C := by
    refine hP.trans ?_
    rintro x hx
    exact hx
  -- The point `P.orbit 0` belongs to `C`, hence to the ω-limit set.
  have hq : P.orbit 0 ∈ C := hP ⟨0, rfl⟩
  have hqΩ : P.orbit 0 ∈ D.omegaSet := hCsub hq
  -- The flow through `P.orbit 0` runs along the periodic orbit.
  have hflow : ∀ t : ℝ≥0, D.flow t (P.orbit 0) = P.orbit ((0 : ℝ) + (t : ℝ)) :=
    flow_eq_orbitShift_of_mem_orbitSet hsmooth P 0 (P.orbit 0) rfl
  have hforw : Set.image2 D.flow (Set.univ : Set ℝ≥0) {P.orbit 0} ⊆ P.orbitSet := by
    rintro y ⟨t, _, x, hx, rfl⟩
    rw [Set.mem_singleton_iff.mp hx]
    rw [hflow t]
    exact ⟨0 + (t : ℝ), by simp⟩
  -- The ω-limit set of `P.orbit 0` is contained in the periodic orbit ...
  have hω_Γ : omegaLimit Filter.atTop D.flow {P.orbit 0} ⊆ P.orbitSet := by
    refine (omegaLimit_subset_closure_image2 Filter.atTop D.flow {P.orbit 0}
      (Filter.univ_mem : (Set.univ : Set ℝ≥0) ∈ (Filter.atTop : Filter ℝ≥0))).trans ?_
    exact closure_minimal hforw (isClosed_orbitSet P)
  -- ... and in `C`.
  have hω_C : omegaLimit Filter.atTop D.flow {P.orbit 0} ⊆ C := by
    refine (omegaLimit_subset_closure_image2 Filter.atTop D.flow {P.orbit 0}
      (Filter.univ_mem : (Set.univ : Set ℝ≥0) ∈ (Filter.atTop : Filter ℝ≥0))).trans ?_
    refine closure_minimal ?_ hCcl
    rintro y ⟨t, _, x, hx, rfl⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact hCinv t hq
  -- The ω-limit set of `P.orbit 0` is a nonempty compact closed invariant set.
  obtain ⟨hωne, hωcpt, hωinv, _⟩ :=
    isCompact_isInvariant_nonempty_omegaLimit_of_mem D.flow D.seed D.compact D.absorbing hqΩ
  have hωcl : IsClosed (omegaLimit Filter.atTop D.flow {P.orbit 0}) :=
    isClosed_omegaLimit _ _ _
  -- Minimality of `C` therefore identifies it with that ω-limit set ...
  have hprop : (omegaLimit Filter.atTop D.flow {P.orbit 0}).Nonempty ∧
      IsCompact (omegaLimit Filter.atTop D.flow {P.orbit 0}) ∧
      IsClosed (omegaLimit Filter.atTop D.flow {P.orbit 0}) ∧
      IsInvariant D.flow (omegaLimit Filter.atTop D.flow {P.orbit 0}) :=
    ⟨hωne, hωcpt, hωcl, hωinv⟩
  have hEq : omegaLimit Filter.atTop D.flow {P.orbit 0} = C :=
    hCmin.eq_of_le hprop hω_C
  -- ... which is contained in the periodic orbit.  Hence `C` is the periodic orbit.
  refine ⟨P, ?_⟩
  have hC_Γ : C ⊆ P.orbitSet := by
    rw [← hEq]
    exact hω_Γ
  exact le_antisymm hC_Γ hP'

/-! ## "No chaos in the plane" -/

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem omegaSet_no_nonregular_minimal_subset (K : PoincareBendixsonKernelBundle) {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) :
    ¬ HasNonregularMinimalSubset field D.flow D.omegaSet := by
  rintro ⟨C, hCsub, hCne, hCcpt, hCcl, hCinv, hCmin, hchaos⟩
  obtain ⟨P, hP⟩ :=
    eq_orbitSet_of_minimal_invariant_subset K D hsmooth hCne hCcpt hCcl hCinv hCsub hCmin
  exact hchaos (Or.inr ⟨P, hP⟩)

/-- **The ω-limit set of a trapped planar `C¹` orbit contains a nonconstant periodic orbit.**

This is the repository's Poincaré–Bendixson omega-limit classification. -/
theorem omegaSet_contains_periodicOrbit (K : PoincareBendixsonKernelBundle)
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) :
    ∃ P : PeriodicTrajectory field, P.orbitSet ⊆ D.omegaSet :=
  K.omegaClassification field D hsmooth

/-- **The ω-limit set of a trapped planar `C¹` orbit is infinite.**

A finite ω-limit set would be a finite collection of equilibria; but the trapping region is
equilibrium-free, and the ω-limit set contains a periodic orbit, which has infinitely many
points.  This is the "the only way to have an infinite ω-limit set is a periodic orbit" half of
the classification which the repository's kernel supports. -/
theorem omegaSet_infinite (K : PoincareBendixsonKernelBundle) {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) : D.omegaSet.Infinite := by
  obtain ⟨P, hP⟩ := omegaSet_contains_periodicOrbit K D hsmooth
  exact (orbitSet_infinite_of_nonconstant P).mono hP

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem omegaSet_has_periodic_structure (K : PoincareBendixsonKernelBundle)
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) :
    D.omegaSet.Infinite ∧ (∃ P : PeriodicTrajectory field, P.orbitSet ⊆ D.omegaSet) ∧
      (∀ C ⊆ D.omegaSet, C.Nonempty → IsCompact C → IsClosed C → IsInvariant D.flow C →
        Minimal (fun E => E.Nonempty ∧ IsCompact E ∧ IsClosed E ∧ IsInvariant D.flow E) C →
        ∃ P : PeriodicTrajectory field, C = P.orbitSet) := by
  refine ⟨omegaSet_infinite K D hsmooth, omegaSet_contains_periodicOrbit K D hsmooth, ?_⟩
  intro C hCsub hCne hCcpt hCcl hCinv hCmin
  exact eq_orbitSet_of_minimal_invariant_subset K D hsmooth hCne hCcpt hCcl hCinv hCsub hCmin


/-- **A point of a minimal invariant subset of the ω-limit set lies on a periodic orbit.**

This is the pointwise reading of the Poincaré–Bendixson classification, restricted to the
minimal invariant subsets of the ω-limit set: the point lies on the geometric image of a
nonconstant periodic trajectory of the field. -/
theorem exists_periodicOrbit_through_of_minimal_subset
    (K : PoincareBendixsonKernelBundle) {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field) (M : MinimalOmegaData D) {x : Phase2} (hx : x ∈ M.carrier) :
    ∃ P : PeriodicTrajectory field, x ∈ P.orbitSet := by
  obtain ⟨P, hP⟩ := eq_orbitSet_of_minimal_invariant_subset K D hsmooth M.nonempty M.compact
    M.minimal.1.2.2.1 M.invariant M.subset_omega M.minimal
  refine ⟨P, ?_⟩
  rw [← hP]
  exact hx

/-- **The pointwise reading of the classification, when the ω-limit set is itself minimal.**

Every point of the ω-limit set is then an equilibrium or lies on a periodic orbit; since the
trapping region is equilibrium-free, every point in fact lies on a periodic orbit. -/
theorem isRegularOmegaSet_of_minimal_subset
    (K : PoincareBendixsonKernelBundle) {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field) (M : MinimalOmegaData D) (hM : M.carrier = D.omegaSet) :
    IsRegularOmegaSet field D.omegaSet := by
  intro x hx
  have hxM : x ∈ M.carrier := by
    rw [hM]
    exact hx
  obtain ⟨P, hP⟩ := exists_periodicOrbit_through_of_minimal_subset K D hsmooth M hxM
  exact Or.inr ⟨P, hP⟩

/-- **The ω-limit set of a trapped planar orbit contains no equilibrium.**

The trapping region is equilibrium-free, and the ω-limit set lies inside it.  This is the
"equilibrium or periodic orbit" half of the classical dichotomy: in the equilibrium-free
setting of `CRNT.Planar.FlowTrappingData` only the periodic-orbit alternative survives. -/
theorem omegaSet_equilibriumFree {field : Phase2 → Phase2} (D : FlowTrappingData field) :
    ∀ x ∈ D.omegaSet, field x ≠ 0 :=
  D.omegaSet_equilibriumFree

end Planar

/-! ## Application to mass-action systems -/

namespace Oscillation

open Set Filter Topology
open scoped BigOperators NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem rankTwo_omegaSet_no_nonregular_minimal_subset
    (K : Planar.PoincareBendixsonKernelBundle) (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (D : Planar.FlowTrappingData (N.rankTwoReducedField h κ x₀))
    (hsmooth : ContDiff ℝ 1 (N.rankTwoReducedField h κ x₀)) :
    ¬ Planar.HasNonregularMinimalSubset (N.rankTwoReducedField h κ x₀) D.flow D.omegaSet :=
  Planar.omegaSet_no_nonregular_minimal_subset K D hsmooth

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem rankTwo_omegaSet_has_periodic_structure
    (K : Planar.PoincareBendixsonKernelBundle) (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (D : Planar.FlowTrappingData (N.rankTwoReducedField h κ x₀))
    (hsmooth : ContDiff ℝ 1 (N.rankTwoReducedField h κ x₀)) :
    D.omegaSet.Infinite ∧ (∃ P : PeriodicTrajectory (N.rankTwoReducedField h κ x₀),
      P.orbitSet ⊆ D.omegaSet) ∧
      (∀ C ⊆ D.omegaSet, C.Nonempty → IsCompact C → IsClosed C → IsInvariant D.flow C →
        Minimal (fun E => E.Nonempty ∧ IsCompact E ∧ IsClosed E ∧ IsInvariant D.flow E) C →
        ∃ P : PeriodicTrajectory (N.rankTwoReducedField h κ x₀), C = P.orbitSet) :=
  Planar.omegaSet_has_periodic_structure K D hsmooth

/-- **A rank-two mass-action network whose ω-limit set lies in the positive chart region has a
positive mass-action periodic orbit.**

This is the "the long-time behaviour of a planar mass-action network is a periodic orbit"
reading, in the network language: the periodic orbit of the *reduced planar field* produced by
the Poincaré–Bendixson classification lifts to a positive periodic orbit of the network
(`CRNT.Network.positivePeriodicOrbitOfRankTwoPlanar`). -/
theorem rankTwo_hasPositivePeriodicOrbit
    (K : Planar.PoincareBendixsonKernelBundle) (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (D : Planar.FlowTrappingData (N.rankTwoReducedField h κ x₀))
    (hsmooth : ContDiff ℝ 1 (N.rankTwoReducedField h κ x₀))
    (hpositive : D.omegaSet ⊆ N.rankTwoPositiveRegion h x₀) :
    N.HasPositivePeriodicOrbit κ :=
  N.hasPositivePeriodicOrbit_of_rankTwo_poincareBendixson K.omegaClassification h κ x₀ D hsmooth
    hpositive

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem rankTwo_no_nonregular_minimal_subset (K : Planar.PoincareBendixsonKernelBundle) (N : Network S)
    (h : N.stoichRank = 2) (κ : N.RateConstants) (x₀ : Concentration S)
    (D : Planar.FlowTrappingData (N.rankTwoReducedField h κ x₀))
    (hsmooth : ContDiff ℝ 1 (N.rankTwoReducedField h κ x₀)) :
    ¬ Planar.HasNonregularMinimalSubset (N.rankTwoReducedField h κ x₀) D.flow D.omegaSet :=
  rankTwo_omegaSet_no_nonregular_minimal_subset K N h κ x₀ D hsmooth

/-! ## The instance: the Lotka network -/

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem lotka_omegaSet_no_nonregular_minimal_subset (K : Planar.PoincareBendixsonKernelBundle)
    (κ : Examples.Lotka.N.RateConstants) (lo hi : ℝ)
    (D : Planar.FlowTrappingData (lotkaClampedField κ lo hi)) :
    ¬ Planar.HasNonregularMinimalSubset (lotkaClampedField κ lo hi) D.flow D.omegaSet :=
  Planar.omegaSet_no_nonregular_minimal_subset K D (contDiff_lotkaClampedField κ lo hi)

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem lotka_canonical_no_nonregular_minimal_subset
    (K : Planar.PoincareBendixsonKernelBundle) (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) :
    ∃ (lo hi : ℝ) (D : Planar.FlowTrappingData (lotkaClampedField κ lo hi)),
      ¬ Planar.HasNonregularMinimalSubset (lotkaClampedField κ lo hi) D.flow D.omegaSet := by
  -- the level set of the first integral through the canonical seed
  set c : ℝ := Examples.Lotka.firstIntegral κ (lotkaSeed κ) with hc
  have hp₀ : (lotkaSeed κ).Positive := lotkaSeed_pos κ h1 h2 h0
  have hp₀ne : lotkaSeed κ ≠ Examples.Lotka.equilibrium κ := lotkaSeed_ne_equilibrium κ h1 h2
  have hc' : Examples.Lotka.firstIntegral κ (Examples.Lotka.equilibrium κ) < c := by
    have h := Examples.Lotka.firstIntegral_gt_equilibrium κ h0 h1 h2 hp₀ hp₀ne
    simpa [c] using h
  -- a cut-off box containing the level set
  obtain ⟨δ, M, hδ, hbox⟩ := Examples.Lotka.sublevel_box κ h0 h1 h2 c
  have hδM : δ ≤ M := by
    have h := hbox (lotkaSeed κ) hp₀ (by simp [c]) Examples.Lotka.A
    linarith [h.1, h.2]
  set lo : ℝ := δ / 2 with lodef
  set hi : ℝ := M + 1 with hidef
  have hlo : 0 < lo := by positivity
  have hle : lo ≤ hi := by linarith
  have hK : ∀ x ∈ lotkaLevelSet κ c, ∀ s, lo < x s ∧ x s < hi := by
    intro x hx s
    have h := hbox x hx.1 hx.2.le s
    constructor <;> linarith
  -- the trapping data
  obtain ⟨D, _hDregion⟩ := exists_lotka_flowTrappingData κ h0 h1 h2 (lotkaSeed κ) hp₀ c
    (by simp [c]) hc' lo hi hlo hle hK
  exact ⟨lo, hi, D, lotka_omegaSet_no_nonregular_minimal_subset K κ lo hi D⟩

/-- Conditional equilibrium/periodic minimal-set classification. The kernel bundle
and trapping hypotheses are explicit; nonregularity uses the predicates in this module. -/
theorem lotka_longTimeBehaviour_is_periodicOrbit
    (K : Planar.PoincareBendixsonKernelBundle) (κ : Examples.Lotka.N.RateConstants)
    (h0 : 0 < κ.k Examples.Lotka.grow) (h1 : 0 < κ.k Examples.Lotka.prey)
    (h2 : 0 < κ.k Examples.Lotka.decay) :
    Examples.Lotka.N.HasPositivePeriodicOrbit κ ∧
      (∃ (lo hi : ℝ) (D : Planar.FlowTrappingData (lotkaClampedField κ lo hi)),
        ¬ Planar.HasNonregularMinimalSubset (lotkaClampedField κ lo hi) D.flow D.omegaSet) := by
  refine ⟨lotka_hasPositivePeriodicOrbit_of_trappingRegion K κ h0 h1 h2, ?_⟩
  exact lotka_canonical_no_nonregular_minimal_subset K κ h0 h1 h2

end Oscillation
end CRNT
