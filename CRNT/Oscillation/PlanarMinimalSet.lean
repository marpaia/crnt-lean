import CRNT.Oscillation.PlanarOmega
import CRNT.Oscillation.PlanarRecurrentSection
import CRNT.Dynamics.MinimalInvariant

/-!
# Minimal invariant sets inside planar omega-limit sets

The classical Poincare--Bendixson proof is most naturally run on a minimal compact invariant subset
of an equilibrium-free omega-limit set.  `CRNT.Dynamics.MinimalInvariant` already supplies this
Zorn-descent construction for arbitrary semiflows.  This module specializes it to the planar
oscillation stack and records the exact remaining geometric theorem at the minimal-set level.
-/

open Filter Set Topology
open scoped NNReal Topology

namespace CRNT

namespace Planar

/-- A minimal compact invariant subset of the trapped orbit's omega-limit set. -/
structure MinimalOmegaData {field : Phase2 → Phase2}
    (D : FlowTrappingData field) where
  carrier : Set Phase2
  subset_omega : carrier ⊆ D.omegaSet
  minimal : Minimal
    (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant D.flow C) carrier

namespace MinimalOmegaData

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}

/-- A minimal omega subset is nonempty. -/
theorem nonempty (M : MinimalOmegaData D) : M.carrier.Nonempty := M.minimal.1.1

/-- A minimal omega subset is compact. -/
theorem compact (M : MinimalOmegaData D) : IsCompact M.carrier := M.minimal.1.2.1

/-- A minimal omega subset is invariant. -/
theorem invariant (M : MinimalOmegaData D) : IsInvariant D.flow M.carrier :=
  M.minimal.1.2.2.2

/-- It contains no equilibrium because it lies inside the equilibrium-free omega-limit set. -/
theorem equilibriumFree (M : MinimalOmegaData D) :
    ∀ x ∈ M.carrier, field x ≠ 0 := by
  intro x hx
  exact D.omegaSet_equilibriumFree x (M.subset_omega hx)


/-- Every point of a minimal compact invariant omega subset has the whole minimal set as its own
omega-limit set.  This is the topological recurrence fact used by the classical planar proof. -/
theorem omegaLimit_self_eq_carrier (M : MinimalOmegaData D)
    {q : Phase2} (hq : q ∈ M.carrier) :
    omegaLimit Filter.atTop D.flow {q} = M.carrier := by
  have hqOmega : q ∈ D.omegaSet := M.subset_omega hq
  obtain ⟨hne, hcpt, hinv, hsub⟩ :=
    isCompact_isInvariant_nonempty_omegaLimit_of_mem
      D.flow D.seed D.compact D.absorbing hqOmega
  have hclosed : IsClosed (omegaLimit Filter.atTop D.flow {q}) :=
    isClosed_omegaLimit _ _ _
  have hprop :
      (omegaLimit Filter.atTop D.flow {q}).Nonempty ∧
      IsCompact (omegaLimit Filter.atTop D.flow {q}) ∧
      IsClosed (omegaLimit Filter.atTop D.flow {q}) ∧
      IsInvariant D.flow (omegaLimit Filter.atTop D.flow {q}) :=
    ⟨hne, hcpt, hclosed, hinv⟩
  have hsubM : omegaLimit Filter.atTop D.flow {q} ⊆ M.carrier := by
    -- The new omega-limit lies in the ambient omega-limit.  Intersecting with the minimal set and
    -- using invariance/minimality identifies it with `M`.  For points already in `M`, invariance of
    -- `M` gives the sharper containment directly.
    intro y hy
    have hforward : ∀ t : ℝ≥0, D.flow t q ∈ M.carrier :=
      fun t => M.invariant t hq
    have hclosure : closure (Set.image2 D.flow (Set.univ : Set ℝ≥0) {q}) ⊆ M.carrier := by
      apply closure_minimal
      · rintro y' ⟨t, _ht, q', hq', rfl⟩
        rw [Set.mem_singleton_iff.mp hq']
        exact hforward t
      · exact M.compact.isClosed
    exact (omegaLimit_subset_closure_image2 Filter.atTop D.flow {q}
      (Filter.univ_mem : (Set.univ : Set ℝ≥0) ∈ Filter.atTop) hy) |> hclosure
  exact M.minimal.eq_of_le hprop hsubM

/-- Hence every point of a minimal omega subset is recurrent: it belongs to its own omega-limit. -/
theorem recurrent (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier) :
    q ∈ omegaLimit Filter.atTop D.flow {q} := by
  rw [M.omegaLimit_self_eq_carrier hq]
  exact hq

/-- Every neighbourhood of a point in a minimal omega subset is revisited arbitrarily late by that
point's own forward orbit. -/
theorem frequently_returns_near (M : MinimalOmegaData D)
    {q : Phase2} (hq : q ∈ M.carrier) {U : Set Phase2} (hU : U ∈ 𝓝 q) :
    ∃ᶠ t : ℝ≥0 in Filter.atTop, D.flow t q ∈ U := by
  have hcluster : MapClusterPt q Filter.atTop (fun t : ℝ≥0 => D.flow t q) := by
    exact (mem_omegaLimit_singleton_iff_mapClusterPt
      (f := Filter.atTop) (ϕ := D.flow) q q).mp (M.recurrent hq)
  exact (mapClusterPt_iff_frequently.mp hcluster) U hU

/-- Constructive recurrence form: after any requested nonnegative time, the orbit returns to every
neighbourhood of `q`. -/
theorem exists_late_return (M : MinimalOmegaData D)
    {q : Phase2} (hq : q ∈ M.carrier) {U : Set Phase2} (hU : U ∈ 𝓝 q)
    (T : ℝ≥0) :
    ∃ t : ℝ≥0, T ≤ t ∧ D.flow t q ∈ U := by
  have hfreq := M.frequently_returns_near hq hU
  have htail : ∀ᶠ t : ℝ≥0 in Filter.atTop, T ≤ t := eventually_ge_atTop T
  obtain ⟨t, hmem, hT⟩ := (hfreq.and_eventually htail).exists
  exact ⟨t, hT, hmem⟩

end MinimalOmegaData

/-- Every certified trapped planar orbit contains a minimal compact invariant omega subset. -/
theorem FlowTrappingData.exists_minimalOmegaData
    {field : Phase2 → Phase2} (D : FlowTrappingData field) :
    Nonempty (MinimalOmegaData D) := by
  obtain ⟨M, hMomega, hMmin⟩ :=
    exists_minimal_compact_invariant_subOmega D.flow D.seed D.compact D.absorbing
  exact ⟨⟨M, hMomega, hMmin⟩⟩

/-- A recurrent transversal interval genuinely constructed **inside** a chosen minimal compact
invariant omega subset.  The embedded `OmegaRecurrentSectionData` already records that the relevant
section flow stays in the ambient omega-limit set; `interval_in_minimal` prevents the minimal-set
argument from becoming a vacuous unused parameter. -/
structure MinimalRecurrentSectionData {field : Phase2 → Phase2}
    {D : FlowTrappingData field} (M : MinimalOmegaData D)
    extends OmegaRecurrentSectionData D where
  interval_in_minimal :
    ∀ u ∈ Set.Icc returnInterval.left returnInterval.right,
      returnInterval.point u ∈ M.carrier

/-- The sharp geometric residue of the Poincare--Bendixson argument: an equilibrium-free minimal
compact invariant subset of a `C¹` planar flow admits a recurrent transversal return interval lying
in that minimal set.

At this point compactness, invariance, nonemptiness, equilibrium exclusion, return-map fixed-point
existence, and rotation closure have all been removed from the frontier. -/
def MinimalSetRecurrentSectionTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D),
    ContDiff ℝ 1 field → Nonempty (MinimalRecurrentSectionData M)

/-- The minimal-set recurrent-section theorem implies the stronger recurrent-section construction
needed by the public Poincare--Bendixson target. -/
theorem omegaRecurrentSection_of_minimalSet
    (hmin : MinimalSetRecurrentSectionTarget) :
    OmegaRecurrentSectionConstructionTarget := by
  intro field D hsmooth
  obtain ⟨M⟩ := D.exists_minimalOmegaData
  obtain ⟨R⟩ := hmin field D M hsmooth
  exact ⟨R.toOmegaRecurrentSectionData⟩

/-- Hence the minimal-set theorem closes the complete omega-limit Poincare--Bendixson interface. -/
theorem poincareBendixsonOmegaClassification_of_minimalSet
    (hmin : MinimalSetRecurrentSectionTarget) :
    PoincareBendixsonOmegaClassificationTarget :=
  poincareBendixsonOmegaClassification_of_omegaRecurrentSection
    (omegaRecurrentSection_of_minimalSet hmin)

end Planar

end CRNT
