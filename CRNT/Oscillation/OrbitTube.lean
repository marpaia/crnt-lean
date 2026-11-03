import CRNT.Oscillation.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Tubes around a periodic orbit

The compactness machinery behind the non-vacuous form of orbital asymptotic stability.

## Why this is a separate module

These results depend only on `CRNT.Oscillation.Basic` (for `PositivePeriodicOrbit` and
`GloballyAttractsSolutions`) plus Mathlib's thickening API. They were originally written inside
`CRNT/Oscillation/Floquet.lean`, which transitively imports `CRNT.Oscillation.MatrixCriteria` --
a module with five pre-existing elaboration errors unrelated to any of this. Splitting them out
means they can be, and are, machine-checked today rather than waiting on that repair.

## What is here

`FloquetOrbitalStabilityTarget` originally asked only for *some basin containing the orbit*. That
is satisfiable by taking the basin to be the orbit itself: forward uniqueness makes any solution
started on the orbit a phase shift of it, so the distance to a suitable phase is `0`. The statement
was therefore vacuous, and the fix is to demand a *tube* of positive radius.

That in turn needs a uniform radius, and the lemmas below supply one for free:

* `orbitTube_eq_thickening` -- the tube is `Metric.thickening δ (Set.range orbit)`;
* `continuous_orbit`, `isCompact_range_orbit` -- the geometric orbit is a continuous image of
  `[0, period]`, hence compact;
* `exists_orbitTube_subset_of_isOpen` -- compactness plus `IsCompact.exists_thickening_subset_open`
  puts a tube inside any open set containing the orbit;
* `exists_tube_attraction_of_open_basin` -- so an *open* attracting basin yields the tube form.

The remaining obligation in the Floquet route is therefore only that the basin produced by the
transverse-section argument is open. See `docs/math-review.md`.
-/

namespace CRNT
namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

namespace PositivePeriodicOrbit

/-- The open `δ`-tube around the geometric orbit: the set of states within `δ` of some phase.
Orbital asymptotic stability is attraction of every solution started in such a tube, so the tube
radius has to appear in the statement. -/
def orbitTube (P : N.PositivePeriodicOrbit κ) (δ : ℝ) : Set (Concentration S) :=
  {x | ∃ phase : ℝ, dist x (P.orbit phase) < δ}

/-- Every point of the orbit lies in every positive-radius tube around it. -/
theorem range_subset_orbitTube (P : N.PositivePeriodicOrbit κ) {δ : ℝ} (hδ : 0 < δ) :
    Set.range P.orbit ⊆ P.orbitTube δ := by
  rintro x ⟨t, rfl⟩
  exact ⟨t, by simpa using hδ⟩

/-- The tube is the metric thickening of the geometric orbit.  `Metric.mem_thickening_iff` is
stated exactly as "some point of the set is within `δ`", which is the definition of `orbitTube`
after unfolding `Set.range`. -/
theorem orbitTube_eq_thickening (P : N.PositivePeriodicOrbit κ) (δ : ℝ) :
    P.orbitTube δ = Metric.thickening δ (Set.range P.orbit) := by
  ext x
  rw [Metric.mem_thickening_iff]
  constructor
  · rintro ⟨phase, hphase⟩
    exact ⟨P.orbit phase, ⟨phase, rfl⟩, hphase⟩
  · rintro ⟨y, ⟨phase, rfl⟩, hy⟩
    exact ⟨phase, hy⟩

/-- The orbit map is continuous: each component is differentiable by `P.solution`, and a map into a
pi type over a finite index is continuous when every component is. -/
theorem continuous_orbit (P : N.PositivePeriodicOrbit κ) : Continuous P.orbit := by
  refine continuous_pi fun s => ?_
  have hdiff : Differentiable ℝ (fun t => P.orbit t s) :=
    fun t => (P.solution t s).differentiableAt
  exact hdiff.continuous

/-- **The geometric orbit is compact.**  By periodicity every value is attained on `[0, period]`,
so the range is the image of a compact interval under a continuous map.

This is the fact that makes a *uniform* tube radius available, and it is the only thing standing
between an open basin around the orbit and the `orbitTube` form of orbital stability. -/
theorem isCompact_range_orbit (P : N.PositivePeriodicOrbit κ) :
    IsCompact (Set.range P.orbit) := by
  have hsub : Set.range P.orbit ⊆ P.orbit '' Set.Icc 0 P.period := by
    rintro x ⟨t, rfl⟩
    obtain ⟨y, hy, hval⟩ := P.periodic.exists_mem_Ico₀ P.period_pos t
    exact ⟨y, ⟨hy.1, hy.2.le⟩, hval.symm⟩
  have hsup : P.orbit '' Set.Icc 0 P.period ⊆ Set.range P.orbit :=
    Set.image_subset_range _ _
  have heq : Set.range P.orbit = P.orbit '' Set.Icc 0 P.period :=
    Set.Subset.antisymm hsub hsup
  rw [heq]
  exact (isCompact_Icc).image P.continuous_orbit

/-- The geometric orbit is nonempty. -/
theorem range_orbit_nonempty (P : N.PositivePeriodicOrbit κ) :
    (Set.range P.orbit).Nonempty := ⟨P.orbit 0, 0, rfl⟩

/-- **Uniform tube radius from an open basin.**  If an open set contains the geometric orbit then
it contains a tube of positive radius around it.

This is the compactness step that reduces the Floquet tube obligation to "the basin produced by the
section argument contains an open set containing the orbit".  `IsCompact.exists_thickening_subset_open`
is the Mathlib statement; `orbitTube_eq_thickening` converts. -/
theorem exists_orbitTube_subset_of_isOpen (P : N.PositivePeriodicOrbit κ)
    {U : Set (Concentration S)} (hU : IsOpen U) (hsub : Set.range P.orbit ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ P.orbitTube δ ⊆ U := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    (P.isCompact_range_orbit).exists_thickening_subset_open hU hsub
  refine ⟨δ, hδpos, ?_⟩
  rw [orbitTube_eq_thickening]
  exact hδ

/-- **Tube attraction from basin attraction.**  Attraction on any set containing a tube gives
attraction on the tube, since `GloballyAttractsSolutions` is monotone in the basin (it is a
universal statement over points of the basin). -/
theorem GloballyAttractsSolutions.mono (P : N.PositivePeriodicOrbit κ)
    {basin basin' : Set (Concentration S)} (hsub : basin' ⊆ basin)
    (h : P.GloballyAttractsSolutions basin) : P.GloballyAttractsSolutions basin' :=
  fun x hx => h x (hsub hx)

/-- **The reduction.**  An open basin containing the orbit, on which the orbit attracts, yields the
tube form of orbital asymptotic stability.  So a proof of the Floquet theorem only has to produce
an *open* basin -- it need not chase a uniform radius by hand. -/
theorem exists_tube_attraction_of_open_basin (P : N.PositivePeriodicOrbit κ)
    {U : Set (Concentration S)} (hU : IsOpen U) (hsub : Set.range P.orbit ⊆ U)
    (hattr : P.GloballyAttractsSolutions U) :
    ∃ δ : ℝ, 0 < δ ∧ P.GloballyAttractsSolutions (P.orbitTube δ) := by
  obtain ⟨δ, hδpos, hδ⟩ := P.exists_orbitTube_subset_of_isOpen hU hsub
  exact ⟨δ, hδpos, GloballyAttractsSolutions.mono P hδ hattr⟩

end PositivePeriodicOrbit

end Network
end CRNT
