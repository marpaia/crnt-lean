import CRNT.Oscillation.Exclusion
import CRNT.Oscillation.KineticBasic
import CRNT.Multistationarity.StoichChart
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Low-rank global non-oscillation

Autonomous deterministic dynamics on a zero- or one-dimensional stoichiometric compatibility class
cannot carry a nonconstant periodic orbit.  Rank zero is already handled in `Exclusion`; this module
closes the rank-one case for mass action without appealing to deficiency or weak reversibility.

The rank-one argument is global:

1. project a putative periodic orbit through the stoichiometric chart onto its unique scalar
   coordinate;
2. Rolle's theorem gives a time at which that scalar velocity vanishes;
3. because the entire mass-action velocity lies in the one-dimensional stoichiometric subspace,
   zero projected velocity means the full velocity is zero;
4. mass-action fields are `C¹`, hence locally Lipschitz, so ODE uniqueness says a trajectory that
   reaches that equilibrium must be constant.

Thus every rank-at-most-one finite mass-action CRN is structurally non-oscillatory for every
positive rate vector.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace PositiveKineticPeriodicOrbit

variable {N : Network S} {K : N.Kinetics}

/-- **A positive periodic orbit under arbitrary admissible kinetics in stoichiometric rank one must
contain an equilibrium.**

This is the kinetics-independent geometric core of the rank-one theorem: only conservation of the
vector field in the stoichiometric subspace and differentiability of the supplied exact trajectory
are used.  Local Lipschitz regularity is needed only afterwards, to invoke uniqueness once the
trajectory reaches the equilibrium. -/
theorem exists_equilibrium_of_stoichRank_one (P : N.PositiveKineticPeriodicOrbit K)
    (h1 : N.stoichRank = 1) :
    ∃ t : ℝ, K.vectorField (P.trajectory.orbit t) = 0 := by
  let j0 : Fin N.stoichRank := ⟨0, by omega⟩
  let g : ℝ → ℝ := fun t => N.stoichProj (P.trajectory.orbit t) j0
  let g' : ℝ → ℝ := fun t => N.stoichProj (K.vectorField (P.trajectory.orbit t)) j0
  have hgderiv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
    intro t
    have hproj : HasDerivAt (fun u => N.stoichProj (P.trajectory.orbit u))
        (N.stoichProj (K.vectorField (P.trajectory.orbit t))) t := by
      have hcomp := N.stoichProj.hasFDerivAt.comp_hasDerivAt t (P.trajectory.solution t)
      simpa [Function.comp_def] using hcomp
    simpa [g, g'] using (hasDerivAt_pi.mp hproj) j0
  have hgcont : Continuous g :=
    continuous_iff_continuousAt.2 fun t => (hgderiv t).continuousAt
  have hgend : g 0 = g P.trajectory.period := by
    exact congrArg (fun x => N.stoichProj x j0) P.trajectory.closes.symm
  obtain ⟨c, _, hgc⟩ := exists_hasDerivAt_eq_zero P.trajectory.period_pos hgcont.continuousOn hgend
    (fun t _ => hgderiv t)
  have hprojzero : N.stoichProj (K.vectorField (P.trajectory.orbit c)) = 0 := by
    funext j
    have hj : j = j0 := by
      apply Fin.ext
      omega
    rw [hj]
    simpa [g'] using hgc
  have hmem : K.vectorField (P.trajectory.orbit c) ∈ N.stoichSubspace :=
    K.vectorField_mem_stoichSubspace (P.trajectory.orbit c)
  have hrecover := N.stoichChart_stoichProj hmem
  refine ⟨c, ?_⟩
  calc
    K.vectorField (P.trajectory.orbit c)
        = N.stoichChart (N.stoichProj (K.vectorField (P.trajectory.orbit c))) := hrecover.symm
    _ = N.stoichChart 0 := by rw [hprojzero]
    _ = 0 := map_zero N.stoichChart

end PositiveKineticPeriodicOrbit

namespace PositivePeriodicOrbit

variable {N : Network S} {κ : N.RateConstants}

/-- Mass-action specialization of the kinetics-independent rank-one equilibrium lemma. -/
theorem exists_equilibrium_of_stoichRank_one (P : N.PositivePeriodicOrbit κ)
    (h1 : N.stoichRank = 1) :
    ∃ t : ℝ, N.massActionVectorField κ (P.orbit t) = 0 := by
  have h := P.toKinetic.exists_equilibrium_of_stoichRank_one h1
  simpa [N.massActionKinetics_vectorField κ, PositivePeriodicOrbit.toKinetic,
    PositivePeriodicOrbit.toPeriodicTrajectory] using h

end PositivePeriodicOrbit

/-- **Rank-one exclusion for a fixed admissible kinetics.**  Local Lipschitz regularity is the
only kinetic regularity assumption needed beyond the base `Kinetics` axioms. -/
theorem not_hasPositiveKineticPeriodicOrbit_of_stoichRank_one
    (N : Network S) (h1 : N.stoichRank = 1) (K : N.Kinetics)
    (hll : LocallyLipschitz K.vectorField) :
    ¬ N.HasPositiveKineticPeriodicOrbit K := by
  intro hperiodic
  obtain ⟨P⟩ := hperiodic
  obtain ⟨t, ht⟩ := P.exists_equilibrium_of_stoichRank_one h1
  exact not_periodicTrajectory_of_equilibrium_of_locallyLipschitz P.trajectory hll ht

/-- **Rank-zero exclusion for arbitrary admissible kinetics.**  No regularity assumption is needed:
the vector field is identically zero. -/
theorem not_hasPositiveKineticPeriodicOrbit_of_stoichRank_zero
    (N : Network S) (h0 : N.stoichRank = 0) (K : N.Kinetics) :
    ¬ N.HasPositiveKineticPeriodicOrbit K := by
  intro hperiodic
  obtain ⟨P⟩ := hperiodic
  exact not_periodicTrajectory_of_field_eq_zero P.trajectory
    (K.vectorField_eq_zero_of_stoichRank_zero h0)

/-- **Rank-zero all-kinetics structural exclusion.**  Because every admissible kinetics has the
identically zero vector field on a zero-dimensional stoichiometric subspace, no regularity
assumption is needed to quantify over the entire `Kinetics` class. -/
theorem neverPositiveKineticPeriodic_of_stoichRank_zero
    (N : Network S) (h0 : N.stoichRank = 0) : N.NeverPositiveKineticPeriodic := by
  intro K
  exact N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_zero h0 K

/-- **Rank-at-most-one exclusion for one locally Lipschitz admissible kinetics.** -/
theorem not_hasPositiveKineticPeriodicOrbit_of_stoichRank_le_one
    (N : Network S) (h : N.stoichRank ≤ 1) (K : N.Kinetics)
    (hll : LocallyLipschitz K.vectorField) :
    ¬ N.HasPositiveKineticPeriodicOrbit K := by
  have hr : N.stoichRank = 0 ∨ N.stoichRank = 1 := by omega
  rcases hr with h0 | h1
  · exact N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_zero h0 K
  · exact N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_one h1 K hll

/-- If every admissible kinetics under consideration is locally Lipschitz, stoichiometric rank at
most one excludes periodic orbits over the entire admissible-kinetics class.  The regularity
hypothesis is explicit because the base `Kinetics` structure intentionally assumes monotonicity but
not continuity or ODE uniqueness. -/
theorem neverPositiveKineticPeriodic_of_stoichRank_le_one_of_all_locallyLipschitz
    (N : Network S) (h : N.stoichRank ≤ 1)
    (hll : ∀ K : N.Kinetics, LocallyLipschitz K.vectorField) :
    N.NeverPositiveKineticPeriodic := by
  intro K
  exact N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_le_one h K (hll K)

/-- **Rank-one structural non-oscillation.** No positive mass-action parameterization of a network
with one-dimensional stoichiometric subspace can admit a nonconstant positive periodic orbit. -/
theorem neverPositivePeriodic_of_stoichRank_one
    (N : Network S) (h1 : N.stoichRank = 1) : N.NeverPositivePeriodic := by
  intro κ hperiodic
  have hll : LocallyLipschitz (N.massActionKinetics κ).vectorField := by
    simpa [N.massActionKinetics_vectorField κ] using
      (N.massActionVectorField_contDiff κ (n := 1)).locallyLipschitz
  have hnone := N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_one
    h1 (N.massActionKinetics κ) hll
  obtain ⟨P⟩ := hperiodic
  exact hnone ⟨P.toKinetic⟩

/-- **All stoichiometric ranks at most one are structurally non-oscillatory.** -/
theorem neverPositivePeriodic_of_stoichRank_le_one
    (N : Network S) (h : N.stoichRank ≤ 1) : N.NeverPositivePeriodic := by
  have hr : N.stoichRank = 0 ∨ N.stoichRank = 1 := by omega
  rcases hr with h0 | h1
  · exact N.neverPositivePeriodic_of_stoichRank_zero h0
  · exact N.neverPositivePeriodic_of_stoichRank_one h1

/-- Capacity form of the low-rank exclusion theorem. -/
theorem not_oscillatoryCapacity_of_stoichRank_le_one
    (N : Network S) (h : N.stoichRank ≤ 1) : ¬ N.OscillatoryCapacity :=
  (N.neverPositivePeriodic_iff_not_oscillatoryCapacity).mp
    (N.neverPositivePeriodic_of_stoichRank_le_one h)

end Network

end CRNT
