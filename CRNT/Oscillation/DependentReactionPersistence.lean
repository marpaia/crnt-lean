import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.ReturnMapFamilyPersistence
import CRNT.Oscillation.ConcentrationEuclidean

/-!
# Closing dependent-reaction return-map persistence to CRN oscillatory capacity

`DependentReaction` embeds addition of a reaction into a smooth real parameter family through
`ε = 0`.  `ReturnMapFamilyPersistence` persists a chosen Poincare fixed-point branch.  This module
joins those two layers.

The only genuinely model-specific hypothesis left here is positivity of the persisting branch flow
for parameters near zero.  Once that is known, a neighbourhood of `0` contains a strictly positive
`ε`; the corresponding branch trajectory is converted to a genuine positive mass-action orbit of
the enlarged network.
-/

namespace CRNT

open Filter Topology

/-- Every neighbourhood property of `0 : ℝ` is realized at some strictly positive parameter.
This elementary lemma is useful whenever an analytic persistence theorem is centered at a zero
reaction-rate boundary but the enlarged CRN requires a positive rate. -/
theorem exists_pos_of_eventually_nhds_zero {Q : ℝ → Prop}
    (hQ : ∀ᶠ ε in 𝓝 (0 : ℝ), Q ε) : ∃ ε : ℝ, 0 < ε ∧ Q ε := by
  rw [Metric.eventually_nhds_iff] at hQ
  obtain ⟨ρ, hρ, hball⟩ := hQ
  refine ⟨ρ / 2, by linarith, ?_⟩
  apply hball
  rw [Real.dist_eq, sub_zero, abs_of_pos]
  · linarith
  · linarith

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- CRN-specific data joining an implicit persistent Poincare branch to the smooth
one-dependent-reaction perturbation family.

`branch_positive` is intentionally a property of the **chosen branch flow**, not of arbitrary
periodic trajectories of the perturbed field.  This avoids an unsound quantifier strengthening. -/
structure DependentReactionReturnPersistenceData
    (N : Network S) (q : Reaction S) (κ : N.RateConstants) where
  persistence : PersistentReturnOrbitData (ConcentrationE S)
  /-- The IFT is centered at zero rate for the newly appended reaction. -/
  parameter_zero : persistence.persistence.parameter = 0
  /-- The section vector field is exactly the smooth dependent-reaction family, read in the
  `ℓ²` model of the concentration space. -/
  field_eq : ∀ ε,
    (persistence.xsection ε).field = euclideanField (N.addedReactionFieldFamily κ q ε)
  /-- The specific flow line through the implicit fixed-point branch stays in the positive orthant
  for all times, for all sufficiently small perturbations. -/
  branch_positive :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t s,
      0 < WithLp.ofLp ((persistence.xsection ε).flow
        (persistence.persistence.fixedPointBranch ε) t) s

namespace DependentReactionReturnPersistenceData

/-- Near zero, the chosen persistent periodic branch can be regarded as a periodic trajectory of the
smooth added-reaction family and remains positive. -/
theorem eventually_positive_family_branch
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (D : DependentReactionReturnPersistenceData N q κ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∃ P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε),
        ∀ t s, 0 < P.orbit t s := by
  have hbranch := D.persistence.eventually_branchPeriodicTrajectory
  rw [D.parameter_zero] at hbranch
  filter_upwards [hbranch, D.branch_positive] with ε hP hpos
  obtain ⟨B⟩ := hP
  refine ⟨PeriodicTrajectory.ofEuclidean (B.trajectory.congrField (D.field_eq ε)), ?_⟩
  intro t s
  have horbit :
      (PeriodicTrajectory.ofEuclidean (B.trajectory.congrField (D.field_eq ε))).orbit t =
        WithLp.ofLp ((D.persistence.xsection ε).flow
          (D.persistence.persistence.fixedPointBranch ε) t) := by
    simp only [PeriodicTrajectory.ofEuclidean_orbit, PeriodicTrajectory.congrField_orbit]
    exact congrArg WithLp.ofLp (congrFun B.orbit_eq t)
  rw [horbit]
  exact hpos t s

/-- **Banaji regular-perturbation closure, conditional only on the concrete return-map package.**
A positive persistent branch through `ε=0` yields a strictly positive reaction rate at which the
enlarged CRN has a positive periodic mass-action orbit. -/
theorem oscillatoryCapacity
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (D : DependentReactionReturnPersistenceData N q κ) :
    (N.addReaction q).OscillatoryCapacity := by
  obtain ⟨ε, hε, P, hpos⟩ :=
    exists_pos_of_eventually_nhds_zero D.eventually_positive_family_branch
  exact N.oscillatoryCapacity_addReaction_of_family_witness q κ hε P hpos

end DependentReactionReturnPersistenceData

end Network

end CRNT
