import CRNT.Oscillation.CoordinateDynamics
import CRNT.Oscillation.PlanarOmega

/-!
# Rank-two CRNs as genuine planar systems

A CRN with stoichiometric rank two has reduced coordinates indexed by `Fin N.stoichRank`, whereas
the planar global-dynamics library uses `Phase2 = EuclideanSpace ℝ (Fin 2)`.  This module removes that otherwise
annoying type gap by reindexing along a proof `N.stoichRank = 2`.

The reindexing is exact.  Planar trajectories transport back to reduced trajectories, and planar
periodic orbits contained in the transported positive chart region lift to positive mass-action
periodic orbits of the original CRN.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reindex a reduced rank-two coordinate vector as a planar vector. -/
noncomputable def reducedToPhase2 (N : Network S) (h : N.stoichRank = 2)
    (y : Fin N.stoichRank → ℝ) : Phase2 :=
  WithLp.toLp 2 (fun i => y (Fin.cast h.symm i))

/-- Reindex a planar vector back into the CRN's reduced coordinate type. -/
noncomputable def phase2ToReduced (N : Network S) (h : N.stoichRank = 2)
    (z : Phase2) : Fin N.stoichRank → ℝ :=
  fun i => z (Fin.cast h i)

@[simp] theorem reducedToPhase2_phase2ToReduced
    (N : Network S) (h : N.stoichRank = 2) (z : Phase2) :
    N.reducedToPhase2 h (N.phase2ToReduced h z) = z := by
  ext i
  simp [reducedToPhase2, phase2ToReduced]

@[simp] theorem phase2ToReduced_reducedToPhase2
    (N : Network S) (h : N.stoichRank = 2) (y : Fin N.stoichRank → ℝ) :
    N.phase2ToReduced h (N.reducedToPhase2 h y) = y := by
  funext i
  simp [reducedToPhase2, phase2ToReduced]

/-- The rank-two reduced mass-action field expressed on the canonical planar phase space. -/
noncomputable def rankTwoReducedField (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S) : Phase2 → Phase2 :=
  fun z => N.reducedToPhase2 h (N.reducedField κ x₀ (N.phase2ToReduced h z))

/-- Positive reduced chart region, transported to `Phase2`. -/
def rankTwoPositiveRegion (N : Network S) (h : N.stoichRank = 2)
    (x₀ : Concentration S) : Set Phase2 :=
  {z | N.phase2ToReduced h z ∈ N.positiveChartRegion x₀}

/-- A planar exact solution of the rank-two reduced field transports back to an exact solution in
native reduced CRN coordinates. -/
theorem rankTwoPlanarSolution_to_reduced
    (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (z : ℝ → Phase2)
    (hz : ∀ t, HasDerivAt z (N.rankTwoReducedField h κ x₀ (z t)) t) :
    ∀ t, HasDerivAt (fun τ => N.phase2ToReduced h (z τ))
      (N.reducedField κ x₀ (N.phase2ToReduced h (z t))) t := by
  intro t
  apply hasDerivAt_pi.mpr
  intro i
  -- `Phase2` is `EuclideanSpace ℝ (Fin 2)`, so components are read off with the continuous
  -- linear projection rather than with `hasDerivAt_pi` on a bare pi type.
  have hi :=
    (EuclideanSpace.proj (Fin.cast h i) : Phase2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
  simpa [rankTwoReducedField, reducedToPhase2, phase2ToReduced, Function.comp_def]
    using hi

/-- Transport a planar periodic trajectory back to the native reduced-coordinate field. -/
noncomputable def reducedPeriodicTrajectoryOfRankTwoPlanar
    (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.rankTwoReducedField h κ x₀)) :
    PeriodicTrajectory (N.reducedField κ x₀) where
  orbit := fun t => N.phase2ToReduced h (P.orbit t)
  period := P.period
  period_pos := P.period_pos
  solution := N.rankTwoPlanarSolution_to_reduced h κ x₀ P.orbit P.solution
  periodic := by
    intro t
    exact congrArg (N.phase2ToReduced h) (P.periodic t)
  nonconstant := by
    obtain ⟨t, ht⟩ := P.nonconstant
    refine ⟨t, ?_⟩
    intro heq
    apply ht
    have := congrArg (N.reducedToPhase2 h) heq
    simpa using this

/-- A planar rank-two periodic orbit inside the transported positive chart region lifts all the way
to a positive periodic orbit of the original mass-action CRN. -/
noncomputable def positivePeriodicOrbitOfRankTwoPlanar
    (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.rankTwoReducedField h κ x₀))
    (hinside : Set.range P.orbit ⊆ N.rankTwoPositiveRegion h x₀) :
    N.PositivePeriodicOrbit κ := by
  let Q := N.reducedPeriodicTrajectoryOfRankTwoPlanar h κ x₀ P
  apply N.positivePeriodicOrbitOfReducedTrajectoryInPositiveRegion κ x₀ Q
  rintro y ⟨t, rfl⟩
  exact hinside ⟨t, rfl⟩

/-- Fixed-parameter oscillation certificate obtained from any positive planar periodic orbit in the
rank-two reduced coordinates. -/
theorem hasPositivePeriodicOrbit_of_rankTwoPlanar
    (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (P : PeriodicTrajectory (N.rankTwoReducedField h κ x₀))
    (hinside : Set.range P.orbit ⊆ N.rankTwoPositiveRegion h x₀) :
    N.HasPositivePeriodicOrbit κ :=
  ⟨N.positivePeriodicOrbitOfRankTwoPlanar h κ x₀ P hinside⟩

/-- End-to-end consumer for the eventual Poincare--Bendixson classification theorem.

If the reduced rank-two field has certified flow/trapping data whose omega-limit set lies in the
positive chart region, the planar classification produces an actual positive CRN periodic orbit. -/
theorem hasPositivePeriodicOrbit_of_rankTwo_poincareBendixson
    (hPB : Planar.PoincareBendixsonOmegaClassificationTarget)
    (N : Network S) (h : N.stoichRank = 2)
    (κ : N.RateConstants) (x₀ : Concentration S)
    (D : Planar.FlowTrappingData (N.rankTwoReducedField h κ x₀))
    (hsmooth : ContDiff ℝ 1 (N.rankTwoReducedField h κ x₀))
    (hpositive : D.omegaSet ⊆ N.rankTwoPositiveRegion h x₀) :
    N.HasPositivePeriodicOrbit κ := by
  obtain ⟨P, hPomega⟩ :=
    Planar.periodicTrajectory_in_omegaSet_of_classification hPB D hsmooth
  exact N.hasPositivePeriodicOrbit_of_rankTwoPlanar h κ x₀ P (hPomega.trans hpositive)

end Network

end CRNT
