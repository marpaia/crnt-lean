import CRNT
import CRNT.Examples.ReversiblePair

/-!
# Oscillation-layer regression tests

Compilation-level examples for the proof-carrying oscillation API.  These tests intentionally
exercise scope conversions and exact algebraic bridges rather than numerical simulations.
-/

open CRNT
open Filter Topology

-- A structural deficiency-zero exclusion specializes soundly to every fixed rate vector.
example (κ : Network.RateConstants Examples.ReversiblePair.N) :
    ((Network.deficiencyZeroOscillationCertificate Examples.ReversiblePair.N
      Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero).toFixed κ).status
      = Network.OscillationStatus.excluded := rfl

-- The same proof is mass-action exclusion, but says nothing negative about all admissible kinetics.
example :
    ((Network.deficiencyZeroOscillationCertificate Examples.ReversiblePair.N
      Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero).toScope).massActionStatus
      = Network.OscillationStatus.excluded := rfl

example :
    ((Network.deficiencyZeroOscillationCertificate Examples.ReversiblePair.N
      Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero).toScope).kineticStatus
      = Network.OscillationStatus.unknown := rfl

-- Ordinary structural exclusion also excludes the stronger class-global limit-cycle question.
example :
    ((Network.deficiencyZeroOscillationCertificate Examples.ReversiblePair.N
      Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero).toGlobal).status
      = Network.OscillationStatus.excluded := rfl

-- Right D-stability excludes a strict right-half-plane eigenvalue already at the unscaled matrix.
example {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hD : M.IsDStable) : ¬ M.HasUnstableEigenvalue :=
  hD.not_hasUnstableEigenvalue

-- The two structural oscillatory-core matrix classes cannot overlap.
example {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hI : M.IsOscillatoryCoreClassI) : ¬ M.IsOscillatoryCoreClassII :=
  hI.not_classII

-- The parameter-rich symbolic Jacobian specializes exactly to the ordinary mass-action Jacobian.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) :
    N.symbolicJacobian (N.massActionReactivity κ x) = N.massActionJacobian κ x :=
  N.symbolicJacobian_massActionReactivity κ x

-- Every positive right-diagonal scaling of a stationary-flux core is an actual mass-action
-- steady-state Jacobian at the reciprocal concentration.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    (d : S → ℝ) (hd : ∀ s, 0 < d s) :
    N.massActionJacobian
        (N.rateConstantsOfPositiveSteadyStateFlux hv
          (Network.concentrationOfPositiveDiagonal_positive hd))
        (Network.concentrationOfPositiveDiagonal d) =
      N.fluxJacobianCore v * Matrix.diagonal d :=
  N.massActionJacobian_reciprocalDiagonalRealization hv d hd

-- D-stability of the flux core is exactly stability of all canonical reciprocal-diagonal
-- mass-action steady-state realizations of the same stationary flux.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v) :
    Matrix.IsDStable (N.fluxJacobianCore v) ↔
      ∀ (d : S → ℝ) (hd : ∀ s, 0 < d s),
        Matrix.IsHurwitzReal
          (N.massActionJacobian
            (N.rateConstantsOfPositiveSteadyStateFlux hv
              (Network.concentrationOfPositiveDiagonal_positive hd))
            (Network.concentrationOfPositiveDiagonal d)) :=
  N.fluxJacobianCore_isDStable_iff_reciprocalRealizations_hurwitz hv

-- Low stoichiometric dimension is an independent structural exclusion route.  In particular, the
-- irreversible rank-one network A -> B is not weakly reversible, so this exercises coverage that the
-- deficiency-zero/weak-reversibility certificate alone did not provide.
def irreversibleRankOneData : NetworkData :=
  { numSpecies := 2
    reactions := #[{ source := #[1, 0], target := #[0, 1] }] }

-- The stoichiometric rank of the reconstructed network is one: the 1 × 1 minor at species `0`
-- (entry `0 - 1 = -1`) bounds it below, and the single reaction vector spans the subspace, so the
-- rank is exactly the span's dimension.  `analyze` reports `computeRank`, which does not kernel-
-- reduce, so the numeral is obtained through the `analyze_stoichRank_eq` bridge instead.
theorem irreversibleRankOne_stoichRank : irreversibleRankOneData.toNetwork.stoichRank = 1 := by
  have hv : irreversibleRankOneData.toNetwork.reactionVector
      (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R) ≠ 0 := by
    intro h
    have h0 : irreversibleRankOneData.toNetwork.reactionVector
        (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R)
        (0 : Fin 2) = (0 : ℝ) :=
      congrFun h (0 : Fin 2)
    simp only [Network.reactionVector, Reaction.vector] at h0
    rw [show (irreversibleRankOneData.toNetwork.reaction
            (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R)).target
          (0 : Fin 2) = 0 from by decide,
      show (irreversibleRankOneData.toNetwork.reaction
            (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R)).source
          (0 : Fin 2) = 1 from by decide] at h0
    norm_num at h0
  have hsub : irreversibleRankOneData.toNetwork.stoichSubspace
      = Submodule.span ℝ {irreversibleRankOneData.toNetwork.reactionVector
          (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R)} := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨r, rfl⟩
      fin_cases r
      exact Submodule.subset_span rfl
    · apply Submodule.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact irreversibleRankOneData.toNetwork.reactionVector_mem_stoichSubspace
        (⟨0, by simp [irreversibleRankOneData]⟩ : irreversibleRankOneData.toNetwork.R)
  rw [Network.stoichRank, hsub, finrank_span_singleton hv]

-- With the rank pinned to one, the low-rank route of the exclusion disjunction certifies no
-- positive periodic orbit; the weak-reversibility/deficiency conjunct is irrelevant to the `or`.
theorem irreversibleRankOne_noPositivePeriodicOrbitCertified :
    irreversibleRankOneData.analyze.noPositivePeriodicOrbitCertified = true := by
  rw [NetworkData.analyze_noPositivePeriodicOrbitCertified_eq,
    NetworkData.analyze_stoichRank_eq, irreversibleRankOne_stoichRank]
  exact Bool.or_true _

example : irreversibleRankOneData.analyze.weaklyReversible = false := by decide
example : irreversibleRankOneData.analyze.stoichRank = 1 := by
  rw [NetworkData.analyze_stoichRank_eq, irreversibleRankOne_stoichRank]
example : irreversibleRankOneData.analyze.noPositivePeriodicOrbitCertified = true :=
  irreversibleRankOne_noPositivePeriodicOrbitCertified
example : irreversibleRankOneData.toNetwork.NeverPositivePeriodic :=
  NetworkData.neverPositivePeriodic_of_analyze irreversibleRankOneData
    irreversibleRankOne_noPositivePeriodicOrbitCertified
example : irreversibleRankOneData.oscillationStatus = Network.OscillationStatus.excluded :=
  NetworkData.oscillationStatus_eq_excluded_of_certified irreversibleRankOneData
    irreversibleRankOne_noPositivePeriodicOrbitCertified

-- The theorem is available directly for any finite CRN, independently of the serialized analyzer.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.stoichRank ≤ 1) :
    N.NeverPositivePeriodic :=
  N.neverPositivePeriodic_of_stoichRank_le_one h

-- The rank-one geometry is not specific to mass action: any admissible kinetics with a locally
-- Lipschitz vector field is excluded on a one-dimensional stoichiometric class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.stoichRank ≤ 1) (K : N.Kinetics) (hll : LocallyLipschitz K.vectorField) :
    ¬ N.HasPositiveKineticPeriodicOrbit K :=
  N.not_hasPositiveKineticPeriodicOrbit_of_stoichRank_le_one h K hll

-- Rank zero is stronger: every admissible kinetics is excluded even without a regularity hypothesis.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h0 : N.stoichRank = 0) :
    N.NeverPositiveKineticPeriodic :=
  N.neverPositiveKineticPeriodic_of_stoichRank_zero h0

-- Every nonconstant exact periodic trajectory admits a least positive period; for locally Lipschitz
-- autonomous fields the corresponding representative is a simple closed cycle.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic P.orbit T ∧
      ∀ U : ℝ, 0 < U → Function.Periodic P.orbit U → T ≤ U :=
  P.exists_leastPositivePeriod

example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (hfield : LocallyLipschitz field) :
    P.leastPeriodRepresentative.SimpleClosedCycle :=
  P.leastPeriodRepresentative_simpleClosedCycle hfield

-- The genuinely planar Poincare--Bendixson residue is now recurrent-section construction; once
-- such a compact return interval exists, periodic-orbit existence is already closed.
example {field : Phase2 → Phase2} {D : Planar.FlowTrappingData field}
    (R : Planar.RecurrentSectionData D) :
    Nonempty (PeriodicTrajectory field) :=
  R.exists_periodicTrajectory

-- Green/Jordan sign integration is no longer an assumption: analytic Jordan-area data plus the
-- Dulac one-sign condition are internally contradictory.
example {field : Phase2 → Phase2} {D : Planar.BendixsonDulacData field}
    {P : PeriodicTrajectory field} (A : Planar.DulacAreaData D P) : False :=
  A.false_of_areaData

-- A concrete scalar Poincare persistence package for the smooth added-reaction family closes to
-- oscillatory capacity of the enlarged CRN.
example {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (D : N.ScalarDependentReactionPersistenceData q κ) :
    (N.addReaction q).OscillatoryCapacity :=
  D.oscillatoryCapacity

-- The lower-dimensional Vassena continuation has explicit local Routh--Hurwitz boundary gates.
example {N : Network (Fin 3)} {W : N.FluxGlobalHopfData}
    (H : N.FluxFin3HopfBoundaryWitness W) :
    H.realEigenvalue.re < 0 ∧ H.pairEigenvalue.re = 0 ∧ H.pairEigenvalue.im ≠ 0 ∧
      H.pairEigenvalue.im ^ 2 =
        (N.massActionJacobian
          (W.toFluxJacobianStabilityTransition.continuationRates H.μ)
          (W.toFluxJacobianStabilityTransition.continuationState H.μ)).c₂Fin3 :=
  H.crossing
