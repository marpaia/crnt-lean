import CRNT
import CRNT.Examples.Minimal
import CRNT.Examples.ReversiblePair
import CRNT.Examples.GACReversiblePair
import CRNT.Examples.IrreversibleChain
import CRNT.Examples.GeneExpression
import CRNT.Examples.Enzyme
import CRNT.Examples.HopfOscillator3
import CRNT.Examples.HopfNetwork3
import CRNT.Examples.HopfNetwork3Branches
import CRNT.Examples.StochasticConvergenceExample
import CRNT.Interop.Analysis

/-!
# Smoke tests

Compilation-level tests that exercise the library API on the example networks:
computed complex counts, weak reversibility (and its failure), deficiency zero, and
the structural conservation laws. Building this file (`lake test`) checks that all
stated example properties hold.
-/

open CRNT
open scoped NNReal
open scoped Finset

-- Computed complex counts reduce as expected.
example : Examples.ReversiblePair.N.numComplexes = 2 := by decide
example : Examples.IrreversibleChain.N.numComplexes = 3 := by decide
example : Examples.Enzyme.N.numComplexes = 3 := by decide
example : Examples.GeneExpression.N.numComplexes = 6 := by decide

-- The stochastic reversible pair is weakly reversible, and the embedded-jump convergence
-- interface's aperiodicity self-loop is unsatisfiable on it.
example : Examples.StochasticConvergenceExample.N.WeaklyReversible :=
  Examples.StochasticConvergenceExample.weaklyReversible
example (κ : Network.RateConstants Examples.StochasticConvergenceExample.N)
    (n : Examples.StochasticConvergenceExample.Species → ℕ)
    (r : Examples.StochasticConvergenceExample.N.R)
    (hr : Examples.StochasticConvergenceExample.N.jumpNextCount n r = n) :
    ¬ 0 < Examples.StochasticConvergenceExample.N.jumpProb κ n r :=
  Examples.StochasticConvergenceExample.pair_no_aperiodic_self_loop κ hr

-- Weak reversibility holds for the reversible pair and fails for the chain.
example : Examples.ReversiblePair.N.WeaklyReversible := Examples.ReversiblePair.weaklyReversible
example : ¬ Examples.IrreversibleChain.N.WeaklyReversible :=
  Examples.IrreversibleChain.not_weaklyReversible
example : ¬ Examples.Minimal.N.WeaklyReversible := Examples.Minimal.not_weaklyReversible

-- The reversible pair has deficiency zero and satisfies the deficiency-zero hypotheses.
example : Examples.ReversiblePair.N.DeficiencyZero := Examples.ReversiblePair.deficiencyZero
example : Examples.ReversiblePair.N.SatisfiesDeficiencyZeroHypotheses :=
  Examples.ReversiblePair.satisfiesDeficiencyZeroHypotheses

-- The oscillation layer promotes the same theorem to an all-parameter non-oscillation certificate.
example : Examples.ReversiblePair.N.NeverPositivePeriodic :=
  Examples.ReversiblePair.N.neverPositivePeriodic_of_weaklyReversible_deficiencyZero
    Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero
example :
    (Network.deficiencyZeroOscillationCertificate Examples.ReversiblePair.N
      Examples.ReversiblePair.weaklyReversible Examples.ReversiblePair.deficiencyZero).status
      = Network.OscillationStatus.excluded := rfl

-- The computable linkage count reduces under `decide`; the computable deficiency assembly
-- agrees with the deficiency via the bridge theorem (the value itself is `#eval`-only).
example : Examples.ReversiblePair.N.computeNumLinkageClasses = 1 := by decide
example : Examples.ReversiblePair.N.deficiency = Examples.ReversiblePair.N.computableDeficiency :=
  Network.deficiency_eq_computableDeficiency _

-- The deficiency-one linkage conditions carry a (total, `#eval`-only) decidability
-- instance, assembled from the per-class and tightness deciders.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    Decidable N.DeficiencyOneConditions := inferInstance

-- A data-driven reversible pair `A ⇌ B` reconstructs to a 2-complex, 2-reaction network.
def interopRevData : NetworkData :=
  { numSpecies := 2,
    reactions := #[ { source := #[1, 0], target := #[0, 1] },
                    { source := #[0, 1], target := #[1, 0] } ] }

/-- The stoichiometric rank of `interopRevData` is one: the 1 × 1 minor at species `0` (entry
`0 - 1`) bounds it below, the backward reaction vector is the negation of the forward one, so the
subspace is the line spanned by a single nonzero vector. -/
theorem interopRev_stoichRank : interopRevData.toNetwork.stoichRank = 1 := by
  have hv : interopRevData.toNetwork.reactionVector
      (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R) ≠ 0 := by
    intro h
    have h0 : interopRevData.toNetwork.reactionVector
        (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R) (0 : Fin 2) = (0 : ℝ) :=
      congrFun h (0 : Fin 2)
    simp only [Network.reactionVector, Reaction.vector] at h0
    rw [show (interopRevData.toNetwork.reaction
            (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R)).target
          (0 : Fin 2) = 0 from by decide,
      show (interopRevData.toNetwork.reaction
            (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R)).source
          (0 : Fin 2) = 1 from by decide] at h0
    norm_num at h0
  have hbwd : interopRevData.toNetwork.reactionVector
      (⟨1, by simp [interopRevData]⟩ : interopRevData.toNetwork.R)
      = fun s => -interopRevData.toNetwork.reactionVector
          (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R) s := by
    funext s
    fin_cases s
    all_goals
      simp [Network.reactionVector, Reaction.vector, NetworkData.toNetwork,
        NetworkData.toComplex, interopRevData]
  have hsub : interopRevData.toNetwork.stoichSubspace
      = Submodule.span ℝ {interopRevData.toNetwork.reactionVector
          (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R)} := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨r, rfl⟩
      fin_cases r
      · exact Submodule.subset_span rfl
      · rw [hbwd]
        exact Submodule.neg_mem _ (Submodule.subset_span rfl)
    · apply Submodule.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact interopRevData.toNetwork.reactionVector_mem_stoichSubspace
        (⟨0, by simp [interopRevData]⟩ : interopRevData.toNetwork.R)
  rw [Network.stoichRank, hsub, finrank_span_singleton hv]

/-- With the rank pinned to one, the low-rank route of the exclusion disjunction certifies no
positive periodic orbit. -/
theorem interopRev_noPositivePeriodicOrbitCertified :
    interopRevData.analyze.noPositivePeriodicOrbitCertified = true := by
  rw [NetworkData.analyze_noPositivePeriodicOrbitCertified_eq,
    NetworkData.analyze_stoichRank_eq, interopRev_stoichRank]
  exact Bool.or_true _

example : interopRevData.toNetwork.numComplexes = 2 := by decide
example : interopRevData.toNetwork.numReactions = 2 := by decide

-- The one-call analysis reports the right invariants, with the deficiency bridged to `N.deficiency`.
example : interopRevData.analyze.numComplexes = 2 := by decide
example : interopRevData.analyze.weaklyReversible = true := by decide
example : interopRevData.analyze.deficiency = interopRevData.toNetwork.deficiency :=
  NetworkData.analyze_deficiency_eq _
-- The conservation-law dimension is bridged to the cokernel dimension (`numSpecies − s`).
example : interopRevData.analyze.conservationLawDim
    = Module.finrank ℝ (CRNT.orthSum interopRevData.toNetwork.stoichSubspace) :=
  NetworkData.analyze_conservationLawDim_eq _

-- The reversible pair carries no structural ACR witness.
example : interopRevData.analyze.acrSpecies = #[] := by decide

-- A reported ACR species index is exactly one carrying a structural Shinar–Feinberg witness.
example (d : NetworkData) (s : Fin d.numSpecies) :
    s.val ∈ d.analyze.acrSpecies ↔ d.toNetwork.HasShinarFeinbergPair s :=
  NetworkData.analyze_acrSpecies_eq d s

-- `mem_acrSpecies` characterizes the structural ACR species set: species `A` of the toy network
-- (`A → P`, `2A → Q`) carries a witness.
example : Examples.ACRPair.Species.A ∈ Examples.ACRPair.N.acrSpecies :=
  (Examples.ACRPair.N.mem_acrSpecies _).mpr (by decide)

-- The reversible pair has a nonempty siphon (the full species set `{A, B}`).
example : interopRevData.analyze.hasSiphon = true := by decide

-- The siphon flag is `true` exactly when a nonempty siphon exists, and `false` soundly excludes
-- every critical siphon (the Farkas-free persistence design filter).
example (d : NetworkData) :
    d.analyze.hasSiphon = true
      ↔ ∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ d.toNetwork.IsSiphon P :=
  NetworkData.analyze_hasSiphon_eq d
example (d : NetworkData) (h : d.analyze.hasSiphon = false) :
    d.toNetwork.HasNoCriticalSiphon :=
  NetworkData.analyze_hasNoCriticalSiphon_of_hasSiphon_false d h

-- The full species set `{A, B}` is the (unique) minimal siphon of the reversible pair.
example : Examples.SiphonReversiblePair.N.IsMinimalSiphon (Finset.univ) := by decide

-- The data-driven reversible pair reports `{0, 1}` as its only minimal siphon.
example : interopRevData.analyze.minimalSiphons = #[#[0, 1]] := by decide

-- Each `minimalSiphons` entry is the ascending index image of a minimal siphon.
example (d : NetworkData) (arr : Array Nat) :
    arr ∈ d.analyze.minimalSiphons ↔
      ∃ l : List (Fin d.numSpecies), l ∈ (List.finRange d.numSpecies).sublists ∧
        d.toNetwork.IsMinimalSiphon l.toFinset ∧ arr = (l.map Fin.val).toArray :=
  NetworkData.mem_analyze_minimalSiphons d arr

-- The data-driven reversible pair does not satisfy the consistent signed SR-cover condition.
example : interopRevData.analyze.srSignConsistent = false := by decide

-- The reported SR-sign-consistency flag is `true` exactly when the network satisfies the
-- decidable consistent signed species–reaction cover condition.
example (d : NetworkData) :
    d.analyze.srSignConsistent = true ↔ d.toNetwork.ConsistentSRSign :=
  NetworkData.analyze_srSignConsistent_eq d

-- The reported critical-siphon flag is `true` exactly when the network has a critical siphon.
example (d : NetworkData) :
    d.analyze.hasCriticalSiphon = true ↔ d.toNetwork.HasCriticalSiphon :=
  NetworkData.analyze_hasCriticalSiphon_eq d

-- The structural-persistence flag is the conjunction `weaklyReversible ∧ ¬hasCriticalSiphon`, and
-- when `true` it certifies the structural half of the global-attractor persistence hypothesis:
-- weak reversibility plus no critical siphon (not a full persistence proof — a positive
-- complex-balanced reference is still supplied to `gac_of_hasNoCriticalSiphon`).
example (d : NetworkData) :
    d.analyze.persistenceStructural
      = (d.analyze.weaklyReversible && !d.analyze.hasCriticalSiphon) :=
  NetworkData.analyze_persistenceStructural_eq d
example (d : NetworkData) (h : d.analyze.persistenceStructural = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.HasNoCriticalSiphon :=
  NetworkData.hasNoCriticalSiphon_of_persistenceStructural d h

-- The decidable critical-siphon verdict drives the global-attractor persistence conclusion: when
-- `decide N.HasCriticalSiphon = false`, a weakly reversible, complex-balanced network converges to
-- the unique equilibrium of any positive compatibility class.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hdec : decide N.HasCriticalSiphon = false)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_decide hwr κ hdec hxs hcb hx0 hx0compat

-- The certified-persistence flag is `weaklyReversible ∧ deficiency = 0 ∧ ¬hasCriticalSiphon`; when
-- `true` the deficiency-zero theorem supplies the complex-balanced reference, so every positive
-- trajectory converges to the complex-balanced equilibrium in its own compatibility class.
example (d : NetworkData) :
    d.analyze.persistenceCertified
      = (d.analyze.weaklyReversible && d.analyze.deficiency == 0
          && !d.analyze.hasCriticalSiphon) :=
  NetworkData.analyze_persistenceCertified_eq d
example (d : NetworkData) (h : d.analyze.persistenceCertified = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.DeficiencyZero
      ∧ d.toNetwork.HasNoCriticalSiphon :=
  NetworkData.certifiedHypotheses_of_persistenceCertified d h

-- Deficiency zero discharges the complex-balanced witness of the global-attractor verdict: weak
-- reversibility, deficiency zero, and no critical siphon give, for any positive start, convergence
-- to a complex-balanced equilibrium in the start's compatibility class.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hδ : N.DeficiencyZero) (hdec : decide N.HasCriticalSiphon = false)
    {x₀ : Concentration S} (hx0 : x₀.Positive) :
    ∃ xstar : Concentration S, xstar.Positive ∧ N.IsComplexBalanced κ xstar
      ∧ N.StoichCompatible x₀ xstar ∧
      ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
        (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
        (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
        omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_deficiencyZero_decide hwr κ hδ hdec hx0

-- The analysis tags the current contract version.
example : interopRevData.analyze.version = 19 := by decide

-- Single-linkage persistence and deficiency-one linkage conditions on the reversible pair `A ⇌ B`.
-- The persistence flag equates to its two-field structural definition (the value's `decide` on weak
-- reversibility need not kernel-reduce, so this exercises the bridge, not the raw value). The
-- deficiency-one flag is `#eval`-only (`computeRank`), so it too is exercised through its bridge.
example (d : NetworkData) :
    d.analyze.persistenceSingleLinkage
      = (d.analyze.weaklyReversible && d.analyze.numLinkageClasses == 1) :=
  NetworkData.analyze_persistenceSingleLinkage_eq d
example (d : NetworkData) (h : d.analyze.persistenceSingleLinkage = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.SingleLinkageClass :=
  NetworkData.singleLinkageHypotheses_of_persistenceSingleLinkage d h
example (d : NetworkData) :
    d.analyze.deficiencyOneConditions = decide d.toNetwork.DeficiencyOneConditions :=
  NetworkData.analyze_deficiencyOneConditions_eq d
example (d : NetworkData) (h : d.analyze.deficiencyOneConditions = true) :
    d.toNetwork.DeficiencyOneConditions :=
  NetworkData.deficiencyOneConditions_of_analyze d h
-- The strong-linkage-class count reduces under `decide`: `A ⇌ B` is a single strong linkage class.
example : interopRevData.analyze.numStrongLinkageClasses = 1 := by decide
example (d : NetworkData) :
    d.analyze.numStrongLinkageClasses = d.toNetwork.numStrongLinkageClasses :=
  NetworkData.analyze_numStrongLinkageClasses_eq d

-- Dense scalar companions of the v11 contract on the reversible pair `A ⇌ B`: one minimal siphon of
-- size 2, no ACR species, one terminal strong linkage class, no positively-driven species, and no
-- Hopf-boundary margin (only defined in dimension three).
example : interopRevData.analyze.numMinimalSiphons = 1 := by decide
example : interopRevData.analyze.minSiphonSize = 2 := by decide
example : interopRevData.analyze.numACRSpecies = 0 := by decide
example : interopRevData.analyze.numTerminalSLC = 1 := by decide
example : interopRevData.analyze.numDiagonalDriveSpecies = 0 := by decide
example : interopRevData.analyze.hopfBoundaryMargin = none := by decide
-- The reversible pair is weakly reversible and deficiency zero, so the analyzer can certify that
-- no positive mass-action parameterization admits a nonconstant positive periodic orbit.  The flag
-- is certified through the rank bridge (`computeRank` does not kernel-reduce under `decide`).
example : interopRevData.analyze.noPositivePeriodicOrbitCertified = true :=
  interopRev_noPositivePeriodicOrbitCertified
example (h : interopRevData.analyze.noPositivePeriodicOrbitCertified = true) :
    interopRevData.toNetwork.NeverPositivePeriodic :=
  NetworkData.neverPositivePeriodic_of_analyze interopRevData h
-- Its stoichiometric rank is one, so it is not a planar (rank-two) compatibility-class candidate.
example : interopRevData.analyze.stoichRankTwo = false := by
  refine Bool.eq_false_iff.mpr ?_
  intro h
  rw [NetworkData.analyze_stoichRankTwo_eq] at h
  rw [interopRev_stoichRank] at h
  omega
example : interopRevData.oscillationStatus = Network.OscillationStatus.excluded :=
  NetworkData.oscillationStatus_eq_excluded_of_certified interopRevData
    interopRev_noPositivePeriodicOrbitCertified
example (d : NetworkData) :
    d.analyze.numDiagonalDriveSpecies = d.numSpecies ↔ d.toNetwork.ConsistentDiagonalDrive :=
  NetworkData.analyze_numDiagonalDriveSpecies_eq_card_iff d
example (d : NetworkData) (h : d.numSpecies ≠ 3) : d.analyze.hopfBoundaryMargin = none :=
  NetworkData.analyze_hopfBoundaryMargin_eq_none_of_ne_three d h

-- A three-species network yields a Hopf-boundary margin: the field is non-vacuous in dimension three.
def interopTriData : NetworkData :=
  { numSpecies := 3,
    reactions := #[ { source := #[1, 0, 0], target := #[0, 1, 0] },
                    { source := #[0, 1, 0], target := #[0, 0, 1] },
                    { source := #[0, 0, 1], target := #[1, 0, 0] } ] }

/-- The stoichiometric rank of the three-cycle is two: the 2 × 2 minor on species `0, 1` and
reactions `0, 1` has determinant `1`, and the third reaction vector is the negation of the sum of
the first two, so the subspace is spanned by two vectors. -/
theorem interopTri_stoichRank : interopTriData.toNetwork.stoichRank = 2 := by
  have hge : 2 ≤ interopTriData.toNetwork.stoichRank :=
    interopTriData.toNetwork.stoichRank_ge_of_det_ne_zero
      (k := 2)
      (fun j => (⟨j.val, j.isLt.trans (by simp [interopTriData])⟩ : interopTriData.toNetwork.R))
      (fun i => (⟨i.val, i.isLt.trans (by simp [interopTriData])⟩ : Fin interopTriData.numSpecies))
      (by
        simp +decide [Matrix.det_fin_one, Matrix.det_fin_two, Matrix.det_fin_three]
        all_goals first | decide | (norm_cast <;> decide))
  have hv2 : interopTriData.toNetwork.reactionVector
      (⟨2, by simp [interopTriData]⟩ : interopTriData.toNetwork.R)
      = fun s =>
        -((interopTriData.toNetwork.reactionVector
            (⟨0, by simp [interopTriData]⟩ : interopTriData.toNetwork.R)) s
          + (interopTriData.toNetwork.reactionVector
            (⟨1, by simp [interopTriData]⟩ : interopTriData.toNetwork.R)) s) := by
    funext s
    fin_cases s
    all_goals
      simp [Network.reactionVector, Reaction.vector, NetworkData.toNetwork,
        NetworkData.toComplex, interopTriData]
  have hle : interopTriData.toNetwork.stoichSubspace
      ≤ Submodule.span ℝ
          {interopTriData.toNetwork.reactionVector
              (⟨0, by simp [interopTriData]⟩ : interopTriData.toNetwork.R),
           interopTriData.toNetwork.reactionVector
              (⟨1, by simp [interopTriData]⟩ : interopTriData.toNetwork.R)} := by
    apply Submodule.span_le.2
    rintro x ⟨r, rfl⟩
    fin_cases r
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [hv2]
      exact Submodule.neg_mem _
        (Submodule.add_mem _
          (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)))
  have hle2 : interopTriData.toNetwork.stoichRank ≤ 2 := by
    rw [Network.stoichRank]
    refine (Submodule.finrank_mono hle).trans ?_
    refine (finrank_span_le_card _).trans ?_
    simpa using Finset.card_le_two
  omega

example : interopTriData.analyze.hopfBoundaryMargin.isSome = true := by decide
-- The three-cycle has a two-dimensional stoichiometric subspace, exposing the planar-global route.
example : interopTriData.analyze.stoichRankTwo = true := by
  rw [NetworkData.analyze_stoichRankTwo_eq, interopTri_stoichRank]
example (d : NetworkData) :
    d.analyze.stoichRankTwo = true ↔ d.toNetwork.stoichRank = 2 :=
  NetworkData.analyze_stoichRankTwo_eq d

-- Sard in equal dimension: the critical values of a differentiable self-map of a finite-dimensional
-- space carry no measure, so almost every value is regular — the measure-theoretic input that lifts
-- the regular-value degree to arbitrary values.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (hf : Differentiable ℝ f) :
    μ {y | ∃ x, f x = y ∧ (fderiv ℝ f x).det = 0} = 0 :=
  CRNT.measure_criticalValues_eq_zero μ f hf

-- The regular values of a differentiable self-map are dense: near any value sits one at which every
-- preimage point has invertible derivative, so the regular-value degree can be read off arbitrarily
-- close to any value — the bridge from the regular-value degree toward a degree at arbitrary values.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (hf : Differentiable ℝ f) :
    Dense {y | ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0} :=
  CRNT.dense_regularValues μ f hf

-- The ∃-side existence backbone: a nonzero regular degree of the reduced steady-state map forces a
-- mass-action steady state in the compatibility class — the degree-theoretic counterpart of the
-- injectivity (∀-side) reduction.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (hfin : ((N.reducedField κ x₀) ⁻¹' {0}).Finite)
    (hdeg : CRNT.regularDegree (N.reducedField κ x₀) 0 hfin ≠ 0) :
    ∃ x, N.StoichCompatible x₀ x ∧ N.IsMassActionSteadyState κ x :=
  N.exists_isMassActionSteadyState_of_reducedDegree_ne_zero κ x₀ hfin hdeg

-- The ∃-side multistationarity criterion: a sign-indefinite reduced Jacobian at two positive zeros
-- of the reduced field affirms the capacity for multiple steady states — the degree-theoretic
-- counterpart of the consistent-sign P-matrix injectivity criterion (the mono/multi opposing pair).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) {y₁ y₂ : Fin N.stoichRank → ℝ}
    (hy₁ : N.reducedField κ x₀ y₁ = 0) (hy₂ : N.reducedField κ x₀ y₂ = 0)
    (hp₁ : Concentration.Positive (N.affineChart x₀ y₁))
    (hp₂ : Concentration.Positive (N.affineChart x₀ y₂))
    (hpos : 0 < (N.reducedJacobian κ x₀ y₁).det) (hneg : (N.reducedJacobian κ x₀ y₂).det < 0) :
    N.HasMultistationarityCapacity :=
  N.hasMultistationarityCapacity_of_signIndefinite κ x₀ hy₁ hy₂ hp₁ hp₂ hpos hneg

-- Toward the deficiency-one-algorithm forward correctness: a nonzero stoichiometric direction yields
-- two distinct positive compatible concentrations whose log-ratio is sign-compatible with it — the
-- positional half of the multistationarity witness (the constructive inverse of signCompatible_logRatio).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {w : S → ℝ}
    (hw : w ∈ N.stoichSubspace) (hw0 : w ≠ 0) :
    ∃ x y : Concentration S, x.Positive ∧ y.Positive ∧ N.StoichCompatible x y ∧ x ≠ y ∧
      SameSign w (fun s => Real.log (y s) - Real.log (x s)) :=
  N.exists_compatible_pair_sameSign_logRatio hw hw0

-- The `crnt_deficiency_zero` tactic certifies deficiency zero from an explicit minor witness:
-- a 1×1 minor for the reversible pair, a 2×2 minor for the irreversible chain.
example : Examples.ReversiblePair.N.DeficiencyZero := by
  crnt_deficiency_zero ![Examples.ReversiblePair.Rxn.fwd], ![Examples.ReversiblePair.Species.A]
example : Examples.IrreversibleChain.N.DeficiencyZero := by
  crnt_deficiency_zero ![Examples.IrreversibleChain.Rxn.r1, Examples.IrreversibleChain.Rxn.r2],
    ![Examples.IrreversibleChain.Species.A, Examples.IrreversibleChain.Species.B]

-- The argument-free form finds the nonsingular minor itself.
example : Examples.ReversiblePair.N.DeficiencyZero := by crnt_deficiency_zero
example : Examples.IrreversibleChain.N.DeficiencyZero := by crnt_deficiency_zero

-- The generalized minor-rank tactic bounds the stoichiometric rank below from a witness.
example : 2 ≤ Examples.IrreversibleChain.N.stoichRank := by
  crnt_stoich_rank_ge ![Examples.IrreversibleChain.Rxn.r1, Examples.IrreversibleChain.Rxn.r2],
    ![Examples.IrreversibleChain.Species.A, Examples.IrreversibleChain.Species.B]

-- The reversible pair has no critical siphon, so the no-critical-siphon global-attraction
-- theorem applies to it: every hypothesis is met on this concrete network.
example : Examples.ReversiblePair.N.HasNoCriticalSiphon :=
  Examples.ReversiblePair.hasNoCriticalSiphon

-- Structural conservation laws (parameter-independent).
example (κ : Network.RateConstants Examples.GeneExpression.N)
    (x : Concentration Examples.GeneExpression.Species) :
    Examples.GeneExpression.N.massActionVectorField κ x .DNA = 0 :=
  Examples.GeneExpression.dDNA_dt_eq_zero κ x

example (κ : Network.RateConstants Examples.Enzyme.N)
    (x : Concentration Examples.Enzyme.Species) :
    Examples.Enzyme.N.massActionVectorField κ x .E +
      Examples.Enzyme.N.massActionVectorField κ x .ES = 0 :=
  Examples.Enzyme.total_enzyme_conserved κ x

-- Algebraic reformulation: complex-balanced concentrations are steady states.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (x : Concentration S) (h : N.IsComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x :=
  Network.IsComplexBalanced.isMassActionSteadyState N κ h

-- The mass-action vector field factors through the complex space as `Y ∘ A_k ∘ Ψ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (x : Concentration S) :
    N.massActionVectorField κ x =
      N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) :=
  N.massActionVectorField_eq κ x

-- The mass-action vector field is a polynomial map, hence differentiable everywhere.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Differentiable ℝ (fun x => N.massActionVectorField κ x) :=
  N.massActionVectorField_differentiable κ

-- The source monomial's Fréchet derivative is the dot product with its gradient.
example {S : Type} [DecidableEq S] [Fintype S] (y : Complex S) (x : Concentration S) :
    HasFDerivAt (fun x => y.massActionMonomial x)
      (∑ j, CRNT.massActionMonomialGrad y x j •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j) x :=
  CRNT.massActionMonomial_hasFDerivAt y x

-- The mass-action Jacobian operator is the Fréchet derivative of the vector field.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x : Concentration S) :
    HasFDerivAt (fun x => N.massActionVectorField κ x) (N.massActionJacobianCLM κ x) x :=
  N.massActionVectorField_hasFDerivAt κ x

-- The Jacobian operator acts as the explicit Jacobian matrix.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x v : Concentration S) :
    N.massActionJacobianCLM κ x v = (N.massActionJacobian κ x).mulVec v :=
  N.massActionJacobianCLM_apply κ x v

-- A C¹ map with positive-definite Jacobian along a convex set is injective there.
example {ι : Type} [Fintype ι] {f : (ι → ℝ) → (ι → ℝ)}
    {f' : (ι → ℝ) → ((ι → ℝ) →L[ℝ] (ι → ℝ))} {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hf : ∀ x ∈ C, HasFDerivAt f (f' x) x)
    (hpos : ∀ x ∈ C, ∀ v : ι → ℝ, v ≠ 0 → 0 < ∑ i, v i * (f' x v) i) :
    Set.InjOn f C :=
  CRNT.injOn_of_hasFDerivAt_dotProduct_pos hC hf hpos

-- The positive compatibility class is convex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) :=
  N.convex_positiveCompatibilityClass x₀

-- Positive-definite mass-action Jacobian on a class ⇒ injective on that class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S)
    (hpos : ∀ x ∈ N.positiveCompatibilityClass x₀, ∀ v : Concentration S, v ≠ 0 →
      0 < ∑ i, v i * ((N.massActionJacobian κ x).mulVec v) i) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pos κ x₀ hpos

-- Deficiency rank bridge: rank(∂) = s + dim(ker Y ∩ Im ∂).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.incidenceRank = N.stoichRank + Module.finrank ℝ N.deficiencySubspace :=
  N.incidenceRank_eq_stoichRank_add

-- Fact B: the incidence-rank identity rank(∂) = n − ℓ.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.incidenceRank + N.numLinkageClasses = N.numComplexes :=
  N.incidenceRank_add_numLinkageClasses

-- Deficiency as a kernel dimension: δ = dim(ker Y ∩ Im ∂).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.deficiencyInt = (Module.finrank ℝ N.deficiencySubspace : ℤ) :=
  N.deficiencyInt_eq_finrank_deficiencySubspace

-- Deficiency zero ⟺ the deficiency subspace `ker Y ∩ Im ∂` vanishes (unconditional).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.DeficiencyZero ↔ N.deficiencySubspace = ⊥ :=
  N.deficiencyZero_iff_deficiencySubspace_eq_bot

-- Laplacian/conservation property of the kinetic matrix: columns sum to zero.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N) (v : N.ComplexIdx → ℝ) :
    (∑ c : N.ComplexIdx, N.kineticMap κ v c) = 0 :=
  N.kineticMap_sum_eq_zero κ v

-- Reactions stay within a linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (r : N.R) :
    N.Linked (N.reaction r).source (N.reaction r).target :=
  N.linked_of_reaction r

-- Perron–Frobenius positivity: a nonnegative nonzero fixed vector of a nonnegative,
-- strongly connected matrix is strictly positive.
example {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hb0 : b ≠ 0)
    (hfix : P.mulVec b = b) (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∀ i, 0 < b i :=
  CRNT.pos_of_nonneg_mulVec_fixed_of_stronglyConnected P hP b hb hb0 hfix hsc

-- Perron–Frobenius existence: a column-stochastic nonnegative matrix has a nonnegative
-- nonzero fixed vector.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1) :
    ∃ b : ι → ℝ, (∀ i, 0 ≤ b i) ∧ b ≠ 0 ∧ P.mulVec b = b :=
  CRNT.exists_nonneg_mulVec_fixed_of_colStochastic P hP hcol

-- Perron–Frobenius (combined): a strongly connected column-stochastic nonnegative
-- matrix has a strictly positive fixed vector.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hcol : ∀ j, ∑ i, P i j = 1)
    (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∃ b : ι → ℝ, (∀ i, 0 < b i) ∧ P.mulVec b = b :=
  CRNT.exists_pos_mulVec_fixed_of_stronglyConnected P hP hcol hsc

-- Milestone 3: a weakly reversible network's kinetic matrix has a strictly positive
-- kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (hwr : N.WeaklyReversible) (κ : Network.RateConstants N) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 :=
  CRNT.PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ

-- Milestone 4 (uniqueness half of Birch): positive vectors in the same coset of `S`
-- with `S`-orthogonal log-ratio are equal.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {x y : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : x - y ∈ S)
    (horth : ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (y i)) * s i = 0) :
    x = y :=
  CRNT.birch_uniqueness S hx hy hxy horth

-- Horn–Jackson Lyapunov function: positive-definite about the reference equilibrium.
example {ι : Type} [Fintype ι] {xstar x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxs : ∀ i, 0 < xstar i) (hne : x ≠ xstar) :
    0 < CRNT.relEntropy xstar x :=
  CRNT.relEntropy_pos_of_ne hx hxs hne

-- Fenchel–Young / Birch dual objective bounded below (well-posedness anchor for the
-- minimization underlying Birch existence).
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (w : ι → ℝ) :
    (∑ i, (c i - c i * Real.log (c i / xstar i))) ≤ CRNT.birchDual xstar c w :=
  CRNT.birchDual_ge hxs hc w

-- Coercivity of the Birch dual objective: bounded sublevel sets.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (M : ℝ) :
    ∃ R : ℝ, ∀ w : ι → ℝ, CRNT.birchDual xstar c w ≤ M → ∀ i, |w i| ≤ R :=
  CRNT.birchDual_coercive hxs hc M

-- The Birch dual objective attains a minimum over any (finite-dimensional) subspace.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) (T : Submodule ℝ (ι → ℝ)) :
    ∃ ŵ ∈ T, ∀ w ∈ T, CRNT.birchDual xstar c ŵ ≤ CRNT.birchDual xstar c w :=
  CRNT.birchDual_exists_isMinOn hxs hc T

-- First-order optimality of the dual minimizer: the gradient `x* ⊙ exp(ŵ) − c` is
-- orthogonal to the minimization subspace.
example {ι : Type} [Fintype ι] {xstar c : ι → ℝ} (T : Submodule ℝ (ι → ℝ))
    {ŵ : ι → ℝ} (hŵT : ŵ ∈ T)
    (hŵmin : ∀ w ∈ T, CRNT.birchDual xstar c ŵ ≤ CRNT.birchDual xstar c w) :
    ∀ v ∈ T, ∑ i, (xstar i * Real.exp (ŵ i) - c i) * v i = 0 :=
  CRNT.birchDual_firstOrder T hŵT hŵmin

-- The dot-product double orthogonal complement returns the original subspace.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    CRNT.orthSum (CRNT.orthSum S) = S :=
  CRNT.orthSum_orthSum S

-- The dot-product complement has codimension `dim S`: `dim Sᗮ = card ι − dim S`.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    Module.finrank ℝ (CRNT.orthSum S) = Fintype.card ι - Module.finrank ℝ S :=
  CRNT.finrank_orthSum S

-- Existence half of Birch's theorem: every positive compatibility class `c + S` contains
-- a positive point with `S`-orthogonal log-ratio (the complex-balanced equilibrium).
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      ∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0 :=
  CRNT.birch_existence S hxs hc

-- Birch's theorem (existence + uniqueness): the positive compatibility class `c + S` has
-- a unique point with `S`-orthogonal log-ratio relative to a positive reference `x*`.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ S ∧
      (∀ s ∈ S, ∑ i, (Real.log (x i) - Real.log (xstar i)) * s i = 0) ∧
      ∀ y : ι → ℝ, (∀ i, 0 < y i) → y - c ∈ S →
        (∀ s ∈ S, ∑ i, (Real.log (y i) - Real.log (xstar i)) * s i = 0) → y = x :=
  CRNT.birch S hxs hc

-- Toric inclusion: relative to a complex-balanced reference, positive points with
-- `S`-orthogonal log-ratio are complex-balanced.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (horth : (fun s => Real.log (x s) - Real.log (xstar s)) ∈ CRNT.orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ x :=
  N.complexBalanced_of_logRatio_orthogonal κ hx hxs hcb horth

-- Given one complex-balanced equilibrium, every positive compatibility class contains a
-- complex-balanced equilibrium.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsComplexBalanced κ x :=
  N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx0

-- Perron–Frobenius uniqueness: a strongly connected nonnegative matrix's positive fixed
-- vector is unique up to scaling.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (a v : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hfa : P.mulVec a = a) (hfv : P.mulVec v = v) (hsc : ∀ i j, CRNT.supportReaches P i j) :
    ∃ t : ℝ, v = t • a :=
  CRNT.mulVec_fixed_unique_of_stronglyConnected P hP a v ha hfa hfv hsc

-- Converse toric inclusion: for a weakly reversible network, two positive complex-balanced
-- concentrations have `S`-orthogonal log-ratio.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {x xstar : Concentration S} (hx : x.Positive)
    (hxs : xstar.Positive) (hcbx : N.IsComplexBalanced κ x) (hcbs : N.IsComplexBalanced κ xstar) :
    (fun s => Real.log (x s) - Real.log (xstar s)) ∈ CRNT.orthSum N.stoichSubspace :=
  N.logRatio_orthogonal_of_complexBalanced hwr κ hx hxs hcbx hcbs

-- Uniqueness of the complex-balanced equilibrium in a positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hcbx : N.IsComplexBalanced κ x) (hcby : N.IsComplexBalanced κ y) : x = y :=
  N.isComplexBalanced_unique_in_positiveClass hwr κ hx hy hcbx hcby

-- Existence of a complex-balanced equilibrium for a weakly reversible deficiency-zero
-- network (the step that consumes δ = 0).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) (κ : Network.RateConstants N) :
    ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x :=
  N.exists_isComplexBalanced hwr hδ κ

-- **The Feinberg–Horn–Jackson deficiency-zero theorem.**
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.SatisfiesDeficiencyZeroHypotheses → N.DeficiencyZeroConclusion :=
  N.deficiencyZeroTheorem

-- The reversible pair `A ⇌ B` satisfies the deficiency-zero conclusion: each positive
-- compatibility class has a unique complex-balanced equilibrium.
example : Examples.ReversiblePair.N.DeficiencyZeroConclusion :=
  Examples.ReversiblePair.N.deficiencyZeroTheorem
    Examples.ReversiblePair.satisfiesDeficiencyZeroHypotheses

-- Dissipation: the relative entropy's directional derivative along the vector field is ≤ 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0 :=
  N.dissipation_nonpos κ hx hxs hcb

-- Vanishing dissipation characterizes complex balance.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h0 : (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) = 0) :
    N.IsComplexBalanced κ x :=
  N.complexBalanced_of_dissipation_eq_zero κ hx hxs hcb h0

-- Lyapunov descent: relEntropy is nonincreasing along positive mass-action solutions.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    Antitone (fun t => CRNT.relEntropy xstar (γ t)) :=
  N.relEntropy_antitone_along_solution κ hxs hcb hpos hsol

-- The mass-action vector field is smooth (regularity for ODE existence theory).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    ContDiff ℝ ⊤ (N.massActionVectorField κ) :=
  N.massActionVectorField_contDiff κ

-- Boundary faces of the orthant are non-attracting.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x : Concentration S} (hx : x.Nonnegative) {s : S} (hs : x s = 0) :
    0 ≤ N.massActionVectorField κ x s :=
  N.massActionVectorField_nonneg_of_zero κ hx hs

-- Local existence of mass-action solutions.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) (t₀ : ℝ) :
    ∃ γ : ℝ → Concentration S, γ t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (N.massActionVectorField κ (γ t)) t :=
  N.exists_local_solution κ x₀ t₀

-- Global existence: a bounded Lipschitz autonomous field has a global integral curve.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E → E}
    {K M : ℝ≥0} (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t :=
  ODE.exists_isIntegralCurve hl hb x₀

-- The flow of a bounded Lipschitz autonomous field: a forward semiflow whose orbits solve
-- the ODE.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E → E}
    {K M : ℝ≥0} (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M) :
    ∃ (ϕ : Flow ℝ≥0 E) (γ : E → ℝ → E), (∀ x, γ x 0 = x) ∧
      (∀ x t, HasDerivAt (γ x) (f (γ x t)) t) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) :=
  ODE.exists_flow hl hb

-- Continuous dependence on initial conditions for an autonomous Lipschitz ODE.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ 0) (γ₂ 0) * Real.exp (K * t) :=
  ODE.dist_le_of_isIntegralCurve hf h₁ h₂ ht

-- LaSalle's invariance principle for forward semiflows.
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) {V : α → ℝ} (hV : Continuous V)
    (x : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmono : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x) ≤ V (ϕ s x)) :
    ∃ c : ℝ, (omegaLimit Filter.atTop ϕ {x}).Nonempty ∧
      IsInvariant ϕ (omegaLimit Filter.atTop ϕ {x}) ∧
      ∀ y ∈ omegaLimit Filter.atTop ϕ {x}, V y = c :=
  Flow.laSalle ϕ hV x hK habs hmono

-- Coercivity of the relative entropy: sublevel sets are bounded coordinatewise.
example {S : Type} [DecidableEq S] [Fintype S] {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Nonnegative) {C : ℝ} (h : CRNT.relEntropy xstar x ≤ C)
    (s : S) : x s ≤ max (Real.exp 2 * xstar s) C :=
  Network.relEntropy_coord_le hxs hx h s

-- First-crossing positivity: `y' ≥ −L·y` (where positive) keeps `y` positive on `[0, ∞)`.
example {y : ℝ → ℝ} {L : ℝ} (hd : ∀ t, HasDerivAt y (deriv y t) t)
    (hineq : ∀ t, 0 < y t → -L * y t ≤ deriv y t) (h0 : 0 < y 0) :
    ∀ t, 0 ≤ t → 0 < y t :=
  CRNT.pos_of_forward_deriv_ge hd hineq h0

-- Bounded-Lipschitz cutoff of the mass-action field (so the flow construction applies).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ (K M : ℝ≥0), LipschitzWith K (N.massActionVectorField κ ∘ Network.clampBox B) ∧
      (∀ x, ‖(N.massActionVectorField κ ∘ Network.clampBox B) x‖ ≤ M) :=
  N.exists_cutoff κ hB

-- Local asymptotic stability: the complex-balanced equilibrium's ω-limit set is `{x*}`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hloc : ∀ s, CRNT.relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit Filter.atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_local hwr κ hxs hcb hx0 hx0compat hloc

-- Deficiency-one statement interface: the existence conclusion refines uniqueness.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.DeficiencyOneExistence → N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_existence

-- Deficiency-one condition (iii): the number of terminal strong linkage classes equals the
-- number of linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.OneTerminalSLCPerLinkageClass) : N.numTerminalSLC = N.numLinkageClasses :=
  N.numTerminalSLC_eq_numLinkageClasses h

-- The kinetic map is block diagonal over linkage classes: restriction to a class commutes
-- with `A_k`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (q : Quotient N.linkedSetoid) (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ (N.restrictToClass q v) = N.restrictToClass q (N.kineticMap κ v) :=
  N.kineticMap_restrictToClass κ q v

-- The kernel of the kinetic map decomposes over linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) :
    N.kineticMap κ v = 0 ↔ ∀ q, N.kineticMap κ (N.restrictToClass q v) = 0 :=
  N.kineticMap_eq_zero_iff_forall_restrictToClass κ v

-- A steady state's kinetic image lies in the deficiency subspace `ker Y ⊓ Im ∂`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) ∈ N.deficiencySubspace :=
  N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx

-- In a deficiency-zero network every mass-action steady state is complex-balanced.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hδ : N.DeficiencyZero)
    (κ : Network.RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x :=
  N.isComplexBalanced_of_steadyState_of_deficiencyZero hδ κ hx

-- Deficiency one pins every steady state's kinetic image to a common line through 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (hδ : N.DeficiencyOne) :
    ∃ g : N.ComplexIdx → ℝ, g ≠ 0 ∧ ∀ ⦃x : Concentration S⦄,
      N.IsMassActionSteadyState κ x →
        ∃ c : ℝ, N.kineticMap κ (N.complexMonomialVector x) = c • g :=
  N.exists_kineticImage_smul_of_deficiencyOne κ hδ

-- A deficiency vector sums to zero over each linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : g ∈ N.deficiencySubspace) (q : Quotient N.linkedSetoid) :
    ∑ c, N.restrictToClass q g c = 0 :=
  N.sum_restrictToClass_eq_zero_of_mem_deficiencySubspace hg q

-- Each linkage class supports a nonnegative nonzero kernel vector of the kinetic map.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_class κ θ

-- The kinetic-map kernel has dimension at least the number of linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.numLinkageClasses ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) :=
  N.numLinkageClasses_le_finrank_ker_kineticMap κ

-- Dually, the rank of the kinetic map is at most `n − ℓ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Module.finrank ℝ (LinearMap.range (N.kineticMap κ)) + N.numLinkageClasses ≤ N.numComplexes :=
  N.finrank_range_kineticMap_add_numLinkageClasses_le κ

-- Every linkage class of a weakly reversible network carries a strictly positive kernel
-- vector of the kinetic map.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, N.classOf c = θ → 0 < b c) ∧
      (∀ c, N.classOf c ≠ θ → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_pos_kernelVector_on_class_of_weaklyReversible hwr κ θ

-- On a strongly connected class the per-class kernel mode is unique up to scaling.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (θ : Quotient N.linkedSetoid)
    (hθ : ∀ c c' : N.ComplexIdx, N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val)
    {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c, N.classOf c = θ → 0 < a c) (haoff : ∀ c, N.classOf c ≠ θ → a c = 0)
    (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c, N.classOf c ≠ θ → v c = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a :=
  N.perClass_kernel_unique κ θ hθ hapos haoff haker hvoff hvker

-- For a weakly reversible network, the kinetic-map kernel has dimension exactly ℓ.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) :
    Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) = N.numLinkageClasses :=
  N.finrank_ker_kineticMap_eq_of_weaklyReversible hwr κ

-- For a weakly reversible network, the kinetic image fills the cut space `Im ∂`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) :
    LinearMap.range (N.kineticMap κ) = LinearMap.range N.incidenceMap :=
  N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ

-- A reaction-closed set of complexes supports a nonnegative nonzero kernel vector of `A_k`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (D : N.ComplexIdx → Prop) (hclosed : ∀ r, D (N.sourceIdx r) → D (N.targetIdx r))
    {c0 : N.ComplexIdx} (hc0 : D c0) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 ≤ b c) ∧ b ≠ 0 ∧
      (∀ c, ¬ D c → b c = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_closed κ D hclosed hc0

-- In particular, each terminal strong linkage class supports such a kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', 0 ≤ b c') ∧ b ≠ 0 ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_nonneg_kernelVector_on_terminalSLC κ hc

-- The terminal-SLC kernel mode is strictly positive on the class and zero off it.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} (hc : N.IsTerminalSLC c.val) :
    ∃ b : N.ComplexIdx → ℝ, (∀ c', N.StronglyLinked c.val c'.val → 0 < b c') ∧
      (∀ c', ¬ N.StronglyLinked c.val c'.val → b c' = 0) ∧ N.kineticMap κ b = 0 :=
  N.exists_pos_kernelVector_on_terminalSLC κ hc

-- The kinetic-map kernel has dimension at least the number of terminal strong linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.numTerminalSLC ≤ Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) :=
  N.numTerminalSLC_le_finrank_ker_kineticMap κ

-- Every complex reaches a terminal strong linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (c : N.ComplexIdx) :
    ∃ d : N.ComplexIdx, N.Reaches c.val d.val ∧ N.IsTerminalSLC d.val :=
  N.exists_terminal_reachable c

-- A nonnegative kernel vector of the kinetic map drains to terminal strong linkage classes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {b : N.ComplexIdx → ℝ} (hbnn : ∀ c, 0 ≤ b c) (hbker : N.kineticMap κ b = 0)
    {c : N.ComplexIdx} (hbc : 0 < b c) : N.IsTerminalSLC c.val :=
  N.isTerminalSLC_of_pos_kernel κ hbnn hbker hbc

-- Weak reversibility ⟺ the kinetic map has a strictly positive kernel vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.WeaklyReversible ↔ ∃ b : N.ComplexIdx → ℝ, (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 :=
  N.weaklyReversible_iff_exists_pos_kernelVector κ

-- The terminal-SLC kernel mode is unique up to scaling.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c : N.ComplexIdx} {a v : N.ComplexIdx → ℝ}
    (hapos : ∀ c', N.StronglyLinked c.val c'.val → 0 < a c')
    (haoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → a c' = 0) (haker : N.kineticMap κ a = 0)
    (hvoff : ∀ c', ¬ N.StronglyLinked c.val c'.val → v c' = 0) (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • a :=
  N.terminalSLC_kernel_unique κ hapos haoff haker hvoff hvker

-- Parallel wave: the new structural modules exercised on the library API.

-- Track K.1 (ACR): a pinned monomial ratio yields absolute concentration robustness in `s`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (s : S)
    (H : N.ShinarFeinbergHypotheses s) (hpin : H.PinnedRatio)
    (hne : ∃ (κ : Network.RateConstants N) (x : Concentration S),
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.HasACR s :=
  Network.HasACR.of_pinnedRatio H hpin hne

-- Track M: the computable stoichiometric-rank lower bound is sound.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.computeStoichRankLB ≤ N.stoichRank :=
  N.computeStoichRankLB_le_stoichRank

-- Track B: the fully open extension satisfies `n⁺ = ℓ⁺ + card S + δ⁺`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.fullyOpen.numComplexes
      = N.fullyOpen.numLinkageClasses + Fintype.card S + N.fullyOpen.deficiency :=
  N.numComplexes_fullyOpen_eq_add

-- Track H.1: the generalized (kinetic-order) Birch existence statement.
example {ι : Type} [Fintype ι] (T : Submodule ℝ (ι → ℝ)) {xstar c : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x - c ∈ T ∧
      (fun i => Real.log (x i) - Real.log (xstar i)) ∈ CRNT.orthSum T :=
  CRNT.gen_birch_existence T hxs hc

-- Track D.2: the species-reaction graph is bipartite.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) : N.srGraph.IsBipartite :=
  N.srGraph_isBipartite

-- Track D.1: an injective mass-action network has at most one steady state per positive class.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {κ : Network.RateConstants N}
    (h : (N.massActionKinetics κ).Injective) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  Network.massAction_subsingleton_steadyState_of_injective h hx hy hsx hsy

-- Parallel wave 2: deciders, motifs, siphons, composition exercised on the API.

-- Track K.2 (adaptation): the antithetic motif pins its output to a setpoint at steady state.
example (κ : Network.RateConstants CRNT.Design.Adaptation.N)
    (x : Concentration CRNT.Design.Adaptation.Species)
    (hss : CRNT.Design.Adaptation.N.IsMassActionSteadyState κ x) :
    κ.k .sense * x CRNT.Design.Adaptation.Species.X = κ.k .ref :=
  CRNT.Design.Adaptation.setpoint κ x hss

-- Track M (ACR companion): the Shinar-Feinberg structural hypotheses imply the decidable pair.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) : N.HasShinarFeinbergPair s :=
  Network.HasShinarFeinbergPair.of_hypotheses H

-- Track E (siphons): siphons are closed under union.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {P Q : Finset S}
    (hP : N.IsSiphon P) (hQ : N.IsSiphon Q) : N.IsSiphon (P ∪ Q) :=
  N.union_isSiphon hP hQ

-- Track L (composition): the stoichiometric subspace of an interconnection is the join.
example {S : Type} [DecidableEq S] [Fintype S] (N₁ N₂ : Network S) :
    (N₁.interconnect N₂).stoichSubspace = N₁.stoichSubspace ⊔ N₂.stoichSubspace :=
  N₁.stoichSubspace_interconnect N₂

-- Track D.2 (decidable cycles): undirected cycle existence is decidable on a finite graph.
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable G.HasCycle :=
  inferInstance

-- Track C.2: the one-terminal-SLC-per-linkage-class condition is decidable.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    Decidable N.OneTerminalSLCPerLinkageClass :=
  inferInstance

-- Localization: a mass-action steady state is complex-balanced on every
-- deficiency-zero linkage class (deficiency-one analysis localizes to the deficient class).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneConditions)
    (κ : Network.RateConstants N) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 :=
  N.restrictToClass_kineticImage_eq_zero h κ hx hq

-- The deficiency subspace decomposes over linkage classes (the structural backbone).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneConditions) :
    N.deficiencySubspace = ⨆ q, N.linkageDeficiencySubspace q :=
  N.deficiencySubspace_eq_iSup h

-- Sign-vector layer: the sign vectors of a subspace and its dot-product orthogonal
-- complement are orthogonal (oriented-matroid covector orthogonality).
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ CRNT.orthSum S) :
    CRNT.SignVector.Orthogonal (CRNT.signVector u) (CRNT.signVector w) :=
  CRNT.orthogonal_signVector_of_mem_orthSum hu hw

-- Conformal vectors in complementary subspaces have pointwise-vanishing products.
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {u w : ι → ℝ}
    (hu : u ∈ S) (hw : w ∈ CRNT.orthSum S) (hc : CRNT.Conformal u w) (i : ι) :
    u i * w i = 0 :=
  CRNT.mul_eq_zero_of_conformal_mem_orthSum hu hw hc i

-- Same-sign is equality of sign vectors.
example {ι : Type} {u v : ι → ℝ} : CRNT.SameSign u v ↔ CRNT.signVector u = CRNT.signVector v :=
  CRNT.sameSign_iff_signVector_eq

-- Deficiency-one uniqueness reduces to the log-ratio (toric) characterization, via the
-- Birch sign argument. This isolates the substantive remaining obligation.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.LogRatioCharacterization) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_logRatio h

-- The toric condition equals constancy of the log-monomial ratio along reactions:
-- log-ratio ⊥ stoichiometric subspace ↔ Φ(target) = Φ(source) for every reaction.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) :
    (fun s => Real.log (x s) - Real.log (y s)) ∈ CRNT.orthSum N.stoichSubspace ↔
      ∀ r, N.logMonomialRatio x y (N.targetIdx r) = N.logMonomialRatio x y (N.sourceIdx r) :=
  N.logRatio_mem_orthSum_iff hx hy

-- On a deficiency-zero linkage class the log-monomial ratio is constant (complex balancing).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : Network.RateConstants N) {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hxss : N.IsMassActionSteadyState κ x) (hyss : N.IsMassActionSteadyState κ y)
    {q : Quotient N.linkedSetoid} (hq : N.linkageDeficiency q = 0)
    {c c' : N.ComplexIdx} (hc : N.classOf c = q) (hc' : N.classOf c' = q) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y c' :=
  N.logMonomialRatio_const_of_deficiencyZeroClass h κ hx hy hxss hyss hq hc hc'

-- Deficiency-one uniqueness reduces to log-ratio constancy on the single deficient class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hdef : N.DeficientClassRatioConst) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_of_deficientClassRatioConst h hdef

-- Signed drainage: a kernel vector of A_k vanishes at every non-terminal complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0)
    {c : N.ComplexIdx} (hc : ¬ N.IsTerminalSLC c.val) : v c = 0 :=
  N.kineticMap_eq_zero_of_not_terminal κ hv hc

-- The deficient-class kernel relation (no strong-connectivity hypothesis): on the
-- deficiency-one class, two steady states satisfy cy·Ψx − cx·Ψy = λ·b pointwise, with b
-- positive on the terminal strong linkage class — reducing the sign argument to forcing λ = 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hδ : N.DeficiencyOne)
    (h : N.DeficiencyOneHypotheses) (κ : Network.RateConstants N) {θ : Quotient N.linkedSetoid}
    {x y : Concentration S} (hxss : N.IsMassActionSteadyState κ x)
    (hyss : N.IsMassActionSteadyState κ y) :
    ∃ (b : N.ComplexIdx → ℝ) (cx cy lam : ℝ),
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      ∀ c, N.classOf c = θ →
        cy * N.complexMonomialVector x c - cx * N.complexMonomialVector y c = lam * b c :=
  N.deficientClass_kernel_relation hδ h κ hxss hyss

-- Substochastic Perron–Frobenius: a column-substochastic matrix whose every index reaches a
-- leak (a strictly-substochastic column) has only the zero fixed vector.
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, ∑ i, M i j ≤ 1)
    (hreach : ∀ j, ∃ ℓ, CRNT.supportReaches M ℓ j ∧ ∑ i, M i ℓ < 1)
    {v : ι → ℝ} (hv : M.mulVec v = v) : v = 0 :=
  CRNT.mulVec_fixed_eq_zero_of_substochastic M hM hcol hreach hv

-- Feinberg's Lemma (the deficiency-one analytic linchpin): a product of power functions with
-- exponents summing to zero, a 0 > 0, antitone shifts, and the partial-sum sign condition is
-- strictly decreasing — so the equilibrium-parameter equation has at most one solution.
example {k : ℕ} (hk : 1 ≤ k) {q a : ℕ → ℝ}
    (hq : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → q j ≤ q i)
    (ha0 : 0 < a 0) (hsum : ∑ i ∈ Finset.range (k + 1), a i = 0)
    (hpartial : ∀ i, 1 ≤ i → i < k → q (i + 1) < q i → 0 ≤ ∑ j ∈ Finset.range (i + 1), a j) :
    StrictAntiOn (fun β => ∏ i ∈ Finset.range k, (β + q (i + 1)) ^ a (i + 1))
      (Set.Ioi (- q k)) :=
  CRNT.powerProd_strictAntiOn hk hq ha0 hsum hpartial

-- Digraph excess additivity: the net boundary flux of a vertex set equals the sum of the
-- per-vertex net fluxes (internal arcs cancel) — the backbone of the kernel balance argument.
example {V E : Type} [DecidableEq V] [Fintype E] (src tgt : E → V) (z : E → ℝ) (U : Finset V) :
    CRNT.excessSet src tgt z U = ∑ i ∈ U, CRNT.excessVertex src tgt z i :=
  CRNT.excessSet_eq_sum_excessVertex src tgt z U

-- Lemma II.6 (per-class kernel mode): a deficiency-one linkage class carries a kernel mode of
-- A_k, positive on its terminal strong linkage class, and every kernel vector supported on the
-- class is a scalar multiple of it (the per-class kernel is one-dimensional).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.DeficiencyOneHypotheses) (κ : Network.RateConstants N) (θ : Quotient N.linkedSetoid) :
    ∃ b : N.ComplexIdx → ℝ,
      (∀ c, N.classOf c = θ → N.IsTerminalSLC c.val → 0 < b c) ∧
      N.kineticMap κ b = 0 ∧
      ∀ v : N.ComplexIdx → ℝ, N.kineticMap κ v = 0 →
        (∀ c, N.classOf c ≠ θ → v c = 0) → ∃ t : ℝ, v = t • b :=
  N.exists_kernel_mode_of_deficiencyOne h κ θ

-- Prop II.5 (kinetic map as digraph excess): on the reaction graph, the per-vertex excess of the
-- mass-action flux is the negative of the kinetic map at that complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) (c : N.ComplexIdx) :
    CRNT.excessVertex N.sourceIdx N.targetIdx (N.kineticFlux κ v) c = - N.kineticMap κ v c :=
  N.excessVertex_eq_neg_kineticMap κ v c

-- A path into a complex set crosses its boundary: from reachability into a set (start outside,
-- end inside), some reaction runs from outside the set to inside it.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (P : Complex S → Prop)
    {c d : Complex S} (h : N.Reaches c d) (hc : ¬ P c) (hd : P d) :
    ∃ r : N.R, ¬ P (N.reaction r).source ∧ P (N.reaction r).target :=
  N.exists_crossing_reaction P h hc hd

-- Prop II.8 (net inflow positivity): if v vanishes on U and some reaction enters U from a complex
-- where v is positive, the kinetic-map total over U is strictly positive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (v : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx) (hvnn : ∀ c, 0 ≤ v c)
    (hv : ∀ c ∈ U, v c = 0) {r₀ : N.R}
    (hsrc : N.sourceIdx r₀ ∉ U) (htgt : N.targetIdx r₀ ∈ U) (hpos : 0 < v (N.sourceIdx r₀)) :
    0 < ∑ c ∈ U, N.kineticMap κ v c :=
  N.sum_kineticMap_pos_of_inflow κ v U hvnn hv hsrc htgt hpos

-- The structured preimage with a zero coordinate: from the terminal-class kernel mode b and a
-- preimage z, the vector y* = z − t·b is a preimage of A_k z, nonnegative on the class, equal to
-- z off it, and zero at the arg-min complex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {c0 : N.ComplexIdx} (b z : N.ComplexIdx → ℝ)
    (hbpos : ∀ c', N.StronglyLinked c0.val c'.val → 0 < b c')
    (hboff : ∀ c', ¬ N.StronglyLinked c0.val c'.val → b c' = 0)
    (hbker : N.kineticMap κ b = 0) :
    ∃ (ystar : N.ComplexIdx → ℝ) (cm : N.ComplexIdx),
      N.kineticMap κ ystar = N.kineticMap κ z ∧
      N.StronglyLinked c0.val cm.val ∧ ystar cm = 0 ∧
      (∀ c', N.StronglyLinked c0.val c'.val → 0 ≤ ystar c') ∧
      (∀ c', ¬ N.StronglyLinked c0.val c'.val → ystar c' = z c') :=
  N.exists_zeroCoord_preimage κ b z hbpos hboff hbker

-- Order-free power-product monotonicity: with a positive lump a0, total a0 + ∑a = 0, a lower
-- bound qmin, and the level-set sign condition, β ↦ ∏ (β + q i)^(a i) is strictly decreasing.
example {ι : Type} [DecidableEq ι] (s : Finset ι) (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0) (hsum : a0 + ∑ i ∈ s, a i = 0) (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∏ i ∈ s, (β + q i) ^ a i) (Set.Ioi (- qmin)) :=
  CRNT.powerProd_strictAntiOn_finset s q a a0 qmin ha0 hsum hqmin hlevel

-- Level-set sign of the kinetic map: for v>0 and a kernel vector b, the A_k y*-total over the
-- super-level set {c : v·y*_c < b_c} is nonnegative.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (b ystar : N.ComplexIdx → ℝ) {v : ℝ} (hv : 0 < v) (hb : N.kineticMap κ b = 0) :
    0 ≤ ∑ c ∈ Finset.univ.filter (fun c => v * ystar c < b c), N.kineticMap κ ystar c :=
  N.sum_kineticMap_superlevel_nonneg κ b ystar hv hb

-- Nonnegativity of the A_k-total over an absorbing (reaction-closed) set, for w ≥ 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (w : N.ComplexIdx → ℝ) (U : Finset N.ComplexIdx)
    (hclosed : ∀ r, N.sourceIdx r ∈ U → N.targetIdx r ∈ U) (hw : ∀ c, 0 ≤ w c) :
    0 ≤ ∑ c ∈ U, N.kineticMap κ w c :=
  N.sum_kineticMap_closed_nonneg κ w U hclosed hw

-- Log-sum form of the order-free monotonicity.
example {ι : Type} [DecidableEq ι] (s : Finset ι) (q a : ι → ℝ) (a0 qmin : ℝ)
    (ha0 : 0 < a0) (hsum : a0 + ∑ i ∈ s, a i = 0) (hqmin : ∀ i ∈ s, qmin ≤ q i)
    (hlevel : ∀ v : ℝ, 0 ≤ a0 + ∑ i ∈ s.filter (fun i => v < q i), a i) :
    StrictAntiOn (fun β => ∑ i ∈ s, a i * Real.log (β + q i)) (Set.Ioi (- qmin)) :=
  CRNT.powerProd_logSum_strictAntiOn s q a a0 qmin ha0 hsum hqmin hlevel

-- Injectivity of the shifted-monomial log-sum: H β₁ = H β₂ ⟹ β₁ = β₂.
example {ι : Type} [DecidableEq ι] (s U : Finset ι) (hdisj : Disjoint s U) (ystar b G : ι → ℝ)
    (hys : ∀ c ∈ s, 0 < ystar c) (hyU : ∀ c ∈ U, ystar c = 0) (ha0 : 0 < ∑ c ∈ U, G c)
    (hsum : (∑ c ∈ U, G c) + ∑ c ∈ s, G c = 0)
    (hlevel : ∀ v : ℝ, 0 ≤ (∑ c ∈ U, G c) + ∑ c ∈ s.filter (fun c => v < b c / ystar c), G c)
    {β₁ β₂ : ℝ} (hd₁ : ∀ c ∈ s, - (b c / ystar c) < β₁) (hd₂ : ∀ c ∈ s, - (b c / ystar c) < β₂)
    (hH : (∑ c ∈ s ∪ U, G c * Real.log (β₁ * ystar c + b c))
        = ∑ c ∈ s ∪ U, G c * Real.log (β₂ * ystar c + b c)) :
    β₁ = β₂ :=
  CRNT.eq_of_shiftedLogSum_eq s U hdisj ystar b G hys hyU ha0 hsum hlevel hd₁ hd₂ hH

-- The deficiency-one uniqueness theorem: a deficiency-one network meeting Feinberg's structural
-- hypotheses has at most one positive mass-action steady state per positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne) : N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness h hδ

-- Multi-deficient-class generalization: uniqueness holds under Feinberg's structural hypotheses
-- alone, dropping the single-deficient-class restriction (the total deficiency may exceed one).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses) :
    N.DeficiencyOneUniqueness :=
  N.deficiencyOneUniqueness_multiClass h

-- The fully open extension carries no boundary equilibria: every nonnegative mass-action steady
-- state of `N⁺` is strictly positive (interior to the orthant).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : Network.RateConstants N.fullyOpen) {x : Concentration S} (hx : x.Nonnegative)
    (hss : N.fullyOpen.IsMassActionSteadyState κ x) : x.Positive :=
  N.fullyOpen_steadyState_positive κ hx hss

-- The partial-open (CFSTR) extension can carry boundary equilibria, but only on closed species:
-- the face supporting any nonnegative steady state is disjoint from the open set `O`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (O : Finset S)
    (κ : Network.RateConstants (N.partialOpen O)) {x : Concentration S} (hx : x.Nonnegative)
    (hss : (N.partialOpen O).IsMassActionSteadyState κ x) : Disjoint (Network.faceOf x) O :=
  N.faceOf_partialOpen_steadyState_disjoint O κ hx hss

-- Routh–Hurwitz in degree two: a monic real quadratic is Hurwitz (both roots in the open left
-- half-plane) iff both lower coefficients are positive.
open Polynomial in
example (a₁ a₀ : ℝ) :
    IsHurwitz (X ^ 2 + C (a₁ : ℂ) * X + C (a₀ : ℂ)) ↔ 0 < a₁ ∧ 0 < a₀ :=
  CRNT.hurwitz_quadratic_iff a₁ a₀

-- Single-linkage-class global stability from relative-entropy confinement: under a positive
-- complex-balanced reference and a start whose relative entropy is below every reference
-- coordinate, the genuine mass-action semiflow's ω-limit is the equilibrium.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_local_confinement hwr κ hxs hcb hx0 hx0compat hloc

-- Fenichel stability transfer over the stationary affine base: with rate > 0 the lifted
-- equilibrium incl σ y₀ = (y₀, σ y₀) is fixed by the full comoving-contract flow at every t ≥ 0
-- and attracts the full trajectory of any point (y₀, z₀) sharing its base coordinate. The slow
-- manifold is normally attracting, so the reduced base equilibrium's stability transfers up to the
-- full system.
open Filter in
example (z₀ : ℝ) (y₀ : ℝ × ℝ) :
    (∀ t : ℝ≥0, (ODE.comovingContractFlow (ODE.affineAllTimeBase ((0, 0) : ℝ × ℝ)) 1
          (fun y : ℝ × ℝ => y.2) ODE.continuous_snd_section).toFun t
          (ODE.incl (fun y : ℝ × ℝ => y.2) y₀) = ODE.incl (fun y : ℝ × ℝ => y.2) y₀)
      ∧ Tendsto (fun t : ℝ≥0 => (ODE.comovingContractFlow (ODE.affineAllTimeBase ((0, 0) : ℝ × ℝ)) 1
          (fun y : ℝ × ℝ => y.2) ODE.continuous_snd_section).toFun t (y₀, z₀)) atTop
          (nhds (ODE.incl (fun y : ℝ × ℝ => y.2) y₀)) :=
  ODE.affineStationaryStability_lift one_pos z₀ y₀

-- Single-linkage-class GAC, conditional on single-linkage persistence: the conjecture for a
-- single-linkage network reduces to the hypothesis `SingleLinkageClass → PersistentFrom`.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (hslc : N.SingleLinkageClass) (κ : N.RateConstants) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.SingleLinkageClass → N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.singleLinkageClass_gac hwr hslc κ hxs hcb hx0 hx0compat hpers

-- Decision-driven single-linkage GAC: the structural single-linkage hypothesis is discharged from
-- the Boolean filter `computeNumLinkageClasses = 1`; the complex-balanced reference and Anderson's
-- single-linkage persistence implication are carried unchanged.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hslc : N.computeNumLinkageClasses = 1) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hpers : N.SingleLinkageClass → N.PersistentFrom κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_singleLinkage_decide hwr κ hslc hxs hcb hx0 hx0compat hpers

-- The reversible pair `A ⇌ B` has a single linkage class.
example : Examples.ReversiblePair.N.SingleLinkageClass :=
  Examples.ReversiblePair.numLinkageClasses_eq

-- Negative (backward) invariance of the ω-limit set: for a semiflow whose orbit through `x₀`
-- stays in a compact set, every ω-point has a `ϕ t`-preimage inside the ω-limit set.
open Filter in
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (hmaps : ∀ s : ℝ≥0, ϕ s x₀ ∈ K) (t : ℝ≥0) {w : α}
    (hw : w ∈ omegaLimit atTop ϕ {x₀}) :
    ∃ w' ∈ omegaLimit atTop ϕ {x₀}, ϕ t w' = w :=
  CRNT.omegaLimit_negInvariant ϕ x₀ hK hmaps t hw

-- Compactness of the ω-limit set of an orbit absorbed by a compact set.
example {α : Type*} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K) (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    IsCompact (omegaLimit Filter.atTop ϕ {x₀}) :=
  (CRNT.isCompact_isInvariant_omegaLimit ϕ x₀ hK habs).1

-- Strict inflow at a non-siphon zero set: if the zero set of a nonnegative concentration is not
-- a siphon, the mass-action field is strictly positive at some empty species.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {w : Concentration S} (hwnn : w.Nonnegative) {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0)
    (hns : ¬ N.IsSiphon P) : ∃ s ∈ P, 0 < N.massActionVectorField κ w s :=
  N.massActionVectorField_pos_of_not_isSiphon κ hwnn hP hns

-- Boundary ω-limit ⇒ siphon: for a bounded mass-action semiflow whose ω-orbits solve the genuine
-- field and are nonnegative, the zero set of any ω-limit point is a siphon.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) : N.IsSiphon P :=
  N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hP

-- Boundary ω-limit ⇒ CRITICAL siphon: for a positive start, a boundary ω-limit point's zero set
-- carries no positive conservation law, so it is a critical siphon.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) : N.IsCriticalSiphon P :=
  N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hw hP hPne

-- No critical siphon ⇒ persistence at the ω-limit: every ω-limit point is strictly positive.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) (hncs : N.HasNoCriticalSiphon)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) : w.Positive :=
  N.omegaLimit_positive_of_hasNoCriticalSiphon κ hϕγ hK hmaps hωnn hgenω hωaff hx0pos hncs hw

-- Unconditional GAC for no-critical-siphon networks: a weakly reversible, no-critical-siphon,
-- complex-balanced network converges to the unique equilibrium of any positive class — no
-- persistence or closeness hypothesis.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat

-- GAC from confinement: a compact region plus a positive per-facet floor on every coordinate
-- discharges persistence, yielding ω = {x*}.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {B : Set (Concentration S)} (hBcpt : IsCompact B) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hconfine : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ B ∧ ∀ s, ε s ≤ Γ t s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_confinement hwr κ hxs hcb hx0 hx0compat hBcpt hε hconfine

-- GAC from a forward-invariant separating region: bounded, floored off every facet, orbit-invariant.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {R B : Set (Concentration S)} {ε : S → ℝ} (hBcpt : IsCompact B) (hε : ∀ s, 0 < ε s)
    (hRB : R ⊆ B) (hRfloor : ∀ y ∈ R, ∀ s, ε s ≤ y s) (hx0R : x₀ ∈ R)
    (hinv : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ R) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingRegion hwr κ hxs hcb hx0 hx0compat hBcpt hε hRB hRfloor hx0R hinv

-- GAC from a separating region via closed-set Nagumo: distance to a closed, bounded, floored region
-- nonincreasing along the orbit yields ω = {x*}.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {R B : Set (Concentration S)} {ε : S → ℝ} (hBcpt : IsCompact B) (hε : ∀ s, 0 < ε s)
    (hRclosed : IsClosed R) (hRB : R ⊆ B) (hRfloor : ∀ y ∈ R, ∀ s, ε s ≤ y s) (hx0R : x₀ ∈ R)
    (hanti : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      AntitoneOn (fun t => Metric.infDist (Γ t) R) (Set.Ici 0)) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingRegion_nagumo hwr κ hxs hcb hx0 hx0compat hBcpt hε hRclosed hRB hRfloor hx0R hanti

-- Capstone reduction: the separating-confinement predicate alone yields ω = {x*}.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (h : N.SeparatingConfinement κ x₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_separatingConfinement hwr κ hxs hcb hx0 hx0compat h

-- The separating-confinement predicate is realizable, not merely hypothesized: near equilibrium
-- (relative entropy of the start below every reference coordinate) it is constructed outright.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    N.SeparatingConfinement κ x₀ :=
  N.separatingConfinement_of_local κ hxs hcb hx0 hloc

-- The separating-confinement predicate is exactly the persistence certificate `PersistentFrom`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx0 : x₀.Positive) :
    N.SeparatingConfinement κ x₀ ↔ N.PersistentFrom κ x₀ :=
  ⟨N.persistentFrom_of_separatingConfinement κ, N.separatingConfinement_of_persistentFrom κ hx0⟩

-- Structural realizability: on the (decidable) no-critical-siphon class the separating-confinement
-- predicate is constructed outright — the orbit may approach the boundary, only its closure is held
-- off every facet. This also yields the persistence certificate `PersistentFrom` the
-- no-critical-siphon argument does not otherwise expose.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) :
    N.SeparatingConfinement κ x₀ ∧ N.PersistentFrom κ x₀ :=
  ⟨N.separatingConfinement_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat,
    N.persistentFrom_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat⟩

-- The reduction is tight: the global attractor conclusion (ω = {x*}) itself yields both the
-- persistence certificate and the separating-confinement predicate, so the geometric predicate is
-- equivalent to the conjecture's own conclusion for these networks.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hω : omegaLimit atTop ϕ {x₀} = {xstar}) :
    N.SeparatingConfinement κ x₀ ∧ N.PersistentFrom κ x₀ :=
  ⟨N.separatingConfinement_of_omegaLimit_singleton κ hxs hcb hx0 hγ0 hϕγ hsol hω,
    N.persistentFrom_of_omegaLimit_singleton κ hxs hcb hx0 hγ0 hϕγ hsol hω⟩

-- Genuine-orbit confinement: a genuine positive-start orbit stays positive with nonincreasing
-- relative entropy, the genuine-field forms of `orbit_pos` / `orbit_relEntropy_le`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    (∀ t, 0 ≤ t → (Γ t).Positive) ∧
      (∀ t, 0 ≤ t → relEntropy xstar (Γ t) ≤ relEntropy xstar (Γ 0)) :=
  let hpos := N.genuineOrbit_pos κ hΓ0 hΓd
  ⟨hpos, N.genuineOrbit_relEntropy_le κ hxs hcb hpos hΓd⟩

-- Uniqueness of the genuine mass-action orbit from a positive start (complex-balanced reference) —
-- the genuine-field counterpart of the clamped-field uniqueness the flow construction rests on.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) {Γ₁ Γ₂ : ℝ → Concentration S} (hΓ₁0 : Γ₁ 0 = x₀) (hΓ₂0 : Γ₂ 0 = x₀)
    (hΓ₁d : ∀ t, 0 ≤ t → HasDerivAt Γ₁ (N.massActionVectorField κ (Γ₁ t)) t)
    (hΓ₂d : ∀ t, 0 ≤ t → HasDerivAt Γ₂ (N.massActionVectorField κ (Γ₂ t)) t) :
    ∀ t, 0 ≤ t → Γ₁ t = Γ₂ t :=
  N.genuineOrbit_unique κ hxs hcb hx0 hΓ₁0 hΓ₂0 hΓ₁d hΓ₂d

-- Toric route: a fan wall carrying an inward reaction separates that reaction's mutually-reachable
-- endpoints, discharging the hand-named separation witness from a finite reaction search.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {n : S → ℝ} (r : N.R) (hr : N.InwardReaction n r) :
    N.SeparatesComplexes n (N.reaction r).source (N.reaction r).target :=
  N.separatesComplexes_of_hasInwardReaction hwr r hr

-- The GAC certificate API: the certificate discharges the global attractor conclusion, and is
-- constructible on the decidable no-critical-siphon class — the verifiable-reward target type.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) (hncs : N.HasNoCriticalSiphon) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) (hx0 : x₀.Positive)
    (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.gac_of_gacCertificate hwr κ hxs hcb hx0 hx0compat
    (N.gacCertificate_of_hasNoCriticalSiphon hwr κ hncs hxs hcb hx0 hx0compat)

-- Anderson siphon-dimension descent (skeleton): the carried comparable-growth descent walks a
-- carried critical siphon down by cardinality to a strictly positive ω-limit point.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    (hdesc : N.ComparableGrowthDescent ϕ x₀) {P₀ : Finset S} (hne : P₀.Nonempty)
    (hcrit : N.IsCriticalSiphon P₀) (hcarr : N.SiphonCarried ϕ x₀ P₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive :=
  N.omegaLimit_positive_of_descend hdesc hne hcrit hcarr

-- Asymptotic facet repulsion (the Anderson–Shiu mechanism, proven): the near-facet dissipation
-- bound plus the field's linear lower bound give a uniform positive floor under a critical-siphon
-- facet — the asymptotic statement the decaying finite-time Grönwall bound does not provide.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {sstar : S} {δ ε G : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hG : 0 ≤ G)
    (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hlog : ∀ t, 0 ≤ t → -(G * γ t sstar) ≤ N.massActionVectorField κ (γ t) sstar)
    (hstart : δ ≤ γ 0 sstar)
    (hnear : ∀ t, 0 ≤ t → γ t sstar ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s)) :
    ∀ t, 0 ≤ t → δ * Real.exp (-(G * (relEntropy xstar (γ 0) / ε))) ≤ γ t sstar :=
  N.siphonFacet_floor_of_nearFacet_dissipation κ hxs hcb hδ hε hG hpos hsol hlog hstart hnear

-- Broader reduction: a single positive ω-limit point forces ω = {x*} (no structural hypothesis).
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar) (hγ0 : ∀ x, γ x 0 = x)
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    omegaLimit atTop ϕ {x₀} = {xstar} :=
  N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ hgenω hωnn hωaff hωc
    hposorbit hex

-- GAC-frontier foundation F1: the maximal invariant subset of a set is invariant.
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (N : Set α) :
    IsInvariant ϕ (maximalInvariantSubset ϕ N) :=
  isInvariant_maximalInvariantSubset ϕ N

-- GAC-frontier foundation F3: an ODE solution embeds as a solution of any inclusion it selects.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : DifferentialInclusion.Field E) {f : E → E} {γ : ℝ → E}
    (hderiv : ∀ t, HasDerivAt γ (f (γ t)) t) (hsel : ∀ x, f x ∈ F x) :
    DifferentialInclusion.IsInclusionSolution F γ :=
  DifferentialInclusion.IsInclusionSolution.of_ode hderiv hsel

-- GAC-frontier foundation F4: dissipation is strictly negative at a positive non-equilibrium.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : Concentration.Positive x) (hxs : Concentration.Positive xstar)
    (hcb : N.IsComplexBalanced κ xstar) (hnotcb : ¬ N.IsComplexBalanced κ x) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) < 0 :=
  N.dissipation_neg_of_not_complexBalanced κ hx hxs hcb hnotcb

-- GAC-frontier foundation F2: reaction vectors lie in the reaction cone; Newton polytope is convex.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (r : N.R) :
    N.reactionVector r ∈ N.reactionCone :=
  N.reactionVector_mem_reactionCone r

example {S : Type} [DecidableEq S] [Fintype S] (Y : Finset (Complex S)) :
    Convex ℝ (newtonPolytope Y) :=
  newtonPolytope_convex Y

-- Anderson–Craciun–Kurtz: for a complex-balanced network the product-of-Poissons density
-- satisfies the stochastic master-equation stationarity condition.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hcb : N.IsComplexBalanced κ c) : N.IsMasterStationary κ c :=
  N.productPoisson_isStationary_of_complexBalanced κ c hcb

-- Degree-free deficiency-one existence: a per-rate-constant complex-balanced witness yields a
-- positive steady state in every positive compatibility class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hδ : N.DeficiencyOne)
    (hCB : ∀ (κ : Network.RateConstants N), ∃ x : Concentration S,
      x.Positive ∧ N.IsComplexBalanced κ x) :
    N.DeficiencyOneExistence :=
  N.deficiencyOneExistence_of_complexBalancedExistence h hδ hCB

-- Degree-free 1-D Brouwer fixed point: a continuous self-map of a closed interval has a fixed point.
example {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) : ∃ x ∈ Set.Icc a b, f x = x :=
  CRNT.Analysis.fixedPoint_Icc hab hf hmaps

-- Nagumo inward condition: the mass-action field points inward on every orthant boundary face.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    Network.InwardOnBoundary (N.massActionVectorField κ) :=
  N.massActionVectorField_inwardOnBoundary κ

-- Generator-level Anderson–Craciun–Kurtz: a complex-balanced product-Poisson density is a
-- stationary state of the chemical-master-equation generator (`πQ = 0`).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hcb : N.IsComplexBalanced κ c) : N.IsGeneratorStationary κ c :=
  N.productPoisson_isGeneratorStationary_of_complexBalanced κ c hcb

-- Oriented matroid of a subspace: the zero covector is realizable.
example {ι : Type} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    (fun _ => 0) ∈ CRNT.RealizableSignVector S :=
  CRNT.realizable_zero S

-- Hurwitz determinant interface: the second Hurwitz determinant of a cubic is `a₂a₁ − a₀`.
example (a : ℕ → ℝ) : CRNT.hurwitzDet a 3 2 (by norm_num) = a 2 * a 1 - a 0 :=
  CRNT.hurwitzDet_two_cubic a

-- Routh–Hurwitz in degree four (Liénard–Chipart necessity): four negative real roots of the
-- monic quartic force the five sign conditions, including the third Hurwitz determinant.
example (r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ : ℝ)
    (hr₁ : r₁ < 0) (hr₂ : r₂ < 0) (hr₃ : r₃ < 0) (hr₄ : r₄ < 0)
    (e₃ : a₃ = -(r₁ + r₂ + r₃ + r₄))
    (e₂ : a₂ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (e₁ : a₁ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (e₀ : a₀ = r₁ * r₂ * r₃ * r₄) :
    0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁ :=
  CRNT.hurwitz_quartic_necessary_allReal r₁ r₂ r₃ r₄ a₃ a₂ a₁ a₀ hr₁ hr₂ hr₃ hr₄ e₃ e₂ e₁ e₀

-- Routh–Hurwitz in degree four (Liénard–Chipart full criterion): the five sign conditions
-- on the monic quartic hold iff all four complex roots lie in the open left half-plane.
example (z₁ z₂ z₃ z₄ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + z₂ + z₃ + z₄))
    (e₂ : (a₂ : ℂ) = z₁ * z₂ + z₁ * z₃ + z₁ * z₄ + z₂ * z₃ + z₂ * z₄ + z₃ * z₄)
    (e₁ : (a₁ : ℂ) = -(z₁ * z₂ * z₃ + z₁ * z₂ * z₄ + z₁ * z₃ * z₄ + z₂ * z₃ * z₄))
    (e₀ : (a₀ : ℂ) = z₁ * z₂ * z₃ * z₄)
    (hstruct : (z₁.im = 0 ∧ z₂.im = 0 ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₃.im = 0 ∧ z₄.im = 0)
      ∨ (z₂ = (starRingEnd ℂ) z₁ ∧ z₄ = (starRingEnd ℂ) z₃)) :
    (0 < a₃ ∧ 0 < a₂ ∧ 0 < a₁ ∧ 0 < a₀ ∧ a₁ ^ 2 + a₃ ^ 2 * a₀ < a₃ * a₂ * a₁) ↔
      (z₁.re < 0 ∧ z₂.re < 0 ∧ z₃.re < 0 ∧ z₄.re < 0) :=
  CRNT.hurwitz_quartic_root_iff z₁ z₂ z₃ z₄ a₃ a₂ a₁ a₀ e₃ e₂ e₁ e₀ hstruct

-- Bridge: the third Hurwitz determinant of a quartic is the Liénard–Chipart `Δ₃`.
example (a : ℕ → ℝ) :
    CRNT.hurwitzDet a 4 3 (by norm_num) = a 3 * a 2 * a 1 - a 1 ^ 2 - a 3 ^ 2 * a 0 :=
  CRNT.hurwitzDet_three_quartic a

-- Singular-perturbation boundary layer: a one-sided contraction toward its equilibrium decays
-- exponentially.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → E} {z : ℝ → E}
    {zstar : E} {lam : ℝ} (hz : ∀ t, HasDerivAt z (f (z t)) t) (hstat : f zstar = 0)
    (hcon : ODE.OneSidedContraction f zstar lam) (hlam : 0 ≤ lam) :
    ∀ t, 0 ≤ t → ‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t) :=
  ODE.norm_sub_le_exp_neg_mul hz hstat hcon hlam

-- Dissipative (logarithmic-norm) tracking: a transverse gap obeying `u' ≤ -λ·u + δ` with `λ > 0`
-- and defect `δ ≥ 0` stays below a horizon-uniform ceiling `u 0 · e^{-λt} + δ/λ` (no `e^{KT}` growth).
example {u u' : ℝ → ℝ} {lam δ T : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hu : ContinuousOn u (Set.Icc 0 T)) (hu' : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt u (u' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico 0 T, u' x ≤ -lam * u x + δ) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ u 0 * Real.exp (-lam * t) + δ / lam :=
  ODE.le_dissipative_of_deriv_le hlam hδ hu hu' hbound

-- Computable matrix rank over ℚ agrees with Mathlib's `Matrix.rank`.
example {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℚ) :
    CRNT.GaussianRank.computeRank A = A.rank :=
  CRNT.GaussianRank.computeRank_eq_rank A

-- ACR cross-class bridge: under the toric/orthogonality property the log-monomial ratio is
-- constant on every linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive) (h : N.ToricRelated x y) {c d : N.ComplexIdx}
    (hcd : N.Linked c.val d.val) : N.logMonomialRatio x y c = N.logMonomialRatio x y d :=
  N.logMonomialRatio_eqOn_linked hx hy h hcd

-- Signed species-reaction graph: every cycle in the SR-graph has even length.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (hw : w.IsCycle) : Even w.length :=
  N.cycle_even_length hw

-- Higher-deficiency localization: under tightness each per-class deficiency subspace has
-- dimension exactly `δ_θ`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.TightLinkageDeficiency)
    (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageDeficiencySubspace q) = (N.linkageDeficiency q).toNat :=
  N.finrank_linkageDeficiencySubspace_eq_of_tight h q

-- Exact computable deficiency over ℚ: the network deficiency equals its Gaussian-rank value.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.deficiency = N.computeDeficiency :=
  N.deficiency_eq_computeDeficiency

-- Per-linkage-class deficiency in exact computable form: `δ_θ = n_θ − 1 − computeRank (class matrix)`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiency q = N.computeLinkageDeficiency q :=
  N.linkageDeficiency_eq_computeLinkageDeficiency q

-- The per-class deficiency-one test `δ_θ ≤ 1` carries a total `Decidable` instance.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (q : Quotient N.linkedSetoid) :
    Decidable (N.linkageDeficiency q ≤ 1) :=
  N.decidableLinkageDeficiency_le_one q

-- Multistationarity capacity is ruled out by injectivity for all rate constants.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : ∀ κ : Network.RateConstants N, (N.massActionKinetics κ).Injective) :
    ¬ N.HasMultistationarityCapacity :=
  N.not_hasMultistationarityCapacity_of_injective h

-- Consistency (positive dependence of reaction vectors): a functional nonnegative on every
-- reaction vector is forced to vanish on all of them.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.IsConsistent)
    {w : S → ℝ} (hw : ∀ r, 0 ≤ ∑ s, w s * N.reactionVector r s) (r : N.R) :
    ∑ s, w s * N.reactionVector r s = 0 :=
  N.inner_reactionVector_eq_zero_of_isConsistent_of_nonneg h hw r

-- A weakly reversible network is consistent (regular's first clause holds for WR networks).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible) :
    N.IsConsistent :=
  N.isConsistent_of_weaklyReversible hwr

-- Cut pairs of the linkage graph are symmetric.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {y y' : {c : Complex S // c ∈ N.complexes}} (h : N.CutPair y y') : N.CutPair y' y :=
  h.symm

-- A regular network is consistent and has one terminal SLC per linkage class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.RegularNetwork) :
    N.IsConsistent ∧ N.OneTerminalSLCPerLinkageClass :=
  ⟨h.isConsistent, h.oneTerminalSLCPerLinkageClass⟩

-- A DOA-system solution carrying a strict inequality is nonzero.
example {S : Type} [DecidableEq S] [Fintype S] (sys : DOASystem S) {μ : S → ℝ}
    (h : sys.Satisfies μ) {p : Complex S × Complex S} (hp : p ∈ sys.gts) : μ ≠ 0 :=
  sys.ne_zero_of_satisfies_mem_gts h hp

-- The cut-pair functional of a confluence vector is antisymmetric.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {g : N.ComplexIdx → ℝ}
    (hg : N.IsConfluenceVector g) {y y' : N.ComplexIdx} (h : N.CutPair y y') :
    N.cutSum g y y' = - N.cutSum g y' y :=
  N.cutSum_antisymm hg h

-- A shelf partition's strict height constraint forces μ ≠ 0.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (sp : N.ShelfPartition)
    {g : N.ComplexIdx → ℝ} {μ : S → ℝ} (h : sp.imposes g μ)
    {y y' : N.ComplexIdx} (hr : (sp.shelf y').rank < (sp.shelf y).rank) : μ ≠ 0 :=
  sp.ne_zero_of_imposes_of_higher h hr

-- The Deficiency One Algorithm verdict is non-vacuous: affirming capacity yields a nonzero
-- stoichiometric vector. (The capacity ⟺ signature theorem itself is the stated target.)
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.DOAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ :=
  N.stoichSubspace_ne_bot_of_doaAffirmsCapacity h

-- DOA forward direction (entry step): capacity yields a nonzero sign-compatible vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.HasMultistationarityCapacity) : ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ :=
  N.exists_signCompatible_of_hasMultistationarityCapacity h

-- Colinearity of reactions is transitive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {r r' r'' : N.R}
    (h₁ : N.ColinearReactions r r') (h₂ : N.ColinearReactions r' r'') : N.ColinearReactions r r'' :=
  h₁.trans h₂

-- Colinearity classes form a genuine quotient: same class iff reaction vectors collinear.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {r r' : N.NonzeroReaction} :
    N.colinearityClass r = N.colinearityClass r' ↔ N.ColinearReactions r.val r'.val :=
  N.colinearityClass_eq

-- Orientation dichotomy: the scalar relating two collinear nonzero vectors is signed.
example {S : Type} {v w : S → ℝ} (hw : w ≠ 0) {a : ℝ} (ha : w = a • v) : 0 < a ∨ a < 0 :=
  ColinearVec.orientation_dichotomy hw ha

-- An interconnection's vector field is the sum of the component vector fields.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    (K₁ : Network.Kinetics N₁) (K₂ : Network.Kinetics N₂) :
    (K₁.sum K₂).vectorField = fun x => K₁.vectorField x + K₂.vectorField x :=
  K₁.sum_vectorField K₂

-- A set is a siphon of an interconnection iff it is a siphon of each component.
example {S : Type} [DecidableEq S] [Fintype S] (N₁ N₂ : Network S) (P : Finset S) :
    (N₁.interconnect N₂).IsSiphon P ↔ N₁.IsSiphon P ∧ N₂.IsSiphon P :=
  N₁.interconnect_isSiphon_iff N₂ P

-- Injectivity of the composed field ⇒ ≤1 steady state per class of the interconnection.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    {K₁ : Network.Kinetics N₁} {K₂ : Network.Kinetics N₂} {x₀ : Concentration S}
    (h : (K₁.sum K₂).InjectiveOnClass x₀) {x y : Concentration S}
    (hx : x ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hy : y ∈ (N₁.interconnect N₂).positiveCompatibilityClass x₀)
    (hsx : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) x)
    (hsy : (N₁.interconnect N₂).IsKineticSteadyState (K₁.sum K₂) y) : x = y :=
  h.sum_subsingleton_steadyState hx hy hsx hsy

-- Stoichiometrically independent components: injectivity of one lifts to the interconnection.
example {S : Type} [DecidableEq S] [Fintype S] {N₁ N₂ : Network S}
    {K₁ : Network.Kinetics N₁} {K₂ : Network.Kinetics N₂} {x₀ : Concentration S}
    (hind : N₁.StoichIndependent N₂)
    (h₁ : Set.InjOn K₁.vectorField ((N₁.interconnect N₂).positiveCompatibilityClass x₀)) :
    (K₁.sum K₂).InjectiveOnClass x₀ :=
  Network.Kinetics.InjectiveOnClass.interconnect_of_stoichIndependent_left hind h₁

-- A concordant network is monostationary under any weakly monotonic kinetics.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hN : N.Concordant)
    {K : Network.Kinetics N} (hwm : K.WeaklyMonotonic) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState K x) (hsy : N.IsKineticSteadyState K y) : x = y :=
  hN.subsingleton_steadyState hwm hx hy hsx hsy

-- The Advanced Deficiency Algorithm verdict is non-vacuous: it yields a nonzero stoichiometric vector.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (h : N.ADAAffirmsCapacity) : N.stoichSubspace ≠ ⊥ :=
  N.stoichSubspace_ne_bot_of_adaAffirmsCapacity h

-- Nagumo-based persistence: a genuine mass-action orbit with an inward dissipativity bound stays
-- in the closed nonnegative orthant for all forward time.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) {L : ℝ}
    {γ : ℝ → Concentration S} (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hLip : ∀ t s, -L * (γ t s) ≤ N.massActionVectorField κ (γ t) s ∨ 0 ≤ γ t s)
    (h0 : (γ 0).Nonnegative) : ∀ t, 0 ≤ t → (γ t).Nonnegative :=
  N.massAction_orbit_nonneg κ hderiv hLip h0

-- Michaelis–Menten boundary layer: the enzyme fast subsystem is a bundled fast subsystem.
example : ODE.FastSubsystem CRNT.MichaelisMenten.E :=
  CRNT.MichaelisMenten.enzymeFastSubsystem 1 (by norm_num) 0

-- Stochastic jump chain: the jump probabilities sum to one wherever the exit rate is positive.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (n : S → ℕ) (h : 0 < N.exitRate κ n) : (∑ r : N.R, N.jumpProb κ n r) = 1 :=
  N.sum_jumpProb_eq_one κ n h

-- Conformal decomposition: every nonzero vector of a subspace is a sum of conforming dominators.
example {ι : Type} [Fintype ι] {S : Submodule ℝ (ι → ℝ)} {v : ι → ℝ} (hv : v ∈ S) (hv0 : v ≠ 0) :
    ∃ L : List (ι → ℝ), L.sum = v ∧ ∀ w ∈ L, CRNT.ConfDom S v w :=
  CRNT.exists_conformalSum hv hv0

-- Hopf crossing gate: at the boundary of the cubic Hurwitz region (`a₂a₁ = a₀`) the conjugate
-- pair is purely imaginary and the real root is negative.
example (z₁ z₂ : ℂ) (a₂ a₁ a₀ : ℝ) (hz₁im : z₁.im = 0)
    (e₂ : (a₂ : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : (a₁ : ℂ) = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (a₀ : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < a₂) (H₀ : 0 < a₀) (HΔ : a₂ * a₁ = a₀) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0 :=
  CRNT.hopf_crossing_gate z₁ z₂ a₂ a₁ a₀ hz₁im e₂ e₁ e₀ H₂ H₀ HΔ

-- Degree-4 Hopf crossing gate: at the boundary of the quartic Hurwitz region (`Δ₃ = 0`) one
-- conjugate pair goes purely imaginary while the other stays in the open left half-plane.
example (z₁ z₃ : ℂ) (a₃ a₂ a₁ a₀ : ℝ)
    (e₃ : (a₃ : ℂ) = -(z₁ + (starRingEnd ℂ) z₁ + z₃ + (starRingEnd ℂ) z₃))
    (e₂ : (a₂ : ℂ) = z₁ * (starRingEnd ℂ) z₁ + z₁ * z₃ + z₁ * (starRingEnd ℂ) z₃
      + (starRingEnd ℂ) z₁ * z₃ + (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃ + z₃ * (starRingEnd ℂ) z₃)
    (e₁ : (a₁ : ℂ) = -(z₁ * (starRingEnd ℂ) z₁ * z₃ + z₁ * (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃
      + z₁ * z₃ * (starRingEnd ℂ) z₃ + (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃))
    (e₀ : (a₀ : ℂ) = z₁ * (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃)
    (H₃ : 0 < a₃) (H₀ : 0 < a₀) (HΔ : a₁ ^ 2 + a₃ ^ 2 * a₀ = a₃ * a₂ * a₁) :
    (z₁.re = 0 ∧ z₁.im ≠ 0 ∧ z₃.re < 0) ∨ (z₃.re = 0 ∧ z₃.im ≠ 0 ∧ z₁.re < 0) :=
  CRNT.hopf_crossing_gate_quartic z₁ z₃ a₃ a₂ a₁ a₀ e₃ e₂ e₁ e₀ H₃ H₀ HΔ

-- One-dimensional Sperner lemma: a Sperner-colored path (false at 0, true at n) has a
-- color-change edge — the base case of the Sperner→Brouwer development.
example {n : ℕ} {c : ℕ → Bool} (h : CRNT.Analysis.Sperner.IsSpernerColoring n c) :
    ∃ i < n, c (i + 1) ≠ c i :=
  CRNT.Analysis.Sperner.sperner_exists_rainbow h

-- Persistence substrate: the siphon-face distance functional is nonnegative on nonnegative
-- concentrations (the Lyapunov functional behind face forward-invariance).
example {S : Type} [DecidableEq S] [Fintype S] {P : Finset S} {x : Concentration S}
    (hx : x.Nonnegative) : 0 ≤ Network.faceSum P x :=
  Network.faceSum_nonneg hx

-- Fenichel slow manifold: each layer fibre of fast-equilibria is the single point of the graph
-- (uniqueness of the attracting slow manifold).
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : ODE.SlowManifold Y E)
    (y : Y) : {w : E | M.fast y w = 0} = {M.h y} :=
  M.fiber_eq_singleton y

-- 2-D Sperner core: a triangle has an odd number of {0,1}-doors iff it is rainbow (3-colored).
example (a b c : CRNT.Analysis.Sperner2D.Color) :
    Odd (CRNT.Analysis.Sperner2D.doorCount a b c) ↔ CRNT.Analysis.Sperner2D.isRainbow a b c :=
  CRNT.Analysis.Sperner2D.doorCount_odd_iff a b c

-- Unconditional confined persistence: a box-confined nonnegative mass-action orbit starting on a
-- siphon face stays on it for all forward time (the dissipativity hypothesis is discharged).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {γ : ℝ → Concentration S} {B : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hbox : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ B)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_confined κ hP hderiv hnn hbox h0

-- Constructed Fenichel slow manifold: the fibre-equilibrium graph map is stationary by construction.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : ODE.SlowManifoldSeed Y E)
    (y : Y) : M.fast y (M.manifoldMap y) = 0 :=
  M.manifoldMap_stat y

-- Fenichel ε-persistence (graph-transform core): the perturbed invariant manifold M_ε is the unique
-- fixed-point section of the Lyapunov–Perron graph transform, O(ε)-C⁰-close to the unperturbed M_0.
open scoped BoundedContinuousFunction in
example {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [CompleteSpace E]
    (G : ODE.GraphTransformData Y E) :
    G.op G.manifold = G.manifold ∧ dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ⟨G.manifold_isFixedPt, G.manifold_dist_base_le⟩

-- Fenichel ε-persistence (flow invariance): for graph-transform data realized by a coupled slow–fast
-- flow at a fixed point of the flow-then-regraph operator, the graph of the persisted manifold M_ε is
-- forward-invariant under the coupled flow and O(ε)-C⁰-close to the unperturbed M_0 — the two halves
-- of persistence.
open scoped BoundedContinuousFunction in
example {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    (G : ODE.GraphTransformData Y E) (F : ODE.CoupledFlowGraphTransform Y E)
    (hfix : F.op (G.manifold : Y → E) = (G.manifold : Y → E)) :
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (ODE.graphSet (G.manifold : Y → E)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le G F hfix

-- Local center manifold (Lyapunov–Perron): when the spectral gap K·δ < α between center and
-- hyperbolic directions dominates the nonlinearity's Lipschitz constant, the center-manifold operator
-- contracts, and its unique fixed-point section h is locally invariant (op h = h) and C⁰-close to the
-- center subspace (the zero section), the C⁰ form of tangency.
open scoped BoundedContinuousFunction in
example {Ec Eh : Type*} [TopologicalSpace Ec] [NormedAddCommGroup Eh] [CompleteSpace Eh]
    (M : ODE.CenterManifoldData Ec Eh) :
    M.op M.manifold = M.manifold ∧
      dist M.base M.manifold ≤ M.defect / (1 - M.lpConst * M.lip / M.rate) :=
  ⟨M.manifold_isFixedPt, M.manifold_dist_zero_le⟩

-- Center-manifold reduction principle (Carr): the transverse gap of a full orbit to the center
-- manifold graph obeys the horizon-uniform dissipative ceiling g 0 + δ/λ (attraction to the
-- manifold), and the reduced field on the center subspace is the center projection of the full field
-- on the manifold, so an on-manifold orbit's center component solves ċ = reducedField c.
example {Ec Eh : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec]
    [NormedAddCommGroup Eh] [InnerProductSpace ℝ Eh]
    (R : ODE.ReductionData Ec Eh) {c : ℝ → Ec} {y : ℝ → Eh} {T : ℝ}
    (g g' : ℝ → ℝ) (hg_def : ∀ t, g t = ‖y t - R.graph (c t)‖)
    (hg : ContinuousOn g (Set.Icc 0 T))
    (hg' : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt g (g' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico 0 T, g' x ≤ -R.rate * g x + R.defect)
    {t : ℝ} (hc : HasDerivAt c (R.field (c t, R.graph (c t))).1 t) :
    (∀ s ∈ Set.Icc 0 T, g s ≤ g 0 + R.defect / R.rate) ∧
      HasDerivAt c (R.reducedField (c t)) t :=
  ⟨R.transverse_gap_ceiling g g' hg_def hg hg' hbound, R.onManifold_center_velocity hc⟩

-- Confined invariance closed: a genuine mass-action orbit with bounded relative entropy that starts
-- on a siphon face stays on it for all forward time (the box hypothesis is discharged).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {C : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ C)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_of_relEntropy_le κ hP hxs hderiv hnn hrele h0

-- True Michaelis–Menten slow-manifold reduction: the substrate-dependent complex equilibrium is the
-- Michaelis–Menten rate law `V_max·s/(K_m+s)`.
example (Km Vmax s : ℝ) :
    CRNT.MichaelisMenten.mmComplexEquil Km Vmax s = Vmax * s / (Km + s) :=
  rfl

-- The constructed Michaelis–Menten slow manifold is C¹ on the substrate ray `s ≥ 0`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiffOn ℝ 1 (CRNT.MichaelisMenten.mmSlowManifoldSeed rate hrate Km Vmax).manifoldMap
      (Set.Ici 0) :=
  CRNT.MichaelisMenten.mmManifoldMap_contDiffOn rate hrate Km Vmax hKm

-- The Michaelis–Menten fast field has the invertible fibre derivative `-rate • id`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax s : ℝ) :
    HasFDerivAt (CRNT.MichaelisMenten.mmFastField rate Km Vmax s)
      (CRNT.MichaelisMenten.mmFibreDeriv rate hrate : CRNT.MichaelisMenten.E →L[ℝ]
        CRNT.MichaelisMenten.E)
      (CRNT.MichaelisMenten.mmComplexEquil Km Vmax s • CRNT.MichaelisMenten.e0) :=
  CRNT.MichaelisMenten.mmFastField_hasFDerivAt_fibre rate hrate Km Vmax s

-- The globally-C¹ regularized Michaelis–Menten seed has its constructed slow manifold C¹ over the
-- whole substrate line, through the abstract implicit-function API, agreeing with the true MM
-- complex-equilibrium curve on the physical ray `s ≥ 0`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) :
    ContDiff ℝ 1 (CRNT.MichaelisMenten.mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap :=
  CRNT.MichaelisMenten.mmRegManifoldMap_contDiff rate hrate Km Vmax hKm

example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) {s : ℝ} (hs : 0 ≤ s) :
    (CRNT.MichaelisMenten.mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap s
      = CRNT.MichaelisMenten.mmComplexEquil Km Vmax s • CRNT.MichaelisMenten.e0 :=
  CRNT.MichaelisMenten.mmRegManifoldMap_eq_mm rate hrate Km Vmax hKm hs

-- Full 2-D Sperner over any door incidence: a Sperner-colored triangulation has a rainbow triangle.
example {Cell : Type*} [Fintype Cell] (D : CRNT.Analysis.SpernerTriangulation.DoorIncidence Cell) :
    ∃ t : Cell, D.IsRainbowCell t :=
  D.exists_rainbow

-- Boundary relative-entropy descent: a complex-balanced-referenced orbit positive on (0,∞) and
-- nonnegative at 0, starting on a siphon face, stays on it (positivity only away from t=0).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hpos : ∀ t, 0 < t → (γ t).Positive) (hnn0 : (γ 0).Nonnegative)
    (h0 : γ 0 ∈ N.SiphonFace P) : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_of_complexBalanced_pos_pos κ hP hxs hcb hderiv hpos hnn0 h0

-- Michaelis–Menten reduced field: the substrate slow-flow field is the MM rate law `-V_max·s/(K_m+s)`
-- on the forward ray (extended by 0 for s < 0).
example (Km Vmax s : ℝ) :
    CRNT.MichaelisMenten.mmReducedField Km Vmax s = (if 0 ≤ s then -(Vmax * s / (Km + s)) else 0) :=
  rfl

-- Certified Michaelis–Menten reduction: the constructed substrate flow is confined to `[0, s₀]` for
-- all forward time by its monotone depletion, the all-time bound resting on no horizon.
example (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) {s₀ : ℝ} (hs0 : 0 ≤ s₀) {t : ℝ} (ht : 0 ≤ t) :
    CRNT.MichaelisMenten.mmSubstrate Km Vmax hKm hV s₀ t ∈ Set.Icc (0 : ℝ) s₀ :=
  CRNT.MichaelisMenten.mmSubstrate_mem_Icc Km Vmax hKm hV hs0 ht

-- Concrete 2-D Sperner: the explicitly-constructed single-cell triangulation has a rainbow triangle
-- (the full DoorIncidence → rainbow pipeline on a genuine `Fintype` cell type).
example : ∃ t : CRNT.Analysis.SpernerGrid.Cell,
    CRNT.Analysis.SpernerGrid.doorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerGrid.exists_rainbow_cell

-- Multi-outer-vertex 2-D Sperner handshaking: over a door graph on `Cell ⊕ Outer` (one outer vertex
-- per boundary sub-edge, no single-vertex collapse), odd-degree cells matching `rainbow` plus an odd
-- number of odd-degree outer vertices force an odd rainbow-triangle count.
example {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]
    (G : SimpleGraph (Cell ⊕ Outer)) [DecidableRel G.Adj]
    (rainbow : Cell → Prop) [DecidablePred rainbow]
    (hcell : ∀ x : Cell, Odd (G.degree (Sum.inl x)) ↔ rainbow x)
    (houter : Odd #{o : Outer | Odd (G.degree (Sum.inr o))}) :
    ∃ x : Cell, rainbow x :=
  CRNT.Analysis.Sperner2D.multiDoorGraph_exists_rainbow G rainbow hcell houter

-- Multi-outer-vertex door-incidence interface: the uncollapsed `DoorIncidence` (one outer vertex per
-- boundary sub-edge) yields the 2-D Sperner conclusion from bundled degree/parity facts.
example {Cell Outer : Type*} [Fintype Cell] [Fintype Outer]
    (D : CRNT.Analysis.SpernerTriangulation.MultiDoorIncidence Cell Outer) :
    ∃ t : Cell, D.IsRainbowCell t :=
  D.exists_rainbow

-- Concrete multi-triangle 2-D Sperner: the N=2 barycentric subdivision (four cells, one interior door
-- and one boundary door) has a rainbow triangle — the full multi-outer pipeline on a real triangulation.
example : ∃ t : CRNT.Analysis.SpernerN2.Cell,
    CRNT.Analysis.SpernerN2.multiDoorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerN2.exists_rainbow_cell

-- The rainbow triangle is exactly the central inverted triangle `dn`.
example : CRNT.Analysis.SpernerN2.multiDoorIncidence.IsRainbowCell CRNT.Analysis.SpernerN2.Cell.dn := by
  decide

-- Geometric derivation: the N=2 door graph built from vertices+coloring (not a hand-listed edge set)
-- still yields a rainbow triangle, with the lattice-edge incidence lemma proved from `triVerts`.
example : ∃ t : CRNT.Analysis.SpernerN2Geo.Cell,
    CRNT.Analysis.SpernerN2Geo.multiDoorIncidence.IsRainbowCell t :=
  CRNT.Analysis.SpernerN2Geo.exists_rainbow_cell

-- The lattice-edge incidence lemma: the interior door edge `mAB–mAC` borders exactly two triangles.
example (t : CRNT.Analysis.SpernerN2Geo.Cell) :
    (CRNT.Analysis.SpernerN2Geo.Vertex.mAB ∈ CRNT.Analysis.SpernerN2Geo.triVerts t ∧
      CRNT.Analysis.SpernerN2Geo.Vertex.mAC ∈ CRNT.Analysis.SpernerN2Geo.triVerts t) ↔
      (t = .up1 ∨ t = .dn) :=
  CRNT.Analysis.SpernerN2Geo.interior_doorEdge_borders_two t

-- Arbitrary-N parametric subdivision (geometry layer): every triangle of the N-subdivision has
-- exactly three vertices — the basis for its three edges and door count.
example {N : ℕ} (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.triVerts c).card = 3 :=
  CRNT.Analysis.SpernerLattice.triVerts_card c

-- Arbitrary-N Sperner boundary conditions: the corner (N,0) is colored 0 under any proper coloring.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    κ.color (CRNT.Analysis.SpernerLattice.mkPt N 0 (by omega)) = 0 :=
  CRNT.Analysis.SpernerLattice.corner_color_i κ

-- ...and a boundary side omits the opposite color: on `i + j = N` the color is never 2.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (i j : ℕ) (h : i + j = N) :
    κ.color (CRNT.Analysis.SpernerLattice.mkPt i j (by omega)) ≠ 2 :=
  CRNT.Analysis.SpernerLattice.side_ij_ne_two κ i j h

-- Lattice-edge incidence lemma (any N): an interior diagonal edge borders exactly two triangles,
-- `up(i,j)` and `down(i,j)`.
example (N i j : ℕ) (hd : i + j + 2 ≤ N) (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.mkPt (i + 1) j (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c ∧
      CRNT.Analysis.SpernerLattice.mkPt i (j + 1) (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c) ↔
      (c = Sum.inl ⟨(i, j), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩ ∨
        c = Sum.inr ⟨(i, j), by rw [CRNT.Analysis.SpernerLattice.mem_downCarrier]; omega⟩) :=
  CRNT.Analysis.SpernerLattice.diag_incidence_interior N i j hd c

-- Lattice-edge incidence (vertical, any N): a boundary vertical edge on the left side bounds exactly
-- one triangle, `up(0,j)`.
example (N j : ℕ) (hj : j + 1 ≤ N) (c : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.mkPt 0 j (by omega) ∈ CRNT.Analysis.SpernerLattice.triVerts c ∧
      CRNT.Analysis.SpernerLattice.mkPt 0 (j + 1) (by omega) ∈
        CRNT.Analysis.SpernerLattice.triVerts c) ↔
      c = Sum.inl ⟨(0, j), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩ :=
  CRNT.Analysis.SpernerLattice.vert_incidence_boundary N j hj c

-- Door confinement (any N): a horizontal edge on the bottom side is never a {0,1} door, so boundary
-- doors are confined to the k=0 side (the setup that collapses the door graph's outer vertices).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a : ℕ) (ha : a + 1 ≤ N) :
    CRNT.Analysis.Sperner2D.isDoor (κ.color (CRNT.Analysis.SpernerLattice.mkPt a 0 (by omega)))
      (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) 0 (by omega))) = false :=
  CRNT.Analysis.SpernerLattice.bottom_H_not_door κ a ha

-- Door graph assembly: the cell adjacency (sharing a {0,1} door edge) is symmetric.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {t t' : CRNT.Analysis.SpernerLattice.Cell N} (h : CRNT.Analysis.SpernerLattice.CellDoor κ t t') :
    CRNT.Analysis.SpernerLattice.CellDoor κ t' t :=
  CRNT.Analysis.SpernerLattice.cellDoor_symm κ h

-- Door graph bipartite: two up-triangles are never door-adjacent (same orientation shares ≤1 vertex).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (u u' : CRNT.Analysis.SpernerLattice.Up N) :
    ¬ CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) (Sum.inl u') :=
  CRNT.Analysis.SpernerLattice.not_cellDoor_inl_inl κ u u'

-- Neighbor locator: a door-neighbor of an up-triangle is a down-triangle.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {u : CRNT.Analysis.SpernerLattice.Up N} {t' : CRNT.Analysis.SpernerLattice.Cell N}
    (h : CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) t') :
    ∃ d : CRNT.Analysis.SpernerLattice.Down N, t' = Sum.inr d :=
  CRNT.Analysis.SpernerLattice.cellDoor_inl_isRight κ h

-- The cell–cell door graph's adjacency is the `CellDoor` relation.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t t' : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.cellDoorGraph κ).Adj t t'
      ↔ CRNT.Analysis.SpernerLattice.CellDoor κ t t' :=
  CRNT.Analysis.SpernerLattice.cellDoorGraph_adj κ t t'

-- The full door graph: cell–cell adjacency is `CellDoor`; cell–outer adjacency joins an outer
-- vertex to its up-triangle exactly when its hypotenuse sub-edge is a door.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t t' : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl t) (Sum.inl t')
      ↔ CRNT.Analysis.SpernerLattice.CellDoor κ t t' :=
  CRNT.Analysis.SpernerLattice.fullDoorGraph_adj_inl_inl κ t t'
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t : CRNT.Analysis.SpernerLattice.Cell N) (k : CRNT.Analysis.SpernerLattice.Outer N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl t) (Sum.inr k)
      ↔ t = CRNT.Analysis.SpernerLattice.outerTri k ∧ CRNT.Analysis.SpernerLattice.BoundaryDoor κ k :=
  CRNT.Analysis.SpernerLattice.fullDoorGraph_adj_inl_inr κ t k

-- An outer vertex has degree 1 if its hypotenuse sub-edge is a door, else 0.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (k : CRNT.Analysis.SpernerLattice.Outer N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr k)
      = if CRNT.Analysis.SpernerLattice.BoundaryDoor κ k then 1 else 0 :=
  CRNT.Analysis.SpernerLattice.outer_degree κ k

-- An outer vertex has odd degree exactly when its sub-edge is a door.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (k : CRNT.Analysis.SpernerLattice.Outer N) :
    Odd ((CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr k))
      ↔ CRNT.Analysis.SpernerLattice.BoundaryDoor κ k :=
  CRNT.Analysis.SpernerLattice.odd_degree_outer_iff κ k

-- The `outer_odd` obligation: the number of odd-degree outer vertices is odd (1-D Sperner on the
-- hypotenuse).
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    Odd #{o : CRNT.Analysis.SpernerLattice.Outer N |
      Odd ((CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inr o))} :=
  CRNT.Analysis.SpernerLattice.outer_odd_count κ

-- A door-neighbour of an up-triangle is pinned to one of its three lattice partners.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    {u : CRNT.Analysis.SpernerLattice.Up N} {d : CRNT.Analysis.SpernerLattice.Down N}
    (h : CRNT.Analysis.SpernerLattice.CellDoor κ (Sum.inl u) (Sum.inr d)) :
    (d.1.1 = u.1.1 ∧ d.1.2 = u.1.2) ∨ (d.1.1 = u.1.1 ∧ d.1.2 + 1 = u.1.2) ∨
      (d.1.1 + 1 = u.1.1 ∧ d.1.2 = u.1.2) :=
  CRNT.Analysis.SpernerLattice.up_cellDoor_partner κ h
-- A down-triangle is never adjacent to an outer vertex.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (d : CRNT.Analysis.SpernerLattice.Down N) (k : CRNT.Analysis.SpernerLattice.Outer N) :
    ¬ (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).Adj (Sum.inl (Sum.inr d)) (Sum.inr k) :=
  CRNT.Analysis.SpernerLattice.down_not_adj_outer κ d k

-- A down-triangle's door-graph degree equals its local door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a b : ℕ) (hd : a + b + 2 ≤ N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree
        (Sum.inl (Sum.inr ⟨(a, b), by rw [CRNT.Analysis.SpernerLattice.mem_downCarrier]; omega⟩))
      = CRNT.Analysis.Sperner2D.doorCount
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a (b + 1) (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) (b + 1) (by omega))) :=
  CRNT.Analysis.SpernerLattice.down_cell_degree κ a b hd

-- An up-triangle's door-graph degree equals its local door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) (a b : ℕ) (hu : a + b + 1 ≤ N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree
        (Sum.inl (Sum.inl ⟨(a, b), by rw [CRNT.Analysis.SpernerLattice.mem_upCarrier]; omega⟩))
      = CRNT.Analysis.Sperner2D.doorCount
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt (a + 1) b (by omega)))
          (κ.color (CRNT.Analysis.SpernerLattice.mkPt a (b + 1) (by omega))) :=
  CRNT.Analysis.SpernerLattice.up_cell_degree κ a b hu

-- **The cell-degree obligation**: every triangle's door-graph degree equals its door count.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N)
    (t : CRNT.Analysis.SpernerLattice.Cell N) :
    (CRNT.Analysis.SpernerLattice.fullDoorGraph κ).degree (Sum.inl t)
      = CRNT.Analysis.Sperner2D.doorCount (CRNT.Analysis.SpernerLattice.col κ t).1
          (CRNT.Analysis.SpernerLattice.col κ t).2.1 (CRNT.Analysis.SpernerLattice.col κ t).2.2 :=
  CRNT.Analysis.SpernerLattice.cell_degree κ t

-- **Two-dimensional Sperner lemma (parametric N)**: every proper Sperner coloring of the
-- N-subdivision of the 2-simplex has a rainbow triangle.
example {N : ℕ} (κ : CRNT.Analysis.SpernerLattice.SpernerColoring N) :
    ∃ t : CRNT.Analysis.SpernerLattice.Cell N,
      CRNT.Analysis.Sperner2D.isRainbow (CRNT.Analysis.SpernerLattice.col κ t).1
        (CRNT.Analysis.SpernerLattice.col κ t).2.1
        (CRNT.Analysis.SpernerLattice.col κ t).2.2 = true :=
  CRNT.Analysis.SpernerLattice.exists_rainbow_cell κ

-- The barycentric realization lands in the standard 2-simplex.
example : CRNT.Analysis.SpernerLattice.realize
      (CRNT.Analysis.SpernerLattice.mkPt 1 1 (by omega) : CRNT.Analysis.SpernerLattice.Pt 3)
    ∈ stdSimplex ℝ (Fin 3) :=
  CRNT.Analysis.SpernerLattice.realize_mem_stdSimplex (by norm_num) _

-- Meshing sequences along which a continuous self-map is coordinate-non-increasing yield a fixed pt.
example (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (hf : Continuous f)
    (x : Fin 3 → ℕ → ↥(stdSimplex ℝ (Fin 3)))
    (hmesh : ∀ i j : Fin 3, Filter.Tendsto (fun n => dist (x i n) (x j n)) Filter.atTop (nhds 0))
    (hdec : ∀ (n : ℕ) (i : Fin 3), (f (x i n) : Fin 3 → ℝ) i ≤ ((x i n : Fin 3 → ℝ) i)) :
    ∃ z : ↥(stdSimplex ℝ (Fin 3)), f z = z :=
  CRNT.Analysis.brouwer_of_meshing_sequences f hf x hmesh hdec

-- **Two-dimensional Brouwer fixed-point theorem**: every continuous self-map of the standard
-- 2-simplex has a fixed point.
example (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (hf : Continuous f) :
    ∃ z, f z = z :=
  CRNT.Analysis.SpernerLattice.brouwer_stdSimplex_fin3 f hf
-- **The n-dimensional Brouwer fixed-point theorem**: every continuous self-map of the standard
-- n-simplex `stdSimplex ℝ (Fin (n+1))` has a fixed point, for every `n`.
example (n : ℕ) (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1))))
    (hf : Continuous f) : ∃ z, f z = z :=
  CRNT.Analysis.SpernerN.brouwer_stdSimplex_fin n f hf
-- **Brouwer on the unit cube**: every continuous self-map of `Set.Icc 0 1 ⊆ Fin n → ℝ` has a fixed point.
example (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : Set.MapsTo f (Set.Icc (0 : Fin n → ℝ) 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x = x :=
  CRNT.Analysis.brouwer_cube f hf hmaps
-- **The Poincaré–Miranda theorem**: a continuous map on the cube with the standard boundary sign
-- conditions on each pair of opposite faces has a zero.
example (n : ℕ) (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hlo : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 0 → f x i ≤ 0)
    (hhi : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 1 → 0 ≤ f x i) :
    ∃ x ∈ Set.Icc (0 : Fin n → ℝ) 1, f x = 0 :=
  CRNT.Analysis.poincare_miranda f hf hlo hhi
-- **Brouwer for compact convex sets**: every continuous self-map of a nonempty compact convex
-- subset of `EuclideanSpace ℝ (Fin n)` has a fixed point.
example {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f K) (hmaps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
  CRNT.Analysis.brouwer_compact_convex hne hconv hcomp f hf hmaps
example {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 :=
  CRNT.Analysis.exists_zero_of_displacement_mapsTo hne hconv hcomp v hv hmaps

-- n-D Kuhn-triangulation framework: every cell has exactly n+1 vertices; lattice points realize
-- into the standard n-simplex; the corners realize to the basis vectors.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) : c.simplexVerts.card = n + 1 :=
  c.simplexVerts_card
example {n N : ℕ} (hN : 0 < N) (p : CRNT.Analysis.SpernerN.Pt n N) :
    CRNT.Analysis.SpernerN.realize p ∈ stdSimplex ℝ (Fin (n + 1)) :=
  CRNT.Analysis.SpernerN.realize_mem_stdSimplex hN p
example {n N : ℕ} (hN : 0 < N) (i : Fin (n + 1)) :
    CRNT.Analysis.SpernerN.realize (CRNT.Analysis.SpernerN.corner n N i) = Pi.single i 1 :=
  CRNT.Analysis.SpernerN.realize_corner hN i

-- n-D Kuhn cell mesh bound: any two vertices of a cell realize within sup-distance 1/N.
example {n N : ℕ} (hN : 0 < N) (c : CRNT.Analysis.SpernerN.Cell n N) (k k' : Fin (n + 1)) :
    dist (CRNT.Analysis.SpernerN.realize (c.vertex k))
        (CRNT.Analysis.SpernerN.realize (c.vertex k')) ≤ 1 / N :=
  CRNT.Analysis.SpernerN.cell_vertex_dist_le hN c k k'

-- n-D local Sperner parity: a colored cell has an odd door count iff it is fully labeled.
example {n : ℕ} (c : Fin (n + 1) → Fin (n + 1)) :
    Odd (CRNT.Analysis.SpernerN.doorCount c) ↔ Function.Bijective c :=
  CRNT.Analysis.SpernerN.doorCount_odd_iff c

-- n-D Kuhn facet incidence: the adjacent-transposition flip shares the dropped facet and is distinct.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) +
      CRNT.Analysis.SpernerN.voff (CRNT.Analysis.SpernerN.flipPerm c.perm m hm0 hmn) m i) :
    CRNT.Analysis.SpernerN.facetVerts (CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv) m
        = CRNT.Analysis.SpernerN.facetVerts c m
      ∧ CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv ≠ c :=
  ⟨CRNT.Analysis.SpernerN.flipCell_facet c m hm0 hmn hv,
    CRNT.Analysis.SpernerN.flipCell_ne c m hm0 hmn hv⟩

-- A Kuhn cell is determined by its vertex function.
example {n N : ℕ} {c c' : CRNT.Analysis.SpernerN.Cell n N}
    (h : ∀ k, c.vertex k = c'.vertex k) : c = c' :=
  CRNT.Analysis.SpernerN.Cell.ext_of_vertex_eq h
-- Facet-incidence index rigidity: a shared interior-chain facet forces the dropped index and base sum.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell n N) (m m' : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : CRNT.Analysis.SpernerN.facetVerts c m = CRNT.Analysis.SpernerN.facetVerts c' m') :
    m' = m ∧ CRNT.Analysis.SpernerN.Wb c = CRNT.Analysis.SpernerN.Wb c' :=
  CRNT.Analysis.SpernerN.facet_eq_index c c' m m' hm0 hmn heq
-- Two permutations agreeing off a 2-element set are equal or differ by that transposition.
example {α : Type} [DecidableEq α] (σ σ' : Equiv.Perm α) (a b : α) (hab : a ≠ b)
    (h : ∀ l, l ≠ a → l ≠ b → σ' l = σ l) : σ' = σ ∨ σ' = σ * Equiv.swap a b :=
  CRNT.Analysis.SpernerN.perm_eq_or_swap σ σ' a b hab h
-- Facet-incidence rigidity: any cell sharing an interior-chain facet is the cell or its flip.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (heq : CRNT.Analysis.SpernerN.facetVerts c m = CRNT.Analysis.SpernerN.facetVerts c' m) :
    c' = c ∨ ∃ hv, c' = CRNT.Analysis.SpernerN.flipCell c m hm0 hmn hv :=
  CRNT.Analysis.SpernerN.facet_eq_imp c c' m hm0 hmn heq
-- n-D Sperner extreme-facet rigidity: a cell sharing the vertex-0 facet is the cell itself or its
-- base-change neighbour (the shiftCell), the extreme analogue of facet_eq_imp.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : CRNT.Analysis.SpernerN.facetVerts c 0 = CRNT.Analysis.SpernerN.facetVerts c' m') :
    c' = c ∨ ∃ h : CRNT.Analysis.SpernerN.ShiftValid c, c' = CRNT.Analysis.SpernerN.shiftCell c h :=
  CRNT.Analysis.SpernerN.facet0_eq_imp c c' m' heq
-- n-D Sperner boundary reduction: dropping the last coordinate is a bijection from the boundary
-- face {x_last = 0} of the (n+1)-simplex to the n-dimensional lattice.
example {n N : ℕ} (q : CRNT.Analysis.SpernerN.Pt n N) (i : Fin (n + 1)) :
    ((CRNT.Analysis.SpernerN.boundaryEquiv n N).symm q).1.1 i.castSucc = q.1 i :=
  CRNT.Analysis.SpernerN.boundaryEquiv_symm_apply_castSucc q i
-- A door facet lying on a boundary face `{x_j = 0}` must lie on the face opposite the top color.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (col : CRNT.Analysis.SpernerN.SpernerColoring n N) (j : Fin (n + 1))
    (hdoor : (CRNT.Analysis.SpernerN.facetVerts c m).image col.color
      = CRNT.Analysis.SpernerN.lowColors n)
    (hface : ∀ p ∈ CRNT.Analysis.SpernerN.facetVerts c m, p.1 j = 0) : j = Fin.last n :=
  CRNT.Analysis.SpernerN.door_face_eq_last c m col j hdoor hface
-- Restricting an (n+1)-D Sperner coloring along the boundary face yields an n-D Sperner coloring;
-- on the face, its color (recast up) matches the original.
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N)
    (p : CRNT.Analysis.SpernerN.Pt (n + 1) N) (hp : p.1 (Fin.last (n + 1)) = 0) :
    ((CRNT.Analysis.SpernerN.restrictColoring col).color
        (CRNT.Analysis.SpernerN.boundaryEquiv n N ⟨p, hp⟩)).castSucc = col.color p :=
  CRNT.Analysis.SpernerN.restrictColoring_color_of_boundary col p hp
-- n-D Sperner boundary geometry: a cell vertex lies on the face x_last=0 iff the cell touches the
-- face (base_last=1) and the vertex comes after the d_last step.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (k : Fin (n + 2)) :
    (c.vertex k).1 (Fin.last (n + 1)) = 0
      ↔ (c.base (Fin.last (n + 1)) = 1
          ∧ ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)) :=
  CRNT.Analysis.SpernerN.vertex_last_zero_iff c k
-- The recursion crux: a boundary door facet of an (n+1)-cell ⟺ its (n-1)-cell is rainbow under the
-- restricted coloring — the bridge that makes #boundary doors = #rainbow (n-1)-cells.
example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N) :
    (CRNT.Analysis.SpernerN.facetVerts c 0).image col.color = CRNT.Analysis.SpernerN.lowColors (n + 1)
      ↔ Function.Bijective
          (fun k => (CRNT.Analysis.SpernerN.restrictColoring col).color
            ((CRNT.Analysis.SpernerN.bcell c hb hp0).vertex k)) :=
  CRNT.Analysis.SpernerN.door_iff_rainbow c hb hp0 col
-- n-D Kuhn cells form a finite type (the counting infrastructure for the handshaking induction).
noncomputable example {n N : ℕ} : Fintype (CRNT.Analysis.SpernerN.Cell n N) := inferInstance
-- An interior (flip-valid) facet borders exactly two Kuhn cells (the handshaking multiplicity).
noncomputable example {n N : ℕ} (c : CRNT.Analysis.SpernerN.Cell n N) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hv : CRNT.Analysis.SpernerN.FlipValid c m hm0 hmn) :
    (CRNT.Analysis.SpernerN.facetSharers c m).card = 2 :=
  CRNT.Analysis.SpernerN.facet_shared_by_two c m hm0 hmn hv
-- n-D Sperner geometric crux (G1): an interior-chain door facet is always flip valid, so it borders a
-- second cell (the door's color structure forbids it from lying on an interior coordinate face).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N)
    (c : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m : Fin (n + 2))
    (h0 : 0 < (m : ℕ)) (hn : (m : ℕ) < n + 1)
    (hdoor : CRNT.Analysis.SpernerN.IsDoorFacet col c m) :
    CRNT.Analysis.SpernerN.FlipValid c m h0 hn :=
  CRNT.Analysis.SpernerN.flipValid_of_doorFacet col c m h0 hn hdoor
-- An odd number of rainbow cells yields one (the final step of the n-D Sperner induction).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring n N)
    (h : Odd (Finset.univ.filter (CRNT.Analysis.SpernerN.IsRainbowCell col)).card) :
    ∃ c, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.exists_rainbow_of_odd col h
-- n-D Sperner base case (dimension 0): the single cell is rainbow.
example {N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring 0 N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell 0 N,
      Function.Bijective (fun k => col.color (c.vertex k)) :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow_zero col
-- n-D Sperner inductive bridge: the boundary door cells biject with the rainbow n-cells on the face,
-- so their counts agree (feeds the inductive hypothesis into the handshake).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring (n + 1) N) (hN : 0 < N) :
    (Finset.univ.filter (CRNT.Analysis.SpernerN.isBoundaryDoorCell col)).card
      = (Finset.univ.filter
          (CRNT.Analysis.SpernerN.IsRainbowCell (CRNT.Analysis.SpernerN.restrictColoring col))).card :=
  CRNT.Analysis.SpernerN.boundary_doors_eq_rainbow col hN
-- The n-dimensional Sperner lemma (unconditional): every proper Sperner coloring of the N-subdivided
-- n-simplex has a rainbow Kuhn cell, and the number of rainbow cells is odd.
example {m N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell m N, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow col hN
example {m N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    Odd (Finset.univ.filter (CRNT.Analysis.SpernerN.IsRainbowCell col)).card :=
  CRNT.Analysis.SpernerN.sperner_odd_rainbow col hN
-- n-D Sperner handshake: the door incidences have the same parity as the rainbow cells (the cell side
-- of the double-count).
example {n N : ℕ} (col : CRNT.Analysis.SpernerN.SpernerColoring n N) :
    (CRNT.Analysis.SpernerN.doorIncidences col).card % 2
      = (#{c : CRNT.Analysis.SpernerN.Cell n N | CRNT.Analysis.SpernerN.IsRainbowCell col c}) % 2 :=
  CRNT.Analysis.SpernerN.card_doorIncidences_mod_two col
-- n-D Sperner last-facet rigidity: a cell sharing the last-vertex facet is the cell or its
-- base-change predecessor.
example {n N : ℕ} (c c' : CRNT.Analysis.SpernerN.Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : CRNT.Analysis.SpernerN.facetVerts c (Fin.last (n + 1))
      = CRNT.Analysis.SpernerN.facetVerts c' m') :
    c' = c ∨ (m' = 0 ∧ ∃ h : CRNT.Analysis.SpernerN.ShiftValid c',
      CRNT.Analysis.SpernerN.shiftCell c' h = c) :=
  CRNT.Analysis.SpernerN.facetLast_eq_imp c c' m' heq
-- n-D Sperner: granting the handshake at every dimension, a rainbow cell exists in every dimension.
example (H : ∀ {N : ℕ}, CRNT.Analysis.SpernerN.SpernerHandshake (N := N)) {m N : ℕ}
    (col : CRNT.Analysis.SpernerN.SpernerColoring m N) (hN : 0 < N) :
    ∃ c : CRNT.Analysis.SpernerN.Cell m N, CRNT.Analysis.SpernerN.IsRainbowCell col c :=
  CRNT.Analysis.SpernerN.sperner_exists_rainbow_of_handshake H col hN

-- Ladder 2 (persistence): the conservation-law clause of siphon criticality equals membership in the
-- dot-product orthogonal complement of the stoichiometric subspace (the Farkas-feasibility entry point).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (v : S → ℝ) :
    (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) ↔ v ∈ CRNT.orthSum N.stoichSubspace :=
  N.conservationLaw_iff_mem_orthSum v

-- Ladder 2 (persistence): a conservation law (orthogonal to the stoichiometric subspace) is a constant
-- of motion — its weighted total is unchanged along every mass-action solution.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {w : S → ℝ} (hw : w ∈ CRNT.orthSum N.stoichSubspace)
    {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ) :
    ∑ s, w s * γ t s = ∑ s, w s * γ 0 s :=
  N.conservationLaw_const_along_solution κ hw ht hsol

-- Ladder 3 (Fenichel/QSSA): on the constructed slow manifold, an ε-slow slow path drives the slaved
-- fast variable with O(ε) displacement — the QSSA drift bound at the Lipschitz tier.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) {L ε : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|) (t t' : ℝ) :
    ‖S.manifoldMap (y t) - S.manifoldMap (y t')‖ ≤ (L / S.rate) * ε * |t - t'| :=
  S.manifoldMap_slowDrift_le hL hlip hy t t'

-- Ladder 3 (Fenichel/QSSA): the slaved slow-manifold curve's QSSA slaving defect decomposes into a
-- curve-velocity bound plus the full field's manifold residual, bounded by their sum εv + εr.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : ODE.SlowManifoldSeed Y E) (full : E → E) {y : ℝ → Y} {γᵣ' : ℝ → E} {a b εv εr : ℝ}
    (hvel : ∀ t ∈ Set.Ico a b, ‖γᵣ' t‖ ≤ εv)
    (hres : ∀ t ∈ Set.Ico a b, ‖full (S.manifoldMap (y t))‖ ≤ εr) :
    ODE.QssaDefect full (fun t => S.manifoldMap (y t)) γᵣ' a b (εv + εr) :=
  S.manifoldMap_qssaDefect_le full hvel hres

-- Ladder 3 (Fenichel/QSSA): when the slaved slow-manifold curve is differentiable, the converse
-- mean-value inequality derives an O(ε) velocity bound ‖γᵣ'‖ ≤ (L / rate) · ε.
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γᵣ' : ℝ → E} (t₀ : ℝ) (hd : HasDerivAt (fun t => S.manifoldMap (y t)) (γᵣ' t₀) t₀) :
    ‖γᵣ' t₀‖ ≤ (L / S.rate) * ε :=
  S.manifoldMap_slowDrift_velocity_le hL hε hlip hy t₀ hd

-- Fenichel C¹: a jointly-C¹ fast field with invertible fibre derivative makes the constructed
-- slow-manifold map genuinely C¹ via the implicit function theorem.
example {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : ODE.SlowManifoldC1Seed Y E) : ContDiff ℝ 1 S.manifoldMap :=
  S.contDiff_manifoldMap

-- Ladder 3 (Fenichel/QSSA): composing the derived O(ε) defect with the Grönwall QSSA engine, the
-- full integral curve tracks the slaved slow-manifold curve within a Grönwall ball on [0, T].
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace Y]
    (S : ODE.SlowManifoldSeed Y E) (full : E → E) {K : ℝ≥0} (hl : LipschitzWith K full)
    {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {y : ℝ → Y} (hcy : Continuous y) (hy : ∀ t t', dist (y t) (y t') ≤ ε * |t - t'|)
    {γ γᵣ' : ℝ → E} {T εr δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hεr : 0 ≤ εr)
    (hγd : ∀ t, HasDerivAt γ (full (γ t)) t)
    (hd : ∀ t ∈ Set.Ico (0:ℝ) T, HasDerivAt (fun u => S.manifoldMap (y u)) (γᵣ' t) t)
    (hres : ∀ t ∈ Set.Ico (0:ℝ) T, ‖full (S.manifoldMap (y t))‖ ≤ εr)
    (h0 : dist (γ 0) (S.manifoldMap (y 0)) ≤ δ) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      dist (γ t) (S.manifoldMap (y t)) ≤ gronwallBound δ K ((L / S.rate) * ε + εr) T :=
  S.manifoldMap_qssa_tracking_le full hl hL hε hlip hcy hy hT hδ hεr hγd hd hres h0

-- Ladder 3 (Fenichel/QSSA): the compact-time tracking ball vanishes as (δ, ε, εr) → (0, 0, 0).
example {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : ODE.SlowManifoldSeed Y E) (L : ℝ) (K : ℝ≥0) (T : ℝ) :
    Filter.Tendsto
      (fun p : ℝ × ℝ × ℝ => gronwallBound p.1 K ((L / S.rate) * p.2.1 + p.2.2) T)
      (nhds (0, 0, 0)) (nhds 0) :=
  S.manifoldMap_qssa_tracking_tendsto_zero L K T

-- Ladder 3 (Fenichel/MM): the constructed Michaelis-Menten substrate curve is monotonically depleted
-- (antitone) — a qualitative property of the reduced flow.
example (Km Vmax : ℝ) (hKm : 0 < Km) (hV : 0 ≤ Vmax) (s₀ : ℝ) :
    Antitone (CRNT.MichaelisMenten.mmSubstrate Km Vmax hKm hV s₀) :=
  CRNT.MichaelisMenten.mmSubstrate_antitone Km Vmax hKm hV s₀

-- Ladder 4 (CTMC): over a finite closed enabled region with positive mass, the normalized restricted
-- stationary measure is an invariant probability measure for the embedded jump kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite)
    (hpos : N.restrictedStationaryMeasure κ c T Set.univ ≠ 0) :
    MeasureTheory.IsProbabilityMeasure
      ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  (N.jumpKernel_normalized_isInvariant_probabilityMeasure κ c hc hcb hT hTfin hpos).2

-- Ladder 4 (CTMC): at a positive concentration on a nonempty finite closed enabled region the
-- positive-mass gate is discharged, so the normalized restricted stationary measure is an
-- unconditional invariant probability measure for the embedded jump kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty) :
    MeasureTheory.IsProbabilityMeasure
      ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) :=
  (N.jumpKernel_isInvariant_probabilityMeasure_of_nonempty κ c hc hcb hT hTfin hne).2

-- Ladder 4 (CTMC): at a positive concentration the normalized invariant jump-chain probability
-- measure is strictly positive on every singleton inside a nonempty finite closed enabled region.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty)
    {m : S → ℕ} (hm : m ∈ T) :
    0 < ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ •
        N.restrictedStationaryMeasure κ c T) {m} :=
  N.jumpKernel_invariantProb_singleton_pos κ c hc hT hTfin hne hm

-- Ladder 4 (CTMC): the normalized invariant jump-chain singleton masses inside a closed enabled
-- region are cross-multiplied proportional through the jump-chain stationary weights (the discrete
-- shadow of the Anderson–Craciun–Kurtz product form).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) {T : Set (S → ℕ)} {m m' : S → ℕ} (hm : m ∈ T) (hm' : m' ∈ T) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m')
      = ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ • N.restrictedStationaryMeasure κ c T) {m'}
        * ENNReal.ofReal (N.jumpStationaryMass κ c m) :=
  N.jumpKernel_invariantProb_singleton_ratio κ c hm hm'

-- Ladder 4 (CTMC): the normalized invariant jump-chain probability measure is nonzero on a
-- singleton exactly when the count lies in the nonempty finite closed enabled region.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) (hTfin : T.Finite) (hne : T.Nonempty)
    (m : S → ℕ) :
    ((N.restrictedStationaryMeasure κ c T Set.univ)⁻¹ •
        N.restrictedStationaryMeasure κ c T) {m} ≠ 0 ↔ m ∈ T :=
  N.jumpKernel_invariantProb_singleton_ne_zero_iff κ c hc hT hTfin hne m

-- Ladder 4 (CTMC): the canonical maximal closed enabled region is itself a closed enabled region
-- (arbitrary union of such regions is one), so it carries the invariant restricted stationary measure.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N) :
    N.ClosedEnabledRegion κ (N.maximalClosedEnabledRegion κ) :=
  N.closedEnabledRegion_maximal κ

-- Ladder 5 (CTMC semigroup): the uniformized transition kernel P_t = exp(tQ) on a finite region is
-- a Markov kernel for every time t.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (t : ℝ≥0) :
    ProbabilityTheory.IsMarkovKernel (N.cmeSemigroup κ hTfin t) :=
  N.instIsMarkovKernel_cmeSemigroup κ hTfin t

-- Ladder 5 (CTMC semigroup): the semigroup starts at the identity kernel, P_0 = id.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) :
    N.cmeSemigroup κ hTfin 0 = ProbabilityTheory.Kernel.id :=
  N.cmeSemigroup_zero κ hTfin

-- Ladder 5 (CTMC semigroup): the normalized product-Poisson law is invariant under every P_t — the
-- process-level companion of the generator stationarity πQ = 0.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (hT : N.ClosedEnabledRegion κ T) (t : ℝ≥0) :
    ProbabilityTheory.Kernel.Invariant (N.cmeSemigroup κ hTfin t)
      ((Network.cmeStationaryMeasure c T Set.univ)⁻¹ • Network.cmeStationaryMeasure c T) :=
  N.cmeSemigroup_preserves_stationarity κ c hc hcb hTfin hT t

-- The uniformized CME semigroup obeys the Chapman–Kolmogorov composition law P_{s+t} = P_s ∘ₖ P_t.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) (s t : ℝ≥0) :
    N.cmeSemigroup κ hTfin (s + t) =
      ProbabilityTheory.Kernel.comp (N.cmeSemigroup κ hTfin s) (N.cmeSemigroup κ hTfin t) :=
  N.cmeSemigroup_comp κ hTfin s t

-- The Poisson point masses convolve over the step-count antidiagonal.
example (r₁ r₂ : ℝ≥0) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        ProbabilityTheory.poissonMeasure r₁ {p.1} * ProbabilityTheory.poissonMeasure r₂ {p.2} =
      ProbabilityTheory.poissonMeasure (r₁ + r₂) {m} :=
  Network.poissonMeasure_singleton_conv r₁ r₂ m

-- An isolated invariant set cannot trap an ω-limit set without containing it (the Butler–McGehee
-- escape core) — here the ω-limit set is invariant.
open Filter in
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) :
    IsInvariant ϕ (omegaLimit atTop ϕ {x₀}) :=
  omegaLimit_isInvariant_two_sided ϕ x₀

-- The forward limit of any ω-point of a compact ω-limit set is again contained in it.
open Filter in
example {α : Type} [TopologicalSpace α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α} (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    {q : α} (hq : q ∈ omegaLimit atTop ϕ {x₀}) :
    omegaLimit atTop ϕ {q} ⊆ omegaLimit atTop ϕ {x₀} :=
  (CRNT.isCompact_isInvariant_nonempty_omegaLimit_of_mem ϕ x₀ hK habs hq).2.2.2

-- Strongly endotactic networks are endotactic.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.StronglyEndotactic) :
    N.Endotactic :=
  h.endotactic

-- The mass-action velocity always lies in the cone generated by the reaction vectors (the embedding
-- substrate for toric differential inclusions, Craciun, Toric differential inclusions…).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : Concentration.Nonnegative x) :
    N.massActionVectorField κ x ∈ N.reactionCone :=
  N.massActionVectorField_mem_reactionCone κ hx

-- The cyclic monomial-ordered velocity lies in the cone of consecutive differences (Abel summation;
-- the hypothesis is monotonicity of the coefficients).
example {S : Type} [DecidableEq S] [Fintype S] (u : ℕ → S → ℝ) (a : ℕ → ℝ) (n : ℕ)
    (hcyc : u n = u 0) (hmono : Monotone a) :
    (∑ i ∈ Finset.range n, a i • (u (i + 1) - u i)) ∈
      generatedCone (fun i : Fin (n - 1) => u 0 - u (i + 1)) :=
  cycle_velocity_mem_generatedCone u a n hcyc hmono

-- The toric differential-inclusion field F_{F,δ}(X) is monotone in δ.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : Fan E) {δ₁ δ₂ : ℝ} (X : E) (hδ : δ₁ ≤ δ₂) :
    (toricField F δ₁ X : Set E) ⊆ (toricField F δ₂ X : Set E) :=
  toricField_mono_delta X hδ

-- A strongly endotactic network has a strictly descending direction at any non-constant functional
-- on its source complexes (Gopalkrishnan–Miller–Shiu).
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (h : N.StronglyEndotactic)
    (w : S → ℝ) (hncon : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 :=
  Network.stronglyEndotactic_strict_dissipation_direction h w hncon

-- A non-siphon codimension-1 facet repels: strictly positive inflow at the empty species
-- (Anderson–Shiu facet repulsion).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hns : ¬ N.IsSiphon ({sstar} : Finset S)) {w : Concentration S}
    (hwnn : Concentration.Nonnegative w) (hzero : ∀ s, w s = 0 ↔ s = sstar) :
    0 < N.massActionVectorField κ w sstar :=
  N.massActionVectorField_pos_on_facet_of_not_isSiphon κ hns hwnn hzero

-- A singleton critical-siphon facet has a linear near-facet influx bound: on a region bounded by M,
-- the s*-component of the field is at least -(c · x s*) (Anderson–Shiu near-facet estimate).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {x : Concentration S}
    (hxnn : x.Nonnegative) {M : ℝ} (hxM : ∀ s, x s ≤ M) :
    -((∑ r : N.R, κ.k r * ((N.reaction r).source sstar : ℝ)
          * (max M 1) ^ ((∑ s, (N.reaction r).source s) - 1)) * x sstar)
      ≤ N.massActionVectorField κ x sstar :=
  N.massActionVectorField_singleton_facet_ge κ hsiph hxnn hxM

-- Integrating the singleton near-facet influx bound by a one-sided Grönwall step keeps the vanishing
-- coordinate strictly positive: from a positive start a confined trajectory never reaches the facet
-- {s* ↦ 0} in finite time (Anderson–Shiu singleton facet escape).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S)) {M : ℝ} {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < γ 0 sstar) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∉ N.SiphonFace ({sstar} : Finset S) :=
  N.massActionTrajectory_notMem_singletonFacet κ hsiph hγd hγnn hγM hpos0 ht

-- Lifting the singleton influx+escape to a general species set P via the aggregate P-mass: the
-- aggregate near-facet influx bound, integrated by the same one-sided Grönwall step, keeps the total
-- P-mass strictly positive, so from a positive-P-mass start a confined trajectory never reaches the
-- full siphon face SiphonFace P in finite time (Anderson–Shiu general-siphon facet escape).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (P : Finset S) {M : ℝ} {γ : ℝ → Concentration S}
    (hγd : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγnn : ∀ t, 0 ≤ t → (γ t).Nonnegative) (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hpos0 : 0 < ∑ s ∈ P, γ 0 s) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∉ N.SiphonFace P :=
  N.massActionTrajectory_notMem_siphonFacet κ P hγd hγnn hγM hpos0 ht

-- The monomial-ordered cyclic velocity lies in the polar cone of any cone for which the cycle's base
-- vertex is minimal (single-cycle toric embedding).
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E}
    (u : ℕ → E) (a : ℕ → ℝ) (n : ℕ) (hcyc : u n = u 0) (hmono : Monotone a) (hmin : CMinimal C u) :
    (∑ i ∈ Finset.range n, a i • (u (i + 1) - u i)) ∈ polarCone C :=
  cycle_velocity_mem_polarCone u a n hcyc hmono hmin

-- A ray [P₀,∞) is a zero-separating region for any 1-D inclusion whose field points nonnegatively —
-- invariance holds with no viability theory.
example {F : DifferentialInclusion.Field ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀)
    (hF : ∀ y, F y ⊆ Set.Ici (0 : ℝ)) :
    DifferentialInclusion.ZeroSeparatingRegion F (Set.Ici P₀) P₀ P₀ :=
  DifferentialInclusion.zeroSeparatingRegion_Ici hP₀ hF

-- A solution staying in s witnesses its velocity in the Bouligand tangent cone — the
-- invariance ⇒ subtangency half of Nagumo's theorem.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {x v : E} {s : Set E}
    (hx : γ 0 = x) (hd : HasDerivAt γ v 0) (hs : ∀ t, 0 ≤ t → γ t ∈ s) :
    v ∈ tangentConeAt ℝ s x :=
  DifferentialInclusion.mem_tangentConeAt_of_solution hx hd hs

-- A finite sum of polar-cone vectors stays in the polar cone — the assembly turning per-cycle
-- embeddings into the full weakly-reversible velocity.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type} [Fintype ι]
    {s : Set E} (v : ι → E) (hv : ∀ j, v j ∈ polarCone s) :
    (∑ j, v j) ∈ polarCone s :=
  sum_univ_mem_polarCone v hv

-- An affine half-plane inward across its boundary band is a (C¹) zero-separating surface in any
-- dimension, with no viability hypothesis.
open scoped InnerProductSpace in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → E} {x₀ n : E} {a δ : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hδ : 0 < δ) (hstart : a ≤ ⟪n, x₀⟫_ℝ)
    (hinward : ∀ y, a - δ ≤ ⟪n, y⟫_ℝ → ⟪n, y⟫_ℝ ≤ a + δ → 0 ≤ ⟪n, f y⟫_ℝ) :
    DifferentialInclusion.ZeroSeparatingSurfaceExists f x₀ :=
  DifferentialInclusion.zeroSeparatingSurfaceExists_halfPlane hn ha hδ hstart hinward

-- Before the first exit time, a curve stays in the closed set.
example {α : Type} [TopologicalSpace α] {γ : ℝ → α} {R : Set α} {s : ℝ}
    (hs0 : 0 ≤ s) (hsτ : s < exitTime γ R) : γ s ∈ R :=
  mem_of_lt_exitTime hs0 hsτ

-- A sublevel set is forward-invariant under a Lyapunov-descent condition.
example {V : ℝ → ℝ} {c : ℝ} (hcont : ContinuousOn V (Set.Ici 0))
    (hdiff : ∀ t > 0, DifferentiableAt ℝ V t) (hderiv : ∀ t > 0, deriv V t ≤ 0) (h0 : V 0 ≤ c) :
    ∀ t ≥ 0, V t ≤ c :=
  sublevel_invariant_of_deriv_nonpos hcont hdiff hderiv h0

-- Subtangency ⇒ descent bridge: a positive-tangent-cone direction at a sublevel boundary has
-- nonpositive derivative of g.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {g' : E →L[ℝ] ℝ} {x : E}
    {c : ℝ} (hg : HasFDerivAt g g' x) (hx : g x = c) {v : E}
    (hv : v ∈ posTangentConeAt {y | g y ≤ c} x) : g' v ≤ 0 :=
  DifferentialInclusion.inner_le_zero_of_mem_posTangentConeAt_sublevel hg hx hv

-- Closed-set Nagumo via distance: if distance to a closed set is nonincreasing along a curve
-- starting inside, the curve stays inside.
example {α : Type} [PseudoMetricSpace α] {γ : ℝ → α} {R : Set α} (hR : IsClosed R) (hne : R.Nonempty)
    (h0 : γ 0 ∈ R) (hanti : AntitoneOn (fun t => Metric.infDist (γ t) R) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ R :=
  invariant_of_infDist_antitoneOn hR hne h0 hanti ht

-- Under neighborhood descent, the genuine flow stays in the sublevel zero-separating region for all
-- forward time.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {γ : ℝ → E} {g : E → ℝ}
    {g' : E → (E →L[ℝ] ℝ)} {c δ : ℝ} (hgc : Continuous g) (hg : ∀ y, HasFDerivAt g (g' y) y)
    (hγcont : Continuous γ) (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t) (hδ : 0 < δ)
    (hdescent : ∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0) (h0 : g (γ 0) ≤ c) :
    ∀ t, 0 ≤ t → g (γ t) ≤ c :=
  DifferentialInclusion.genuine_sublevel_invariant hgc hg hγcont hγderiv hδ hdescent h0

-- In a weakly reversible network every reaction lies on a directed cycle.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (h : N.WeaklyReversible) (r : N.R) :
    N.OnDirectedCycle r :=
  h.onDirectedCycle r

-- A 1-D field that is nonnegative near P₀ admits a zero-separating surface (wired into the
-- genuine-flow persistence layer).
example {f : ℝ → ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀) (hf : ∀ y, P₀ - y ≤ 1 → 0 ≤ f y) :
    DifferentialInclusion.ZeroSeparatingSurfaceExists f P₀ :=
  DifferentialInclusion.zeroSeparatingSurfaceExists_one_dim hP₀ hf

-- The exposed face of a cone in the zero direction is the whole cone.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : PointedCone ℝ E) : exposedFace C 0 = C :=
  exposedFace_zero C

-- The polygonal zero-separating region (intersection of region-side half-planes) is closed — the
-- property the distance-based Nagumo invariance rests on.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (faces : List (E × ℝ)) :
    IsClosed (ZeroSeparatingCurve2D.polyRegion faces) :=
  ZeroSeparatingCurve2D.isClosed_polyRegion faces

-- At a deep-interior point of a fan cell the toric field is exactly that cell's polar cone — the
-- explicit polar-cone description.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {F : Fan E}
    {δ : ℝ} {X : E} {C₀ : ProperCone ℝ E} (hC₀F : C₀ ∈ F) (hC₀d : Metric.infDist X (C₀ : Set E) < δ)
    (hiso : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → C = C₀) :
    toricField F δ X = (coneDual (C₀ : Set E)).toPointedCone :=
  toricField_eq_coneDual_of_isolated hC₀F hC₀d hiso

-- If the region normal lies in every δ-near cell, the toric field is a support face — the
-- uncertainty-region subtangency condition.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {F : Fan E}
    {δ : ℝ} {X n : E} (h : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ (C : Set E))
    {a : ℝ} {faces : List (E × ℝ)} {v : E} (hv : v ∈ toricField F δ X) :
    ZeroSeparatingCurve2D.IsSupportFace (fun _ => v) faces n a :=
  isSupportFace_of_mem_forall h hv

-- If distance to the convex polygonal region is nonincreasing, the curve stays in it (the
-- support ⇒ invariance half, for the convex region).
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    (h0 : γ 0 ∈ ZeroSeparatingCurve2D.polyRegion faces)
    (hanti : AntitoneOn (fun t => Metric.infDist (γ t) (ZeroSeparatingCurve2D.polyRegion faces)) (Set.Ici 0))
    {t : ℝ} (ht : 0 ≤ t) : γ t ∈ ZeroSeparatingCurve2D.polyRegion faces :=
  ZeroSeparatingCurve2D.stays_in_polyRegion_of_support h0 hanti ht

-- A polygonal separating region for the genuine field, fed the subtangency-to-distance bridge,
-- keeps the genuine trajectory a fixed positive distance from the origin.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → E} {x₀ : E}
    (h : ZeroSeparatingCurve2D.PolyZeroSeparatingExists f x₀) {γ : ℝ → E} (hstart : γ 0 = x₀)
    (hbridge : ∀ faces : List (E × ℝ), ZeroSeparatingCurve2D.IsSupportField f faces →
      AntitoneOn (fun t => Metric.infDist (γ t) (ZeroSeparatingCurve2D.polyRegion faces)) (Set.Ici 0)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 :=
  h.away_from_origin hstart hbridge

-- The polygonal separating predicate is inhabited: a constant field into the diagonal half-plane.
open scoped InnerProductSpace in
example {v x₀ : EuclideanSpace ℝ (Fin 2)} (hv : 0 ≤ ⟪ZeroSeparatingCurve2D.diagNormal, v⟫_ℝ)
    (hx₀ : x₀ ∈ ZeroSeparatingCurve2D.polyRegion ZeroSeparatingCurve2D.diagFaces) :
    ZeroSeparatingCurve2D.PolyZeroSeparatingExists (fun _ => v) x₀ :=
  ZeroSeparatingCurve2D.polyZeroSeparatingExists_diag hv hx₀

-- The diagonal direction is attracting for every cell of the cross-fan — a worked instance of the
-- support-segment geometry.
example (δ : ℝ) (X : FaithfulCurveExample.Plane) :
    Faithful.AttractsTowardAll FaithfulCurveExample.crossFan δ X ZeroSeparatingCurve2D.diagNormal :=
  FaithfulCurveExample.diagNormal_attractsTowardAll δ X

-- Under per-face support the genuine curve stays in the convex polygonal region for all forward
-- time — via per-half-plane invariance (no Hoffman bound).
open scoped InnerProductSpace in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    {f : E → E} (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : ∀ na ∈ faces, ∀ t > 0, 0 ≤ ⟪na.1, f (γ t)⟫_ℝ)
    (h0 : γ 0 ∈ ZeroSeparatingCurve2D.polyRegion faces) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ ZeroSeparatingCurve2D.polyRegion faces :=
  ZeroSeparatingCurve2D.polyRegion_invariant_of_support hγcont hγ hsupp h0 ht

-- A genuine trajectory of the cross-fan toric inclusion, started in the zero-separating region,
-- stays distance 1 from the origin for all time — the full chain (support → invariance →
-- separation → persistence) composed in a worked case.
open ZeroSeparatingCurve2D FaithfulCurveExample FaithfulCurveExistence in
example {δ : ℝ} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x : Plane, f x ∈ toricField crossFan δ (logCoords x))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion crossFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 :=
  crossFan_genuine_persistent hsel hγcont hγ h0 ht

-- Two distinct chaining normals (the axis normals) cut a corner zero-separating region; the genuine
-- toric trajectory stays distance 1 from 0.
open ZeroSeparatingCurve2D FaithfulCurveExample FaithfulCurveExistence FaithfulCurveGeneral in
example {δ : ℝ} {x₀ : Plane} {f : Plane → Plane} {γ : ℝ → Plane}
    (hsel : ∀ x, f x ∈ toricField crossFan δ (logCoords x₀))
    (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (h0 : γ 0 ∈ polyRegion twoWallFaces) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ dist (γ t) 0 :=
  twoWall_genuine_persistent hsel hγcont hγ h0 ht

-- Boundary-local strict subtangency — checked only at active faces at the curve's actual position —
-- forces the polygonal region to be forward-invariant, so distinct/conflicting segment normals are
-- handled without any global all-faces condition.
open scoped InnerProductSpace in
open ZeroSeparatingCurve2D in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {faces : List (E × ℝ)} {γ : ℝ → E}
    {f : E → E} (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (f (γ t)) t)
    (hsupp : IsStrictSupportField f faces) (hstart : ∀ nf ∈ faces, nf.2 < ⟪nf.1, γ 0⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ polyRegion faces :=
  polyRegion_invariant_of_strictSupport hγcont hγ hsupp hstart ht

-- The Euclidean inner product of two attracting-direction unit vectors is the cosine of the angle
-- between them — the bridge driving the monotone rotation of the faithful curve's edge normals.
open scoped InnerProductSpace in
open FaithfulCurve2D in
example (θ₁ θ₂ : ℝ) : ⟪dir θ₁, dir θ₂⟫_ℝ = Real.cos (θ₁ - θ₂) :=
  inner_dir θ₁ θ₂

-- For fan walls fitting in a sector of width < π with one positive-offset wall, the constructed
-- angular region has a nonempty strict interior AND excludes a ball about 0 — both halves of
-- "zero-separating" built outright (no abstract existence assumed).
open scoped InnerProductSpace in
open FaithfulCurve2D ZeroSeparatingCurve2D in
example (walls : List (ℝ × ℝ)) {φ θ₀ a : ℝ} (hsec : ∀ w ∈ walls, |w.1 - φ| < Real.pi / 2)
    (hmem : (θ₀, a) ∈ walls) (hpos : 0 < a) :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles walls) ⊆ (Metric.ball (0 : Plane) a)ᶜ :=
  exists_faithful_separating_region walls hsec hmem hpos

-- Three distinct conflicting attracting directions (angles 0, π/4, π/2) chain into one constructed
-- zero-separating region — a non-degenerate instance, not a single collapsed direction.
open scoped InnerProductSpace in
open FaithfulCurve2D ZeroSeparatingCurve2D in
example :
    (∃ x : Plane, ∀ nf ∈ facesOfAngles threeWalls, nf.2 < ⟪nf.1, x⟫_ℝ) ∧
      polyRegion (facesOfAngles threeWalls) ⊆ (Metric.ball (0 : Plane) 1)ᶜ :=
  threeWall_separating_region

-- The wall direction dir θ₁ is a genuine attracting direction of the adjacent two-cell fan, so the
-- toric field lies in the wall's region-side half-plane — support from concrete planar fan geometry.
open scoped InnerProductSpace in
open FaithfulCurve2D FaithfulCurve2DFan in
example {θ₀ θ₁ θ₂ : ℝ} (h₀₁ : |θ₁ - θ₀| ≤ Real.pi / 2) (h₁₂ : |θ₂ - θ₁| ≤ Real.pi / 2)
    (δ : ℝ) (X : Plane) :
    (toricField (adjacentFan θ₀ θ₁ θ₂) δ X : Set Plane) ⊆ {y : Plane | 0 ≤ ⟪dir θ₁, y⟫_ℝ} :=
  toricField_subset_wall_halfPlane h₀₁ h₁₂ δ X

-- The constant apex field (ρ • dir φ, ρ > 0) is a STRICT support field for the angular faces under
-- the sector hypothesis — the per-wall strict attracting-direction condition derived, not assumed.
open scoped InnerProductSpace in
open FaithfulCurve2D ZeroSeparatingCurve2D in
example (walls : List (ℝ × ℝ)) {φ ρ : ℝ} (hρ : 0 < ρ)
    (hsector : ∀ w ∈ walls, |w.1 - φ| < Real.pi / 2) :
    IsStrictSupportField (E := Plane) (fun _ => ρ • dir φ) (facesOfAngles walls) :=
  apexField_isStrictSupportField hρ hsector

-- Persistence under the apex field with NO strict-support hypothesis: the strict boundary-local
-- support is produced from the same sector datum that places the interior start, so the angular
-- planar construction is self-contained for the apex field.
open scoped InnerProductSpace in
open FaithfulCurve2D in
example (walls : List (ℝ × ℝ)) {φ θ₀ a r ρ : ℝ} (hρ : 0 < ρ)
    (hsector : ∀ w ∈ walls, |w.1 - φ| < Real.pi / 2) (hmem : (θ₀, a) ∈ walls) (har : r ≤ a)
    {γ : ℝ → Plane} (hγcont : Continuous γ) (hγ : ∀ t > 0, HasDerivAt γ (ρ • dir φ) t)
    (hstart : ∀ nf ∈ facesOfAngles walls, nf.2 < ⟪nf.1, γ 0⟫_ℝ) {t : ℝ} (ht : 0 ≤ t) :
    r ≤ dist (γ t) 0 :=
  apexField_region_persistent walls hρ hsector hmem har hγcont hγ hstart ht

-- A ruled patch's surface normal must be orthogonal to its active tangency directions; below finrank
-- such a normal exists (3 in ℝ⁴), once they span it is killed (4 in ℝ⁴). The threshold dichotomy for
-- the surface-normal constraint system; whether a patch is forced to carry 4 directions is not decided here.
open scoped InnerProductSpace in
open ZeroSeparatingInduction in
example :
    (∀ v : Fin 3 → EuclideanSpace ℝ (Fin 4),
        ∃ n : EuclideanSpace ℝ (Fin 4), n ≠ 0 ∧ ∀ i, ⟪v i, n⟫_ℝ = 0) ∧
      (∀ n : EuclideanSpace ℝ (Fin 4),
        (∀ i, ⟪EuclideanSpace.basisFun (Fin 4) ℝ i, n⟫_ℝ = 0) → n = 0) :=
  over_determined_in_dim_four

-- Fan refinement transfers faithfulness to a coarser fan: a normal admissible for a finer cell
-- C' ⊆ C is admissible for the coarse cell C, so the finer surface is faithful for the coarse fan.
open CRNT.Faithful FanRefinement in
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : E} {C C' : ProperCone ℝ E}
    (hsub : (C' : Set E) ⊆ (C : Set E)) (h : AttractsToward n C') : AttractsToward n C :=
  attractsToward_coarse_of_fine hsub h

-- The Schur complement of a P-matrix (at the last coordinate) is a P-matrix — the dimension-drop
-- step for the inductive Gale–Nikaido theorem.
example {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (h : M.IsPMatrix) :
    (Matrix.schurLast M).IsPMatrix :=
  h.schurLast
-- The Schur determinant identity at the last coordinate.
example {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hd : M (Fin.last n) (Fin.last n) ≠ 0) :
    M.det = M (Fin.last n) (Fin.last n) * (Matrix.schurLast M).det :=
  Matrix.det_schurLast M hd

-- Gale–Nikaido step 1: a map with everywhere-strict derivative whose Jacobian is a P-matrix at every
-- point is a local homeomorphism (local injectivity).
example {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {f' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
    (hf : ∀ x, HasStrictFDerivAt f (f' x) x)
    (hP : ∀ x, (CRNT.jacobianMatrix (f' x)).IsPMatrix) : IsLocalHomeomorph f :=
  CRNT.isLocalHomeomorph_of_pmatrix_fderiv hf hP
-- Gale–Nikaido step 2: the one-dimensional base case — a P-matrix Jacobian on a 1-D box gives
-- injectivity.
example {f : (Fin 1 → ℝ) → (Fin 1 → ℝ)} {f' : (Fin 1 → ℝ) → ((Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ))}
    {a b : Fin 1 → ℝ} (hf : ∀ x ∈ Set.Icc a b, HasFDerivAt f (f' x) x)
    (hP : ∀ x ∈ Set.Icc a b, (CRNT.jacobianMatrix (f' x)).IsPMatrix) :
    Set.InjOn f (Set.Icc a b) :=
  CRNT.injOn_of_pmatrix_fderiv_dim_one hf hP
-- Gale–Nikaido step 3: a P-matrix stays a P-matrix under ±1 diagonal (signature) conjugation —
-- the coordinatewise sign-flip reduction.
example {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (h : M.IsPMatrix)
    {ε : Fin n → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (Matrix.of (fun i j => ε i * M i j * ε j)).IsPMatrix :=
  h.signatureConj hε
-- Gale–Nikaido step 4: the reduced map (last coordinate solved by `φ`) has Jacobian equal to the
-- Schur complement of the full Jacobian — the dimension-drop step.
example {n : ℕ} {Dφ : (Fin n → ℝ) →L[ℝ] ℝ}
    {L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (himp : ∀ Δ : Fin n → ℝ, Dφ Δ = -(CRNT.jacobianMatrix L (Fin.last n) (Fin.last n))⁻¹ *
        ∑ j, CRNT.jacobianMatrix L (Fin.last n) j.castSucc * Δ j) :
    CRNT.jacobianMatrix ((ContinuousLinearMap.pi (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc)).comp
      (L.comp (ContinuousLinearMap.pi
        (Fin.lastCases Dφ (fun j => ContinuousLinearMap.proj j)))))
      = Matrix.schurLast (CRNT.jacobianMatrix L) :=
  CRNT.jacobianMatrix_reduced_eq_schurLast himp
-- Gale–Nikaido on a box (conditional): a C¹ map with everywhere P-matrix Jacobian is injective, given
-- last-coordinate sections through each colliding pair along which the reduced map is injective.
example {n : ℕ} {F : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {F' : (Fin (n + 1) → ℝ) → ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))}
    {a b : Fin (n + 1) → ℝ}
    (hF : ∀ z ∈ Set.Icc a b, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc a b, (CRNT.jacobianMatrix (F' z)).IsPMatrix)
    (hsec : ∀ p ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b, F p = F q →
      ∃ φ : (Fin n → ℝ) → ℝ,
        φ (Fin.init p) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        φ (Fin.init q) ∈ Set.Icc (a (Fin.last n)) (b (Fin.last n)) ∧
        F (Fin.snoc (Fin.init p) (φ (Fin.init p))) (Fin.last n) = F p (Fin.last n) ∧
        F (Fin.snoc (Fin.init q) (φ (Fin.init q))) (Fin.last n) = F q (Fin.last n) ∧
        Set.InjOn (fun x => fun i : Fin n => F (Fin.snoc x (φ x)) i.castSucc)
          (Set.Icc (Fin.init a) (Fin.init b))) :
    Set.InjOn F (Set.Icc a b) :=
  CRNT.injOn_of_pmatrix_fderiv_of_sections hF hP hsec
-- **The Gale–Nikaido global univalence theorem (unconditional):** a C¹ map whose Jacobian is a
-- P-matrix at every point of a box is injective on that box. (Degree-free.)
example {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ}
    (hF : ∀ z ∈ Set.Icc lo hi, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc lo hi, (CRNT.jacobianMatrix (F' z)).IsPMatrix) :
    Set.InjOn F (Set.Icc lo hi) :=
  CRNT.injOn_of_pmatrix_fderiv hF hP

-- The determinant expands as a sum over permutations with the sign read off the cycle type.
example {n : Type} [DecidableEq n] [Fintype n] {R : Type} [CommRing R] (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n,
      ((σ.cycleType.map fun k => -(-1 : ℤˣ) ^ k).prod) • ∏ i, M (σ i) i :=
  CRNT.det_eq_sum_over_perm_cycleType M

-- Every species–reaction-graph cycle has even length `2k` (bipartite alternation).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (hcyc : w.IsCycle) : ∃ k, w.length = 2 * k :=
  N.srCycle_length_eq_two_mul hcyc

-- The stoichiometric-subspace chart recovers a class point from its coordinate.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {x₀ x : Concentration S}
    (h : N.StoichCompatible x₀ x) : N.affineChart x₀ (N.chartCoord x₀ x) = x :=
  N.affineChart_chartCoord h

-- A P-matrix reduced Jacobian on a class ⇒ mass-action injectivity on that class, binding the
-- box Gale–Nikaido theorem to CRN compatibility classes via coordinate reduction.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.reducedJacobian κ x₀ y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_jacobian_pmatrix κ x₀ hbox hpm

-- A consistent signed species–reaction cover, with positive Jacobian diagonal and a coordinate
-- selection presenting the reduced Jacobian as a principal submatrix, ⇒ mass-action injectivity
-- on the compatibility class: the Craciun–Feinberg SR-graph injectivity verdict.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hweight : ∀ y ∈ Set.Icc lo hi, ∀ (s : Finset S) (σ : Equiv.Perm s) (ρ : s → N.R),
      0 ≤ ((CRNT.coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ y ∈ Set.Icc lo hi, ∀ i : S,
      0 < (N.massActionJacobian κ (N.affineChart x₀ y)) i i)
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_consistentSRSign κ x₀ hf hbox hpos hweight hdiag hsub

-- A P-matrix pivot-reduced Jacobian on the box ⇒ mass-action injectivity on the class, through a
-- pivot-row coordinate chart: the box Gale–Nikaido theorem in pivot coordinates, a non-vacuous
-- verdict on the genuine chart compression `pivotSel ρ ∘ J ∘ B` (Craciun–Feinberg via Gale–Nikaido).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) (ρ : Fin N.stoichRank → S)
    (B : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (hBsec : ∀ w ∈ N.stoichSubspace, B (fun i => w (ρ i)) = w)
    {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi, (N.pivotReducedJacobian κ x₀ ρ B y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix κ x₀ ρ B hBsec hbox hpm

-- The concrete pivot chart discharges the section identity `hBsec` automatically: for the explicit
-- chart `B = concretePivotChart ρ γ` built from a nonsingular maximal minor, `B (w ∘ ρ) = w` for
-- every `w ∈ S(N)` — the section law is a theorem, not an assumption.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (ρ : Fin (CRNT.GaussianRank.computeRank N.stoichMatrixQ) → S)
    (γ : Fin (CRNT.GaussianRank.computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    {w : S → ℝ} (hw : w ∈ N.stoichSubspace) :
    N.concretePivotChart ρ γ (fun i => w (ρ i)) = w :=
  N.concretePivotChart_section ρ γ hdet hw

-- Concrete-chart mass-action injectivity with no section hypothesis: a nonsingular maximal minor
-- gives the explicit chart, the box covers the class, and the pivot-reduced Jacobian is a P-matrix on
-- the box; injectivity follows. The reduced P-matrix property is a genuine consumer input (the
-- pivot-reduced Jacobian is an oblique compression, not a principal submatrix of `J`).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S)
    (ρ : Fin (CRNT.GaussianRank.computeRank N.stoichMatrixQ) → S)
    (γ : Fin (CRNT.GaussianRank.computeRank N.stoichMatrixQ) → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0)
    {lo hi : Fin (CRNT.GaussianRank.computeRank N.stoichMatrixQ) → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.pivotChartCoord x₀ ρ x ∈ Set.Icc lo hi)
    (hpm : ∀ y ∈ Set.Icc lo hi,
      (N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y).IsPMatrix) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_concretePivotChart κ x₀ ρ γ hdet hbox hpm

-- The decidable point-free certificate (consistent signed cover + positive diagonal drive) ⇒ the
-- full mass-action Jacobian is a P-matrix at every positive concentration: the point-free keystone
-- discharged by a kernel sign computation.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (C : Set (Concentration S)) (hC : ∀ x ∈ C, x.Positive)
    (hsign : N.ConsistentSRSign) (hdrive : N.ConsistentDiagonalDrive) :
    ∀ x ∈ C, (N.massActionJacobian κ x).IsPMatrix :=
  N.isPMatrix_massActionJacobian_box_of_decide κ C hC hsign hdrive

-- The reported point-independent P-matrix flag is `true` exactly when the network satisfies the two
-- decidable point-free conditions; when `true` the full Jacobian is a P-matrix at every positive
-- concentration.
example (d : NetworkData) :
    d.analyze.srPMatrixPointIndep = true ↔
      d.toNetwork.ConsistentSRSign ∧ d.toNetwork.ConsistentDiagonalDrive :=
  NetworkData.analyze_srPMatrixPointIndep_eq d

-- For a general stoichiometric chart the reduced Jacobian is the oblique compression P · M · B of
-- the full mass-action Jacobian, with P · B = 1 — the Cauchy–Binet matrix scaffolding for the
-- general-chart species–reaction graph injectivity verdict.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobian κ x₀ y
      = N.stoichProjMatrix * N.massActionJacobian κ (N.affineChart x₀ y) * N.stoichChartMatrix :=
  N.reducedJacobian_eq_mul κ x₀ y

-- The mass-action Jacobian lands in the stoichiometric subspace, so the chart matrix conjugates
-- the reduced Jacobian onto the full Jacobian: B · reducedJacobian = M · B. The reduced determinant
-- is thus the chart-independent restriction determinant of the full Jacobian to S(N), with no
-- coordinate-selection hypothesis on the chart.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    N.stoichChartMatrix * N.reducedJacobian κ x₀ y
      = N.massActionJacobian κ (N.affineChart x₀ y) * N.stoichChartMatrix :=
  N.stoichChartMatrix_mul_reducedJacobian κ x₀ y

-- A consistent reduced-cover sign condition in the chart makes the reduced Jacobian a P-matrix, and
-- when it holds throughout the chart box it yields an hsub-free general-chart injectivity verdict:
-- the reduced-coordinate Craciun-Feinberg monostationarity conclusion, with no coordinate-selection
-- hypothesis on the chart.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedConsistentSRSign κ x₀ y) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_reducedConsistentSRSign κ x₀ hbox hsign

-- The consistent reduced-cover sign condition, re-expressed on network data: when every
-- principal-submatrix cover term of the chart-transported full Jacobian P · M · B is sign-consistent
-- throughout the chart box, the hsub-free general-chart injectivity verdict holds, now checkable from
-- the network's own data through the chart B/P.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hsign : ∀ y ∈ Set.Icc lo hi, N.ReducedJacobianCompressionSRSign κ x₀ y) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_compressionSRSign κ x₀ hbox hsign

-- Brouwer zero-of-field in concentration space: an inward-displacement-preserving continuous
-- vector field on a nonempty compact convex set of concentrations has a zero there.
example {S : Type} [Fintype S] {K : Set (CRNT.Concentration S)} (hne : K.Nonempty)
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (v : CRNT.Concentration S → CRNT.Concentration S) (hv : ContinuousOn v K)
    (hmaps : Set.MapsTo (fun x => x - v x) K K) : ∃ x ∈ K, v x = 0 :=
  CRNT.Analysis.exists_zero_of_displacement_mapsTo_concentration hne hconv hcomp v hv hmaps
-- The forward limit of an omega-point is contained in the omega-limit set, and every boundary
-- point of it carries a critical siphon on its zero set.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit Filter.atTop ϕ {x₀}, (y : Concentration S).Nonnegative)
    (hgenω : ∀ y ∈ omegaLimit Filter.atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit Filter.atTop ϕ {x₀},
      (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx0pos : x₀.Positive) {q : Concentration S}
    (hq : q ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    omegaLimit Filter.atTop ϕ {q} ⊆ omegaLimit Filter.atTop ϕ {x₀} ∧
      ∀ w ∈ omegaLimit Filter.atTop ϕ {q}, ∀ P : Finset S,
        (∀ s, s ∈ P ↔ w s = 0) → P.Nonempty → N.IsCriticalSiphon P :=
  let ⟨_, _, _, hsub, hface⟩ := N.forwardLimit_subOmega_criticalSiphonFace κ hϕγ hK hKcl hmaps
    hωnn hgenω hωaff hx0pos hq
  ⟨hsub, hface⟩

example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {K : Set (CRNT.Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hmaps : Set.MapsTo (fun x => x - N.massActionVectorField κ x) K K) :
    ∃ x ∈ K, N.IsMassActionSteadyState κ x :=
  N.exists_isMassActionSteadyState_of_displacement_mapsTo κ hne hconv hcomp hmaps
-- The ω-limit set of a precompact orbit contains a minimal compact invariant subset: a nonempty
-- compact closed invariant set with no proper nonempty compact closed invariant subset.
open Filter in
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) (x₀ : α) {K : Set α}
    (hK : IsCompact K)
    (habs : ∃ v ∈ (Filter.atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    ∃ M, M ⊆ omegaLimit atTop ϕ {x₀} ∧
      Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M :=
  CRNT.exists_minimal_compact_invariant_subOmega ϕ x₀ hK habs
-- Two minimal nonempty compact closed invariant sets are either equal or disjoint: the minimal
-- sets form a pairwise-disjoint antichain.
example {α : Type} [TopologicalSpace α] [T2Space α] (ϕ : Flow ℝ≥0 α) {M₁ M₂ : Set α}
    (h₁ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₁)
    (h₂ : Minimal (fun C => C.Nonempty ∧ IsCompact C ∧ IsClosed C ∧ IsInvariant ϕ C) M₂) :
    M₁ = M₂ ∨ Disjoint M₁ M₂ :=
  CRNT.eq_or_disjoint_of_minimal_compact_invariant ϕ h₁ h₂
-- Planar trace–determinant stability test: a real 2×2 matrix has both characteristic-polynomial
-- roots in the open left half-plane iff its trace is negative and its determinant is positive.
example (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ z : ℂ, z * z + (-M.trace : ℂ) * z + (M.det : ℂ) = 0 → z.re < 0) ↔
      (M.trace < 0 ∧ 0 < M.det) :=
  hurwitz_matrix_fin_two_iff M
-- Stampacchia variational inequality for mass action: on a nonempty compact convex set of
-- concentrations the mass-action field lies in the outward normal cone at some point.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {K : Set (CRNT.Concentration S)} (hne : K.Nonempty) (hconv : Convex ℝ K) (hcomp : IsCompact K) :
    ∃ x ∈ K, ∀ w ∈ K, 0 ≤ ∑ s, N.massActionVectorField κ x s * (w s - x s) :=
  N.exists_steadyState_normalCone_of_compact κ hne hconv hcomp

-- Gershgorin diagonal-dominance Hurwitz test: strict row diagonal dominance with negative diagonal
-- forces every eigenvalue into the open left half-plane, in any finite dimension.
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 :=
  hurwitz_of_strict_diag_dominance A h

-- Column form of the Gershgorin diagonal-dominance Hurwitz test: strict column diagonal dominance
-- with negative diagonal forces every eigenvalue into the open left half-plane, in any finite
-- dimension.
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (h : ∀ k, (A k k).re + ∑ i ∈ Finset.univ.erase k, ‖A i k‖ < 0) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0 :=
  hurwitz_of_strict_col_diag_dominance A h

-- Routh–Hurwitz, degree 3 (matrix form): a real 3×3 matrix has all three characteristic-polynomial
-- roots in the open left half-plane iff the four Routh–Hurwitz coefficient conditions on its trace,
-- second invariant, and determinant hold.
example (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ z : ℂ, z ^ 3 + (-M.trace : ℂ) * z ^ 2 + (M.c₂Fin3 : ℂ) * z + (-M.det : ℂ) = 0 →
        z.re < 0) ↔
      (0 < -M.trace ∧ 0 < M.c₂Fin3 ∧ 0 < -M.det ∧ -M.det < (-M.trace) * M.c₂Fin3) :=
  hurwitz_matrix_fin_three_iff M
-- Spatial Hopf eigenvalue-crossing gate: a real 3×3 matrix on the boundary of the cubic Hurwitz
-- region carries a purely imaginary conjugate eigenvalue pair (im² = c₂Fin3) and a negative real
-- eigenvalue — the algebraic precondition for a Hopf bifurcation.
example (M : Matrix (Fin 3) (Fin 3) ℝ) (z₁ z₂ : ℂ)
    (hz₁im : z₁.im = 0)
    (e₂ : (-M.trace : ℂ) = -(z₁ + z₂ + (starRingEnd ℂ) z₂))
    (e₁ : (M.c₂Fin3 : ℂ) = z₁ * z₂ + z₁ * ((starRingEnd ℂ) z₂) + z₂ * ((starRingEnd ℂ) z₂))
    (e₀ : (-M.det : ℂ) = -(z₁ * z₂ * ((starRingEnd ℂ) z₂)))
    (H₂ : 0 < -M.trace) (H₀ : 0 < -M.det) (HΔ : (-M.det) = (-M.trace) * M.c₂Fin3) :
    z₁.re < 0 ∧ z₂.re = 0 ∧ z₂.im ≠ 0 ∧ z₂.im ^ 2 = M.c₂Fin3 :=
  CRNT.hurwitz_matrix_fin_three_hopf_crossing M z₁ z₂ hz₁im e₂ e₁ e₀ H₂ H₀ HΔ
-- Hopf transversality: on the cubic Hopf boundary, with the eigenvalue real part p, real eigenvalue
-- r, and squared imaginary part q differentiable at the crossing μ₀ (p μ₀ = 0, q μ₀ ≥ 0, a₀ > 0), a
-- nonzero boundary-function velocity g'(μ₀) forces a transversal imaginary-axis crossing, p' ≠ 0.
example {r p q : ℝ → ℝ} {μ₀ r' p' q' : ℝ}
    (hr : HasDerivAt r r' μ₀) (hp : HasDerivAt p p' μ₀) (hq : HasDerivAt q q' μ₀)
    (hp0 : p μ₀ = 0) (hqnn : 0 ≤ q μ₀)
    (H₀ : 0 < -(r μ₀ * (p μ₀ ^ 2 + q μ₀)))
    (hg : deriv (fun μ => CRNT.hopfBoundaryFn (r μ) (p μ) (q μ)) μ₀ ≠ 0) :
    p' ≠ 0 :=
  CRNT.hopf_transversal_crossing hr hp hq hp0 hqnn H₀ hg
-- Hopf admissibility: a one-parameter mass-action Jacobian family that crosses the cubic Hurwitz
-- boundary transversally, with a center-manifold seed supplied, satisfies the planar Hopf theorem's
-- input hypotheses — purely-imaginary non-hyperbolic spectrum (p μ₀ = 0, 0 < q μ₀, r μ₀ < 0) and a
-- transversal crossing (p' ≠ 0) — without asserting the (out-of-scope) periodic-orbit conclusion.
example {J : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {μ₀ : ℝ} (h : CRNT.hopfAdmissible J μ₀) :
    h.p μ₀ = 0 ∧ 0 < h.q μ₀ ∧ h.r μ₀ < 0 ∧ h.p' ≠ 0 :=
  h.planarHopfHypotheses
-- Planar Hopf normal form: with first Lyapunov coefficient ℓ₁ ≠ 0, a positive equilibrium of the
-- radial amplitude field Ṙ = α R + ℓ₁ R³ is the bifurcating-orbit amplitude R² = −α/ℓ₁; when α/ℓ₁ < 0
-- it exists and equals √(−α/ℓ₁), the √|μ−μ₀| amplitude law of the Hopf–Andronov theorem.
example (H : CRNT.PlanarHopfData) {μ : ℝ} (hℓ : H.firstLyapunov ≠ 0)
    (hsign : H.α μ / H.firstLyapunov < 0) :
    ∃ Rstar : ℝ, 0 < Rstar ∧ Rstar = Real.sqrt (-H.α μ / H.firstLyapunov)
      ∧ H.radialField μ Rstar = 0 :=
  H.radial_equilibrium hℓ hsign
-- Hopf–Andronov bifurcation (conditional): a transversal crossing (α' ≠ 0) with nondegenerate first
-- Lyapunov coefficient (ℓ₁ ≠ 0) and a periodic-orbit seed yields a one-parameter family of
-- nonconstant periodic orbits emerging from the crossing with the √(−α/ℓ₁) amplitude law.
example (H : CRNT.PlanarHopfData) (htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0)
    (seed : H.PeriodicOrbitSeed) :
    H.μ₀ ∈ closure seed.branch ∧
      ∀ μ ∈ seed.branch, 0 < seed.T μ
        ∧ Function.Periodic (seed.orbit μ) (seed.T μ)
        ∧ (∃ s t, seed.orbit μ s ≠ seed.orbit μ t)
        ∧ (∃ s, ‖seed.orbit μ s‖ = Real.sqrt (-H.α μ / H.firstLyapunov)) :=
  H.hopf_andronov_periodic_orbits htrans hℓ seed
-- Closed-form Hopf limit cycle: the truncated normal form ẇ = (α+iω)w + c₁w|w|² is solved exactly by
-- the rotating curve w(t) = Rstar·exp(I(θ₀+Ωt)) at the radial equilibrium Rstar (radialField = 0),
-- Ω = ω + (Im c₁)Rstar²: its derivative equals the field evaluated along the curve.
example (H : CRNT.PlanarHopfData) {μ Rstar : ℝ} (θ₀ : ℝ) (hR : 0 ≤ Rstar)
    (hrad : H.radialField μ Rstar = 0) (t : ℝ) :
    HasDerivAt (H.hopfLimitCycle Rstar θ₀) (H.normalForm μ (H.hopfLimitCycle Rstar θ₀ t)) t :=
  H.hopfLimitCycle_solves θ₀ hR hrad t
-- The closed-form limit cycle is periodic with the positive period |2π/Ω| (Ω ≠ 0) and nonconstant
-- (Rstar > 0): a genuine cycle of the truncated field, not the equilibrium.
example (H : CRNT.PlanarHopfData) {Rstar : ℝ} (θ₀ : ℝ) (hR : 0 < Rstar)
    (hΩ : H.cycleFreq Rstar ≠ 0) :
    Function.Periodic (H.hopfLimitCycle Rstar θ₀) |2 * Real.pi / H.cycleFreq Rstar|
      ∧ (∃ s t, H.hopfLimitCycle Rstar θ₀ s ≠ H.hopfLimitCycle Rstar θ₀ t) :=
  ⟨H.hopfLimitCycle_periodic_abs θ₀ hΩ, H.hopfLimitCycle_nonconstant θ₀ hR hΩ⟩
-- The periodic-orbit seed of the truncated normal form is CONSTRUCTED, not assumed: on a branch whose
-- closure contains μ₀ with the sign and frequency conditions, hopf_andronov_periodic_orbits fires
-- with the closed-form limit cycle supplying the seed.
example (H : CRNT.PlanarHopfData) (htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0) (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hbranch : ∀ ν ∈ branch, H.α ν / H.firstLyapunov < 0)
    (hfreq : ∀ ν ∈ branch, H.cycleFreq (Real.sqrt (-H.α ν / H.firstLyapunov)) ≠ 0) :
    H.μ₀ ∈ closure branch ∧
      ∀ μ ∈ branch, (0 : ℝ) < |2 * Real.pi / H.cycleFreq (Real.sqrt (-H.α μ / H.firstLyapunov))|
        ∧ Function.Periodic (H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0)
            |2 * Real.pi / H.cycleFreq (Real.sqrt (-H.α μ / H.firstLyapunov))|
        ∧ (∃ s t, H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 s
            ≠ H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 t)
        ∧ (∃ s, ‖H.hopfLimitCycle (Real.sqrt (-H.α μ / H.firstLyapunov)) 0 s‖
            = Real.sqrt (-H.α μ / H.firstLyapunov)) :=
  H.hopf_andronov_truncated htrans hℓ branch hclosure hbranch hfreq
-- Nondegeneracy of the truncated radial equilibrium: the R-partial α + 3ℓ₁R² of the radial field at a
-- positive equilibrium collapses to 2ℓ₁R² ≠ 0, the implicit-function nondegeneracy that ℓ₁ ≠ 0 and
-- R > 0 furnish for free.
example (H : CRNT.PlanarHopfData) {μ Rstar : ℝ} (hℓ : H.firstLyapunov ≠ 0) (hR : 0 < Rstar)
    (hrad : H.radialField μ Rstar = 0) :
    H.α μ + 3 * H.firstLyapunov * Rstar ^ 2 ≠ 0 :=
  H.radialDeriv_ne_zero hℓ hR hrad
-- Persistence of the limit-cycle amplitude through the O(|w|⁴) tail: at a nondegenerate positive root
-- of the full averaged radial field, the implicit function theorem furnishes an amplitude branch that
-- remains a root of the full field for every nearby parameter.
example {μ₁ R₀ : ℝ} (F : CRNT.PlanarHopfData.FullRadialField μ₁ R₀) :
    ∀ᶠ μ in nhds μ₁, F.G μ (CRNT.PlanarHopfData.amplitudeBranch F μ) = 0 :=
  CRNT.PlanarHopfData.amplitudeBranch_isRoot F
-- Hopf–Andronov for the full field: with the persistent amplitude branch a positive root matching the
-- radial equilibrium on a branch whose closure contains μ₀, and the rotation-closure realizing each
-- root as a genuine nonconstant periodic orbit, the full field carries the bifurcating family.
example (H : CRNT.PlanarHopfData) (htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0)
    {μ₁ R₀ : ℝ} (F : CRNT.PlanarHopfData.FullRadialField μ₁ R₀) (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hpos : ∀ ν ∈ branch, 0 < CRNT.PlanarHopfData.amplitudeBranch F ν)
    (hroot : ∀ ν ∈ branch, F.G ν (CRNT.PlanarHopfData.amplitudeBranch F ν) = 0)
    (radialEq : ∀ ν ∈ branch,
      CRNT.PlanarHopfData.amplitudeBranch F ν = Real.sqrt (-H.α ν / H.firstLyapunov))
    (T : ℝ → ℝ) (hT : ∀ ν ∈ branch, 0 < T ν) (orbit : ℝ → ℝ → ℂ)
    (realizes : ∀ ν ∈ branch, ∀ ρ, F.G ν ρ = 0 → 0 < ρ →
      Function.Periodic (orbit ν) (T ν)
        ∧ (∃ s t, orbit ν s ≠ orbit ν t)
        ∧ (∃ s, ‖orbit ν s‖ = ρ)) :
    H.μ₀ ∈ closure branch ∧
      (∀ μ ∈ branch, 0 < T μ
        ∧ Function.Periodic (orbit μ) (T μ)
        ∧ (∃ s t, orbit μ s ≠ orbit μ t)
        ∧ (∃ s, ‖orbit μ s‖ = Real.sqrt (-H.α μ / H.firstLyapunov))) :=
  H.hopf_andronov_full_field htrans hℓ F branch hclosure hpos hroot radialEq T hT orbit realizes
-- Hopf–Andronov for the full field with `realizes` discharged: a return-map fixed point at the
-- amplitude point of each branch parameter (carried as HopfRealizationData, the smooth-ODE-dependence
-- the section records) supplies the rotation closure, so the full field carries the bifurcating
-- family of nonconstant periodic orbits with the √(−α/ℓ₁) amplitude law — no realizes hypothesis.
example (H : CRNT.PlanarHopfData) (htrans : H.α' ≠ 0) (hℓ : H.firstLyapunov ≠ 0)
    {μ₁ R₀ : ℝ} (F : CRNT.PlanarHopfData.FullRadialField μ₁ R₀) (branch : Set ℝ)
    (hclosure : H.μ₀ ∈ closure branch)
    (hpos : ∀ ν ∈ branch, 0 < CRNT.PlanarHopfData.amplitudeBranch F ν)
    (hroot : ∀ ν ∈ branch, F.G ν (CRNT.PlanarHopfData.amplitudeBranch F ν) = 0)
    (radialEq : ∀ ν ∈ branch,
      CRNT.PlanarHopfData.amplitudeBranch F ν = Real.sqrt (-H.α ν / H.firstLyapunov))
    (uniq : ∀ ν ∈ branch, ∀ ρ, F.G ν ρ = 0 → 0 < ρ → ρ = CRNT.PlanarHopfData.amplitudeBranch F ν)
    (data : ∀ ν ∈ branch, H.HopfRealizationData ν (CRNT.PlanarHopfData.amplitudeBranch F ν)) :
    H.μ₀ ∈ closure branch ∧
      (∀ μ ∈ branch, 0 < CRNT.PlanarHopfData.realizedPeriod H data μ
        ∧ Function.Periodic (CRNT.PlanarHopfData.realizedOrbit H data μ)
            (CRNT.PlanarHopfData.realizedPeriod H data μ)
        ∧ (∃ s t, CRNT.PlanarHopfData.realizedOrbit H data μ s
            ≠ CRNT.PlanarHopfData.realizedOrbit H data μ t)
        ∧ (∃ s, ‖CRNT.PlanarHopfData.realizedOrbit H data μ s‖
            = Real.sqrt (-H.α μ / H.firstLyapunov))) :=
  H.hopf_andronov_full_field_realized htrans hℓ F branch hclosure hpos hroot radialEq uniq data
-- Critical-siphon feasibility under Farkas duality: a species vector lies in the conservation cone
-- (nonnegative, orthogonal to the stoichiometric subspace) iff every direction nonnegative on the
-- cone is nonnegative on it.
open scoped RealInnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (b : EuclideanSpace ℝ S) :
    b ∈ N.conservationCone ↔
      ∀ y : EuclideanSpace ℝ S, (∀ x ∈ N.conservationCone, 0 ≤ ⟪x, y⟫) → 0 ≤ ⟪b, y⟫ :=
  N.mem_conservationCone_iff_farkas b
-- Cauchy–Binet formula: the determinant of a product of rectangular matrices expands as a sum
-- over the m-element subsets of the inner index set, one minor-product per subset.
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach,
      (A.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2)).det *
        (B.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id).det :=
  Matrix.det_mul_eq_sum_powersetCard A B
-- Sign-definiteness from cycle-cover terms: if every Leibniz cycle-cover term of a real square
-- matrix is nonnegative and its diagonal (identity-permutation) term is strictly positive, the
-- determinant is nonzero — the determinant-level form of the consistent-cycle-sign criterion.
example {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hnn : ∀ σ : Equiv.Perm n, 0 ≤ CRNT.coverTerm M σ)
    (hd : 0 < CRNT.coverTerm M (1 : Equiv.Perm n)) :
    M.det ≠ 0 :=
  CRNT.det_ne_zero_of_coverTerm_signDefinite M (Or.inl ⟨hnn, hd⟩)
-- Stiemke/Gordan strict alternative: a critical siphon is a nonempty siphon for which some species
-- of it admits no supported conservation vector positive there — the strict-support feasibility
-- obstruction recast as a finite conjunction of single-coordinate Farkas problems.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ∃ s ∈ P, ¬ ∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s :=
  N.isCriticalSiphon_iff_exists_pointwise P
-- Jacobian cycle-sign bridge: a one-reaction cover product of the factored mass-action Jacobian
-- splits into its nonnegative rate-and-gradient magnitude times the real cast of the product of
-- the cover's signed SR-graph incidence signs.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (σ : Equiv.Perm S) (ρ : S → N.R) :
    N.coverProductSingle κ x σ ρ =
      N.coverMagnitudeSingle κ x σ ρ *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ) :=
  N.coverProductSingle_eq_magnitude_mul_sign κ x σ ρ
-- Consistent signed SR-cover criterion: at a positive concentration, if every reaction-choice cover
-- of the mass-action Jacobian has a nonnegative signed-incidence weight and the diagonal cover term
-- is strictly positive, then the Jacobian determinant is nonzero.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (σ : Equiv.Perm S) (ρ : S → N.R),
      0 ≤ ((CRNT.coverCoeff σ : ℤ) : ℝ) *
        ((∏ i, N.signedEdge (σ i) (ρ i) : SignType) : ℝ))
    (hdiag : 0 < CRNT.coverTerm (N.massActionJacobian κ x) (1 : Equiv.Perm S)) :
    (N.massActionJacobian κ x).det ≠ 0 :=
  N.det_massActionJacobian_ne_zero_of_consistentSRSign κ hx hweight hdiag

-- CTMC ergodicity: on a finite closed enabled region that is a single communicating class, the
-- embedded jump chain has a unique invariant probability measure supported on the region — any
-- such measure equals the canonical normalized stationary measure, via finite-state
-- Perron–Frobenius standing in for the absent general Meyn–Tweedie ergodicity.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hirr : N.regionStronglyConnected κ T)
    (μ : @MeasureTheory.Measure (S → ℕ) CRNT.Network.instMeasurableSpaceCount)
    (hμprob :
      @MeasureTheory.IsProbabilityMeasure (S → ℕ) CRNT.Network.instMeasurableSpaceCount μ)
    (hμsupp : μ Tᶜ = 0)
    (hμinv : ProbabilityTheory.Kernel.Invariant (N.jumpKernel κ) μ) :
    μ = N.stationaryProbabilityMeasure κ c T := by
  haveI := hμprob
  exact N.invariant_probabilityMeasure_unique_on_region κ c hc hcb hT hne hirr μ hμsupp hμinv
-- P-matrix from consistent signed SR-cycles: at a positive concentration, if every signed-incidence
-- cover weight over every restricted species set is nonnegative and every Jacobian diagonal entry is
-- positive, then the mass-action Jacobian is a P-matrix — every principal minor positive, the form the
-- box Gale–Nikaido univalence chain consumes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hweight : ∀ (s : Finset S) (σ : Equiv.Perm s) (ρ : s → N.R),
      0 ≤ ((CRNT.coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ))
    (hdiag : ∀ i : S, 0 < (N.massActionJacobian κ x) i i) :
    (N.massActionJacobian κ x).IsPMatrix :=
  N.isPMatrix_massActionJacobian_of_consistentSRSign κ hx hweight hdiag
-- ε-coupled Michaelis–Menten slow drift: along the slow flow ṡ = ε·g(s, z) of the globally C¹
-- regularized fast subsystem, the slaved complex curve has O(ε) velocity — derived from the
-- seed's global C¹ regularity, with only the substrate path assumed differentiable.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s z
        - CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s' z‖ ≤ L * dist s s')
    {s : ℝ → ℝ} (hspeed : ∀ t t', dist (s t) (s t') ≤ (ε * G) * |t - t'|)
    {s' : ℝ → ℝ} {t₀ : ℝ} (hs : HasDerivAt s (s' t₀) t₀) :
    ‖CRNT.MichaelisMenten.mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀) (s' t₀)‖
      ≤ (L / rate) * (ε * G) :=
  CRNT.MichaelisMenten.mmRegSlavedVelocity_le rate hrate Km Vmax hKm hL hε hG hlip hspeed hs
-- Concrete non-vacuity of Hopf admissibility: the explicit block-diagonal family `J` (a hyperbolic
-- real eigenvalue and a planar rotation-scaling block with conjugate pair `μ ± i`) is genuinely
-- Hopf-admissible at `μ₀ = 0`, so every field of `hopfAdmissible` — the eigenvalue-side algebraic
-- gates and the center-manifold seed — is simultaneously satisfiable on a real object.
noncomputable example :
    CRNT.hopfAdmissible CRNT.Examples.HopfOscillator3.J CRNT.Examples.HopfOscillator3.μ₀ :=
  CRNT.Examples.HopfOscillator3.admissible
-- The substrate-path speed bound dist (s t) (s t') ≤ (ε·G)·|t - t'| is derived from the coupled
-- drift law ṡ = ε·g(s, z) with ‖g‖ ≤ G, by the one-dimensional mean-value inequality, removing it
-- as a hypothesis of the O(ε) slaved-velocity bound.
example {ε G : ℝ} (hε : 0 ≤ ε) {g : ℝ → CRNT.MichaelisMenten.E → ℝ}
    (hg : ∀ a b, ‖g a b‖ ≤ G) {s : ℝ → ℝ} {z : ℝ → CRNT.MichaelisMenten.E}
    (hs : ∀ τ, HasDerivAt s (CRNT.MichaelisMenten.mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t t', dist (s t) (s t') ≤ (ε * G) * |t - t'| :=
  CRNT.MichaelisMenten.mmRegSubstrate_speed_le hε hg hs
-- The O(ε) slaved complex velocity bound now rests only on the drift bound ‖g‖ ≤ G and the
-- fast-field substrate Lipschitz constant L, with the speed hypothesis discharged.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km)
    {L ε G : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hlip : ∀ s s' z, ‖CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s z
        - CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s' z‖ ≤ L * dist s s')
    {g : ℝ → CRNT.MichaelisMenten.E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G)
    {s : ℝ → ℝ} {z : ℝ → CRNT.MichaelisMenten.E}
    (hs : ∀ τ, HasDerivAt s (CRNT.MichaelisMenten.mmRegSlowDrift ε g (s τ) (z τ)) τ) {t₀ : ℝ} :
    ‖CRNT.MichaelisMenten.mmRegSlavedVelocity rate hrate Km Vmax hKm (s t₀)
        (CRNT.MichaelisMenten.mmRegSlowDrift ε g (s t₀) (z t₀))‖ ≤ (L / rate) * (ε * G) :=
  CRNT.MichaelisMenten.mmRegSlavedVelocity_le_of_drift rate hrate Km Vmax hKm hL hε hG hlip hg hs

-- CTMC ergodic convergence: on a finite closed enabled region whose restricted transition matrix
-- is strictly positive (primitivity at the first step — the strongest finite-state aperiodicity),
-- the embedded jump chain mixes geometrically. The singleton-mass vector of the n-step matrix
-- evolution converges entrywise to the canonical stationary singleton masses, via the
-- finite-state Perron–Frobenius / Doeblin convergence theorem.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hpos : N.regionPositive κ T)
    (μ : @MeasureTheory.Measure (S → ℕ) CRNT.Network.instMeasurableSpaceCount)
    (hμprob :
      @MeasureTheory.IsProbabilityMeasure (S → ℕ) CRNT.Network.instMeasurableSpaceCount μ)
    (hμsupp : μ Tᶜ = 0) (i : ↥T) :
    Filter.Tendsto
        (fun n => ((N.regionMatrix κ T) ^ n).mulVec (CRNT.Network.stationaryVec (T := T) μ) i)
        Filter.atTop
        (nhds (CRNT.Network.stationaryVec (T := T)
          (N.stationaryProbabilityMeasure κ c T) i)) := by
  haveI := hμprob
  exact N.regionMatrix_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hpos μ hμsupp i

-- CTMC ergodic convergence under the general primitivity hypothesis: on a finite closed enabled
-- region whose restricted transition matrix has some strictly positive power (regionPrimitive — the
-- standard finite-state irreducibility-and-aperiodicity condition, weaker than first-step
-- positivity), the embedded jump chain still mixes geometrically to the canonical stationary law.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hprim : N.regionPrimitive κ T)
    (μ : @MeasureTheory.Measure (S → ℕ) CRNT.Network.instMeasurableSpaceCount)
    (hμprob :
      @MeasureTheory.IsProbabilityMeasure (S → ℕ) CRNT.Network.instMeasurableSpaceCount μ)
    (hμsupp : μ Tᶜ = 0) (i : ↥T) :
    Filter.Tendsto
        (fun n => ((N.regionMatrix κ T) ^ n).mulVec (CRNT.Network.stationaryVec (T := T) μ) i)
        Filter.atTop
        (nhds (CRNT.Network.stationaryVec (T := T)
          (N.stationaryProbabilityMeasure κ c T) i)) := by
  haveI := hμprob
  exact N.regionMatrix_primitive_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hprim μ hμsupp i
-- A genuine three-species mass-action network on the Hopf boundary: at `x = (1,1,1)` (a positive
-- steady state for every rate) the actual `Network.massActionJacobian` at the crossing rate `μ₀`
-- has a purely-imaginary conjugate eigenvalue pair and a strictly negative real eigenvalue.
example (hμ : 3 < CRNT.Examples.HopfNetwork3.μ₀) :
    (((-9 : ℂ)).re < 0) ∧ ((Real.sqrt 12 * Complex.I).re = 0)
      ∧ ((Real.sqrt 12 * Complex.I).im ≠ 0)
      ∧ (Real.sqrt 12 * Complex.I).im ^ 2
        = (CRNT.Examples.HopfNetwork3.N.massActionJacobian
            (CRNT.Examples.HopfNetwork3.κ CRNT.Examples.HopfNetwork3.μ₀ hμ)
            CRNT.Examples.HopfNetwork3.xeq).c₂Fin3 :=
  CRNT.Examples.HopfNetwork3.hopf_crossing_at_μ₀ hμ
-- The chosen point is a genuine steady state of the network for every rate.
example (μ : ℝ) (hμ : 3 < μ) :
    CRNT.Examples.HopfNetwork3.N.massActionVectorField
      (CRNT.Examples.HopfNetwork3.κ μ hμ) CRNT.Examples.HopfNetwork3.xeq = 0 :=
  CRNT.Examples.HopfNetwork3.equilibrium μ hμ
-- The network Jacobian crosses the Hurwitz (Hopf) boundary transversally in the autocatalytic rate.
example :
    CRNT.Examples.HopfNetwork3.boundaryFn CRNT.Examples.HopfNetwork3.μ₀ = 0
      ∧ deriv CRNT.Examples.HopfNetwork3.boundaryFn CRNT.Examples.HopfNetwork3.μ₀ ≠ 0 :=
  CRNT.Examples.HopfNetwork3.boundary_crossing_transversal

-- Fourier–Motzkin elimination of the last variable preserves rational feasibility.
example (sys : List (CRNT.RationalFarkas.Ineq (1 + 1))) :
    CRNT.RationalFarkas.Feasible (CRNT.RationalFarkas.eliminateLast sys)
      ↔ CRNT.RationalFarkas.Feasible sys :=
  CRNT.RationalFarkas.feasible_eliminateLast_iff sys
-- Region primitivity from strong connectivity and a self-loop: the abstract finite-state
-- Perron–Frobenius criterion (irreducibility plus a period-one self-loop) yields a strictly
-- positive matrix power, discharging the primitivity hypothesis of the convergence theorem.
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hsc : ∀ i j, CRNT.supportReaches P i j) {s : ι} (hs : 0 < P s s) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, 0 < (P ^ N) i j :=
  CRNT.primitive_of_stronglyConnected_self_loop P hP hsc hs
-- Strong connectivity of the region discharged from network jump-reachability: forward
-- positive-probability enabled jumps connecting every pair of region states (count-level
-- irreducibility) reverse to matrix support walks, giving the abstract regionStronglyConnected.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} [Fintype ↥T] (h : N.RegionJumpStronglyConnected κ T) :
    N.regionStronglyConnected κ T :=
  N.regionStronglyConnected_of_jumpReaches κ h
-- Unconditional geometric convergence to the stationary law for a concrete structural class: a
-- jump-strongly-connected closed enabled region carrying a holding reaction. Both the irreducibility
-- and the aperiodicity are discharged from the network's enabled-reaction structure — no abstract
-- regionStronglyConnected or regionPrimitive assumption remains.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hjsc : N.RegionJumpStronglyConnected κ T)
    {n : S → ℕ} (hn : n ∈ T) (hexit : N.exitRate κ n ≠ 0)
    {r : N.R} (hr : N.jumpNextCount n r = n) (hprob : 0 < N.jumpProb κ n r)
    (μ : @MeasureTheory.Measure (S → ℕ) CRNT.Network.instMeasurableSpaceCount)
    (hμprob :
      @MeasureTheory.IsProbabilityMeasure (S → ℕ) CRNT.Network.instMeasurableSpaceCount μ)
    (hμsupp : μ Tᶜ = 0) (i : ↥T) :
    Filter.Tendsto
        (fun k => ((N.regionMatrix κ T) ^ k).mulVec (CRNT.Network.stationaryVec (T := T) μ) i)
        Filter.atTop
        (nhds (CRNT.Network.stationaryVec (T := T)
          (N.stationaryProbabilityMeasure κ c T) i)) := by
  haveI := hμprob
  exact N.jumpStronglyConnected_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hjsc
    hn hexit hr hprob μ hμsupp i
-- Single-reaction lift: firing any reaction at a count of a closed enabled region is a region jump
-- step. Enabledness gives positive propensity hence positive jump probability, and the region's
-- forward closure keeps the post-firing count inside, so the complex-graph edge realizes a
-- count-space step.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) {n : S → ℕ} (hn : n ∈ T) (r : N.R) :
    N.JumpStep κ T n (N.jumpNextCount n r) :=
  N.jumpStep_of_mem_region κ hT hn r
-- Convergence from weak reversibility plus fireable-list connectivity: with the count-level
-- irreducibility hypothesis replaced by reaction lists realizing every pair of region counts, the
-- embedded jump chain mixes geometrically to the stationary law for a weakly reversible network.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (c : Concentration S) (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    {T : Set (S → ℕ)} [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) (hne : T.Nonempty)
    (hwr : N.WeaklyReversible)
    (hpairs : ∀ n ∈ T, ∀ m ∈ T, ∃ rs : List N.R,
      N.FireableList κ T n rs ∧ N.fireListTarget n rs = m)
    {n : S → ℕ} (hn : n ∈ T) (hexit : N.exitRate κ n ≠ 0)
    {r : N.R} (hr : N.jumpNextCount n r = n) (hprob : 0 < N.jumpProb κ n r)
    (μ : @MeasureTheory.Measure (S → ℕ) CRNT.Network.instMeasurableSpaceCount)
    (hμprob :
      @MeasureTheory.IsProbabilityMeasure (S → ℕ) CRNT.Network.instMeasurableSpaceCount μ)
    (hμsupp : μ Tᶜ = 0) (i : ↥T) :
    Filter.Tendsto
        (fun k => ((N.regionMatrix κ T) ^ k).mulVec (CRNT.Network.stationaryVec (T := T) μ) i)
        Filter.atTop
        (nhds (CRNT.Network.stationaryVec (T := T)
          (N.stationaryProbabilityMeasure κ c T) i)) := by
  haveI := hμprob
  exact N.weaklyReversible_pow_mulVec_tendsto_stationaryVec κ c hc hcb hT hne hwr hpairs
    hn hexit hr hprob μ hμsupp i
-- The computable signed incidence agrees with the real reaction-vector incidence sign.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (s : S) (r : N.R) :
    N.intSignedEdge s r = N.signedEdge s r :=
  N.intSignedEdge_eq s r

-- A single-species production `A → 2A` discharges the consistent signed SR-cover certificate by
-- `decide`: its only cover is the positive singleton, so the sign condition holds.
example :
    (⟨Unit, inferInstance, inferInstance,
      fun _ => { source := fun _ => 1, target := fun _ => 2 }⟩ :
        Network (Fin 1)).ConsistentSRSign := by decide

-- The decidable certificate's real-cast image is exactly the weight hypothesis the
-- species–reaction graph injectivity verdict consumes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.ConsistentSRSign) :
    ∀ (s : Finset S) (σ : Equiv.Perm s) (ρ : s → N.R),
      0 ≤ ((CRNT.coverCoeff σ : ℤ) : ℝ) *
        ((∏ a : s, N.signedEdge ((σ a : S)) (ρ a) : SignType) : ℝ) :=
  N.hweight_of_consistentSRSign h
-- The C¹ eigenvalue branches of the network Jacobian, built by the implicit function theorem, give
-- the eigenvalue-real-part crossing speed: the conjugate pair crosses the imaginary axis
-- transversally, p'(μ₀) ≠ 0, for the genuine three-species autocatalytic network.
example : ((-1 - CRNT.Examples.HopfNetwork3Branches.r') / 2 : ℝ) ≠ 0 :=
  CRNT.Examples.HopfNetwork3Branches.eigenvalue_real_part_transversal
-- The horizon-uniform Michaelis–Menten tracking ceiling: under the coupled transverse one-sided
-- contraction at rate `λ` and an `O(ε)` reference defect `δ`, the transverse gap between the exact
-- trajectory and the moving slow-manifold reference is bounded by `gap 0 + δ/λ` for all forward time.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {full : E → E} {x m m' : ℝ → E} {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hx : ∀ t, HasDerivAt x (full (x t)) t) (hm : ∀ t, HasDerivAt m (m' t) t)
    (hcon : ∀ t, 0 ≤ t →
      inner ℝ (full (x t) - full (m t)) (x t - m t) ≤ -lam * ‖x t - m t‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t → ‖full (m t) - m' t‖ ≤ δ) :
    ∀ t, 0 ≤ t → ‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / lam :=
  ODE.coupled_dissipative_ceiling hlam hδ hx hm hcon hdef

-- The regularized Michaelis–Menten fast field has the frozen-fibre exact transverse contraction at
-- rate `rate`: at any fixed substrate `s`, the inner product of the field difference with the state
-- difference equals `-rate · ‖z - w‖²` for every pair of complex states, the negative logarithmic-norm
-- identity that discharges the coupled transverse contraction hypothesis.
example (rate Km Vmax s : ℝ) (z w : CRNT.MichaelisMenten.E) :
    inner ℝ (CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s z
        - CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s w) (z - w)
      = -rate * ‖z - w‖ ^ 2 :=
  CRNT.MichaelisMenten.mmRegFastField_coupled_contraction rate Km Vmax s z w

-- The regularized Michaelis–Menten fast field is substrate-Lipschitz with the explicit constant
-- `rate · 6 · |Vmax| / Km` read off the model parameters: this discharges the `hlip` hypothesis of the
-- coupled tracking ceiling as a theorem, leaving the certified `O(ε)` reduction to depend only on the
-- positivity of `rate, Km`, the non-negativity of `ε`, and the physical drift bound `‖g‖ ≤ G`.
example (rate Km Vmax : ℝ) (hrate : 0 ≤ rate) (hKm : 0 < Km) (s s' : ℝ)
    (z : CRNT.MichaelisMenten.E) :
    ‖CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s z
        - CRNT.MichaelisMenten.mmRegFastField rate Km Vmax s' z‖
      ≤ CRNT.MichaelisMenten.mmRegFastFieldLipConst rate Km Vmax * dist s s' :=
  CRNT.MichaelisMenten.mmRegFastField_substrate_lipschitz rate Km Vmax hrate hKm s s' z

-- Rational linear feasibility decides by Fourier–Motzkin elimination (`decide`, not
-- `native_decide`). At the `Fin 0` base case feasibility is the nonnegativity of every
-- bound: an empty system and one with a nonnegative bound are feasible; one with a
-- negative bound is not.
example : CRNT.RationalFarkas.Feasible ([] : List (CRNT.RationalFarkas.Ineq 0)) := by decide
example :
    CRNT.RationalFarkas.Feasible
      [({ coeff := ![], bound := 3 } : CRNT.RationalFarkas.Ineq 0),
       { coeff := ![], bound := 0 }] := by decide
example :
    ¬ CRNT.RationalFarkas.Feasible
      [({ coeff := ![], bound := -1 } : CRNT.RationalFarkas.Ineq 0)] := by decide

-- Strict rational linear feasibility decides by the strict Fourier–Motzkin variant (`decide`, not
-- `native_decide`). At the `Fin 0` base case strict feasibility is the positivity of every bound:
-- an empty system and one with a strictly positive bound are strictly feasible; one with a
-- zero bound is not (`0 < 0` fails).
example : CRNT.RationalFarkas.FeasibleStrict ([] : List (CRNT.RationalFarkas.Ineq 0)) := by decide
example :
    CRNT.RationalFarkas.FeasibleStrict
      [({ coeff := ![], bound := 3 } : CRNT.RationalFarkas.Ineq 0),
       { coeff := ![], bound := 1 }] := by decide
example :
    ¬ CRNT.RationalFarkas.FeasibleStrict
      [({ coeff := ![], bound := 0 } : CRNT.RationalFarkas.Ineq 0)] := by decide
-- Spectral splitting: a real linear endomorphism complexified into a finite-dimensional ℂ-space
-- yields a center/stable/unstable internal direct sum. We exercise the abstract construction on a
-- concrete endomorphism of `Fin 1 → ℂ`.
example :
    DirectSum.IsInternal
      (fun i : Fin 3 =>
        ![CRNT.SpectralSplitting.stableSubspace (V := Fin 1 → ℂ) 0,
          CRNT.SpectralSplitting.centerSubspace (V := Fin 1 → ℂ) 0,
          CRNT.SpectralSplitting.unstableSubspace (V := Fin 1 → ℂ) 0] i) :=
  CRNT.SpectralSplitting.isInternal_stable_center_unstable (V := Fin 1 → ℂ) 0

example (A : Module.End ℂ (Fin 1 → ℂ)) :
    Set.MapsTo A (CRNT.SpectralSplitting.centerSubspace A)
      (CRNT.SpectralSplitting.centerSubspace A) :=
  CRNT.SpectralSplitting.mapsTo_centerSubspace A

-- A complex-shift region discharges the count-level irreducibility hypothesis with no count
-- reachability assumed: its reaction-graph-reachable offset complexes lift to fireable reaction
-- lists between every pair of region counts (`fireablePairs_of_complexShiftRegion`).
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {T : Set (S → ℕ)} (hR : N.ComplexShiftRegion κ T) :
    ∀ n ∈ T, ∀ m ∈ T, ∃ rs : List N.R,
      N.FireableList κ T n rs ∧ N.fireListTarget n rs = m :=
  N.fireablePairs_of_complexShiftRegion κ hR

-- The critical-siphon verdict is decidable: the encoded rational system's feasibility matches the
-- single-coordinate supported-positivity test, and `IsCriticalSiphon`, `HasCriticalSiphon`, and
-- `HasNoCriticalSiphon` all carry `Decidable` instances.
example {S : Type} [DecidableEq S] [Fintype S] (N : CRNT.Network S)
    (e : S ≃ Fin (Fintype.card S)) (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (s₀ : S) :
    CRNT.RationalFarkas.Feasible (N.supportedFeasSystem e eR P s₀)
      ↔ ∃ w : S → ℝ, N.SupportedConservationVector P w ∧ 0 < w s₀ :=
  N.feasible_supportedFeasSystem_iff e eR P s₀

example {S : Type} [DecidableEq S] [Fintype S] (N : CRNT.Network S) (P : Finset S) :
    Nonempty (Decidable (N.IsCriticalSiphon P)) :=
  ⟨inferInstance⟩

example {S : Type} [DecidableEq S] [Fintype S] (N : CRNT.Network S) :
    Nonempty (Decidable N.HasCriticalSiphon) :=
  ⟨inferInstance⟩

example {S : Type} [DecidableEq S] [Fintype S] (N : CRNT.Network S) :
    N.HasNoCriticalSiphon ↔ ¬ N.HasCriticalSiphon :=
  N.hasNoCriticalSiphon_iff_not_hasCriticalSiphon

-- The rational–real feasibility bridge: a rational `Ineq` system is real-feasible iff feasible.
example {n : ℕ} (sys : List (CRNT.RationalFarkas.Ineq n)) :
    CRNT.RationalFarkas.Feasibleℝ sys ↔ CRNT.RationalFarkas.Feasible sys :=
  CRNT.RationalFarkas.feasibleℝ_iff_feasible sys
-- Real descent: complexifying a real matrix and pushing the sign-class subspaces back to `ℝⁿ`
-- gives a real center/stable/unstable internal direct sum, each invariant under `A.mulVec`.
example (A : Matrix (Fin 2) (Fin 2) ℝ) :
    DirectSum.IsInternal
      (fun i : Fin 3 =>
        ![CRNT.SpectralSplittingReal.realStableSubspace A,
          CRNT.SpectralSplittingReal.realCenterSubspace A,
          CRNT.SpectralSplittingReal.realUnstableSubspace A] i) :=
  CRNT.SpectralSplittingReal.isInternal_real_stable_center_unstable A

example (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Set.MapsTo A.mulVec (CRNT.SpectralSplittingReal.realCenterSubspace A)
      (CRNT.SpectralSplittingReal.realCenterSubspace A) :=
  CRNT.SpectralSplittingReal.mulVec_mapsTo_realCenterSubspace A

-- The abstract certified reduction: for any C¹ slow-manifold seed, the substrate-Lipschitz bound `L`,
-- the `O(ε)` slow drift, and the coupled transverse contraction at the fibre rate `λ = S.rate` give
-- the horizon-uniform `O(ε)` tracking ceiling `‖x t - m t‖ ≤ ‖x 0 - m 0‖ + (L/λ)·ε/λ` for all
-- forward time, the slaved velocity derived from the implicit-function regularity of `manifoldMap`.
example {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : ODE.SlowManifoldC1Seed Y E) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hlip : ∀ y y' z, ‖S.fast y z - S.fast y' z‖ ≤ L * dist y y')
    {s : ℝ → Y} {s' : ℝ → Y} {x : ℝ → E}
    (hspeed : ∀ t t', dist (s t) (s t') ≤ ε * |t - t'|)
    (hsd : ∀ t, HasDerivAt s (s' t) t)
    (hx : ∀ t, HasDerivAt x (S.fast (s t) (x t)) t)
    (hcon : ∀ t, 0 ≤ t →
      inner ℝ (S.fast (s t) (x t) - S.fast (s t) (S.manifoldMap (s t)))
          (x t - S.manifoldMap (s t))
        ≤ -S.rate * ‖x t - S.manifoldMap (s t)‖ ^ 2) :
    ∀ t, 0 ≤ t →
      ‖x t - S.manifoldMap (s t)‖
        ≤ ‖x 0 - S.manifoldMap (s 0)‖ + (L / S.rate) * ε / S.rate :=
  S.certified_reduction hL hε hlip hspeed hsd hx hcon

-- The Michaelis–Menten horizon-uniform tracking ceiling re-derived as an instance of the abstract
-- certified reduction: the regularized seed's three abstract inputs are discharged from model data,
-- recovering the bespoke `O(ε)` ceiling with `L = mmRegFastFieldLipConst rate Km Vmax`.
example (rate : ℝ) (hrate : 0 < rate) (Km Vmax : ℝ) (hKm : 0 < Km) {ε G : ℝ}
    (hε : 0 ≤ ε) (hG : 0 ≤ G) {g : ℝ → CRNT.MichaelisMenten.E → ℝ} (hg : ∀ a b, ‖g a b‖ ≤ G)
    {x : ℝ → CRNT.MichaelisMenten.E} {s : ℝ → ℝ} {z : ℝ → CRNT.MichaelisMenten.E}
    (hx : ∀ t, HasDerivAt x (CRNT.MichaelisMenten.mmRegFastField rate Km Vmax (s t) (x t)) t)
    (hs : ∀ τ, HasDerivAt s (CRNT.MichaelisMenten.mmRegSlowDrift ε g (s τ) (z τ)) τ) :
    ∀ t, 0 ≤ t →
      ‖x t - (CRNT.MichaelisMenten.mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s t)‖
        ≤ ‖x 0
            - (CRNT.MichaelisMenten.mmRegSlowManifoldSeed rate hrate Km Vmax hKm).manifoldMap (s 0)‖
          + (CRNT.MichaelisMenten.mmRegFastFieldLipConst rate Km Vmax / rate) * (ε * G) / rate :=
  CRNT.MichaelisMenten.mmReg_tracking_ceiling_via_abstract rate hrate Km Vmax hKm hε hG hg hx hs
-- Exponential invariance: the linear flow `exp (t • A)` preserves each real spectral subspace.
example (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Set.MapsTo (NormedSpace.exp (t • A)).mulVec
      (CRNT.SpectralSplittingReal.realStableSubspace A)
      (CRNT.SpectralSplittingReal.realStableSubspace A) :=
  CRNT.ExponentialDichotomy.mulVec_exp_smul_mapsTo_realStableSubspace A t
-- Non-vacuous convergence via the uniformized kernel: on a finite strongly connected closed enabled
-- region the uniformized region matrix is primitive — its diagonal holding mass `1 − w > 0` supplies
-- the aperiodicity self-loop the embedded jump chain lacks — so the powers `U^{∘n}` converge
-- geometrically to the unique stationary law, entrywise and in `ℓ¹`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T]
    (hT : N.ClosedEnabledRegion κ T) (hsc : N.regionStronglyConnected κ T)
    (x : ↥T → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥T → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ hTfin).mulVec b = b ∧
      Filter.Tendsto (fun n => CRNT.l1Dist ((N.uRegionMatrix κ hTfin ^ n).mulVec x) b)
        Filter.atTop (nhds 0) ∧
      ∀ i, Filter.Tendsto (fun n => (N.uRegionMatrix κ hTfin ^ n).mulVec x i)
        Filter.atTop (nhds (b i)) :=
  N.uRegionMatrix_pow_mulVec_tendsto κ hTfin hT hsc x hx

-- The uniformized region matrix has a strictly positive diagonal at every region state: the
-- self-loop supplied by `U`'s holding term, absent from the embedded jump chain.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] (j : ↥T) :
    0 < N.uRegionMatrix κ hTfin j j :=
  N.uRegionMatrix_diag_pos κ hTfin j
-- Computable rational stoichiometric chart: an explicit nonsingular maximal minor selection
-- yields a computable rational chart `B` and projection `P` with `P · B = 1`.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R)
    (hdet : (N.stoichMatrixQ.submatrix ρ γ).det ≠ 0) :
    N.chartProjQ ρ γ * N.chartBasisQ γ = 1 :=
  N.chartProjQ_mul_chartBasisQ ρ γ hdet
-- The reduced-compression cover-sign certificate at a rational chart point is decidable.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R) (kq : N.R → ℚ) (xq : S → ℚ) :
    Decidable (N.CompressionCoverSignQ ρ γ kq xq) :=
  inferInstance
-- The reduced-pivot cover-sign certificate (matching the pivot-reduced Jacobian) is decidable.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R) (kq : N.R → ℚ) (xq : S → ℚ) :
    Decidable (N.PivotCoverSignQ ρ γ kq xq) :=
  inferInstance
-- Pointwise reduced-P-matrix bridge: at a rational data point whose chart point is the cast of a
-- rational concentration, the decidable rational cover-sign certificate makes the pivot-reduced
-- Jacobian a P-matrix there. The reduced cover-sign pattern is concentration dependent, so this is a
-- pointwise verdict, not a box-quantified one.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : Concentration S) {k : ℕ} (ρ : Fin k → S) (γ : Fin k → N.R) (y : Fin k → ℝ)
    (kq : N.R → ℚ) (xq : S → ℚ) (hk : ∀ r, κ.k r = (kq r : ℝ))
    (hpt : Network.pivotAffineChart x₀ (N.concretePivotChart ρ γ) y = fun s => ((xq s : ℝ)))
    (h : N.PivotCoverSignQ ρ γ kq xq) :
    (N.pivotReducedJacobian κ x₀ ρ (N.concretePivotChart ρ γ) y).IsPMatrix :=
  N.isPMatrix_pivotReducedJacobian_of_pivotCoverSignQ κ x₀ ρ γ y kq xq hk hpt h
-- Exponential decay from a Lyapunov certificate: a Hurwitz generator's flow contracts at an
-- exponential rate `‖exp (t • A) x‖ ≤ √(C₀/c₀) · e^{-t/(2 C₀)} · ‖x‖` on the stable directions.
example (A : Matrix (Fin 2) (Fin 2) ℝ)
    (cert : CRNT.ExponentialDecay.LyapunovCertificate (CRNT.ExponentialDecay.act A))
    (x : CRNT.ExponentialDecay.Phase 2) {t : ℝ} (ht : 0 ≤ t) :
    ‖CRNT.ExponentialDecay.act (NormedSpace.exp (t • A)) x‖
      ≤ Real.sqrt (cert.C₀ / cert.c₀) * Real.exp (-(1 / (2 * cert.C₀)) * t) * ‖x‖ :=
  cert.norm_exp_smul_le x ht
-- Point-independence of the consistent-SR-cover P-matrix verdict: the point-free signed-incidence
-- weight and diagonal-drive conditions make the full mass-action Jacobian a P-matrix at every
-- positive concentration of a set, so one check of the incidence data discharges the box.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (C : Set (CRNT.Concentration S)) (hC : ∀ x ∈ C, x.Positive)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    ∀ x ∈ C, (N.massActionJacobian κ x).IsPMatrix :=
  N.isPMatrix_massActionJacobian_box_of_pointIndep κ C hC hweight hdrive

-- Genuinely non-vacuous convergence on a real network: on the `A ⇌ B` conservation class
-- `{n : n_A + n_B = K}` (`1 ≤ K`), a relaxed finite region that exists where no closed enabled
-- region can, the uniformized powers `U^{∘n}` converge geometrically to the unique stationary law —
-- unconditionally, with every hypothesis discharged from network structure.
example (κ : Network.RateConstants CRNT.Examples.StochasticConvergenceExample.N) (K : ℕ)
    (hK : 1 ≤ K) (x : ↥(CRNT.Examples.ConservationClassRegion.conservationClass K) → ℝ)
    (hx : ∑ i, x i = 1) :
    ∃ b : ↥(CRNT.Examples.ConservationClassRegion.conservationClass K) → ℝ,
      (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (Network.uRegionMatrix _ κ
        (CRNT.Examples.ConservationClassRegion.conservationClass_finite K)).mulVec b = b ∧
      Filter.Tendsto (fun n => CRNT.l1Dist ((Network.uRegionMatrix _ κ
        (CRNT.Examples.ConservationClassRegion.conservationClass_finite K) ^ n).mulVec x) b)
        Filter.atTop (nhds 0) ∧
      ∀ i, Filter.Tendsto (fun n => (Network.uRegionMatrix _ κ
        (CRNT.Examples.ConservationClassRegion.conservationClass_finite K) ^ n).mulVec x i)
        Filter.atTop (nhds (b i)) :=
  CRNT.Examples.ConservationClassRegion.conservationClass_pow_mulVec_tendsto κ K hK x hx
-- The continuous-time companion: the uniformized chemical-master-equation semigroup on the `A ⇌ B`
-- conservation class relaxes unconditionally to the stationary law as `t → ∞`. The Poisson mixture
-- `P_t x = ∑_k Po(Λt){k} · (U^{∘k} x)` of the discrete powers converges entrywise to `b`, lifting the
-- geometric discrete mixing to continuous-time relaxation by the Poisson-tail argument.
example (κ : Network.RateConstants CRNT.Examples.StochasticConvergenceExample.N) (K : ℕ)
    (hK : 1 ≤ K) (x : ↥(CRNT.Examples.ConservationClassRegion.conservationClass K) → ℝ)
    (hx : ∑ i, x i = 1) :
    ∃ b : ↥(CRNT.Examples.ConservationClassRegion.conservationClass K) → ℝ,
      (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (Network.uRegionMatrix _ κ
        (CRNT.Examples.ConservationClassRegion.conservationClass_finite K)).mulVec b = b ∧
      ∀ i, Filter.Tendsto (fun t : NNReal => Network.cmeRegionVec _ κ
        (CRNT.Examples.ConservationClassRegion.conservationClass_finite K) x t i)
        Filter.atTop (nhds (b i)) :=
  CRNT.Examples.ConservationClassRegion.conservationClass_cmeRegionVec_tendsto κ K hK x hx
-- The abstract Poisson-average lift in isolation: the Poisson average of any convergent real sequence
-- relaxes to its limit as the rate tends to infinity.
example {a : ℕ → ℝ} {L : ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun r : NNReal => ∑' k, (ProbabilityTheory.poissonMeasure r {k}).toReal * a k)
      Filter.atTop (nhds L) :=
  CRNT.tendsto_poissonAverage_atTop ha
-- A sound general injectivity verdict from point-free network data: on a coordinate-selection
-- chart whose box covers the class and reads the full Jacobian on the pivot rows, the point-free
-- signed-incidence weight and diagonal-drive conditions make mass-action kinetics injective on the
-- positive compatibility class — no per-point or per-chart-cover assumption.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    (x₀ : CRNT.Concentration S) {lo hi : Fin N.stoichRank → ℝ}
    {f : Fin N.stoichRank → S} (hf : Function.Injective f)
    (hbox : ∀ x ∈ N.positiveCompatibilityClass x₀, N.chartCoord x₀ x ∈ Set.Icc lo hi)
    (hpos : ∀ y ∈ Set.Icc lo hi, Concentration.Positive (N.affineChart x₀ y))
    (hsub : ∀ y ∈ Set.Icc lo hi, N.reducedJacobian κ x₀ y
      = (N.massActionJacobian κ (N.affineChart x₀ y)).submatrix f f)
    (hweight : N.SignCoverWeightNonneg) (hdrive : N.PositiveDiagonalDrive) :
    (N.massActionKinetics κ).InjectiveOnClass x₀ :=
  N.massActionInjectiveOnClass_of_pointIndep κ x₀ hf hbox hpos hsub hweight hdrive

-- End-to-end Fenichel ε-persistence for the explicit bounded constant fast-drift coupled field,
-- with the operator-from-flow `flow_mapsTo` proved from a genuine `exists_flow` flow on `ℝ × ℝ`:
-- the persisted manifold graph is forward-invariant under the iterate coupled semiflow and `M_ε`
-- sits within `O(ε)` of `M_0` in the supremum metric, with every hypothesis discharged.
example (τ : NNReal) :
    let G := ODE.scaleGapData (Y := ℝ) (E := ℝ) 2 1 (by norm_num) (by norm_num) (by norm_num)
    let F := ODE.constDriftCoupled (Y := ℝ) (E := ℝ) 0 τ
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_constDrift 2 1 (by norm_num) (by norm_num) (by norm_num) τ

-- End-to-end Fenichel ε-persistence for the genuinely contracting fast-fibre field on `ℝ × ℝ`
-- (`ż = -rate·(z - c)`), with the operator-from-flow `flow_mapsTo` proved from the closed-form
-- contracting flow: the persisted manifold is the genuine attracting fibre `z = c` (a non-trivial
-- moving manifold, not the zero section), its graph forward-invariant under the iterate coupled
-- semiflow and `M_ε` close to the base section, with every hypothesis discharged.
example :
    let G := ODE.contractGapData (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
      (by norm_num) (by norm_num)
    let F := ODE.contractingCoupled (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_contracting 3 (7 : ℝ) (1 : NNReal) (by norm_num) (by norm_num)
-- End-to-end Fenichel ε-persistence over a GENUINELY DRIFTING slow base on `ℝ × ℝ`
-- (`ẏ = ε·b`, `ż = -rate·(z - c)`): the base coordinate honestly moves under the closed-form coupled
-- flow `(y, z) ↦ (y + (ε·t)·b, c + e^{-rate·t}·(z - c))`, removing the frozen-base idealization. The
-- persisted manifold is the attracting fibre `z = c`, its graph forward-invariant under the iterate
-- coupled drifting-base semiflow and `M_ε` close to the base section, every hypothesis discharged.
example :
    let G := ODE.contractGapData (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
      (by norm_num) (by norm_num)
    let F := ODE.coupledDriftCoupled (Y := ℝ) (E := ℝ) (5 : ℝ) (2 : ℝ) 3 (7 : ℝ) (1 : NNReal)
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_coupledDrift (5 : ℝ) (2 : ℝ) 3 (7 : ℝ) (1 : NNReal)
    (by norm_num) (by norm_num)
-- End-to-end Fenichel ε-persistence over a GENERAL NONLINEAR slow base flow on `ℝ × ℝ`: the base
-- evolves by the genuine `exists_flow` semiflow of the bounded Lipschitz nonlinear field `ε·sin y`
-- (`logisticDriftFlow`), not a translation, while the fast fibre contracts onto `c`. The persisted
-- manifold is the attracting fibre `z = c`, its graph forward-invariant under the iterate product
-- semiflow over the nonlinear base and `M_ε` within the O(ε) ceiling, every hypothesis discharged via
-- the contracting-manifold machinery, with NO base invertibility used.
example :
    let G := ODE.contractGapData (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
      (by norm_num) (by norm_num)
    IsInvariant
        (fun n : ℕ => (ODE.productContractFlow (ODE.logisticDriftFlow (5 : ℝ)) 3 (7 : ℝ)).toFun
          (n • (1 : NNReal))) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_logisticDrift (5 : ℝ) 3 (7 : ℝ) (1 : NNReal) (by norm_num) (by norm_num)
-- End-to-end Fenichel ε-persistence of a MOVING slow manifold over a genuinely moving base on
-- `ℝ × ℝ`: the non-constant fibre `h(y)` is regraphed through the base back-map `slowInv` (the
-- moving-target machinery is exercised on every candidate section by `movingFlow_mapsTo`), here over
-- the affine constant-velocity base flow `ẏ = v` whose time-τ translation has the explicit inverse
-- `y ↦ y - τ·v`. The persisted manifold is the attracting fibre `z = c`, its graph forward-invariant
-- under the iterate product semiflow over the moving base and `M_ε` within the O(ε) ceiling, every
-- hypothesis discharged.
example :
    let G := ODE.contractGapData (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
      (by norm_num) (by norm_num)
    IsInvariant
        (fun n : ℕ => (ODE.productContractFlow (ODE.affineBaseFlow (5 : ℝ)) 3 (7 : ℝ)).toFun
          (n • (1 : NNReal))) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_affineBase (5 : ℝ) 3 (7 : ℝ) (1 : NNReal) (by norm_num) (by norm_num)
-- End-to-end Fenichel ε-persistence of a MOVING slow manifold over the genuinely CURVED logistic base
-- `ẏ = ε·sin y` on `ℝ × ℝ`, with NO explicit inverse supplied: the time-τ base map's left-inverse
-- comes from injectivity alone (`logisticDriftFlow_injective`, via integral-curve uniqueness), bundled
-- abstractly as `Function.invFun`. The non-constant fibre is regraphed through this abstract back-map;
-- the persisted manifold is the attracting fibre `z = c`, its graph forward-invariant under the
-- iterate product semiflow over the curved base and `M_ε` within the O(ε) ceiling.
example :
    let G := ODE.contractGapData (Y := ℝ) (E := ℝ) 3 (7 : ℝ) (1 : NNReal)
      (by norm_num) (by norm_num)
    let F := ODE.movingCoupled (ODE.logisticInjectiveBase (5 : ℝ) (1 : NNReal)) 3 (7 : ℝ)
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ)) (ODE.graphSet (G.manifold : ℝ → ℝ)) ∧
      dist G.base G.manifold ≤ G.defect / (1 - G.factor) :=
  ODE.graphTransform_discrete_invariant_and_dist_le_logisticMovingBase (5 : ℝ) 3 (7 : ℝ) (1 : NNReal)
    (by norm_num) (by norm_num)
-- Strict boundary support for the GENUINE toric mass-action field, discharged from the dynamics:
-- the fan cone geometry gives only `0 ≤ ⟪n, v⟫`; an enabled strictly-inward reaction per active
-- wall upgrades it to the strict `IsStrictSupportField` the persistence engine consumes.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (h : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = CRNT.toEuclid n₀ ∧
      N.EnabledStrictlyInwardFace κ faces n₀ nf.2) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  N.toricMassActionField_isStrictSupportField κ h

-- Fenichel ε-persistence of the genuinely substrate-varying Michaelis–Menten slow manifold: the
-- coupled-flow graph transform whose fibre relaxes toward the moving target `mmRegEquil Km Vmax s · e0`
-- over the substrate interval `[0, s₀]`, with the operator-from-flow `flow_mapsTo` proved from the
-- closed-form moving-target contracting flow. The persisted manifold is the substrate-varying
-- equilibrium graph (a genuinely base-varying manifold), forward-invariant under the iterate coupled
-- semiflow, sitting within the honest `O(ε)` slaved-velocity ceiling of the base section.
example :
    let G' := CRNT.MichaelisMenten.mmFenichelData 3 (by norm_num) 2 5 (by norm_num) 10
      (1 : NNReal) (by norm_num) (L := 4) (ε := 1) (G := 6) (by norm_num) (by norm_num) (by norm_num)
    let F := CRNT.MichaelisMenten.mmCoupledFlowGraphTransform 3 2 5 (by norm_num) 10 (1 : NNReal)
    IsInvariant (fun n : ℕ => F.flow.toFun (n • F.τ))
        (ODE.graphSet (G'.manifold : CRNT.MichaelisMenten.SubstrateIcc 10 → CRNT.MichaelisMenten.E)) ∧
      dist G'.base G'.manifold ≤ G'.defect / (1 - G'.factor) :=
  CRNT.MichaelisMenten.mmFenichelPersistence 3 (by norm_num) 2 5 (by norm_num) 10 (1 : NNReal)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
-- All-time continuous-semiflow Fenichel invariance of the Michaelis–Menten slow manifold: the graph
-- of the substrate-varying equilibrium section is forward-invariant under the full continuous coupled
-- semiflow `Φ t` at every forward time (not merely sampled at multiples of the horizon `τ`), paired
-- with the unchanged honest `O(ε)` `C⁰`-closeness ceiling — the complete geometric Fenichel statement.
example :
    let G' := CRNT.MichaelisMenten.mmFenichelData 3 (by norm_num) 2 5 (by norm_num) 10
      (1 : NNReal) (by norm_num) (L := 4) (ε := 1) (G := 6) (by norm_num) (by norm_num) (by norm_num)
    let F := CRNT.MichaelisMenten.mmCoupledFlowGraphTransform 3 2 5 (by norm_num) 10 (1 : NNReal)
    IsInvariant F.flow.toFun
        (ODE.graphSet (G'.manifold : CRNT.MichaelisMenten.SubstrateIcc 10 → CRNT.MichaelisMenten.E)) ∧
      dist G'.base G'.manifold ≤ G'.defect / (1 - G'.factor) :=
  CRNT.MichaelisMenten.mmFenichelPersistence_allTime 3 (by norm_num) 2 5 (by norm_num) 10 (1 : NNReal)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
-- Kurtz density-dependent scaling: the volume-scaled generator of the reversible pair `A ⇌ B`,
-- applied to any differentiable observable, converges as `V → ∞` to the derivative of the
-- observable along the deterministic mass-action field `F`.
example (κ : Network.RateConstants Examples.ReversiblePair.N)
    {f : Concentration Examples.ReversiblePair.Species → ℝ}
    {x : Concentration Examples.ReversiblePair.Species}
    {L : Concentration Examples.ReversiblePair.Species →L[ℝ] ℝ} (hf : HasFDerivAt f L x) :
    Filter.Tendsto (fun V : ℝ => Examples.ReversiblePair.N.scaledGenerator κ V f x) Filter.atTop
      (nhds (L (Examples.ReversiblePair.N.massActionVectorField κ x))) :=
  Examples.ReversiblePair.tendsto_scaledGenerator_reversiblePair κ hf

-- The limit field's `A`-component is the linear law `ẋ_A = −κ_f x_A + κ_b x_B`.
example (κ : Network.RateConstants Examples.ReversiblePair.N)
    (x : Concentration Examples.ReversiblePair.Species) :
    Examples.ReversiblePair.N.massActionVectorField κ x Examples.ReversiblePair.Species.A =
      -(κ.k Examples.ReversiblePair.Rxn.fwd * x Examples.ReversiblePair.Species.A)
        + κ.k Examples.ReversiblePair.Rxn.bwd * x Examples.ReversiblePair.Species.B :=
  Examples.ReversiblePair.massActionVectorField_A κ x
-- The strictly-inward reaction per active wall, discharged from weak reversibility: a wall whose
-- complex potential is straddled by a directed reaction path (a WR cycle through it) has a reaction
-- whose reaction vector points strictly into the region, `0 < ⟪n, reactionVector r⟫`.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) {n : S → ℝ}
    (h : N.WallCrossedByPath n) :
    ∃ r : N.R, 0 < ⟪CRNT.toEuclid n, CRNT.toEuclid (N.reactionVector r)⟫_ℝ :=
  N.exists_strictlyInward_of_wallCrossed h
-- The full discharge: with every wall crossed (WR cycle through it), every reaction
-- non-strictly inward (fan cone geometry), and every boundary point a strictly-positive
-- concentration (enabling), the genuine toric field is a strict support field with no assumed
-- `EnabledStrictlyInwardFace`.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = CRNT.toEuclid n₀ ∧
      N.WallCrossedByPath n₀ ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  N.toricMassActionField_isStrictSupportField_of_wallsCrossed κ hfaces
-- An active wall of a weakly-reversible network is crossed by a directed path: non-constancy of the
-- wall potential on a strongly-connected component plus symmetric reachability gives a directed
-- uphill path straddling a threshold.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    {n : S → ℝ} (h : N.ActiveWall n) : N.WallCrossedByPath n :=
  hwr.wallCrossedByPath_of_activeWall h
-- An active wall of a weakly-reversible network has a strictly-inward reaction, with the crossing
-- discharged from weak reversibility rather than assumed.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    {n : S → ℝ} (h : N.ActiveWall n) :
    ∃ r : N.R, 0 < ⟪CRNT.toEuclid n, CRNT.toEuclid (N.reactionVector r)⟫_ℝ :=
  hwr.exists_strictlyInward_of_activeWall h
-- The full discharge from weak reversibility: every wall active (non-constant potential), every
-- reaction non-strictly inward (fan cone geometry), every boundary point a strictly-positive
-- concentration. The crossing clause is no longer assumed.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (hwr : N.WeaklyReversible)
    (κ : Network.RateConstants N) {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ n₀ : S → ℝ, nf.1 = CRNT.toEuclid n₀ ∧
      N.ActiveWall n₀ ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  hwr.toricMassActionField_isStrictSupportField_of_activeWalls κ hfaces
-- A separating exposed-face wall of a polyhedral fan is active: the structural fan/separation data
-- discharges the per-wall `ActiveWall` obligation from geometry, with no hand-supplied activity.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S}
    {F : CRNT.Fan (EuclideanSpace ℝ S)} (hF : CRNT.IsPolyhedralFan F)
    {D C : ProperCone ℝ (EuclideanSpace ℝ S)} {n : S → ℝ} {c d : Complex S}
    (hwall : N.IsFanWall F D C n) (hsep : N.SeparatesComplexes n c d) : N.ActiveWall n :=
  hF.activeWall_of_separatesComplexes hwall hsep
-- The genuine toric field is a strict support field with the per-wall activity replaced by the
-- structural fan/separation hypothesis: strict support rests on the fan geometry alone.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : CRNT.Fan (EuclideanSpace ℝ S)} (hF : CRNT.IsPolyhedralFan F) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S))
      (c d : Complex S), nf.1 = CRNT.toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ N.SeparatesComplexes n₀ c d ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  hF.toricMassActionField_isStrictSupportField_of_separatingWalls hwr κ hfaces
-- The fully-structural deliverable: the genuine toric field is a strict support field from the
-- polyhedral-fan geometry and weak reversibility alone. Each wall is a fan exposed-face wall carrying
-- a strictly-inward reaction (its non-triviality); the separation witness is that reaction's
-- mutually-reachable endpoints, so no `SeparatesComplexes` hypothesis is supplied by hand.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : CRNT.Fan (EuclideanSpace ℝ S)} (hF : CRNT.IsPolyhedralFan F) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S)) (r : N.R),
      nf.1 = CRNT.toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ 0 < ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  hF.toricMassActionField_isStrictSupportField_of_fan hwr κ hfaces
-- Face-properness alone drives the toric strict-support verdict: each wall is a fan exposed-face wall
-- whose cone `D` is a proper subcone (`D ⊊ C`) of its reaction-generated ambient cone, and the
-- strictly-inward reaction is extracted from that properness rather than supplied by hand.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : CRNT.Fan (EuclideanSpace ℝ S)} (hF : CRNT.IsPolyhedralFan F) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S)),
      nf.1 = CRNT.toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧ N.GeneratedByReactions C ∧
      (D : Set (EuclideanSpace ℝ S)) ⊂ (C : Set (EuclideanSpace ℝ S)) ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  hF.toricMassActionField_isStrictSupportField_of_properFan hwr κ hfaces

-- A polyhedral, reaction-generated fan supplies the per-wall `GeneratedByReactions` clause from fan
-- membership: each wall's ambient cone is a cone of the fan, hence reaction-generated. The per-wall
-- input shrinks to fan-wall data, face-properness (`D ⊊ C`), cone-nonnegativity, and boundary
-- positivity, with cone generation proved from the fan rather than asserted per wall.
open scoped InnerProductSpace in
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (hwr : N.WeaklyReversible)
    {F : CRNT.Fan (EuclideanSpace ℝ S)} (hF : CRNT.IsPolyhedralFan F)
    (hgen : N.ReactionGeneratedFan F) (κ : Network.RateConstants N)
    {faces : List (EuclideanSpace ℝ S × ℝ)}
    (hfaces : ∀ nf ∈ faces, ∃ (n₀ : S → ℝ) (D C : ProperCone ℝ (EuclideanSpace ℝ S)),
      nf.1 = CRNT.toEuclid n₀ ∧
      N.IsFanWall F D C n₀ ∧
      (D : Set (EuclideanSpace ℝ S)) ⊂ (C : Set (EuclideanSpace ℝ S)) ∧
      (∀ r : N.R, 0 ≤ ⟪CRNT.toEuclid n₀, CRNT.toEuclid (N.reactionVector r)⟫_ℝ) ∧
      (∀ p : EuclideanSpace ℝ S,
        CRNT.ZeroSeparatingCurve2D.OnFaceBoundary faces (CRNT.toEuclid n₀) nf.2 p →
          Concentration.Positive (CRNT.toEuclid.symm p))) :
    CRNT.ZeroSeparatingCurve2D.IsStrictSupportField (N.toricMassActionField κ) faces :=
  hF.toricMassActionField_isStrictSupportField_of_reactionFan hwr hgen κ hfaces

-- The reaction directions of a network generate a genuine `ProperCone` — the reaction hull cone —
-- whose carrier is the conical hull of the reaction directions, and which is reaction-generated by
-- reflexivity. The singleton reaction fan is reaction-generated, so the strict-support deliverable
-- over the reaction fan supplies the `GeneratedByReactions` clause from the geometry rather than
-- carrying it as an unproven datum.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    (N.reactionHullCone : Set (EuclideanSpace ℝ S))
        = (PointedCone.hull ℝ
            (Set.range (fun r : N.R => CRNT.toEuclid (N.reactionVector r))) :
          Set (EuclideanSpace ℝ S)) ∧
      N.GeneratedByReactions N.reactionHullCone ∧
      N.ReactionGeneratedFan N.reactionFan :=
  ⟨N.coe_reactionHullCone, N.generatedByReactions_reactionHullCone,
    N.reactionGeneratedFan_reactionFan⟩

-- Deterministic skeleton of the Kurtz fluid limit: the limiting reaction-rate ODE
-- `ẋ = F(x)` admits a local solution from every start (Picard–Lindelöf via the C¹
-- mass-action field), instantiated on the reversible pair `A ⇌ B`.
example (κ : Network.RateConstants Examples.ReversiblePair.N)
    (x₀ : Concentration Examples.ReversiblePair.Species) (t₀ : ℝ) :
    ∃ x : ℝ → Concentration Examples.ReversiblePair.Species, x t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt x (Examples.ReversiblePair.N.massActionVectorField κ (x t)) t :=
  Examples.ReversiblePair.exists_fluidODE_local_reversiblePair κ x₀ t₀

-- The mass-action field is locally Lipschitz: on a convex region where its Fréchet
-- derivative is bounded by `K`, it is `K`-Lipschitz — the uniqueness input for the
-- limiting ODE.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {s : Set (Concentration S)} (hs : Convex ℝ s) {K : ℝ≥0}
    (hK : ∀ x ∈ s, ‖fderiv ℝ (N.massActionVectorField κ) x‖₊ ≤ K) :
    LipschitzOnWith K (N.massActionVectorField κ) s :=
  N.massActionVectorField_lipschitzOnWith_of_fderiv_le κ hs hK

-- Conditional Grönwall fluid limit: a scaled trajectory `X` whose drift matches the
-- deterministic field up to a fluctuation residual `η` stays within the Grönwall
-- envelope of the ODE solution `x`. The residual `η` is the isolated probabilistic
-- (martingale/Poisson) hypothesis.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : Network.RateConstants N)
    {r : Set (Concentration S)} {K : ℝ≥0}
    (hK : LipschitzOnWith K (N.massActionVectorField κ) r)
    {x X X' : ℝ → Concentration S} {a b δ η : ℝ}
    (hx : ContinuousOn x (Set.Icc a b))
    (hx' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Ici t) t)
    (hxr : ∀ t ∈ Set.Ico a b, x t ∈ r)
    (hX : ContinuousOn X (Set.Icc a b))
    (hX' : ∀ t ∈ Set.Ico a b, HasDerivWithinAt X (X' t) (Set.Ici t) t)
    (hXr : ∀ t ∈ Set.Ico a b, X t ∈ r)
    (hfluct : ∀ t ∈ Set.Ico a b, dist (X' t) (N.massActionVectorField κ (X t)) ≤ η)
    (ha : dist (X a) (x a) ≤ δ) :
    ∀ t ∈ Set.Icc a b, dist (X t) (x t) ≤ gronwallBound δ K (η + 0) (t - a) :=
  N.fluidLimit_dist_le κ hK hx hx' hxr hX hX' hXr hfluct ha

-- Regular-value topological degree existence principle: a nonzero regular degree forces
-- the value to be attained. On the identity map of a finite-dimensional real space the
-- derivative is everywhere the identity (determinant `1 > 0`), so the degree at any value
-- is `1`, and the existence principle recovers a preimage.
example (y : EuclideanSpace ℝ (Fin 3)) :
    regularDegree (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) y
      (finite_preimage_id y) = 1 :=
  regularDegree_id y

example (y : EuclideanSpace ℝ (Fin 3)) :
    (id ⁻¹' {y} : Set (EuclideanSpace ℝ (Fin 3))).Nonempty :=
  preimage_nonempty_of_regularDegree_ne_zero (id : EuclideanSpace ℝ (Fin 3) → _) y
    (finite_preimage_id y) (by rw [regularDegree_id]; norm_num)
-- Transversal first-crossing time: from a Poincaré section whose flow crosses transversally
-- at a base state, the crossing time `τ(x)` makes the flow line of every nearby `x` meet the
-- section (the implicit-function content underlying the first-return map).
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Sec : CRNT.TransversalSection (E := E)) :
    ∀ᶠ x in nhds Sec.base, Sec.sectionCoord x (Sec.crossingTime x) = 0 :=
  Sec.crossingTime_isCrossing

-- The crossing time emerges from the known crossing: `τ(x) → time` as `x → base`. With the
-- strict Fréchet derivative this is the C¹ dependence of the first-crossing time on the state.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Sec : CRNT.TransversalSection (E := E)) :
    Filter.Tendsto Sec.crossingTime (nhds Sec.base) (nhds Sec.time) :=
  Sec.crossingTime_tendsto
-- Discharge step of the fluctuation residual: with total intensity `r = V · a`, a single
-- volume-scaled Poisson count has variance `a / V`, the `O(1/V)` decay that sends the
-- martingale/Poisson fluctuation to zero as the volume grows.
example (a : ℝ≥0) {V : ℝ} (hV : 0 < V) :
    ProbabilityTheory.variance (fun n : ℕ => (n : ℝ) / V)
      (ProbabilityTheory.poissonMeasure (⟨V, hV.le⟩ * a)) = (a : ℝ) / V :=
  CRNT.Stochastic.variance_scaled_intensity_poissonMeasure hV a

-- Aggregate multi-reaction fluctuation: for a finite family of pairwise independent scaled
-- clocks with per-term variance `c r / V`, the total scaled fluctuation `∑_r X r` has the
-- aggregate `O(1/V)` variance `(∑_r c r) / V` with constant `C = ∑_r c r`.
example {R : Type} [Fintype R] {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {X : R → Ω → ℝ} {c : R → ℝ} {V : ℝ}
    (hmem : ∀ r, MeasureTheory.MemLp (X r) 2 μ)
    (hindep : Pairwise fun r s => ProbabilityTheory.IndepFun (X r) (X s) μ)
    (hvar : ∀ r, ProbabilityTheory.variance (X r) μ = c r / V) :
    ProbabilityTheory.variance (∑ r, X r) μ = (∑ r, c r) / V :=
  CRNT.Stochastic.variance_aggregate hmem hindep hvar

-- The concrete independent Poisson clock family discharges the carried hypotheses: on the product
-- law `⊗_r Po(V · a_r)`, the total weighted scaled count `∑_r weight_r · (N_r / V)` has the
-- self-contained aggregate `O(1/V)` variance `(∑_r weight_r² · a_r) / V`.
example {R : Type} [Fintype R] (a : R → ℝ≥0) (weight : R → ℝ) {V : ℝ} (hV : 0 < V) :
    ProbabilityTheory.variance (∑ r, CRNT.Stochastic.scaledClock weight V r)
        (CRNT.Stochastic.clockMeasure hV a)
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V :=
  CRNT.Stochastic.variance_aggregate_scaledClock hV a weight

-- Time-changed fluctuation at a deterministic integrated intensity `Λ_r = V · A_r` along the limit
-- trajectory: the total centered, volume-scaled, weighted increment `∑_r M_r` has the self-contained
-- aggregate `O(1/V)` variance `(∑_r weight_r² · A_r) / V`, the compensated form of the scaled clocks.
example {R : Type} [Fintype R] (A : R → ℝ≥0) (weight : R → ℝ) {V : ℝ} (hV : 0 < V) :
    ProbabilityTheory.variance (∑ r, CRNT.Stochastic.centeredTimeChange weight V A r)
        (CRNT.Stochastic.clockMeasure hV A)
      = (∑ r, weight r ^ 2 * (A r : ℝ)) / V :=
  CRNT.Stochastic.variance_aggregate_centeredTimeChange hV A weight

-- The degree of an invertible continuous linear map is the orientation sign of its
-- determinant: the preimage is a single point and the derivative is the map itself.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hdet : LinearMap.det T.toLinearMap ≠ 0) (y : E) :
    regularDegree (⇑T) y (finite_preimage_of_det_ne_zero T hdet y) =
      ((SignType.sign (LinearMap.det T.toLinearMap) : SignType) : ℤ) :=
  regularDegree_continuousLinearMap T hdet y

-- The orientation-reversing case: the negation `-id` of `EuclideanSpace ℝ (Fin 1)`
-- reflects the single coordinate (determinant `-1`), so its regular degree is `-1`.
example (y : EuclideanSpace ℝ (Fin 1)) :
    regularDegree (⇑(-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))) y
      (finite_preimage_of_det_ne_zero _ det_neg_id_fin_one_ne_zero y) = -1 :=
  regularDegree_neg_id_eq_neg_one y

-- Poincaré first-return map: the return map `P(x) = Φ x (τ x)` lands every nearby state back on
-- the transversal section, and the base returns to the section's seed point — the fixed-point
-- compatibility whose orbit is the periodic solution the Hopf rotation-closure step needs.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Sec : CRNT.TransversalSection (E := E)) :
    Sec.returnMap Sec.base = Sec.point :=
  Sec.returnMap_base
-- Rotation closure: a fixed point `Φ x T = x` of the return map (a genuine return) closes the flow
-- line of `x` into a periodic orbit of period the crossing time — the orbit-from-fixed-point bridge.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Sec : CRNT.TransversalSection (E := E)) {x : E}
    (hsemi : ∀ a b : ℝ, Sec.flow x (a + b) = Sec.flow (Sec.flow x a) b)
    (hfix : Sec.returnMap x = x) :
    Function.Periodic (Sec.flow x) (Sec.crossingTime x) :=
  Sec.isPeriodic_returnMap_fixedPoint hsemi hfix
-- Excision of a region with no solutions: a region disjoint from the preimage contributes
-- nothing to the degree. The empty region around any value of `f` carries local degree `0`.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) :
    localDegree f y hfin (∅ : Set E) = 0 :=
  localDegree_eq_zero_of_preimage_inter_empty f y hfin (Set.inter_empty _)

-- Additivity: the local degree over the whole space recovers the global regular degree —
-- the trivial one-region cover. Splitting the preimage into local pieces is exact.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (y : E)
    (hfin : (f ⁻¹' {y}).Finite) :
    localDegree f y hfin Set.univ = regularDegree f y hfin :=
  localDegree_univ f y hfin

-- The C¹ first-return map: the Poincaré return map `P(x) = Φ x (τ x)` is Fréchet differentiable
-- at the base, its derivative the joint flow derivative composed with the state-and-crossing-time
-- pairing — the differentiable Poincaré map whose derivative spectrum closes the Hopf step.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Sec : CRNT.TransversalSection (E := E)) :
    HasFDerivAt Sec.returnMap
      ((Sec.jointFlowDeriv Sec.base Sec.time).comp
        ((ContinuousLinearMap.id ℝ E).prod
          (-(ContinuousLinearMap.toSpanSingleton ℝ
              (inner ℝ (Sec.field Sec.point) Sec.normal)).inverse ∘L
            Sec.spaceCoordDeriv Sec.base Sec.time)))
      Sec.base :=
  Sec.hasFDerivAt_returnMap
-- Local constancy of the degree in the value: near a nondegenerate preimage point `x₀` of a
-- C¹ map, for every value `y` in a neighbourhood of `f x₀` the local degree on the
-- inverse-function neighbourhood is the constant orientation sign `sign (det (Df x₀))`. This
-- is the analytic heart of Brouwer-degree well-definedness on a connected set of regular values.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (f : E → E) {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    (hdet : LinearMap.det (fderiv ℝ f x₀).toLinearMap ≠ 0) :
    ∀ᶠ y in nhds (f x₀),
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        localDegree f y hfin
            ((hasStrictFDerivAt_fderivEquiv f hf hdet).toOpenPartialHomeomorph f).source =
          ((SignType.sign (LinearMap.det (fderiv ℝ f x₀).toLinearMap) : SignType) : ℤ) :=
  eventually_localDegree_eq f hf hdet

-- Composition multiplicativity (linear case): the degree of a composite of invertible
-- continuous linear maps is the product of the degrees, `sign (det (T ∘ U))
-- = sign (det T) · sign (det U)`, the linear shadow of the chain rule for the Jacobian.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T U : E →L[ℝ] E) (hT : LinearMap.det T.toLinearMap ≠ 0)
    (hU : LinearMap.det U.toLinearMap ≠ 0) (y : E) :
    regularDegree (⇑(T.comp U)) y
        (finite_preimage_of_det_ne_zero (T.comp U)
          (by rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
              exact mul_ne_zero hT hU) y) =
      regularDegree (⇑T) y (finite_preimage_of_det_ne_zero T hT y) *
        regularDegree (⇑U) y (finite_preimage_of_det_ne_zero U hU y) :=
  regularDegree_comp_continuousLinearMap T U hT hU y

-- A simplicial cone is closed: the nonnegative span of the two standard basis vectors of `Fin 2 → ℝ`
-- — a linearly independent family — is a closed set, the first case of finitely-generated cones being
-- closed.
example : IsClosed (CRNT.nonnegSpan (Pi.basisFun ℝ (Fin 2))) :=
  CRNT.isClosed_nonnegSpan_of_linearIndependent _ (Pi.basisFun ℝ (Fin 2)).linearIndependent
-- Global local constancy of the regular degree in the value: for a regular value `y₀` of a
-- C¹ map with finite nondegenerate preimage, and assuming solutions stay confined to the
-- inverse-function neighbourhoods near `y₀`, the regular degree at nearby values is the
-- constant `∑ x ∈ f⁻¹{y₀}, sign (det (Df x))`. This is the well-definedness backbone of the
-- Brouwer degree on a connected set of regular values.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (f : E → E) {y₀ : E} (hf : ∀ x ∈ f ⁻¹' {y₀}, ContDiffAt ℝ 1 f x)
    (hdet : ∀ x ∈ f ⁻¹' {y₀}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (hfin₀ : (f ⁻¹' {y₀}).Finite)
    (hconf : ∀ᶠ y in nhds y₀, f ⁻¹' {y} ⊆
      ⋃ x : (f ⁻¹' {y₀} : Set E),
        ((hasStrictFDerivAt_fderivEquiv f (hf x x.2) (hdet x x.2)).toOpenPartialHomeomorph
          f).source) :
    ∀ᶠ y in nhds y₀,
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        regularDegree f y hfin =
          ∑ x ∈ hfin₀.toFinset,
            ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) :=
  eventually_regularDegree_eq f hf hdet hfin₀ hconf
-- Continuous-time non-constant moving-target Fenichel mapping property: for EVERY time `t` and
-- EVERY candidate section `h`, the time-`t` product semiflow over a base injective at every time
-- carries the graph of `h` into the graph of the time-`t` moving target `movingRegraphAt`. The
-- genuinely non-constant moving-target mapping property along the whole forward semiflow, with the
-- "only at multiples of τ" restriction removed.
example {Y E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : ODE.AllTimeInjectiveBaseFlow Y) (rate : ℝ) (c : E) (t : ℝ≥0) (h : Y → E) :
    Set.MapsTo ((ODE.productContractFlow B.slowFlow rate c).toFun t) (ODE.graphSet h)
      (ODE.graphSet (ODE.movingRegraphAt B rate c t h)) :=
  ODE.movingFlowAt_mapsTo B rate c t h

-- Confinement is automatic for a proper map: at a regular value `y₀` of a proper C¹ map the
-- regular degree at nearby values is the constant `∑ x ∈ f⁻¹{y₀}, sign (det (Df x))`, with no
-- analytic side condition carried. Solutions cannot escape to infinity because the preimage of a
-- compact neighbourhood of `y₀` is compact.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (f : E → E) (hfp : IsProperMap f) {y₀ : E}
    (hf : ∀ x ∈ f ⁻¹' {y₀}, ContDiffAt ℝ 1 f x)
    (hdet : ∀ x ∈ f ⁻¹' {y₀}, LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (hfin₀ : (f ⁻¹' {y₀}).Finite) :
    ∀ᶠ y in nhds y₀,
      ∀ (hfin : (f ⁻¹' {y}).Finite),
        regularDegree f y hfin =
          ∑ x ∈ hfin₀.toFinset,
            ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) :=
  eventually_regularDegree_eq_of_isProperMap f hfp hf hdet hfin₀
-- A genuinely non-constant slow manifold invariant at EVERY continuous time: over the affine base on
-- ℝ × ℝ with drift (1, 0), the second-coordinate section y ↦ y.2 is comoving and non-constant, and
-- its graph {((y₁, y₂), y₂)} is invariant under the full continuous product semiflow that contracts
-- onto the comoving section, for every t ≥ 0. The comoving property cancels the contraction's pull
-- along the moving base, so the manifold persists without collapsing to a constant fibre.
example (rate : ℝ) :
    IsInvariant
      (ODE.comovingContractFlow (ODE.affineAllTimeBase ((1, 0) : ℝ × ℝ)) rate (fun y : ℝ × ℝ => y.2)
        ODE.continuous_snd_section).toFun
      (ODE.graphSet (fun y : ℝ × ℝ => y.2)) :=
  ODE.affineComovingManifold_isInvariant rate

-- A finitely-generated cone is closed without any independence hypothesis: the conical hull of the
-- three vectors `(1,0)`, `(0,1)`, `(1,1)` in `Fin 2 → ℝ` — a linearly dependent family — is closed.
example :
    IsClosed (PointedCone.hull ℝ
      (({![1, 0], ![0, 1], ![1, 1]} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) :
      Set (Fin 2 → ℝ)) :=
  CRNT.isClosed_coe_hull_of_finite _
-- Variational equation: along `[0, T]` the difference between the genuine flow separation
-- `y t - x t` and its linear prediction `h • W t` (the solution of the linear variational ODE
-- `Ẇ = Df (x t) · W`, `W 0 = v`) is controlled by Grönwall's growth function, with the driving
-- term linear in `|h|` and vanishing with the `Df`-modulus `ρ`. The analytic core of smooth
-- dependence of an ODE flow on its initial condition.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x y W : ℝ → E} {v : E} {h K ρ T : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hx : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t)
    (hW : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt W ((fderiv ℝ f (x t)) (W t)) t)
    (hxc : ContinuousOn x (Set.Icc 0 T)) (hyc : ContinuousOn y (Set.Icc 0 T))
    (hWc : ContinuousOn W (Set.Icc 0 T))
    (hDfK : ∀ t ∈ Set.Ico (0 : ℝ) T, ‖fderiv ℝ f (x t)‖ ≤ K)
    (hmod : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ‖f (y t) - f (x t) - (fderiv ℝ f (x t)) (y t - x t)‖ ≤ ρ * ‖y t - x t‖)
    (hsep : ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t - x t‖ ≤ |h| * ‖v‖ * Real.exp (K * t))
    (h0 : (y 0 - x 0) - h • W 0 = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖(y t - x t) - h • W t‖ ≤ gronwallBound 0 K (ρ * (|h| * ‖v‖ * Real.exp (K * T))) t :=
  ODE.norm_flow_variational_error_le (v := v) hK hρ hx hy hW hxc hyc hWc hDfK hmod hsep h0
-- Fenichel reduction principle, equilibrium lift: over the stationary affine base (drift 0) on
-- ℝ × ℝ every base point y₀ is an equilibrium of the slow flow, so its lift incl σ y₀ = (y₀, σ y₀)
-- is an equilibrium of the full comoving-contract flow at every time t ≥ 0. The reduction conjugacy
-- transports the base steady state up to the slow manifold.
example (rate : ℝ) (y₀ : ℝ × ℝ) (t : ℝ≥0) :
    (ODE.comovingContractFlow (ODE.affineAllTimeBase ((0, 0) : ℝ × ℝ)) rate (fun y : ℝ × ℝ => y.2)
          ODE.continuous_snd_section).toFun t (ODE.incl (fun y : ℝ × ℝ => y.2) y₀)
      = ODE.incl (fun y : ℝ × ℝ => y.2) y₀ :=
  ODE.equilibrium_lift_of_baseEquilibrium (ODE.affineAllTimeBase ((0, 0) : ℝ × ℝ)) rate
    (fun y : ℝ × ℝ => y.2) ODE.continuous_snd_section
    (fun t => by
      rw [ODE.affineAllTimeBase_slowFlow, ODE.affineBaseFlow_toFun]; simp) t

-- Homotopy invariance of the regular-value degree on the constant homotopy `H(s, x) = x`: every
-- slice is the identity, with single-point preimage `{y}`, and the degree at `y` agrees at the
-- endpoint slices `H(0, ·)` and `H(1, ·)`. The parameter local-constancy data is the trivial
-- one-piece cover by the whole space, whose local degree is the orientation sign `+1` of the
-- identity's derivative.
set_option linter.unnecessarySimpa false in
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (y : E) :
    regularDegree (fun x => (fun p : ℝ × E => p.2) (0, x)) y (by simpa using finite_preimage_id y) =
      regularDegree (fun x => (fun p : ℝ × E => p.2) (1, x)) y
        (by simpa using finite_preimage_id y) := by
  refine regularDegree_homotopy_invariant (fun p : ℝ × E => p.2) y
    (fun s _ => by simpa using finite_preimage_id y) ?_
  intro s₀ _ hfin₀
  refine Filter.Eventually.of_forall (fun s => ?_)
  refine ⟨by simpa using finite_preimage_id y, fun _ => Set.univ, ?_, ?_, ?_⟩
  · intro z _
    exact Set.mem_iUnion.2 ⟨⟨y, by simp⟩, Set.mem_univ z⟩
  · intro a b hab z _ _
    apply hab; apply Subtype.ext
    have ha : (a : E) = y := Set.mem_singleton_iff.mp (by simpa using a.2)
    have hb : (b : E) = y := Set.mem_singleton_iff.mp (by simpa using b.2)
    rw [ha, hb]
  · intro x
    rw [localDegree_univ]
    have hrd : regularDegree (fun x => (fun p : ℝ × E => p.2) (s, x)) y
        (by simpa using finite_preimage_id y) = 1 := regularDegree_id y
    rw [hrd]
    show (1 : ℤ) = ((SignType.sign (LinearMap.det (fderiv ℝ (id : E → E) (x : E)).toLinearMap)
      : SignType) : ℤ)
    rw [fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id, sign_one]
    rfl

-- Differentiability of the flow in its initial condition (fixed direction): the time-`t` flow
-- `h ↦ Φ (x₀ + h • v) t`, packaged as the family `Y` with `Y 0 = x`, has derivative the
-- variational solution `W t` at `h = 0`, extracted from the Grönwall variational error bound as
-- the modulus `ρ h → 0`. The `→ 0` directional-derivative limit underlying smooth dependence on
-- initial conditions.
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x W : ℝ → E} {v : E} {K T t : ℝ} {ρ : ℝ → ℝ}
    (hK : 0 ≤ K) (ht : t ∈ Set.Icc (0 : ℝ) T)
    {Y : ℝ → ℝ → E} (hY0 : Y 0 = x)
    (hρ0 : ∀ h, 0 ≤ ρ h) (hρlim : Filter.Tendsto ρ (nhdsWithin 0 {0}ᶜ) (nhds 0))
    (herr : ∀ h, ‖(Y h t - x t) - h • W t‖ ≤
      gronwallBound 0 K (ρ h * (|h| * ‖v‖ * Real.exp (K * T))) t) :
    HasDerivAt (fun h => Y h t) (W t) 0 :=
  ODE.hasDerivAt_flow_initial (v := v) hK ht hY0 hρ0 hρlim herr

-- The computable terminal-strong-linkage-class count agrees with the cardinality definition and
-- reduces by `decide` on a concrete network: the reversible pair `A ⇌ B` is a single terminal
-- strong linkage class.
example : interopRevData.toNetwork.computeNumTerminalSLC = 1 := by decide
example (N : Network (Fin 2)) : N.computeNumTerminalSLC = N.numTerminalSLC :=
  N.computeNumTerminalSLC_eq_numTerminalSLC

-- The diagonal-drive species count equals the species count exactly when every species is
-- positively driven (`ConsistentDiagonalDrive`); the reversible pair `A ⇌ B` has no positively
-- self-driven species, so the count is 0.
example : interopRevData.toNetwork.numDiagonalDriveSpecies = 0 := by decide
example (N : Network (Fin 2)) :
    N.numDiagonalDriveSpecies = Fintype.card (Fin 2) ↔ N.ConsistentDiagonalDrive :=
  N.numDiagonalDriveSpecies_eq_card_iff

-- The rational Hopf-boundary scalar casts to the real Routh–Hurwitz Hopf-boundary combination
-- `det − trace · c₂Fin3` of the cast matrix.
example (M : Matrix (Fin 3) (Fin 3) ℚ) :
    ((hopfBoundaryQ M : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)).det - (M.map (Rat.castHom ℝ)).trace
          * (M.map (Rat.castHom ℝ)).c₂Fin3 :=
  hopfBoundaryQ_cast M

-- The real cast of the Gershgorin row value is the row value of the cast matrix.
example (M : Matrix (Fin 2) (Fin 2) ℚ) (k : Fin 2) :
    ((gershgorinRowValueQ M k : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)) k k
        + ∑ j ∈ Finset.univ.erase k, |(M.map (Rat.castHom ℝ)) k j| :=
  gershgorinRowValueQ_cast M k

-- The Gershgorin margin is negative exactly when every Gershgorin row value is negative — the strict
-- row diagonal-dominance Hurwitz condition.
example (M : Matrix (Fin 2) (Fin 2) ℚ) :
    gershgorinMarginQ M < 0 ↔ ∀ k, gershgorinRowValueQ M k < 0 :=
  gershgorinMarginQ_neg_iff M

-- The real cast of the Gershgorin column value is the column value of the cast matrix.
example (M : Matrix (Fin 2) (Fin 2) ℚ) (k : Fin 2) :
    ((gershgorinColValueQ M k : ℚ) : ℝ)
      = (M.map (Rat.castHom ℝ)) k k
        + ∑ i ∈ Finset.univ.erase k, |(M.map (Rat.castHom ℝ)) i k| :=
  gershgorinColValueQ_cast M k

-- The column-form Gershgorin margin is negative exactly when every Gershgorin column value is
-- negative — the strict column diagonal-dominance Hurwitz condition.
example (M : Matrix (Fin 2) (Fin 2) ℚ) :
    gershgorinColMarginQ M < 0 ↔ ∀ k, gershgorinColValueQ M k < 0 :=
  gershgorinColMarginQ_neg_iff M

-- The reversible pair `A ⇌ B` yields a Gershgorin stability margin: the field is non-vacuous for a
-- network with species.
example : interopRevData.analyze.gershgorinStabilityMargin.isSome = true := by decide

-- The Gershgorin stability-margin field is `none` exactly for a network with no species.
example (d : NetworkData) (h : d.numSpecies = 0) :
    d.analyze.gershgorinStabilityMargin = none :=
  NetworkData.analyze_gershgorinStabilityMargin_eq_none_of_zero_species d h

-- The reversible pair `A ⇌ B` yields a column-form Gershgorin stability margin: the field is
-- non-vacuous for a network with species.
example : interopRevData.analyze.gershgorinColStabilityMargin.isSome = true := by decide

-- The column-form Gershgorin stability-margin field is `none` exactly for a network with no species.
example (d : NetworkData) (h : d.numSpecies = 0) :
    d.analyze.gershgorinColStabilityMargin = none :=
  NetworkData.analyze_gershgorinColStabilityMargin_eq_none_of_zero_species d h

/-! ## The newest modules, exercised on the library API -/

-- Hopf averaging: the radial drift of the averaged field is the cubic normal form.
example (α ω : ℝ) (c₁ : ℂ) (R : ℝ) :
    CRNT.Hopf.radialDrift (fun w => (↑α + ↑ω * Complex.I) * w + c₁ * w * ↑(Complex.normSq w)) R
      = α * R + c₁.re * R ^ 3 :=
  CRNT.Hopf.radialDrift_normalForm α ω c₁ R

-- The Poincaré–Dulac normal form to cubic order: the quadratic jet at the critical point.
example (lam a b : ℂ) (hlam : lam ≠ 0) (w : ℂ) :
    CRNT.Hopf.quadJet lam a b (-a / lam) w
      = lam * w + CRNT.Hopf.e3 lam a b * w ^ 3 + CRNT.Hopf.e4 lam a b * w ^ 4
        + CRNT.Hopf.e5 lam a b * w ^ 5 :=
  CRNT.Hopf.cubic_normal_form hlam w

-- The Lyapunov calibration: the cubic combination of the planar partials is `16·c₂₁`.
example (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    (CRNT.Hopf.planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxxx
      + (CRNT.Hopf.planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxyy
      + (CRNT.Hopf.planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gxxy
      + (CRNT.Hopf.planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gyyy
      = 16 * c21.re :=
  CRNT.Hopf.cubicCombination_eq q20 q11 q02 c30 c21 c12 c03

-- Hirsch generic convergence: a strongly monotone flow with a convex ω-limit set converges.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S]
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ Filter.atTop, closure (Set.image2 ϕ.toFun v {x₀}) ⊆ K)
    (hmonoV : ∀ (s t : ℝ≥0), s ≤ t → V (ϕ.toFun t x₀) ≤ V (ϕ.toFun s x₀))
    (hVcrit : ∀ y ∈ K, (∀ (t : ℝ≥0), V (ϕ.toFun t y) = V y) → f y = 0)
    (hc : ℝ) (hsm : CRNT.OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc)
    (hωoc : ∀ (a b z : Concentration S),
      a ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} →
        b ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} → a ≤ z → z ≤ b →
        z ∈ omegaLimit Filter.atTop ϕ.toFun {x₀})
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ) :
    ∃ xstar, f xstar = 0 ∧
      Filter.Tendsto (fun t => ϕ.toFun t x₀) Filter.atTop (nhds xstar) :=
  CRNT.converges_of_lasalle_of_stronglyMonotoneOperator ϕ f V hV x₀ K hK habs hmonoV hVcrit hc hsm hcpos hωoc hmonFlow

-- The mass-action instance of the Hirsch theorem.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {c : ℝ} (hc : 0 < c) (hsm : CRNT.OrderPreservingStronglyMonotoneOperator (N.massActionVectorField κ) c)
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ Filter.atTop, closure (Set.image2 ϕ.toFun v {x₀}) ⊆ K)
    (hmonoV : ∀ (s t : ℝ≥0), s ≤ t → V (ϕ.toFun t x₀) ≤ V (ϕ.toFun s x₀))
    (hVcrit : ∀ y ∈ K, (∀ (t : ℝ≥0), V (ϕ.toFun t y) = V y) → f y = 0)
    (hωoc : ∀ (a b z : Concentration S),
      a ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} →
        b ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} → a ≤ z → z ≤ b →
        z ∈ omegaLimit Filter.atTop ϕ.toFun {x₀})
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ) (hf : f = N.massActionVectorField κ) :
    ∃ xstar, N.massActionVectorField κ xstar = 0 ∧
      Filter.Tendsto (fun t => ϕ.toFun t x₀) Filter.atTop (nhds xstar) :=
  CRNT.massAction_converges_of_lasalle_of_stronglyMonotoneOperator N κ hc hsm ϕ f V hV x₀ K hK habs hmonoV hVcrit hωoc hmonFlow hf

-- Order convexity of the ω-limit set of a strongly monotone flow.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S]
    (f : Concentration S → Concentration S) (ϕ : Flow ℝ≥0 (Concentration S)) (hc : ℝ)
    (hsm : CRNT.OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ Filter.atTop, closure (Set.image2 ϕ.toFun v {x₀}) ⊆ K)
    (hΩE : ∀ y ∈ omegaLimit Filter.atTop ϕ.toFun {x₀}, f y = 0)
    (p q z : Concentration S) :
    p ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} →
      q ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} → p ≤ z → z ≤ q →
      z ∈ omegaLimit Filter.atTop ϕ.toFun {x₀} :=
  CRNT.omegaLimit_orderConvex_of_stronglyMonotoneOperator f ϕ hc hsm hcpos x₀ K hK habs hΩE p q z

-- Escape direction: a trajectory stays in the orthogonal complement of the conservation laws.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ (τ : ℝ), 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    x t - x 0 ∈ CRNT.orthSum N.conservationLawSpace :=
  N.escape_in_orthogonalComplement κ ht hsol

-- Tikhonov: a Hurwitz linear part decays exponentially.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →L[ℝ] E} {μ : ℝ}
    (hA : CRNT.HurwitzRate A μ) (hμ : 0 < μ) {z : ℝ → E}
    (hz : ∀ (t : ℝ), HasDerivAt z (A (z t)) t) (t : ℝ) :
    0 ≤ t → ‖z t‖ ≤ Real.exp (-μ * t) * ‖z 0‖ :=
  CRNT.hurwitz_linear_decay hA hμ hz t

-- Exit mass: the exit mass factors through the one-step kernel stopped outside the set.
example {α : Type} [DecidableEq α] (J : CRNT.JumpSystem α) (K : Finset α) (c : α)
    {h₁ h₂ : ℝ} (ht₁ : 0 ≤ h₁) (ht₂ : 0 ≤ h₂) :
    J.exitMass K c (h₁ + h₂) = ∑' (c' : α), (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂ :=
  J.exitMass_factor K c ht₁ ht₂

-- The ENN-valued counterpart: the mass outside the set factors the same way.
example {α : Type} [DecidableEq α] (J : CRNT.JumpSystem α) (K : Finset α) (c : α)
    {h₁ h₂ : ℝ} (ht₁ : 0 ≤ h₁) (ht₂ : 0 ≤ h₂) :
    J.outsideMassENN K c (h₁ + h₂) =
      ∑' (c' : α), ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ :=
  J.outsideMassENN_factor K c ht₁ ht₂

-- Endotactic positive recurrence: an endotactic network with a linear Lyapunov function has a
-- stationary law and converges to it geometrically.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (d : N.LinearLyapunovData κ) (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ,
      (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s, 0 ≤ s → ∀ b, ∑' (x : S → ℕ), π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
          ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
            ∑' (b : S → ℕ),
              |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * CRNT.Network.linearObservable d.w b) ≤
                C₀ * (1 + CRNT.Network.linearObservable d.w a) * ρ ^ ⌊t⌋₊ :=
  CRNT.Network.positiveRecurrence_of_linearLyapunovData N κ d hirr

-- The Foster hitting-time estimate that feeds the recurrence statement.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (d : N.LinearLyapunovData κ) [DecidablePred fun x => x ∈ d.C] (x : S → ℕ) :
    (∀ m, ∑ k ∈ Finset.range m, (N.jumpChain κ).survival d.C k x ≤
        1 + (N.jumpChain κ).expect (CRNT.Network.linearObservable d.w) x / d.εJ) ∧
      Filter.Tendsto (fun m => (N.jumpChain κ).survival d.C m x) Filter.atTop (nhds 0) :=
  CRNT.Network.foster_hitting_time_of_linearLyapunovData N κ d x

-- Tier-wise positive recurrence: a tier balance gives a stationary law with full support.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (T : N.CountTier) (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ,
      (∀ b : S → ℕ, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s : ℝ, 0 ≤ s → ∀ b : S → ℕ,
          ∑' (x : S → ℕ), π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
          (∀ b : S → ℕ, 0 < π b) ∧
            ∀ a : S → ℕ, Filter.Tendsto (fun t => N.transition κ t a a) Filter.atTop (nhds (π a)) :=
  CRNT.Network.tier_positiveRecurrence N κ T hirr

-- Non-explosion of the tier-wise semigroup.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (T : N.CountTier) {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 :=
  CRNT.Network.tier_nonExplosion N κ T ht n

-- Geometric ergodicity of the tier-wise semigroup.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (T : N.CountTier) (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ,
      (∀ b : S → ℕ, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s : ℝ, 0 ≤ s → ∀ b : S → ℕ,
          ∑' (x : S → ℕ), π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
          ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a : S → ℕ, ∀ t : ℝ, 0 ≤ t →
            ∑' (b : S → ℕ),
              |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * N.CountLyapunov κ T b) ≤
                C₀ * (1 + N.CountLyapunov κ T a) * ρ ^ ⌊t⌋₊ :=
  CRNT.Network.tier_geometricErgodic N κ T hirr

-- The tier-balance hypothesis is a genuine drift condition: constant negative drift off a
-- finite set.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (B : N.CountTierBalance κ) :
    ∃ V : (S → ℕ) → ℝ,
      (∀ n : S → ℕ, 0 ≤ V n) ∧ (∀ R : ℝ, {n | V n ≤ R}.Finite) ∧
        ∃ C : Set (S → ℕ), C.Finite ∧ ∃ c : ℝ, 0 < c ∧
          ∀ n ∉ C, N.observableGenerator κ V n ≤ -c :=
  CRNT.Network.tierBalanceDrift_le_of N κ B

-- Tier-balanced networks are positively recurrent.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (B : N.CountTierBalance κ) (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ,
      (∀ b : S → ℕ, 0 ≤ π b) ∧ HasSum π 1 ∧
        (∀ s : ℝ, 0 ≤ s → ∀ b : S → ℕ,
          ∑' (x : S → ℕ), π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
          (∀ b : S → ℕ, 0 < π b) ∧
            ∀ a : S → ℕ, Filter.Tendsto (fun t => N.transition κ t a a) Filter.atTop (nhds (π a)) :=
  CRNT.Network.tierBalance_positiveRecurrence N κ B hirr

-- The tier-domination counterexample: the top tier does not dominate the escape count.
example (k : ℕ) (hk : 1 ≤ k) :
    CRNT.Network.countDescFactorial (CRNT.Examples.EndotacticCounterexample.net.reaction 3).source
        (CRNT.Examples.EndotacticCounterexample.escapeCount k) >
      CRNT.Network.countDescFactorial (CRNT.Examples.EndotacticCounterexample.net.reaction 1).source
        (CRNT.Examples.EndotacticCounterexample.escapeCount k) :=
  CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate k hk

-- The weak multivariate CLT for the open system.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xs : Concentration S} (heq : N.massActionVectorField κ xs = 0)
    (hxs0 : ∀ s : S, 0 ≤ xs s) {T : ℝ} (hT : 0 < T) (n : ℕ → S → ℕ)
    {z₀ : S → ℝ}
    (hz : Tendsto (fun k : ℕ => CRNT.Network.zeta ((k : ℝ) + 1) xs (n k)) atTop (nhds z₀)) :
    Tendsto
      (fun k : ℕ => N.flucLawOpenDefect κ (V := (k : ℝ) + 1) (by positivity) xs hT.le (n k))
      atTop (nhds (N.gaussLimit κ xs T z₀)) :=
  CRNT.Network.multivariate_clt_open_weak N κ heq hxs0 hT n hz

-- Uniform concentration of the fluctuation increments on the uniform time grid.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {T Rx δ : ℝ} (hT : 0 < T) (hRx : 0 ≤ Rx) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Set.Icc 0 T))
    (hx : ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc 0 fun _ => Rx) (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (nhds 0)) :
    ∃ m : ℕ, 0 < m ∧
      (∀ i < m, ∀ σ ∈ Set.Icc 0 (T / m),
        ∑ s, (x (i * (T / m) + σ) s - x (i * (T / m)) s) ^ 2 ≤ δ ^ 2 / 4) ∧
      (Tendsto (fun k : ℕ => ∑ i ∈ Finset.range m,
          N.windowExitMass κ (V := (k : ℝ) + 1) (by positivity) Rx δ (T / m) x i (n k))
        atTop (nhds 0)) ∧
      (∀ k : ℕ, ∀ i < m, ∀ c : S → ℕ, ∀ τ ∈ Set.Icc 0 (T / m),
        (∑' b, (if b ∈ CRNT.Network.ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).Pmin τ c b))
          ≤ (∑' b, (if b ∈ CRNT.Network.ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
              (CRNT.Network.ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin (T / m) c b))) :=
  CRNT.Network.fluctuation_uniform_concentration N κ hT hRx hδ hδ1 x hxc hx hxB n hn0

-- Degree existence: a nonzero degree on the nonnegative class forces a positive steady state.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x :=
  CRNT.Network.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero N κ x₀ hfin hdeg hbd

-- Degree structure: the class degree is the sign of the reduced Jacobian determinant.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y₀ : N.ClassCoord)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0) (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y : N.ClassCoord, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) :=
  CRNT.Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage N κ x₀ y₀ hzero hy₀ huniq hfin

-- A positive reduced determinant at the unique preimage forces a positive steady state.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y₀ : N.ClassCoord)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0) (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y : N.ClassCoord, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ y₀).det)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x :=
  CRNT.Network.exists_positiveSteadyState_of_positive_reducedDet N κ x₀ y₀ hzero hy₀ huniq hfin
    hdet hbd

-- Degree multistationarity: a negative local degree against the class degree gives two
-- distinct positive steady states.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (ystar : N.ClassCoord)
    (hzero : N.steadyStateMap κ x₀ ystar = 0) (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0)
    (hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        = -(N.nonnegativeClassDegree κ x₀ hfin))
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y :=
  CRNT.Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree N κ x₀ ystar hzero
    hystar hfin hdeg hlocal hbd

-- The deficiency-one algorithm decides the multistationarity capacity.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.HasMultistationarityCapacity ↔ N.DOAFeasible :=
  CRNT.Network.hasMultistationarityCapacity_iff_doaFeasible N

-- The one-reaction case is decided by an explicit inequality.
example {S : Type} [DecidableEq S] [Fintype S] (a b : Complex S) :
    (CRNT.Network.oneRxn a b).fullyOpen.DOAFeasible ↔ 1 < ∑ s with a s < b s, a s :=
  CRNT.Network.oneRxn_doaFeasible_iff a b

-- The advanced deficiency algorithm decides the multistationarity capacity too.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.HasMultistationarityCapacity ↔ N.ADAFeasible :=
  CRNT.Network.hasMultistationarityCapacity_iff_adaFeasible N

-- The advanced deficiency algorithm's verdict affirms the capacity.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (h : N.ADAFeasible) :
    N.ADAAffirmsCapacity :=
  CRNT.Network.adaFeasible_implies_adaAffirmsCapacity N h

-- The two-reaction atom criterion.
example {S : Type} [DecidableEq S] [Fintype S] (a b c d : Complex S) :
    CRNT.Network.TwoRxnIsAtom a b c d ↔
      (CRNT.Network.twoRxnOpen a b c d).fullyOpen.HasMultistationarityCapacity ∧
        ∑ s with a s < b s, a s ≤ 1 ∧ ∑ s with c s < d s, c s ≤ 1 :=
  CRNT.Network.twoRxnOpen_isAtom_iff a b c d

-- The multistationarity region is open.
example {S : Type} [DecidableEq S] [Fintype S] {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]
    (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] E₁ → ℝ) (L : (S → ℝ) →ₗ[ℝ] E₂ → ℝ)
    (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0)
    (hL : ∀ v : S → ℝ, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) :
    IsOpen (N.MultistationarityRegion Z L) :=
  CRNT.Network.isOpen_multistationarityRegion N Z L hZ hL hcard

-- SingletonSource networks: the steady-state condition is a linear one.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (hM : N.SingletonSource) (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔ ∀ s : S, ∑ i, N.singletonSourceCoeff κ i s * x i = 0 :=
  CRNT.Network.singletonSource_steadyState_iff_linear N κ hM x

-- SingletonSource networks: there is no pair of distinct positive steady states in a class.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (hM : N.SingletonSource) {c x y : Concentration S} (hx : x ∈ N.PositiveSteadyStatesInClass κ c)
    (hy : y ∈ N.PositiveSteadyStatesInClass κ c) (hxy : x ≠ y) :
    x ∈ N.PositiveSteadyStatesInClass κ c ∧
      y ∈ N.PositiveSteadyStatesInClass κ c ∧
        (fun s => (x s + y s) / 2) ∈ N.PositiveSteadyStatesInClass κ c ∧
          x ≠ (fun s => (x s + y s) / 2) ∧ (fun s => (x s + y s) / 2) ≠ y :=
  CRNT.Network.singletonSource_no_exactly_two N κ hM hx hy hxy

-- SingletonSource networks: the steady-state invariants are the row space of the coefficient matrix.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (hM : N.SingletonSource) (w : S → ℝ) :
    N.IsSteadyStateInvariant κ w ↔ ∃ c : S → ℝ, ∀ i : S, w i = ∑ s, c s * N.singletonSourceCoeff κ i s :=
  CRNT.Network.singletonSource_linearInvariant_iff_rowSpace N κ hM w

-- Toric parametrization: the positive steady states are the parametrized kernel.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { CRNT.toricParametrization xs v | v ∈ CRNT.expLogKernel a b } :=
  CRNT.Network.toric_positiveSteadyStates_eq_parametrization N κ a b c hc htor hxs hxss

-- Toric parametrization: the steady-state invariants are the log-orthogonal ones.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (g : Concentration S → ℝ) :
    (∀ x y : Concentration S, x.Positive → N.IsMassActionSteadyState κ x →
      y.Positive → N.IsMassActionSteadyState κ y → g x = g y) ↔
      ∀ v ∈ CRNT.expLogKernel a b, g (CRNT.toricParametrization xs v) = g xs :=
  CRNT.Network.steadyStateInvariant_iff_log_orthogonal N κ a b c hc htor hxs hxss g

-- Non-isothermal kinetics: at a fixed temperature the species equations are the mass-action ones.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (k : CRNT.NonIsothermal.TemperatureDependentRates N) (ΔH : N.R → ℝ) (ρ cp T₀ : ℝ)
    (x : Concentration S) :
    N.massActionVectorField
        ({ k := fun r => k.k r T₀, positive := fun r => k.pos r T₀ } : N.RateConstants) x =
      CRNT.NonIsothermal.nonIsothermalVectorField N k ΔH ρ cp x T₀ :=
  CRNT.NonIsothermal.isothermal_species_eq_massAction N k ΔH ρ cp T₀ x

-- Non-isothermal kinetics: the temperature equation is minus the total heat release.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (k : CRNT.NonIsothermal.TemperatureDependentRates N) (ΔH : N.R → ℝ) (ρ cp : ℝ)
    (x : Concentration S) (T : ℝ) :
    CRNT.NonIsothermal.temperatureEquation N k ΔH ρ cp x T =
      -(1 / (ρ * cp)) * ∑ r, ΔH r * CRNT.NonIsothermal.nonIsothermalRate N k T r x :=
  CRNT.NonIsothermal.temperatureEquation_eq_neg_sum_heat N k ΔH ρ cp x T

-- Delay equations: the limit of a delay trajectory is a steady state.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (τ : N.R → ℝ) {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x)
    (y : Concentration S) (hy : Tendsto x atTop (nhds y)) :
    N.IsMassActionSteadyState κ y :=
  CRNT.Network.delay_limit_isSteadyState N κ τ hx y hy

-- Delay equations: a compact delay trajectory with a unique cluster point converges to it.
open Filter in
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (τ : N.R → ℝ) {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x)
    (hcompact : IsCompact (closure (Set.range x))) (y : Concentration S)
    (huniq : ∀ z : Concentration S, ClusterPt z (Filter.map x atTop) → z = y) :
    Tendsto x atTop (nhds y) ∧ N.IsMassActionSteadyState κ y :=
  CRNT.Network.delay_semistability N κ τ hx hcompact y huniq

-- Reaction-diffusion: local existence of a solution of the reaction-diffusion equation.
example {ι : Type} [Fintype ι] [DecidableEq ι] (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hf : ∀ (i : ι) (x y : ℝ), |f i x - f i y| ≤ L * |x - y|) (x₀ : ι → ℝ)
    [Nonempty ι] :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ, γ 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt γ (CRNT.ReactionDiffusion.reactionDiffusionField D f (γ t)) t :=
  CRNT.ReactionDiffusion.exists_reactionDiffusion_solution D f L hL hf x₀

-- Reaction-diffusion: the Brusselator is Turing-unstable.
example :
    CRNT.IsHurwitz (CRNT.Turing.charPoly (2 - 1) (3 ^ 2) (-2) (-(3 ^ 2))) ∧
      0 < 64 * (2 - 1) + 1 * (-(3 ^ 2)) ∧
      4 * 1 * 64 * ((2 - 1) * (-(3 ^ 2)) - 3 ^ 2 * (-2))
        < (64 * (2 - 1) + 1 * (-(3 ^ 2))) ^ 2 :=
  CRNT.ReactionDiffusion.brusselator_turing_instance

-- General-plant design: the antithetic loop pins the output at its setpoint.
example {n : ℕ} (P : CRNT.Design.GeneralPlant.LinearPlant n) {μ θ : ℝ} (hθ : θ ≠ 0)
    {z : (Fin n → ℝ) × ℝ} (h : P.antitheticLoop μ θ z = (0, 0)) : P.output z.1 = μ / θ :=
  CRNT.Design.GeneralPlant.LinearPlant.antitheticLoop_setpoint P hθ h

-- General-plant design: a Foster drift makes the stochastic plant ergodic.
example {α : Type*} [Countable α] [Nonempty α] [DecidableEq α]
    (J : CRNT.JumpSystem α) (V f : α → ℝ) (H : CRNT.Design.GeneralPlant.FosterDrift J V f)
    (hstoch : ∀ t : ℝ, 0 ≤ t → ∀ x : α, HasSum (fun b => J.Pmin t x b) 1)
    (hirr : ∀ a b : α, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ b : α, 0 < π b) ∧ HasSum π 1 ∧
      (∀ s : ℝ, 0 ≤ s → ∀ b : α, ∑' x, π x * J.Pmin s x b = π b) ∧
        (∀ a : α, Filter.Tendsto (fun t => ∑' b, |J.Pmin t a b - π b|) Filter.atTop (nhds 0)) ∧
          (∀ μ : α → ℝ, (∀ b : α, 0 ≤ μ b) → HasSum μ 1 →
            (∀ s : ℝ, 0 ≤ s → ∀ b : α, ∑' x, μ x * J.Pmin s x b = μ b) → μ = π) :=
  CRNT.Design.GeneralPlant.ergodic_of_fosterDrift J V f H hstoch hirr

-- Planar oscillation: a monotone planar periodic solution is constant.
example {F : Concentration (Fin 2) → Concentration (Fin 2)} (hmono : Monotone F)
    {x : ℝ → Concentration (Fin 2)} (hsol : ∀ (t : ℝ), HasDerivAt x (F (x t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic x T) {lo hi : ℝ}
    (horizon : ∀ (t : ℝ), x t ∈ CRNT.Oscillation.planarBox lo hi)
    (hLip : ∃ L, LipschitzOnWith L F (CRNT.Oscillation.planarBox lo hi)) :
    ∃ p, ∀ (t : ℝ), x t = p :=
  CRNT.Oscillation.periodicSolution_constant_of_monotone hmono hsol hT hper horizon hLip

-- Planar oscillation: a cooperative planar network has no positive periodic orbit.
example {N : Network (Fin 2)} (hcoop : N.IsCooperativeNetwork) : N.NeverPositivePeriodic :=
  CRNT.Oscillation.Network.neverPositivePeriodic_of_cooperative hcoop

-- Trapping regions: the Lotka network has a positive periodic orbit.
example (K : CRNT.Planar.PoincareBendixsonKernelBundle)
    (κ : CRNT.Examples.Lotka.N.RateConstants) (h0 : 0 < κ.k CRNT.Examples.Lotka.grow)
    (h1 : 0 < κ.k CRNT.Examples.Lotka.prey) (h2 : 0 < κ.k CRNT.Examples.Lotka.decay) :
    CRNT.Examples.Lotka.N.HasPositivePeriodicOrbit κ :=
  CRNT.Oscillation.lotka_hasPositivePeriodicOrbit_of_trappingRegion K κ h0 h1 h2

-- No chaos: a planar trapping-region ω-set is not chaotic.
example (K : CRNT.Planar.PoincareBendixsonKernelBundle) {field : CRNT.Phase2 → CRNT.Phase2}
    (D : CRNT.Planar.FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) :
    ¬ CRNT.Planar.HasNonregularMinimalSubset field D.flow D.omegaSet :=
  CRNT.Planar.omegaSet_no_nonregular_minimal_subset K D hsmooth

-- Descartes' rule of signs for exponential sums.
example {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : StrictMono w) (c : Fin (n + 1) → ℝ)
    (hc : ∃ k, c k ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, ∑ k, c k * Real.exp (w k * t) = 0) :
    Z.card ≤ CRNT.CircuitDescartes.signVariations c :=
  CRNT.CircuitDescartes.card_zeros_exp_sum_le w hw c hc Z hZ

-- Circuit polynomials: the number of positive solutions is bounded by the sign variations.
example {n : ℕ} (Cm : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit Cm.det)
    (c₀ c₁ μ : Fin n → ℝ)
    (hP : CRNT.Circuit.circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ ≠ 0)
    (Y : Finset (Fin n → ℝ))
    (hY : ∀ y ∈ Y, (∀ k : Fin n, 0 < y k) ∧ Cm.mulVec y + c₀ + CRNT.Circuit.rmono μ y • c₁ = 0) :
    Y.card ≤
      (CRNT.Circuit.circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ).signVariations + 1 :=
  CRNT.Circuit.card_circuit_solutions_le_signVariations Cm hC c₀ c₁ μ hP Y hY

-- Tropical reduction: the reduced system has the same support.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (h : N.IsTropicalEquilibration a w) :
    {s : S | ∃ r ∈ N.tropicalReduced a w, N.reactionVector r s ≠ 0} =
      {s : S | ∃ r : N.R, N.reactionVector r s ≠ 0} :=
  CRNT.Network.tropicalReduced_species_eq N a w h

-- Tropical reduction: the leading system of the reduction is the leading system of the network.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (_h : N.IsTropicalEquilibration a w) :
    Finset.image (fun r => r.1)
        ((N.restrictReactions (N.tropicalReduced a w)).tropicalLeadingSystem (fun r => a r.1) w) =
      N.tropicalLeadingSystem a w :=
  CRNT.Network.leadingSystem_eq_reduced_of_equilibration N a w _h

-- PiecewiseNatAffine computation: `2 ^ v` is not piecewiseNatAffine.
example : ¬ CRNT.Computation.PiecewiseNatAffine fun v : Fin 1 → ℕ => 2 ^ v 0 :=
  CRNT.Computation.not_piecewiseNatAffine_pow2

-- PiecewiseNatAffine computation: the affine chemical reaction network stably computes its update map.
example (k a : ℕ) (m : Fin k → ℕ) :
    CRNT.Computation.StablyComputes (CRNT.Computation.affineCRN k a m) (CRNT.Computation.affineInit k)
      (Sum.inr (0 : Fin 2)) (fun x => a + ∑ j, m j * x j) :=
  CRNT.Computation.affineCRN_stablyComputes k a m

-- The presented deficiency-one algorithm: a run of the algorithm affirms the capacity.
example {S : Type} [DecidableEq S] [Fintype S] {N : Network S} (run : N.DOARun)
    (d : N.DOAShelfFluxes)
    (hsrc : ∀ sh ∈ d.shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = CRNT.Network.Shelf.middle) :
    N.HasMultistationarityCapacity :=
  CRNT.Network.doaRun_hasMultistationarityCapacity run d hsrc
