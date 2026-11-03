import CRNT
import CRNT.Examples.Minimal
import CRNT.Examples.ReversiblePair
import CRNT.Examples.IrreversibleChain
import CRNT.Interop.Analysis

/-!
# Non-vacuity / negative controls

Every check in `Smoke.lean` is a *positive* control: it confirms that some predicate holds where it
should.  Positive controls cannot detect a predicate that holds everywhere, which is exactly the
failure this repository had:

* `HasNoDrainableSiphon`, `HasNoSelfReplicableSiphon` and `MinimalCriticalSiphonDichotomy` were
  defined as `∃ (_ : Unit), True` with `Decidable` instances given by `isTrue`, so the analyzer's
  corresponding flags were `true` for every network and the "proof-producing" bridges into
  `BoundaryOmegaCertificate` fired unconditionally.
* Six certificate structures were `structure C where dummy : True`, so every certificate carried no
  information.
* `StructurallyPersistent`, `StructurallyPermanent` and `IsMassActionFlow` were `:= True`.

A single test asserting that one of those flags is `false` on one network would have failed
immediately.  This file is that test, generalized: for every Boolean the analyzer exposes and every
structural predicate the library exposes, there is a witness on which it is **false**.

Rule for new predicates: a predicate is not finished until this file contains a network where it
fails.  `scripts/check_stubs.py` catches the syntactic shapes above; this file catches semantic
vacuity that is syntactically invisible.
-/

open CRNT
open scoped NNReal

namespace CRNT.Test.NonVacuity

/-! ## Structural predicates: witnesses where they fail

Lines below reuse `decide` only on analyzer fields that `Smoke.lean` already reduces
(`weaklyReversible`, `srSignConsistent`, `acrSpecies`, `numACRSpecies`, `hopfBoundaryMargin`).
Compound flags go through their bridge lemmas instead, and `noPositivePeriodicOrbitCertified` is
certified through the stoichiometric-rank bridge, because the `computeRank`-backed value does not
kernel-reduce. -/

-- Weak reversibility fails on the irreversible chain and on the minimal network.
example : ¬ Examples.IrreversibleChain.N.WeaklyReversible :=
  Examples.IrreversibleChain.not_weaklyReversible

example : ¬ Examples.Minimal.N.WeaklyReversible := Examples.Minimal.not_weaklyReversible

/-! ## Analyzer flags: witnesses where they are `false`

Each line below pins a flag to `false` on a concrete `NetworkData`.  If a flag ever becomes
unconditionally `true` -- because its underlying predicate was weakened, or because someone
supplied an `isTrue` decider -- the corresponding line stops reducing and this file fails. -/

/-- The data-driven reversible pair `A ⇌ B`, as in `Smoke.lean`. -/
def revPair : NetworkData :=
  { numSpecies := 2,
    reactions := #[ { source := #[1, 0], target := #[0, 1] },
                    { source := #[0, 1], target := #[1, 0] } ] }

/-- The stoichiometric rank of `revPair` is one: the 1 × 1 minor at species `0` (entry `0 - 1`)
bounds it below, the backward reaction vector is the negation of the forward one, so the subspace
is the line spanned by a single nonzero vector. -/
theorem revPair_stoichRank : revPair.toNetwork.stoichRank = 1 := by
  have hv : revPair.toNetwork.reactionVector
      (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R) ≠ 0 := by
    intro h
    have h0 : revPair.toNetwork.reactionVector
        (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R) (0 : Fin 2) = (0 : ℝ) :=
      congrFun h (0 : Fin 2)
    simp only [Network.reactionVector, Reaction.vector] at h0
    rw [show (revPair.toNetwork.reaction (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R)).target
          (0 : Fin 2) = 0 from by decide,
      show (revPair.toNetwork.reaction (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R)).source
          (0 : Fin 2) = 1 from by decide] at h0
    norm_num at h0
  have hbwd : revPair.toNetwork.reactionVector (⟨1, by simp [revPair]⟩ : revPair.toNetwork.R)
      = fun s => -revPair.toNetwork.reactionVector
          (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R) s := by
    funext s
    fin_cases s
    all_goals
      simp [Network.reactionVector, Reaction.vector, NetworkData.toNetwork,
        NetworkData.toComplex, revPair]
  have hsub : revPair.toNetwork.stoichSubspace
      = Submodule.span ℝ {revPair.toNetwork.reactionVector
          (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R)} := by
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
      exact revPair.toNetwork.reactionVector_mem_stoichSubspace
        (⟨0, by simp [revPair]⟩ : revPair.toNetwork.R)
  rw [Network.stoichRank, hsub, finrank_span_singleton hv]

/-- With the rank pinned to one, the low-rank route of the exclusion disjunction certifies no
positive periodic orbit. -/
theorem revPair_noPositivePeriodicOrbitCertified :
    revPair.analyze.noPositivePeriodicOrbitCertified = true := by
  rw [NetworkData.analyze_noPositivePeriodicOrbitCertified_eq,
    NetworkData.analyze_stoichRank_eq, revPair_stoichRank]
  exact Bool.or_true _

/-- The irreversible chain `A → B → C`: weak reversibility must report `false`. -/
def chain : NetworkData :=
  { numSpecies := 3,
    reactions := #[ { source := #[1, 0, 0], target := #[0, 1, 0] },
                    { source := #[0, 1, 0], target := #[0, 0, 1] } ] }

example : chain.analyze.weaklyReversible = false := by decide

-- Both persistence flags are `false` on the chain.  These go through the field bridges rather than
-- `decide` on the flag itself, because `decide` on weak reversibility is not guaranteed to
-- kernel-reduce inside the compound flag (see the note in `Smoke.lean`).  With the old hollow
-- siphon predicates the analogous `noDrainableSiphon` flag could not be made `false` by *any*
-- input, so no proof in this style existed.
example : chain.analyze.persistenceStructural = false := by
  rw [NetworkData.analyze_persistenceStructural_eq,
    show chain.analyze.weaklyReversible = false from by decide]
  simp

example : chain.analyze.persistenceCertified = false := by
  rw [NetworkData.analyze_persistenceCertified_eq,
    show chain.analyze.weaklyReversible = false from by decide]
  simp

-- The SR-sign-consistency verdict is `false` on the reversible pair, so the P-matrix route is
-- genuinely conditional rather than always available.
example : revPair.analyze.srSignConsistent = false := by decide

-- Structural ACR is not universal: the reversible pair reports no ACR species.
example : revPair.analyze.acrSpecies = #[] := by decide
example : revPair.analyze.numACRSpecies = 0 := by decide

-- The Hopf-boundary margin is `none` outside dimension three, so the field is not a constant.
example : revPair.analyze.hopfBoundaryMargin = none := by decide

/-! ## The oscillation exclusion route is conditional

`noPositivePeriodicOrbitCertified` is the disjunction of the deficiency-zero and low-rank routes.
It must be `true` where a route applies and `false` where none does -- a flag that were always
`true` would make `neverPositivePeriodic_of_analyze` an unconditional non-oscillation theorem. -/

-- Rank ≤ 1 route applies to the reversible pair (rank 1), so the flag is `true`.  The value is
-- certified through the rank bridge because `computeRank` does not kernel-reduce under `decide`.
example : revPair.analyze.noPositivePeriodicOrbitCertified = true :=
  revPair_noPositivePeriodicOrbitCertified

-- And the certified conclusion really follows from the flag, for this concrete network.
example : revPair.toNetwork.NeverPositivePeriodic :=
  NetworkData.neverPositivePeriodic_of_analyze revPair revPair_noPositivePeriodicOrbitCertified

/-! ## Negative controls that live in the frontier

The strongest available negative control is the Lotka network, which genuinely oscillates and on
which both exclusion routes must therefore fail. It is in `test/LotkaNonVacuity.lean` rather than
here, because `CRNT.Examples.Lotka` has never been elaborated and this file gates the core build.
Move it here once the example compiles. -/

/-! ## The newest modules: negative controls

The rule above applies to the predicates introduced by the newest wave of modules as well: each
of them must be able to *fail*.  The entries below give a network on which each new verdict
fails, so a predicate that silently became `True` would break this file. -/

/-- The toy network `2A → B`: the source complex has total molecularity two, so the network is
**not** a SingletonSource network. -/
def singletonSourceCounter : Network (Fin 2) :=
  { R := Unit, decEqR := inferInstance, fintypeR := inferInstance,
    reaction := fun _ => { source := ![2, 0], target := ![0, 1] } }

/-- **The SingletonSource predicate can fail.**  A network with a bimolecular source is not SingletonSource, so the
linear steady-state machinery of `CRNT/Equilibria/SingletonSource.lean` is conditional. -/
example : ¬ singletonSourceCounter.SingletonSource := by
  intro hM
  obtain ⟨i, hi⟩ := hM ()
  have h1 : (![2, 0] : Complex (Fin 2)) i = 1 := hi.1
  fin_cases i <;> simp at h1

/-- **The deficiency-one and advanced-deficiency algorithms can report "no".**  For the
one-reaction network whose source and target coincide no species is consumed, so the
feasibility condition `1 < ∑ s with a s < b s, a s` fails; neither algorithm affirms the
multistationarity capacity. -/
example {S : Type} [DecidableEq S] [Fintype S] (a : Complex S) :
    ¬ (Network.oneRxn a a).fullyOpen.DOAFeasible ∧
      ¬ (Network.oneRxn a a).fullyOpen.ADAFeasible := by
  have hno : ¬ (Network.oneRxn a a).fullyOpen.DOAFeasible := by
    intro h
    have h' := (Network.oneRxn_doaFeasible_iff a a).mp h
    have hz : (∑ s with a s < a s, a s) = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_filter] at hs
      exact absurd hs.2 (lt_irrefl _)
    rw [hz] at h'
    omega
  refine ⟨hno, ?_⟩
  intro h
  have hcap := (Network.hasMultistationarityCapacity_iff_adaFeasible
    (Network.oneRxn a a).fullyOpen).mpr h
  have hdoa := (Network.hasMultistationarityCapacity_iff_doaFeasible
    (Network.oneRxn a a).fullyOpen).mp hcap
  exact hno hdoa

/-- **The escape-direction conclusion is conditional.**  The autocatalytic network `A → 2A`
genuinely escapes to infinity, so the "no escape" theorem of
`CRNT/Dynamics/EscapeDirection.lean` cannot be unconditional. -/
example : Filter.Tendsto (fun t => ‖(CRNT.Examples.EscapeAutocatalysis.sol t :
    CRNT.Examples.EscapeAutocatalysis.Species → ℝ)‖) Filter.atTop Filter.atTop :=
  CRNT.Examples.EscapeAutocatalysis.sol_escapes

/-- **The tier-domination claim can fail.**  In the endotactic counterexample the top tier does
not dominate the escape count, so the domination criterion of
`CRNT/Stochastic/EndotacticTierDomination.lean` is a genuine obstruction and not a tautology. -/
example (k : ℕ) (hk : 1 ≤ k) :
    CRNT.Network.countDescFactorial (CRNT.Examples.EndotacticCounterexample.net.reaction 3).source
        (CRNT.Examples.EndotacticCounterexample.escapeCount k) >
      CRNT.Network.countDescFactorial (CRNT.Examples.EndotacticCounterexample.net.reaction 1).source
        (CRNT.Examples.EndotacticCounterexample.escapeCount k) :=
  CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate k hk

end CRNT.Test.NonVacuity
