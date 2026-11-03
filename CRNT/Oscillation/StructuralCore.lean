import CRNT.Oscillation.MatrixCriteria
import CRNT.Oscillation.ParameterRich
import CRNT.Deficiency.Consistent
import CRNT.Stoich.Vector

/-!
# Child selections and structural oscillatory cores

This module formalizes the finite CRN objects used by the modern structural-oscillation literature.
A child selection pairs selected species bijectively with equally many reactions, with every species
occurring as a reactant of its paired reaction.  Reordering the corresponding stoichiometric columns
produces a square child-selection matrix.

The exact matrix notions of unstable cores and oscillatory cores of classes I/II live in
`MatrixCriteria` and are lifted here to CRNs.  The 2026 oscillatory-core results use
**parameter-rich kinetics**.  Consequently this file deliberately targets the general admissible-
kinetics predicate `KineticOscillatoryCapacity`, not mass-action `OscillatoryCapacity`.  The latter
has a separate 2025 route in `VassenaCriteria`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A **child selection**: selected species are matched bijectively to selected reactions in which
that species occurs as a reactant. -/
structure ChildSelection (N : Network S) where
  species : Finset S
  reactions : Finset N.R
  pairing : {s : S // s ∈ species} ≃ {r : N.R // r ∈ reactions}
  reactant : ∀ s : {s : S // s ∈ species},
    0 < (N.reaction (pairing s).1).source s.1

namespace ChildSelection

variable {N : Network S}

/-- Species index type of a child selection. -/
abbrev Idx (C : N.ChildSelection) := {s : S // s ∈ C.species}

/-- The stoichiometric child-selection matrix. Column `j` is the reaction vector paired to species
`j`; rows are the selected species. -/
def matrix (C : N.ChildSelection) : Matrix C.Idx C.Idx ℝ :=
  fun i j => N.reactionVector (C.pairing j).1 i.1

/-- Child selections contain equally many species and reactions. -/
theorem card_species_eq_card_reactions (C : N.ChildSelection) :
    C.species.card = C.reactions.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr C.pairing

/-- One child selection extends another when it contains its species/reactions and preserves the
species-to-reaction pairing on the smaller selection. -/
def Extends (large small : N.ChildSelection) : Prop :=
  ∃ (hs : small.species ⊆ large.species),
    small.reactions ⊆ large.reactions ∧
      ∀ (s : S) (hsm : s ∈ small.species),
        (small.pairing ⟨s, hsm⟩).1 =
          (large.pairing ⟨s, hs hsm⟩).1

/-- Reflexivity of child-selection extension. -/
theorem extends_refl (C : N.ChildSelection) : C.Extends C := by
  refine ⟨fun _ h => h, fun _ h => h, ?_⟩
  intro s hs
  rfl

/-- Principal submatrix selected by a finite subset of the child-selection species indices. -/
def principalSubmatrix (C : N.ChildSelection) (I : Finset C.Idx) :
    Matrix {i : C.Idx // i ∈ I} {i : C.Idx // i ∈ I} ℝ :=
  C.matrix.principalSubmatrix I

/-- A child-selection matrix is Hurwitz-unstable in the strict sense of carrying an eigenvalue in
the open right half-plane. -/
def IsUnstable (C : N.ChildSelection) : Prop :=
  C.matrix.HasUnstableEigenvalue

/-- A child-selection matrix is Hurwitz stable. -/
def IsStable (C : N.ChildSelection) : Prop :=
  C.matrix.IsHurwitzReal

/-- A minimal unstable child-selection matrix. -/
def IsUnstableCore (C : N.ChildSelection) : Prop :=
  C.matrix.IsUnstableCore

/-- Determinant sign associated with unstable-negative feedback. -/
def HasNegativeFeedbackSign (C : N.ChildSelection) : Prop :=
  C.matrix.HasNegativeFeedbackSign

/-- Determinant sign associated with unstable-positive feedback. -/
def HasPositiveFeedbackSign (C : N.ChildSelection) : Prop :=
  C.matrix.HasPositiveFeedbackSign

/-- A minimal unstable negative-feedback child selection. -/
def IsUnstableNegativeFeedback (C : N.ChildSelection) : Prop :=
  C.matrix.IsUnstableNegativeFeedback

/-- A minimal unstable positive-feedback child selection. -/
def IsUnstablePositiveFeedback (C : N.ChildSelection) : Prop :=
  C.matrix.IsUnstablePositiveFeedback

/-- Exact class-I oscillatory-core predicate lifted from the child-selection matrix. -/
def IsOscillatoryCoreClassI (C : N.ChildSelection) : Prop :=
  C.matrix.IsOscillatoryCoreClassI

/-- Exact class-II oscillatory-core predicate lifted from the child-selection matrix. -/
def IsOscillatoryCoreClassII (C : N.ChildSelection) : Prop :=
  C.matrix.IsOscillatoryCoreClassII

/-- Class-I cores are Hurwitz-stable child selections. -/
theorem IsOscillatoryCoreClassI.isStable {C : N.ChildSelection}
    (h : C.IsOscillatoryCoreClassI) : C.IsStable := by
  show C.matrix.IsHurwitzReal
  exact Matrix.IsOscillatoryCoreClassI.stable h

/-- Class-II cores are unstable-negative feedbacks. -/
theorem IsOscillatoryCoreClassII.isUnstableNegativeFeedback {C : N.ChildSelection}
    (h : C.IsOscillatoryCoreClassII) : C.IsUnstableNegativeFeedback := by
  show C.matrix.IsUnstableNegativeFeedback
  exact Matrix.IsOscillatoryCoreClassII.unstableNegativeFeedback h

/-- A child selection cannot simultaneously be a class-I and class-II oscillatory core. -/
theorem IsOscillatoryCoreClassI.not_classII {C : N.ChildSelection}
    (h : C.IsOscillatoryCoreClassI) : ¬ C.IsOscillatoryCoreClassII := by
  exact Matrix.IsOscillatoryCoreClassI.not_classII h

/-- Symmetric class-I/class-II exclusivity for child selections. -/
theorem IsOscillatoryCoreClassII.not_classI {C : N.ChildSelection}
    (h : C.IsOscillatoryCoreClassII) : ¬ C.IsOscillatoryCoreClassI := by
  exact Matrix.IsOscillatoryCoreClassII.not_classI h

/-- Historical precursor object: an unstable-positive-feedback child selection embedded in a stable
larger child selection.  This is useful data, but by itself it does **not** encode the minimality
required by the exact class-I oscillatory-core definition. -/
structure PositiveFeedbackStableSuperSelection (N : Network S) : Type where
  core : N.ChildSelection
  superSelection : N.ChildSelection
  core_is_upf : core.IsUnstablePositiveFeedback
  extends_core : superSelection.Extends core
  super_stable : superSelection.IsStable

end ChildSelection

/-- A proof-carrying CRN witness of an exact class-I oscillatory core. -/
structure OscillatoryCoreClassICertificate (N : Network S) : Type where
  selection : N.ChildSelection
  isClassI : selection.IsOscillatoryCoreClassI

/-- A proof-carrying CRN witness of an exact class-II oscillatory core. -/
structure OscillatoryCoreClassIICertificate (N : Network S) : Type where
  selection : N.ChildSelection
  isClassII : selection.IsOscillatoryCoreClassII

/-- A network contains one of the two exact oscillatory-core classes. -/
def HasOscillatoryCore (N : Network S) : Prop :=
  Nonempty (OscillatoryCoreClassICertificate N) ∨
    Nonempty (OscillatoryCoreClassIICertificate N)

/-- **2026 parameter-rich realization frontier.**

The paper-level recipes use parameter-rich kinetics rather than mass action.  This proposition is
therefore stated against a specified parameter-rich family rather than mass action.  The family
must also coherently realize smooth reactivity paths; pointwise realizability alone is not enough for
a global-Hopf continuation argument.  Consistency is included explicitly because it supplies the positive stationary flux/steady-state
compatibility required in the recipe interpretation.  Symbolic nondegeneracy records the required
rank-reduced nonsingularity when conservation laws make the full Jacobian singular.  The proposition
is a theorem target, not an axiom. -/
def ParameterRichOscillatoryCoreRealizationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T)
    (F : N.SteadyStateParameterRichFamily),
    N.SupportsSmoothReactivityPaths F →
    N.IsConsistent → N.IsSymbolicallyNondegenerate →
    N.HasOscillatoryCore → N.ParameterRichOscillatoryCapacity F

/-- Consume a proved parameter-rich realization theorem using a class-I core. -/
theorem OscillatoryCoreClassICertificate.parameterRichOscillatoryCapacity
    {N : Network S} (hRealize : ParameterRichOscillatoryCoreRealizationTarget)
    (F : N.SteadyStateParameterRichFamily) (hpaths : N.SupportsSmoothReactivityPaths F)
    (hcons : N.IsConsistent) (hnd : N.IsSymbolicallyNondegenerate)
    (C : OscillatoryCoreClassICertificate N) :
    N.ParameterRichOscillatoryCapacity F :=
  hRealize N F hpaths hcons hnd (Or.inl ⟨C⟩)

/-- Consume a proved parameter-rich realization theorem using a class-II core. -/
theorem OscillatoryCoreClassIICertificate.parameterRichOscillatoryCapacity
    {N : Network S} (hRealize : ParameterRichOscillatoryCoreRealizationTarget)
    (F : N.SteadyStateParameterRichFamily) (hpaths : N.SupportsSmoothReactivityPaths F)
    (hcons : N.IsConsistent) (hnd : N.IsSymbolicallyNondegenerate)
    (C : OscillatoryCoreClassIICertificate N) :
    N.ParameterRichOscillatoryCapacity F :=
  hRealize N F hpaths hcons hnd (Or.inr ⟨C⟩)

/-- Backwards-facing name for the positive-feedback recipe certificate, now tied to the exact
class-I definition rather than the weaker stable-super-selection precursor. -/
abbrev PositiveFeedbackRecipeCertificate (N : Network S) := OscillatoryCoreClassICertificate N

/-- Backwards-facing name for the negative-feedback recipe certificate, now tied to the exact
class-II definition (including the Fisher--Fuller/stable-codimension-one alternative). -/
abbrev NegativeFeedbackCoreCertificate (N : Network S) := OscillatoryCoreClassIICertificate N

end Network

end CRNT
