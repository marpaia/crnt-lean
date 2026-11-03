import CRNT.Kinetics.GeneralizedNetwork
import CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT
import CRNT.Kinetics.GeneralizedConditions
import CRNT.Graph.WeakReversibility
import CRNT.Equilibria.GeneralizedComplexBalanceToric

/-!
# Generalized deficiency-zero CRNT

This module packages the theorem hypotheses used in generalized mass-action CRNT when
both the stoichiometric and kinetic-order deficiencies vanish.  The oriented-matroid
closure, uniqueness, face, and nondegeneracy conditions then control robustness,
existence, and uniqueness of positive complex-balanced equilibria.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- The two subspaces relevant for generalized Birch theory. -/
noncomputable def StoichKineticPair (G : N.GeneralizedMassActionData) :
    Submodule ℝ (S → ℝ) × Submodule ℝ (S → ℝ) :=
  (N.stoichSubspace, G.kineticOrderSubspace)

/-- Structural hypotheses for the generalized deficiency-zero CBE theorem. -/
structure GeneralizedDeficiencyZeroHypotheses (G : N.GeneralizedMassActionData) : Prop where
  weaklyReversible : N.WeaklyReversible
  stoichDeficiencyZero : N.deficiency = 0
  kineticDeficiencyZero : G.kineticDeficiency = 0

/-- Uniqueness sign condition attached to a generalized CRN. -/
def HasCBEUniquenessSignCondition (G : N.GeneralizedMassActionData) : Prop :=
  GeneralizedUniquenessCondition N.stoichSubspace G.kineticOrderSubspace

/-- Closure condition attached to a generalized CRN. -/
def HasCBEClosureCondition (G : N.GeneralizedMassActionData) : Prop :=
  GeneralizedClosureCondition N.stoichSubspace G.kineticOrderSubspace

/-- Face condition attached to a generalized CRN. -/
def HasCBEFaceCondition (G : N.GeneralizedMassActionData) : Prop :=
  GeneralizedFaceCondition N.stoichSubspace G.kineticOrderSubspace

/-- Positive generalized CBE in the positive stoichiometric class of `c`. -/
def PositiveCBEInClass (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (c x : Concentration S) : Prop :=
  x.Positive ∧ N.StoichCompatible c x ∧ G.IsComplexBalanced κ x

/-- At most one positive CBE per stoichiometric class under the Müller--Regensburger sign
condition.  The zero-deficiency hypotheses identify generalized complex-balanced states
with the toric leaf to which generalized Birch uniqueness applies. -/
theorem cbe_unique_in_class_of_signCondition
    (G : N.GeneralizedMassActionData)
    (h0 : G.GeneralizedDeficiencyZeroHypotheses)
    (hsign : G.HasCBEUniquenessSignCondition)
    (κ : N.RateConstants) {c x y : Concentration S}
    (hx : G.PositiveCBEInClass κ c x)
    (hy : G.PositiveCBEInClass κ c y) : x = y := by
  have hsign' : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace) := by
    simpa [HasCBEUniquenessSignCondition, GeneralizedUniquenessCondition] using hsign
  have hclass : N.SameStoichClass x y := by
    change x - y ∈ N.stoichSubspace
    have hxy : x - y = (x - c) - (y - c) := by
      ext s
      simp [Pi.sub_apply]
    rw [hxy]
    exact N.stoichSubspace.sub_mem hx.2.1 hy.2.1
  exact G.complexBalanced_unique_in_stoichClass_of_signCompatible κ
    h0.weaklyReversible hsign' hx.1 hy.1 hx.2.2 hy.2.2 hclass

/-- Generalized deficiency-zero existence interface.  Closure, face compatibility and
nondegeneracy are the genuinely extra conditions absent from ordinary mass action. -/
theorem exists_positive_cbe_in_class
    (G : N.GeneralizedMassActionData)
    (h0 : G.GeneralizedDeficiencyZeroHypotheses)
    (hclosure : G.HasCBEClosureCondition)
    (hface : G.HasCBEFaceCondition)
    -- `GeneralizedNondegenerate` is declared nowhere in the tree; the intended
    -- hypothesis is the Müller--Regensburger sign condition, as used in
    -- `Equilibria/GeneralizedComplexBalanceToric`.
    (hnondeg : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    (κ : N.RateConstants) {c : Concentration S} (hc : c.Positive) :
    ∃ x : Concentration S, G.PositiveCBEInClass κ c x := by
  have hδ : G.IsGeneralizedDeficiencyZero :=
    ⟨h0.weaklyReversible, h0.stoichDeficiencyZero, h0.kineticDeficiencyZero⟩
  have hom : G.CRNOrientedMatroidConditions := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [HasCBEClosureCondition] using hclosure
    · simpa [GeneralizedUniquenessCondition] using hnondeg
    · simpa [HasCBEFaceCondition] using hface
  obtain ⟨x, hx, _⟩ :=
    G.existsUnique_complexBalanced_in_every_positiveClass κ hδ hom c hc
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- Existence plus the sign condition gives exactly one positive generalized CBE in every
positive stoichiometric class. -/
theorem existsUnique_positive_cbe_in_class
    (G : N.GeneralizedMassActionData)
    (h0 : G.GeneralizedDeficiencyZeroHypotheses)
    (hclosure : G.HasCBEClosureCondition)
    (hsign : G.HasCBEUniquenessSignCondition)
    (hface : G.HasCBEFaceCondition)
    -- `GeneralizedNondegenerate` is declared nowhere in the tree; the intended
    -- hypothesis is the Müller--Regensburger sign condition, as used in
    -- `Equilibria/GeneralizedComplexBalanceToric`.
    (hnondeg : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    (κ : N.RateConstants) {c : Concentration S} (hc : c.Positive) :
    ∃! x : Concentration S, G.PositiveCBEInClass κ c x := by
  obtain ⟨x, hx⟩ := G.exists_positive_cbe_in_class h0 hclosure hface hnondeg κ hc
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact G.cbe_unique_in_class_of_signCondition h0 hsign κ hy hx

/-- Classical mass action is recovered when the kinetic complexes equal the ordinary
complexes. -/
theorem classical_generalizedDeficiencyZeroHypotheses_iff
    (N : Network S) :
    (GeneralizedMassActionData.classical N).GeneralizedDeficiencyZeroHypotheses ↔
      N.WeaklyReversible ∧ N.deficiency = 0 := by
  constructor
  · intro h; exact ⟨h.weaklyReversible, h.stoichDeficiencyZero⟩
  · rintro ⟨hwr, hδ⟩
    refine ⟨hwr, hδ, ?_⟩
    rw [classical_kineticDeficiency_eq_deficiency, hδ]

end GeneralizedMassActionData
end Network
end CRNT
