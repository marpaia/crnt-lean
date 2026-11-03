import CRNT.Kinetics.GeneralizedDeficiencyZeroCRNT
import CRNT.Kinetics.GeneralizedBirchExistence
import CRNT.Equilibria.GeneralizedTreeConstantCriterion
import CRNT.LinearAlgebra.OrientedMatroidConditions

/-!
# Generalized deficiency-zero existence and uniqueness

This module packages the Müller--Regensburger generalized deficiency-zero theorem at the
network level.  Weak reversibility and zero kinetic deficiency make the generalized
complex-balance equations a toric affine system.  Oriented-matroid closure/face
conditions control existence of an intersection with each positive stoichiometric class,
while the sign-compatibility condition controls uniqueness and transversality.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Structural hypotheses for generalized complex-balance existence in every positive
stoichiometric class.  The representation-independent oriented-matroid conditions are
kept explicit because different papers use row-space or kernel representations. -/
structure GeneralizedDeficiencyZeroExistenceHypotheses
    (G : N.GeneralizedMassActionData) : Prop where
  weaklyReversible : N.WeaklyReversible
  kineticDeficiencyZero : G.kineticDeficiency = 0
  closureCondition : GeneralizedClosureCondition
    N.stoichSubspace G.kineticOrderSubspace
  faceCondition : GeneralizedFaceCondition
    N.stoichSubspace G.kineticOrderSubspace

/-- Existence half of generalized deficiency zero: every positive stoichiometric class
contains a generalized complex-balanced equilibrium. -/
theorem exists_complexBalanced_in_every_positiveClass
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (H : G.GeneralizedDeficiencyZeroExistenceHypotheses)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, G.IsComplexBalanced κ x := by
  obtain ⟨xstar, hxs, hcbs⟩ :=
    G.exists_positive_complexBalanced_of_logTreeSolution κ H.weaklyReversible
      (G.exists_logTreeSolution_of_kineticDeficiency_zero κ
        H.weaklyReversible H.kineticDeficiencyZero)
  obtain ⟨x, hxpos, hclass, htoric⟩ :=
    generalized_birch_existence_of_conditions
      N.stoichSubspace G.kineticOrderSubspace
      H.closureCondition xstar x₀ hxs hx₀
  refine ⟨x, ⟨hclass, hxpos⟩, ?_⟩
  apply G.complexBalanced_of_toricLeaf κ H.weaklyReversible hxs hcbs
  exact ⟨hxpos, by simpa [logRatio] using htoric⟩

/-- Add sign compatibility to obtain uniqueness. -/
structure GeneralizedDeficiencyZeroUniquenessHypotheses
    (G : N.GeneralizedMassActionData)
    extends GeneralizedDeficiencyZeroExistenceHypotheses G : Prop where
  signCompatible : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace)

/-- Generalized deficiency-zero uniqueness in each positive class. -/
theorem unique_complexBalanced_in_positiveClass
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (H : G.GeneralizedDeficiencyZeroUniquenessHypotheses)
    {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀)
    (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hcx : G.IsComplexBalanced κ x)
    (hcy : G.IsComplexBalanced κ y) : x = y := by
  have hclass : N.SameStoichClass x y := by
    change x - y ∈ N.stoichSubspace
    have hxy : x - y = (x - x₀) - (y - x₀) := by
      ext s
      simp [Pi.sub_apply]
    rw [hxy]
    exact N.stoichSubspace.sub_mem hx.1 hy.1
  exact G.complexBalanced_unique_in_stoichClass_of_signCompatible κ
    H.weaklyReversible H.signCompatible hx.2 hy.2 hcx hcy hclass

/-- Full existence-and-uniqueness formulation. -/
theorem existsUnique_complexBalanced_in_positiveClass
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (H : G.GeneralizedDeficiencyZeroUniquenessHypotheses)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ G.IsComplexBalanced κ x := by
  obtain ⟨x, hx, hcb⟩ := G.exists_complexBalanced_in_every_positiveClass κ H.toGeneralizedDeficiencyZeroExistenceHypotheses hx₀
  refine ⟨x, ⟨hx, hcb⟩, ?_⟩
  intro y hy
  exact G.unique_complexBalanced_in_positiveClass κ H hy.1 hx hy.2 hcb

/-- If both ordinary and kinetic deficiency vanish, weak reversibility plus the oriented-
matroid existence/uniqueness conditions give one generalized CBE in every class. -/
theorem generalized_deficiency_zero_theorem
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hδ : N.deficiency = 0) (hδk : G.kineticDeficiency = 0)
    (hwr : N.WeaklyReversible)
    (hclosure : GeneralizedClosureCondition
      N.stoichSubspace G.kineticOrderSubspace)
    (hface : GeneralizedFaceCondition
      N.stoichSubspace G.kineticOrderSubspace)
    (hsign : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ G.IsComplexBalanced κ x := by
  let H : G.GeneralizedDeficiencyZeroUniquenessHypotheses :=
    { weaklyReversible := hwr
      kineticDeficiencyZero := hδk
      closureCondition := hclosure
      faceCondition := hface
      signCompatible := hsign }
  exact G.existsUnique_complexBalanced_in_positiveClass κ H hx₀

end GeneralizedMassActionData
end Network
end CRNT
