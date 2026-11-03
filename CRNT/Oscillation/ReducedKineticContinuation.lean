import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.RecipeZeroContinuation
import CRNT.Oscillation.SmoothGlobalHopf
import CRNT.Multistationarity.ReducedJacobian

/-!
# Rank-reduced smooth kinetic continuation interfaces

Conservation laws make the ambient species Jacobian singular. The selected-principal-block to
stoichiometric-chart conjugacy, smooth reduced continuation, and positive-chart radius are explicit
construction targets here; the earlier implementation referred to undeclared helpers for each step.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}


/-- Fréchet-Jacobian matrix of a differentiable admissible kinetics at one state. -/
noncomputable def Kinetics.jacobianAt (K : N.Kinetics) (x : Concentration S) : Matrix S S ℝ :=
  jacobianMatrix (fderiv ℝ K.vectorField x)

/-- Reduced kinetic field on a compatibility-class chart. -/
noncomputable def reducedKineticField
    (K : N.Kinetics) (x : Concentration S) :
    (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  fun y => N.stoichProj (K.vectorField (N.affineChart x y))

/-- Reduced derivative operator of a general differentiable kinetics at the chart origin. -/
noncomputable def kineticReducedJacobianCLM
    (K : N.Kinetics) (x : Concentration S) :
    (Fin N.stoichRank → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ) :=
  N.stoichProj.comp ((fderiv ℝ K.vectorField x).comp N.stoichChart)

/-- Matrix of the reduced derivative. -/
noncomputable def kineticReducedJacobian
    (K : N.Kinetics) (x : Concentration S) :
    Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  jacobianMatrix (N.kineticReducedJacobianCLM K x)

@[simp] theorem kineticReducedJacobianCLM_apply
    (K : N.Kinetics) (x : Concentration S) (v : Fin N.stoichRank → ℝ) :
    N.kineticReducedJacobianCLM K x v =
      N.stoichProj (fderiv ℝ K.vectorField x (N.stoichChart v)) := rfl

/-- A smooth kinetic path together with a rank-sized principal coordinate block that represents the
linearization on the compatibility class. -/
structure RankReducedKineticContinuation
    (F : N.SteadyStateParameterRichFamily) (x : Concentration S) : Type where
  kinetics : ℝ → N.Kinetics
  member : ∀ μ ∈ Set.Icc (0 : ℝ) 1, kinetics μ ∈ F.members
  positiveState : x.Positive
  steady : ∀ μ ∈ Set.Icc (0 : ℝ) 1, N.IsKineticSteadyState (kinetics μ) x
  species : Finset S
  rankSized : species.card = N.stoichRank
  reducedMatrix : ℝ → Matrix species species ℝ
  reducedMatrix_eq : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    reducedMatrix μ =
      ((kinetics μ).jacobianAt x).principalSubmatrix species
  fieldSmooth : ContDiff ℝ ⊤
    (fun p : ℝ × Concentration S => (kinetics p.1).vectorField p.2)
  matrixContinuous : Continuous reducedMatrix
  stable : (reducedMatrix 0).IsHurwitzReal
  unstable : (reducedMatrix 1).HasUnstableEigenvalue
  nonsingular : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (reducedMatrix μ).det ≠ 0


end Network
end CRNT
