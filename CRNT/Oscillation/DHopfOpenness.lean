import CRNT.Oscillation.ChildSelectionReactivity
import CRNT.Oscillation.SpectralOpenness

/-!
# Finite-matrix openness behind the epsilon child-selection construction

The child-selection embedding is completely explicit: the selected symbolic block converges
entrywise to the D-Hopf core matrix as `eps -> 0`.  What remains is not a CRN theorem but a standard
finite-dimensional spectral-openness fact: a matrix with one Hurwitz diagonal scaling and one
strictly unstable diagonal scaling retains those strict properties under a sufficiently small
matrix perturbation.

This file isolates precisely that matrix statement and proves that it is sufficient for the
child-selection perturbation theorem.
-/

namespace Matrix

/-- Local openness of one fixed strong D-Hopf witness under entrywise-continuous perturbations. -/
def StrongDHopfPerturbationTarget : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (W : StrongDHopfWitness M)
    (A : ℝ → Matrix n n ℝ),
    A 0 = M →
    (∀ i j, ContinuousAt (fun ε => A ε i j) 0) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          Nonempty (StrongDHopfWitness (A ε))

end Matrix

namespace Matrix

/-- Concrete implementation of the formerly abstract finite-matrix openness dependency. -/
theorem strongDHopfPerturbationTarget_proved : StrongDHopfPerturbationTarget := by
  intro n _ _ M W A hA0 hcont
  exact strongDHopfPerturbation_exists M W A hA0 hcont

end Matrix

namespace CRNT
namespace Network

/-- Matrix openness immediately closes the epsilon child-selection perturbation theorem because the
selected block is continuous and equals the child-selection matrix at zero. -/
theorem childSelectionDHopfPerturbation_of_matrixOpenness
    (hopen : Matrix.StrongDHopfPerturbationTarget) :
    ChildSelectionDHopfPerturbationTarget := by
  intro T _ _ N I _ _ C hcore
  obtain ⟨W⟩ := hcore
  let A : ℝ → Matrix I I ℝ :=
    fun ε => C.selectedSymbolicBlock (C.epsilonReactivity ε)
  have hA0 : A 0 = C.matrix := by
    simpa [A] using C.selectedSymbolicBlock_epsilon_zero
  have hcont : ∀ i j, ContinuousAt (fun ε => A ε i j) 0 := by
    intro i j
    simpa [A] using (C.continuous_selectedSymbolicBlock_apply i j).continuousAt
  exact hopen C.matrix W A hA0 hcont

end Network
end CRNT
