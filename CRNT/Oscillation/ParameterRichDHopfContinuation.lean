import CRNT.Oscillation.ReactivityScaling

/-!
# Parameter-rich D-Hopf continuation

This module composes the finite child-selection construction with the operational
`SteadyStateParameterRichFamily` interface.

Starting from a D-Hopf child selection:

1. `epsilonReactivity` produces a fully admissible CRN reactivity matrix;
2. positive column scaling lifts the D-Hopf stable/unstable diagonals to the full CRN;
3. `SupportsSmoothReactivityPaths` realizes the straight path between those endpoint reactivities
   by a coherent smooth family of kinetics at one fixed positive steady state.

Consequently the remaining theorem is purely dynamical: a smooth parameter-rich kinetic path whose
rank-relevant symbolic Jacobian contains the certified D-Hopf block must generate a periodic orbit.
The CRN combinatorics and endpoint realization are no longer part of that frontier.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A concrete admissible reactivity matrix carrying a selected strong D-Hopf block. -/
structure IndexedDHopfReactivityWitness (N : Network S) : Type 1 where
  I : Type
  decI : DecidableEq I
  finI : Fintype I
  selection : @IndexedChildSelection S _ _ N I decI finI
  reactivity : N.ReactivityMatrix
  admissible : N.IsReactivityMatrix reactivity
  dhopf : Nonempty (Matrix.StrongDHopfWitness
    (@IndexedChildSelection.selectedSymbolicBlock S _ _ N I decI finI selection reactivity))

attribute [instance] IndexedDHopfReactivityWitness.decI
attribute [instance] IndexedDHopfReactivityWitness.finI

/-- Build a concrete admissible D-Hopf reactivity witness from an indexed child-selection D-Hopf
certificate using the small-positive-epsilon perturbation theorem. -/
noncomputable def indexedDHopfReactivityWitnessOfCore
    (hopen : ChildSelectionDHopfPerturbationTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (N : Network S) (C : N.IndexedChildSelection I)
    (hcore : Nonempty (Matrix.StrongDHopfWitness C.matrix)) :
    N.IndexedDHopfReactivityWitness := by
  let hex := exists_admissible_reactivity_with_strongDHopfBlock hopen N C hcore
  let R := Classical.choose hex
  have hspec := Classical.choose_spec hex
  exact
    { I := I
      decI := inferInstance
      finI := inferInstance
      selection := C
      reactivity := R
      admissible := hspec.1
      dhopf := hspec.2 }

namespace IndexedDHopfReactivityWitness

variable {N : Network S}

/-- Chosen strong D-Hopf proof object carried by the witness. -/
noncomputable def chosenDHopf (W : N.IndexedDHopfReactivityWitness) :
    Matrix.StrongDHopfWitness
      (W.selection.selectedSymbolicBlock W.reactivity) :=
  Classical.choice W.dhopf

/-- Lift the selected D-Hopf stable/unstable diagonal scalings to two full admissible reactivities. -/
noncomputable def endpoints (W : N.IndexedDHopfReactivityWitness) :=
  W.selection.liftDHopfReactivityEndpoints W.reactivity W.admissible W.chosenDHopf

/-- A smooth kinetic realization of the lifted D-Hopf endpoint path at one positive steady state. -/
structure SmoothKineticContinuation
    (W : N.IndexedDHopfReactivityWitness)
    (F : N.SteadyStateParameterRichFamily) (x : Concentration S) : Type where
  positiveState : x.Positive
  realization : N.SmoothLinearReactivityRealization F x
    W.endpoints.stableReactivity W.endpoints.unstableReactivity

/-- Parameter-rich smooth-path support constructs the required kinetic continuation at every chosen
positive state. -/
theorem exists_smoothKineticContinuation
    (W : N.IndexedDHopfReactivityWitness)
    (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (x : Concentration S) (hx : x.Positive) :
    Nonempty (W.SmoothKineticContinuation F x) := by
  obtain ⟨P⟩ := hpaths x hx
    W.endpoints.stableReactivity W.endpoints.unstableReactivity
    W.endpoints.stableAdmissible W.endpoints.unstableAdmissible
  exact ⟨{ positiveState := hx, realization := P }⟩

end IndexedDHopfReactivityWitness

/-- Exact remaining nonlinear theorem for the parameter-rich route.

All finite CRN algebra is explicit in the inputs: `W` supplies an admissible symbolic Jacobian with
an actual selected D-Hopf block, and `P` supplies the coherent smooth kinetic path realizing the
stable/unstable endpoint reactivities at a fixed positive steady state.  Symbolic nondegeneracy is
retained for conservation-law/rank reduction.  A proof of this proposition is therefore the global
D-Hopf/periodic-orbit theorem itself. -/
def ParameterRichDHopfContinuationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T]
    (N : Network T) (F : N.SteadyStateParameterRichFamily)
    (W : N.IndexedDHopfReactivityWitness)
    (x : Concentration T) (P : W.SmoothKineticContinuation F x),
    N.IsSymbolicallyNondegenerate → N.ParameterRichOscillatoryCapacity F

/-- Consume the remaining D-Hopf theorem after all child-selection/reactivity construction is done. -/
theorem IndexedDHopfReactivityWitness.parameterRichOscillatoryCapacity
    {N : Network S} (hDHopf : ParameterRichDHopfContinuationTarget)
    (W : N.IndexedDHopfReactivityWitness)
    (F : N.SteadyStateParameterRichFamily)
    (x : Concentration S) (P : W.SmoothKineticContinuation F x)
    (hnd : N.IsSymbolicallyNondegenerate) :
    N.ParameterRichOscillatoryCapacity F :=
  hDHopf N F W x P hnd

/-- End-to-end indexed-core pipeline, leaving only the finite D-Hopf perturbation theorem and the
nonlinear parameter-rich D-Hopf theorem as explicit mathematical dependencies. -/
theorem parameterRichOscillatoryCapacity_of_indexed_strongDHopfCore
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (N : Network S) (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (hnd : N.IsSymbolicallyNondegenerate)
    (C : N.IndexedChildSelection I)
    (hcore : Nonempty (Matrix.StrongDHopfWitness C.matrix))
    (x : Concentration S) (hx : x.Positive) :
    N.ParameterRichOscillatoryCapacity F := by
  let W := indexedDHopfReactivityWitnessOfCore hopen N C hcore
  obtain ⟨P⟩ := W.exists_smoothKineticContinuation F hpaths x hx
  exact hDHopf N F W x P hnd

end Network
end CRNT
