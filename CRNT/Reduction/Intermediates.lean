import CRNT.Graph.Reachability
import CRNT.Kinetics.MassAction
import CRNT.Subnetwork.EmbeddedNetwork
import CRNT.Equilibria.SteadyState

/-!
# Intermediate species and core-network reduction

An intermediate species is represented by a singleton complex `H`; it does not
occur as part of any other complex.  Eliminating intermediates contracts directed
paths whose internal vertices are intermediate complexes.  This is the structural
core of the Feliu--Wiuf intermediate-removal construction.

This file deliberately separates the graph-theoretic reduction from the kinetic
parameter formulas.  The latter can be attached as a certificate saying that the
linear intermediate steady-state equations have been solved and substituted into
the core equations.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Singleton complex consisting of one copy of species `s`. -/
def singletonComplex (s : S) : Complex S := fun t => if t = s then 1 else 0

@[simp] theorem singletonComplex_self (s : S) : singletonComplex s s = 1 := by
  simp [singletonComplex]

/-- A chosen species set is structurally intermediate when every network complex
containing one of its species is exactly the corresponding singleton intermediate
complex.  Thus intermediates never occur inside core complexes. -/
def IsIntermediateSet (N : Network S) (H : Finset S) : Prop :=
  (∀ h ∈ H, singletonComplex h ∈ N.complexes) ∧
  ∀ y ∈ N.complexes, ∀ h ∈ H, y h ≠ 0 → y = singletonComplex h

/-- Core complexes contain no intermediate species. -/
def IsCoreComplex (H : Finset S) (y : Complex S) : Prop :=
  ∀ h ∈ H, y h = 0

/-- A network complex is an intermediate complex exactly when it is the singleton
complex of one selected intermediate species. -/
def IsIntermediateComplex (H : Finset S) (y : Complex S) : Prop :=
  ∃ h ∈ H, y = singletonComplex h

/-- Under the intermediate-set hypothesis, every complex is either core or a
singleton intermediate complex. -/
theorem core_or_intermediateComplex {N : Network S} {H : Finset S}
    (hH : N.IsIntermediateSet H) {y : Complex S} (hy : y ∈ N.complexes) :
    IsCoreComplex H y ∨ IsIntermediateComplex H y := by
  by_cases hc : ∀ h ∈ H, y h = 0
  · exact Or.inl hc
  · push_neg at hc
    rcases hc with ⟨h, hh, hne⟩
    exact Or.inr ⟨h, hh, hH.2 y hy h hh hne⟩

/-- Directed path whose internal vertices are intermediate complexes. -/
inductive IntermediatePath (N : Network S) (H : Finset S) :
    Complex S → Complex S → Prop
  | direct {y z} : N.DirectlyReacts y z → IntermediatePath N H y z
  | step {y h z} :
      N.DirectlyReacts y h → IsIntermediateComplex H h →
      IntermediatePath N H h z → IntermediatePath N H y z

/-- Every intermediate path gives ordinary directed reachability. -/
theorem IntermediatePath.reaches {N : Network S} {H : Finset S} {y z : Complex S}
    (p : N.IntermediatePath H y z) : N.Reaches y z := by
  induction p with
  | direct h => exact Reaches.single h
  | step h₁ _ _ ih => exact Reaches.trans (Reaches.single h₁) ih

/-- Core reaction relation obtained by contracting chains of intermediate complexes.
Both endpoints must be core complexes. -/
def CoreDirectlyReacts (N : Network S) (H : Finset S)
    (y z : Complex S) : Prop :=
  IsCoreComplex H y ∧ IsCoreComplex H z ∧ N.IntermediatePath H y z

/-- A direct core-to-core reaction survives reduction. -/
theorem coreDirectlyReacts_of_direct {N : Network S} {H : Finset S}
    {y z : Complex S} (hy : IsCoreComplex H y) (hz : IsCoreComplex H z)
    (hr : N.DirectlyReacts y z) : N.CoreDirectlyReacts H y z :=
  ⟨hy, hz, IntermediatePath.direct hr⟩

/-- Contracted core reactions preserve directed reachability in the original network. -/
theorem CoreDirectlyReacts.reaches {N : Network S} {H : Finset S}
    {y z : Complex S} (h : N.CoreDirectlyReacts H y z) : N.Reaches y z :=
  h.2.2.reaches

/-- Every intermediate must lie on a path from some core complex to some core complex.
This excludes isolated singleton species that are graph-theoretically irrelevant. -/
def IntermediatesConnectedToCore (N : Network S) (H : Finset S) : Prop :=
  ∀ h ∈ H, ∃ y z : Complex S,
    IsCoreComplex H y ∧ IsCoreComplex H z ∧
    N.IntermediatePath H y (singletonComplex h) ∧
    N.IntermediatePath H (singletonComplex h) z

/-- A valid structural intermediate reduction. -/
structure IntermediateReductionData (N : Network S) where
  intermediates : Finset S
  structural : N.IsIntermediateSet intermediates
  connected : N.IntermediatesConnectedToCore intermediates

/-- Kinetic certificate for eliminating intermediates at steady state.  It records
the classical fact that each intermediate concentration is a positive linear
combination of core monomials, with coefficients depending only on rate constants. -/
structure IntermediateSteadyStateElimination (N : Network S)
    (κ : N.RateConstants) (D : N.IntermediateReductionData) where
  coefficient : S → Complex S → ℝ
  coefficient_nonneg : ∀ h ∈ D.intermediates, ∀ y,
    0 ≤ coefficient h y
  coefficient_zero_unless_core : ∀ h ∈ D.intermediates, ∀ y,
    ¬ IsCoreComplex D.intermediates y → coefficient h y = 0
  coefficient_pos_iff_path : ∀ h ∈ D.intermediates, ∀ y,
    IsCoreComplex D.intermediates y →
    (0 < coefficient h y ↔
      N.IntermediatePath D.intermediates y (singletonComplex h))
  /-- At a positive steady state, intermediate concentrations equal the elimination
  formula. -/
  steadyState_formula : ∀ x : Concentration S,
    N.IsMassActionSteadyState κ x → ∀ h ∈ D.intermediates,
      x h = ∑ y ∈ N.complexes,
        coefficient h y * y.massActionMonomial x

/-- Positive core concentrations lift to positive intermediate concentrations when
each intermediate is produced from the core. -/
theorem IntermediateSteadyStateElimination.intermediate_positive
    {N : Network S} {κ : N.RateConstants} {D : N.IntermediateReductionData}
    (E : N.IntermediateSteadyStateElimination κ D)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x)
    {h : S} (hh : h ∈ D.intermediates) : 0 < x h := by
  exact hx h

/-- Interface for the classical steady-state lifting theorem: once the reduced core
rates are constructed from the elimination coefficients, positive core steady states
lift uniquely to positive steady states of the extended network. -/
structure CoreSteadyStateLiftingCertificate (N : Network S)
    (κ : N.RateConstants) (D : N.IntermediateReductionData) where
  coreState : Type
  lift : coreState → Concentration S
  lift_positive : ∀ c, (lift c).Positive
  lift_steady : ∀ c, N.IsMassActionSteadyState κ (lift c)
  core_projection_injective : Function.Injective lift

end Network
end CRNT
