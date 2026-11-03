import CRNT.Dynamics.GlobalPersistenceCertificates
import CRNT.Geometry.EndotacticGlobal
import CRNT.Geometry.EndotacticStandard
import CRNT.Stoich.Subspace

/-!
# Established low-dimensional global-persistence classes

This module records precise proposition-level interfaces for established global results that are
not yet proved in the Lean development.  It is intended for the explicit theorem-frontier module,
not the default trusted import surface.

The statements are kept at the exact strength supported by the literature:

* Pantea's two-dimensional stoichiometric-subspace result assumes bounded positive trajectories and
  concludes persistence for weakly reversible systems;
* Craciun--Nazarov--Pantea prove permanence for two-*species* endotactic mass-action systems, hence
  in particular for two-species weakly reversible systems.

No proposition in this file is an axiom: downstream code must receive a proof before using it.
-/

open scoped NNReal Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every positive trajectory of one genuine mass-action flow stays in some compact set.  The
compact set may depend on the initial condition; this captures exactly the trajectory-boundedness
hypothesis needed by the two-dimensional persistence theorem without silently strengthening it to
permanence. -/
def PositiveTrajectoriesBoundedForFlow (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ →
    ∀ x₀ : Concentration S, x₀.Positive →
      ∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K

/-- Boundedness of all positive trajectories for fixed rates, independent of flow realization. -/
def PositiveTrajectoriesBoundedForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
    N.PositiveTrajectoriesBoundedForFlow κ ϕ γ

/-- Structural trajectory boundedness: every positive-rate mass-action system has bounded positive
trajectories. -/
def StructurallyBoundedPositiveTrajectories (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.PositiveTrajectoriesBoundedForRates κ

/-- Pantea's weakly-reversible two-dimensional-stoichiometric-subspace persistence theorem, lifted
to structural quantifiers by explicitly requiring bounded positive trajectories for every rate
vector. -/
def TwoDimensionalWRBoundedPersistenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.stoichRank = 2 →
    N.StructurallyBoundedPositiveTrajectories → N.StructurallyPersistentStd

/-- Craciun--Nazarov--Pantea two-species endotactic permanence theorem.  `Fintype.card S = 2`
means ambient species dimension two, which is intentionally distinct from stoichiometric rank two.

The hypothesis is the standard (`w`-essential) notion `EndotacticStd`. An earlier version used the
library's weaker `Endotactic` and was false: `0 ⇌ X₀`, `X₁ → 0` satisfies `Endotactic` but
`x₁ → 0` (`CRNT.Examples.WeakEndotactic.weakTwoSpeciesEndotacticPermanence_false`). -/
def TwoSpeciesEndotacticPermanenceClaim (N : Network S) : Prop :=
  Fintype.card S = 2 → N.EndotacticStd → N.StructurallyPermanent

/-- Two-species weakly-reversible permanence, stated independently for convenient downstream use. -/
def TwoSpeciesWRPermanenceClaim (N : Network S) : Prop :=
  Fintype.card S = 2 → N.WeaklyReversible → N.StructurallyPermanent

/-- The weakly-reversible two-species theorem follows formally from the stronger endotactic
permanence theorem because weak reversibility implies endotacticity in the library. -/
theorem twoSpeciesWRPermanence_of_endotacticPermanence (N : Network S)
    (h : N.TwoSpeciesEndotacticPermanenceClaim) : N.TwoSpeciesWRPermanenceClaim := by
  intro hcard hwr
  exact h hcard hwr.endotacticStd

/-- Two-species weakly-reversible permanence implies ordinary structural persistence. -/
theorem twoSpeciesWRPersistence_of_permanence (N : Network S)
    (h : N.TwoSpeciesWRPermanenceClaim) (hcard : Fintype.card S = 2)
    (hwr : N.WeaklyReversible) : N.StructurallyPersistentStd :=
  (h hcard hwr).toPersistentStd

/-! ## 2026 first-order endotactic frontier -/

/-- Every occurring complex has molecularity at most one.  This is the natural finite-network
encoding of a first-order reaction graph: its complexes are `0` or single-species complexes. -/
def IsFirstOrder (N : Network S) : Prop :=
  ∀ c : Complex S, c ∈ N.complexes → (∑ s : S, c s) ≤ 1

/-- Persistence-level corollary of the 2026 first-order endotactic global-stability theorem.  The
published theorem is stronger (WR0 realization plus a unique positive exponentially globally
attracting equilibrium in each positive class); the current library lacks a general dynamical-
realization API, so this interface records only the global persistence consequence that composes
with the present persistence framework. -/
def FirstOrderEndotacticPersistenceClaim (N : Network S) : Prop :=
  N.IsFirstOrder → N.EndotacticStd → N.StructurallyPersistentStd

end Network
end CRNT
