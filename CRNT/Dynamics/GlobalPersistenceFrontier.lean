import CRNT.Dynamics.GlobalPersistenceCertificates
import CRNT.Decision.StrictConeRealization
import CRNT.Dynamics.TierPersistence
import CRNT.Dynamics.TierDirectionFeasibility
import CRNT.Dynamics.SingleLinkageStructure
import CRNT.Dynamics.KnownGlobalPersistenceClasses

/-!
# Global-persistence theorem frontier

Published global claims that are not yet discharged by this Lean development are represented here as
ordinary propositions.  This module is deliberately **not** imported by `CRNT.lean`.

There are no axioms and no `sorry`s.  A downstream theorem can use a frontier claim only by receiving
an actual proof of it.

The distinction between bounded-orbit omega persistence, uniform coordinate persistence, and the
repository's stronger `PersistentFrom` certificate is explicit here.  In particular the direct
no-drainable theorem is no longer a frontier item at omega-persistence strength.
-/

namespace CRNT

open scoped NNReal

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Standard strongly-endotactic permanence theorem, using the audited stoichiometric trigger. -/
def StrongEndotacticStdPermanenceClaim (N : Network S) : Prop :=
  N.StronglyEndotacticStd → N.StructurallyPermanent

/-- Legacy-definition form of strongly-endotactic permanence. -/
def StrongEndotacticPermanenceClaim (N : Network S) : Prop :=
  N.StronglyEndotactic → N.StructurallyPermanent

/-- **Completed structural bridge.** Weak reversibility plus one linkage class is strongly
endotactic in the standard stoichiometric sense.  Kept under the old public name as a theorem
rather than a frontier proposition. -/
theorem singleLinkageStrongEndotactic {N : Network S}
    (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass) : N.StronglyEndotacticStd :=
  hwr.stronglyEndotacticStd_of_singleLinkageClass hslc

/-- Single-linkage weakly-reversible standard permanence theorem. -/
def SingleLinkagePermanenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.SingleLinkageClass → N.StructurallyPermanent

/-- Single-linkage weakly-reversible ordinary persistence theorem. -/
def SingleLinkagePersistenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.SingleLinkageClass → N.StructurallyPersistentStd

/-- Stronger single-linkage claim at the repository's compact-confinement level.  This is not the
standard published persistence theorem and is intentionally named separately. -/
def SingleLinkageStrongPersistenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.SingleLinkageClass → N.StructurallyPersistent

/-- Pure finite-dimensional tier lemma: every transversal tier sequence makes its explicit
rational direction system real-feasible.  `TierDirectionFeasibility` proves that this is enough to
construct the exact linear tier witness.  This is now the smallest structural obligation behind
the forward strongly-endotactic/tier characterization. -/
def TierDirectionSystemFeasibilityClaim (N : Network S) : Prop :=
  N.EveryTransversalTierDirectionSystemFeasible

/-- Remaining hard half of the published characterization: every standard strongly-endotactic
network is tier descending.  The reverse implication is now proved constructively from the
explicit exponential direction sequence in `TierPersistence`. -/
def StrongEndotacticTierDescendingClaim (N : Network S) : Prop :=
  N.StronglyEndotacticStd → N.TierDescending

/-- The finite system-feasibility theorem discharges the full forward tier characterization. -/
theorem strongEndotacticTierDescending_of_systemFeasibility (N : Network S)
    (h : N.TierDirectionSystemFeasibilityClaim) : N.StrongEndotacticTierDescendingClaim :=
  fun hse => hse.tierDescending_of_systemFeasibility h

/-- Once the remaining forward tier claim is supplied, the full published characterization follows
using the already-proved reverse implication. -/
theorem stronglyEndotacticStd_iff_tierDescending_of_forwardClaim (N : Network S)
    (hforward : N.StrongEndotacticTierDescendingClaim) :
    N.StronglyEndotacticStd ↔ N.TierDescending :=
  ⟨hforward, TierDescending.stronglyEndotacticStd⟩

/-- Deterministic tier theorem upgrading tier descent to structural permanence. -/
def TierDescendingPermanenceClaim (N : Network S) : Prop :=
  N.TierDescending → N.StructurallyPermanent

/-- Frontier alias for the flux-cone core of the Deshpande--Gopalkrishnan
minimal-critical-siphon dichotomy.  The stable proposition lives in `SiphonAutocatalysis`; only
its proof remains frontier mathematics. -/
abbrev MinimalCriticalSiphonFluxDichotomyClaim (N : Network S) : Prop :=
  N.MinimalCriticalSiphonFluxDichotomy

/-- Frontier alias for the finite-pathway minimal-critical-siphon dichotomy. -/
abbrev MinimalCriticalSiphonDichotomyClaim (N : Network S) : Prop :=
  N.MinimalCriticalSiphonDichotomy

/-- Stronger, unbounded-orbit coordinate-lower-bound version of the no-drainable theorem.  The
direct theorem proved in the stable library establishes bounded-orbit omega persistence.

This proposition is **false** in general: `X → 2X`, `X + Y → X`, `0 → Y` has no drainable siphon
and an explicit global mass-action flow, along which `y` is not bounded below by a positive
constant (`CRNT.Examples.NoDrainableUnbounded.claim_false`). -/
def NoDrainableSiphonUniformPersistenceClaim (N : Network S) : Prop :=
  N.HasNoDrainableSiphon → N.StructurallyUniformlyPersistent

/-- **Completed theorem:** no drainable siphons imply structural bounded-orbit omega persistence. -/
theorem noDrainableSiphonOmegaPersistence (N : Network S) :
    N.HasNoDrainableSiphon → N.StructurallyOmegaPersistent :=
  N.structurallyBoundaryOmegaExcludedStd_of_hasNoDrainableSiphon

/-- **Completed theorem:** weak reversibility plus absence of self-replicable siphons implies
structural bounded-orbit omega persistence. -/
theorem nonautocatalyticWROmegaPersistence (N : Network S) :
    N.WeaklyReversible → N.HasNoSelfReplicableSiphon → N.StructurallyOmegaPersistent := by
  intro hwr hnosr
  exact N.structurallyBoundaryOmegaExcludedStd_of_weaklyReversible_hasNoSelfReplicableSiphon
    hwr hnosr

/-- Stronger uniform-persistence form of the non-autocatalytic theorem. -/
def NonautocatalyticWRUniformPersistenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.HasNoSelfReplicableSiphon → N.StructurallyUniformlyPersistent

/-- If the stronger no-drainable uniform theorem is supplied, the corresponding weakly-reversible
non-autocatalytic uniform theorem follows formally. -/
theorem nonautocatalyticWRUniformPersistence_of_noDrainable (N : Network S)
    (hnd : N.NoDrainableSiphonUniformPersistenceClaim) :
    N.NonautocatalyticWRUniformPersistenceClaim := by
  intro hwr hnosr
  exact hnd (N.hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon'
    hwr hnosr)

/-- The classical deterministic Persistence Conjecture at ordinary CRNT persistence strength. -/
def PersistenceConjecture (N : Network S) : Prop :=
  N.WeaklyReversible → N.StructurallyPersistentStd

/-- A genuinely stronger conjectural statement using the repository's compact-interior
`PersistentFrom` certificate.  This must not be confused with the classical conjecture. -/
def PersistenceConjectureStrong (N : Network S) : Prop :=
  N.WeaklyReversible → N.StructurallyPersistent

/-- The general Persistence Conjecture at the omega-limit boundary-exclusion level, under the
bounded/genuine-flow hypotheses built into `BoundaryOmegaExcluded`. -/
def PersistenceConjectureOmega (N : Network S) : Prop :=
  N.WeaklyReversible → N.StructurallyBoundaryOmegaExcluded

/-- The strong compact-confinement conjecture implies ordinary persistence. -/
theorem persistenceConjectureStrong_implies_standard {N : Network S}
    (h : N.PersistenceConjectureStrong) : N.PersistenceConjecture :=
  fun hwr => (h hwr).toStd

/-- A proof of the ordinary persistence conjecture specializes to the single-linkage theorem. -/
theorem persistenceConjecture_implies_singleLinkage {N : Network S}
    (h : N.PersistenceConjecture) : N.SingleLinkagePersistenceClaim :=
  fun hwr _hslc => h hwr

/-- A proof of the stronger conjecture specializes to the stronger single-linkage statement. -/
theorem persistenceConjectureStrong_implies_singleLinkage {N : Network S}
    (h : N.PersistenceConjectureStrong) : N.SingleLinkageStrongPersistenceClaim :=
  fun hwr _hslc => h hwr

/-- Existing no-critical-siphon machinery discharges the corresponding structural omega-limit
claim unconditionally. -/
theorem noCriticalSiphon_globalOmegaPersistence (N : Network S)
    (hncs : N.HasNoCriticalSiphon) : N.StructurallyBoundaryOmegaExcluded :=
  N.structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon hncs

/-- Once the tier characterization and tier permanence theorem are supplied, standard strong
endotacticity gives structural permanence by pure composition. -/
theorem structurallyPermanent_of_tierClaims (N : Network S)
    (hforward : N.StrongEndotacticTierDescendingClaim)
    (hperm : N.TierDescendingPermanenceClaim)
    (hse : N.StronglyEndotacticStd) : N.StructurallyPermanent :=
  hperm (hforward hse)

/-- The published single-linkage permanence theorem is a formal corollary of the already-proved
single-linkage strong-endotactic bridge plus strongly-endotactic permanence. -/
theorem singleLinkagePermanence_of_strongEndotacticPermanence (N : Network S)
    (hperm : N.StrongEndotacticStdPermanenceClaim) : N.SingleLinkagePermanenceClaim := by
  intro hwr hslc
  exact hperm (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc)

/-- Single-linkage permanence immediately implies ordinary single-linkage persistence. -/
theorem singleLinkagePersistence_of_permanence (N : Network S)
    (hperm : N.SingleLinkagePermanenceClaim) : N.SingleLinkagePersistenceClaim := by
  intro hwr hslc
  exact (hperm hwr hslc).toPersistentStd

/-- Combining the two preceding reductions: strongly-endotactic permanence is the only missing
analytic ingredient for the ordinary single-linkage persistence theorem. -/
theorem singleLinkagePersistence_of_strongEndotacticPermanence (N : Network S)
    (hperm : N.StrongEndotacticStdPermanenceClaim) : N.SingleLinkagePersistenceClaim :=
  N.singleLinkagePersistence_of_permanence
    (N.singleLinkagePermanence_of_strongEndotacticPermanence hperm)

/-- If the stronger single-linkage persistence theorem has been established for `N`, the existing
GAC reduction consumes it without an orbit-specific persistence premise at the call site.  Ordinary
persistence alone is intentionally insufficient for this existing GAC API. -/
theorem singleLinkageClass_gac_of_strongGlobalClaim (N : Network S)
    (hglobal : N.SingleLinkageStrongPersistenceClaim) (hwr : N.WeaklyReversible)
    (hslc : N.SingleLinkageClass) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit Filter.atTop ϕ {x₀} = {xstar} := by
  have hpers : N.StructurallyPersistent := hglobal hwr hslc
  exact N.gac_of_structurallyPersistent hwr hpers κ hxs hcb hx0 hx0compat

end Network
end CRNT
