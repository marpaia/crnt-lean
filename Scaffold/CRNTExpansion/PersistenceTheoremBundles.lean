import CRNT.Dynamics.GlobalPersistenceFrontier
import CRNT.Dynamics.TierDirectionProjection
import CRNT.Dynamics.PermanenceAssembly

/-!
# Published persistence/permanence kernels versus open conjectures

The 15-hole base has advanced beyond the earlier scaffold: the difficult structural direction

`StronglyEndotacticStd -> TierDescending`

is now an actual theorem (`StronglyEndotacticStd.tierDescending`).  Therefore the previous
finite-feasibility premise is no longer part of the permanence frontier.

The remaining strongly-endotactic permanence problem is analytic: turn tier descent into a
class-uniform compact interior absorbing set.  This file exposes that boundary in two equivalent
layers:

* `TierDescendingPermanenceClaim`, the published theorem-facing statement already present in the
  frontier module;
* `TierDescendingAbsorbingBoundsKernel`, a lower-level sufficient kernel matching the generic
  `PermanenceAssembly` API: eventual entry plus uniform forward coordinate bounds.

The general weakly-reversible Persistence Conjecture remains open and is not bundled as a theorem
kernel.
-/

namespace CRNT

open scoped NNReal

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Analytic kernel sufficient for the tier-descending permanence theorem.  For every rate vector,
genuine mass-action flow, positive compatibility class, and tier-descending network, it supplies a
set eventually reached by every positive orbit in the class together with uniform positive lower
and finite upper coordinate bounds thereafter. -/
def TierDescendingAbsorbingBoundsKernel (N : Network S) : Prop :=
  ∀ (κ : N.RateConstants) (ϕ : Flow ℝ≥0 (Concentration S))
      (γ : Concentration S → ℝ → Concentration S),
    N.IsMassActionFlow κ ϕ γ → N.TierDescending →
      ∀ xref : Concentration S, xref.Positive →
        ∃ Υ : Set (Concentration S),
          N.EveryPositiveClassOrbitEnters ϕ xref Υ ∧
            UniformForwardCoordinateBounds ϕ Υ

/-- The absorbing-bounds kernel discharges the theorem-facing tier-descending permanence claim by
the generic permanence assembly theorem. -/
theorem tierDescendingPermanence_of_absorbingBoundsKernel
    (N : Network S) (K : N.TierDescendingAbsorbingBoundsKernel) :
    N.TierDescendingPermanenceClaim := by
  intro htier κ ϕ γ hflow
  exact N.permanentForFlow_of_entry_and_uniform_bounds hflow
    (K κ ϕ γ hflow htier) hflow

/-- The single remaining kernel for the standard strongly-endotactic permanence route. -/
structure StrongEndotacticPermanenceKernels (N : Network S) : Prop where
  tierAbsorbingBounds : N.TierDescendingAbsorbingBoundsKernel

namespace StrongEndotacticPermanenceKernels

variable {N : Network S}

/-- The current core already supplies strongly-endotactic -> tier-descending, so the analytic
absorbing-bounds kernel alone assembles the published strongly-endotactic permanence theorem. -/
theorem stronglyEndotacticPermanence (K : N.StrongEndotacticPermanenceKernels) :
    N.StrongEndotacticStdPermanenceClaim := by
  intro hse
  exact (N.tierDescendingPermanence_of_absorbingBoundsKernel K.tierAbsorbingBounds)
    hse.tierDescending

end StrongEndotacticPermanenceKernels

/-- Literature-backed permanence/persistence kernels still awaiting direct Lean proofs.  The
strongly-endotactic field has now been reduced to the analytic absorbing-bounds statement above. -/
structure PublishedPersistenceKernels (N : Network S) : Prop where
  stronglyEndotactic : N.StrongEndotacticPermanenceKernels
  twoDimensionalWRBoundedPersistence : N.TwoDimensionalWRBoundedPersistenceClaim
  twoSpeciesEndotacticPermanence : N.TwoSpeciesEndotacticPermanenceClaim
  firstOrderEndotacticPersistence : N.FirstOrderEndotacticPersistenceClaim

namespace PublishedPersistenceKernels

variable {N : Network S}

/-- Strongly-endotactic permanence supplies the published single-linkage permanence corollary
through the already-formalized single-linkage structural bridge. -/
theorem singleLinkagePermanence (K : N.PublishedPersistenceKernels) :
    N.SingleLinkagePermanenceClaim :=
  N.singleLinkagePermanence_of_strongEndotacticPermanence
    K.stronglyEndotactic.stronglyEndotacticPermanence

/-- The same kernel yields ordinary single-linkage persistence. -/
theorem singleLinkagePersistence (K : N.PublishedPersistenceKernels) :
    N.SingleLinkagePersistenceClaim :=
  N.singleLinkagePersistence_of_strongEndotacticPermanence
    K.stronglyEndotactic.stronglyEndotacticPermanence

/-- Two-species weakly-reversible permanence is a formal corollary of the published endotactic
permanence theorem. -/
theorem twoSpeciesWRPermanence (K : N.PublishedPersistenceKernels) :
    N.TwoSpeciesWRPermanenceClaim :=
  N.twoSpeciesWRPermanence_of_endotacticPermanence K.twoSpeciesEndotacticPermanence

end PublishedPersistenceKernels

end Network
end CRNT
