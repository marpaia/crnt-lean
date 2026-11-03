import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.GlobalPermanence
import CRNT.Dynamics.SingleLinkageStructure
import CRNT.Decision.StrictConeRealization
import CRNT.Dynamics.NoDrainableSiphonPersistence

/-!
# Proof-carrying global persistence certificates

Stable wrappers for completed global theorems.  Constructors in this module require genuine proofs;
there is no constructor from a heuristic or structural boolean alone.

The certificate hierarchy distinguishes three different strengths that should not be conflated:

* `StandardPersistenceCertificate`: the historical coordinate-lower-bound (uniform-persistence)
  certificate;
* `GlobalPersistenceCertificate`: the repository's stronger compact-interior `PersistentFrom`
  certificate for every positive start and every rate vector;
* `GlobalPermanenceCertificate`: standard class-uniform permanence.

A permanence certificate always produces a standard persistence certificate.  A strong
`GlobalPersistenceCertificate` also produces a standard persistence certificate, but neither
conversion is reversed here.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Proof-carrying standard structural persistence certificate. -/
structure StandardPersistenceCertificate (N : Network S) : Prop where
  sound : N.StructurallyPersistentStd

/-- Extract standard structural persistence. -/
theorem StandardPersistenceCertificate.structurallyPersistentStd {N : Network S}
    (c : N.StandardPersistenceCertificate) : N.StructurallyPersistentStd :=
  c.sound

/-- Package any independently proved standard structural persistence theorem. -/
def StandardPersistenceCertificate.ofProof (N : Network S) (h : N.StructurallyPersistentStd) :
    N.StandardPersistenceCertificate :=
  ⟨h⟩

/-- A proof-carrying strong structural persistence certificate. -/
structure GlobalPersistenceCertificate (N : Network S) : Prop where
  sound : N.StructurallyPersistent

/-- Extract the theorem carried by a strong persistence certificate. -/
theorem GlobalPersistenceCertificate.structurallyPersistent {N : Network S}
    (c : N.GlobalPersistenceCertificate) : N.StructurallyPersistent :=
  c.sound

/-- Package any independently proved structural persistence theorem. -/
def GlobalPersistenceCertificate.ofProof (N : Network S) (h : N.StructurallyPersistent) :
    N.GlobalPersistenceCertificate :=
  ⟨h⟩

/-- A strong compact-interior certificate implies ordinary CRNT persistence. -/
def GlobalPersistenceCertificate.toStandard {N : Network S}
    (c : N.GlobalPersistenceCertificate) : N.StandardPersistenceCertificate :=
  ⟨c.sound.toStd⟩

/-- Fully proved constructor for the deficiency-zero/no-critical-siphon structural class. -/
def GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (hncs : N.HasNoCriticalSiphon) :
    N.GlobalPersistenceCertificate :=
  ⟨N.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon hwr hδ hncs⟩

/-- The same completed class, exposed directly at standard-persistence strength. -/
def StandardPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (hncs : N.HasNoCriticalSiphon) :
    N.StandardPersistenceCertificate :=
  (GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon N hwr hδ hncs).toStandard

/-- Proof-carrying certificate for the clean bounded-orbit omega-persistence property.  This is the
preferred certificate for ordinary CRNT persistence statements that are proved by excluding
boundary omega-limit points. -/
structure OmegaPersistenceCertificate (N : Network S) : Prop where
  sound : N.StructurallyOmegaPersistent

/-- Extract structural bounded-orbit omega persistence. -/
theorem OmegaPersistenceCertificate.structurallyOmegaPersistent {N : Network S}
    (c : N.OmegaPersistenceCertificate) : N.StructurallyOmegaPersistent :=
  c.sound

/-- Package any independently proved structural omega-persistence theorem. -/
def OmegaPersistenceCertificate.ofProof (N : Network S) (h : N.StructurallyOmegaPersistent) :
    N.OmegaPersistenceCertificate :=
  ⟨h⟩

/-- Uniform persistence implies omega persistence. -/
def StandardPersistenceCertificate.toOmega {N : Network S}
    (c : N.StandardPersistenceCertificate) : N.OmegaPersistenceCertificate :=
  ⟨c.sound.toBoundaryOmegaExcludedStd⟩

/-- **Completed global theorem:** absence of drainable siphons gives structural omega persistence,
with no weak-reversibility, deficiency, or minimal-critical-siphon assumption. -/
def OmegaPersistenceCertificate.ofNoDrainableSiphon (N : Network S)
    (h : N.HasNoDrainableSiphon) : N.OmegaPersistenceCertificate :=
  ⟨N.structurallyBoundaryOmegaExcludedStd_of_hasNoDrainableSiphon h⟩

/-- **Completed non-autocatalytic weakly-reversible theorem.** -/
def OmegaPersistenceCertificate.ofWeaklyReversibleNoSelfReplicable (N : Network S)
    (hwr : N.WeaklyReversible) (h : N.HasNoSelfReplicableSiphon) :
    N.OmegaPersistenceCertificate :=
  ⟨N.structurallyBoundaryOmegaExcludedStd_of_weaklyReversible_hasNoSelfReplicableSiphon hwr h⟩

/-- Proof-carrying certificate for the older technical structural omega-limit interface. -/
structure BoundaryOmegaCertificate (N : Network S) : Prop where
  sound : N.StructurallyBoundaryOmegaExcluded

/-- Extract the theorem carried by a boundary-omega certificate. -/
theorem BoundaryOmegaCertificate.structurallyBoundaryOmegaExcluded {N : Network S}
    (c : N.BoundaryOmegaCertificate) : N.StructurallyBoundaryOmegaExcluded :=
  c.sound

/-- No critical siphon produces a fully proved global boundary-omega persistence certificate. -/
def BoundaryOmegaCertificate.ofNoCriticalSiphon (N : Network S)
    (h : N.HasNoCriticalSiphon) : N.BoundaryOmegaCertificate :=
  ⟨N.structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon h⟩

/-- Weak reversibility plus the finite minimal-critical-siphon theorem turns absence of
self-replicable siphons into a fully proved omega-limit boundary-exclusion certificate.  The two
remaining explicit input `MinimalCriticalSiphonDichotomy` is the genuine finite sign theorem;
strict real-flux realization is now proved unconditionally in `StrictConeRealization`. -/
def BoundaryOmegaCertificate.ofWeaklyReversibleNoSelfReplicable (N : Network S)
    (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.BoundaryOmegaCertificate :=
  ⟨N.structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoSelfReplicableSiphon'
    hdich hwr hnosr⟩

/-- Dual certificate constructor for weakly reversible networks with no drainable siphon. -/
def BoundaryOmegaCertificate.ofWeaklyReversibleNoDrainable (N : Network S)
    (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnd : N.HasNoDrainableSiphon) :
    N.BoundaryOmegaCertificate :=
  ⟨N.structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoDrainableSiphon'
    hdich hwr hnd⟩

/-- In deficiency zero, the same structural hypotheses upgrade all the way to the repository's
strong compact-interior persistence certificate because the derived `HasNoCriticalSiphon` can be
fed into the already-proved deficiency-zero persistence theorem. -/
def GlobalPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoSelfReplicable
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero)
    (hnosr : N.HasNoSelfReplicableSiphon) : N.GlobalPersistenceCertificate :=
  GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon N hwr hδ
    (N.hasNoCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon'
      hdich hwr hnosr)

/-- Deficiency-zero/no-drainable analogue of the preceding strong certificate. -/
def GlobalPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoDrainable
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero)
    (hnd : N.HasNoDrainableSiphon) : N.GlobalPersistenceCertificate :=
  GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon N hwr hδ
    (N.hasNoCriticalSiphon_of_weaklyReversible_hasNoDrainableSiphon'
      hdich hwr hnd)

/-- Standard-persistence projection of the non-autocatalytic deficiency-zero certificate. -/
def StandardPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoSelfReplicable
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero)
    (hnosr : N.HasNoSelfReplicableSiphon) : N.StandardPersistenceCertificate :=
  (GlobalPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoSelfReplicable N
    hdich hwr hδ hnosr).toStandard

/-- Standard-persistence projection of the no-drainable deficiency-zero certificate. -/
def StandardPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoDrainable
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero)
    (hnd : N.HasNoDrainableSiphon) : N.StandardPersistenceCertificate :=
  (GlobalPersistenceCertificate.ofDeficiencyZeroWeaklyReversibleNoDrainable N
    hdich hwr hδ hnd).toStandard

/-- Proof-carrying structural permanence certificate. -/
structure GlobalPermanenceCertificate (N : Network S) : Prop where
  sound : N.StructurallyPermanent

/-- Extract standard structural permanence. -/
theorem GlobalPermanenceCertificate.structurallyPermanent {N : Network S}
    (c : N.GlobalPermanenceCertificate) : N.StructurallyPermanent :=
  c.sound

/-- Package an independently proved structural permanence theorem. -/
def GlobalPermanenceCertificate.ofProof (N : Network S) (h : N.StructurallyPermanent) :
    N.GlobalPermanenceCertificate :=
  ⟨h⟩

/-- Standard permanence implies standard persistence. -/
def GlobalPermanenceCertificate.toStandardPersistence {N : Network S}
    (c : N.GlobalPermanenceCertificate) : N.StandardPersistenceCertificate :=
  ⟨c.sound.toPersistentStd⟩

/-- Proof-carrying structural certificate for the standard strong-endotactic predicate. -/
structure StrongEndotacticCertificate (N : Network S) : Prop where
  sound : N.StronglyEndotacticStd

/-- Package an independently proved strong-endotactic theorem. -/
def StrongEndotacticCertificate.ofProof (N : Network S) (h : N.StronglyEndotacticStd) :
    N.StrongEndotacticCertificate :=
  ⟨h⟩

/-- Weak reversibility plus one linkage class now has a fully proved strong-endotactic
certificate; no persistence theorem is assumed here. -/
def StrongEndotacticCertificate.ofWeaklyReversibleSingleLinkage (N : Network S)
    (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass) :
    N.StrongEndotacticCertificate :=
  ⟨hwr.stronglyEndotacticStd_of_singleLinkageClass hslc⟩

end Network
end CRNT
