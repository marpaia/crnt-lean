import CRNT
import CRNT.Dynamics.GlobalPersistenceFrontier

/-!
# Global persistence API smoke checks

This file intentionally contains only name/type checks.  It catches accidental module/export
regressions under the pinned Lean and Mathlib toolchain.
-/

#check CRNT.Network.PersistentForRates
#check CRNT.Network.StructurallyPersistent
#check CRNT.Network.BoundaryOmegaExcluded
#check CRNT.Network.StructurallyBoundaryOmegaExcluded
#check CRNT.Network.boundaryOmegaExcluded_of_hasNoCriticalSiphon
#check CRNT.Network.structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon
#check CRNT.Network.PermanentForFlow
#check CRNT.Network.PermanentForRates
#check CRNT.Network.StructurallyPermanent
#check CRNT.Network.StoichActiveDirection
#check CRNT.Network.StronglyEndotacticStd
#check CRNT.Network.WeaklyReversible.endotactic
#check CRNT.Network.StronglyEndotactic.toStd_of_weaklyReversible
#check CRNT.Network.ReactionPathway
#check CRNT.Network.IsDrainable
#check CRNT.Network.IsSelfReplicable
#check CRNT.Network.TierDescending
#check CRNT.Network.stronglyEndotacticStd_iff_tierDescending
#check CRNT.Network.GlobalPersistenceCertificate
#check CRNT.Network.PersistenceConjectureStrong
#check CRNT.Network.PersistenceConjectureOmega
#check CRNT.Network.AllComplexesLinked
#check CRNT.Network.allComplexesLinked_of_singleLinkageClass
#check CRNT.Network.WeaklyReversible.reaches_of_singleLinkageClass
#check CRNT.Network.singleLinkageStrongEndotactic
#check CRNT.Network.BoundaryOmegaCertificate
#check CRNT.Network.BoundaryOmegaCertificate.ofNoCriticalSiphon
#check CRNT.Network.GlobalPermanenceCertificate
#check CRNT.Network.structurallyPersistent_of_deficiencyZero_hasNoCriticalSiphon
#check CRNT.Network.GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon
#check CRNT.NetworkData.globalPersistenceCertificate_of_persistenceCertified

#check CRNT.Network.PersistentOrbit
#check CRNT.Network.StructurallyPersistentStd
#check CRNT.Network.PermanentOnPositiveClass
#check CRNT.Network.WeaklyReversible.stronglyEndotacticStd_of_singleLinkageClass
#check CRNT.Network.FluxSignRealizable
#check CRNT.Network.hasNoCriticalSiphon_of_noDrainable_of_minimalCriticalDichotomy
#check CRNT.Network.MinimalCriticalSiphonFluxDichotomyClaim
#check CRNT.Network.noDrainableSiphonOmegaPersistence
#check CRNT.Network.TwoDimensionalWRBoundedPersistenceClaim
#check CRNT.Network.TwoSpeciesEndotacticPermanenceClaim
#check CRNT.Network.FirstOrderEndotacticPersistenceClaim
#check CRNT.NetworkData.strongEndotacticCertificate_of_persistenceSingleLinkage
