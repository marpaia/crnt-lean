import CRNT.Oscillation.Certificate
import CRNT.Interop.Analysis

/-!
# Proof-carrying oscillation analysis entry point

This module connects the versioned `NetworkData.analyze` record to the proof-carrying oscillation
certificate API.  It is intentionally total on input networks but partial in mathematical coverage:
every network receives a certificate value, while unsupported cases are `unknown` rather than an
unsound negative or positive answer.

At present the automatic kernel-backed routes recognize (i) weakly reversible deficiency-zero
networks and (ii) every network of stoichiometric rank at most one.  Either route returns a global
all-parameter mass-action exclusion.  Future planar, Hopf, structural-core, and inheritance
procedures can add branches without changing the meaning of `unknown`.
-/

namespace CRNT

namespace NetworkData

/-- Total proof-carrying oscillation analysis for a data-driven finite CRN.

The current automatic branch promotes either compiled non-oscillation route (deficiency-zero or
stoichiometric rank at most one) back into its kernel theorem; all other networks are conservatively
`unknown`. -/
noncomputable def oscillationCertificate (d : NetworkData) : d.toNetwork.OscillationCertificate :=
  if h : d.analyze.noPositivePeriodicOrbitCertified = true then
    .excluded (NetworkData.neverPositivePeriodic_of_analyze d h)
  else
    .unknown

/-- The proof-erased status returned by the current certificate engine. -/
noncomputable def oscillationStatus (d : NetworkData) : Network.OscillationStatus :=
  (d.oscillationCertificate).status

/-- Global-limit-cycle certificate derived from the ordinary certificate engine.  A proved
all-periodic-orbit exclusion also excludes a class-global cycle; other ordinary statuses are kept
conservative because periodic existence alone does not prove global attraction. -/
noncomputable def globalOscillationCertificate (d : NetworkData) : d.toNetwork.GlobalOscillationCertificate :=
  d.oscillationCertificate.toGlobal

/-- Proof-erased class-global-limit-cycle status. -/
noncomputable def globalOscillationStatus (d : NetworkData) : Network.OscillationStatus :=
  d.globalOscillationCertificate.status

/-- A positive structural non-oscillation analyzer flag is reflected as `excluded`. -/
theorem oscillationStatus_eq_excluded_of_certified (d : NetworkData)
    (h : d.analyze.noPositivePeriodicOrbitCertified = true) :
    d.oscillationStatus = Network.OscillationStatus.excluded := by
  simp [oscillationStatus, oscillationCertificate, h,
    Network.OscillationCertificate.status]

/-- Without the currently implemented exclusion certificate, the engine reports `unknown` rather
than guessing from a failed sufficient test. -/
theorem oscillationStatus_eq_unknown_of_not_certified (d : NetworkData)
    (h : d.analyze.noPositivePeriodicOrbitCertified ≠ true) :
    d.oscillationStatus = Network.OscillationStatus.unknown := by
  simp [oscillationStatus, oscillationCertificate, h,
    Network.OscillationCertificate.status]

/-- A certified all-parameter exclusion is also a certified exclusion of class-global attracting
limit cycles. -/
theorem globalOscillationStatus_eq_excluded_of_certified (d : NetworkData)
    (h : d.analyze.noPositivePeriodicOrbitCertified = true) :
    d.globalOscillationStatus = Network.OscillationStatus.excluded := by
  simp [globalOscillationStatus, globalOscillationCertificate, oscillationCertificate, h,
    Network.OscillationCertificate.toGlobal, Network.GlobalOscillationCertificate.status]

/-- When the current ordinary engine has no theorem, the global engine also remains `unknown`. -/
theorem globalOscillationStatus_eq_unknown_of_not_certified (d : NetworkData)
    (h : d.analyze.noPositivePeriodicOrbitCertified ≠ true) :
    d.globalOscillationStatus = Network.OscillationStatus.unknown := by
  simp [globalOscillationStatus, globalOscillationCertificate, oscillationCertificate, h,
    Network.OscillationCertificate.toGlobal, Network.GlobalOscillationCertificate.status]

end NetworkData

end CRNT
