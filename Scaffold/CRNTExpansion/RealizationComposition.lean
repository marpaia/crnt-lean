import Scaffold.CRNTExpansion.RealizationCertificates

/-!
# Composition of realization certificates

Realization searches are naturally staged: simplify a network, find a dynamically equivalent target,
then further transform that target into a weakly reversible / low-deficiency realization.  This file
makes those stages compositional so a later certificate-producing algorithm can be verified one
step at a time.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace MassActionRealization

variable {N : Network S} {κN : N.RateConstants}

/-- Dynamically equivalent realizations compose. -/
def trans (R : MassActionRealization N κN)
    (Q : MassActionRealization R.network R.rates) : MassActionRealization N κN where
  network := Q.network
  rates := Q.rates
  equivalent := R.equivalent.trans Q.equivalent

end MassActionRealization

namespace StoichiometricMassActionRealization

variable {N : Network S} {κN : N.RateConstants}

/-- Stoichiometric realizations compose, preserving both the vector field and the compatibility
subspace. -/
def trans (R : StoichiometricMassActionRealization N κN)
    (Q : StoichiometricMassActionRealization R.network R.rates) :
    StoichiometricMassActionRealization N κN where
  network := Q.network
  rates := Q.rates
  equivalent := R.equivalent.trans Q.equivalent
  stoich_eq := R.stoich_eq.trans Q.stoich_eq

end StoichiometricMassActionRealization

namespace SourceCoefficientRealizationCertificate

variable {N : Network S} {κN : N.RateConstants}

/-- Finite source-coefficient certificates compose by transitivity of coefficient equality. -/
def trans (C : SourceCoefficientRealizationCertificate N κN)
    (D : SourceCoefficientRealizationCertificate C.network C.rates) :
    SourceCoefficientRealizationCertificate N κN where
  network := D.network
  rates := D.rates
  coefficients := C.coefficients.trans D.coefficients

/-- Composition at the finite-certificate level agrees with composition after forgetting to
ordinary mass-action realizations. -/
theorem trans_equivalent
    (C : SourceCoefficientRealizationCertificate N κN)
    (D : SourceCoefficientRealizationCertificate C.network C.rates) :
    (C.trans D).toMassActionRealization.equivalent =
      C.toMassActionRealization.equivalent.trans D.toMassActionRealization.equivalent := by
  rfl

end SourceCoefficientRealizationCertificate

namespace StoichiometricSourceCoefficientRealizationCertificate

variable {N : Network S} {κN : N.RateConstants}

/-- Stoichiometric source-coefficient certificates compose. -/
def trans (C : StoichiometricSourceCoefficientRealizationCertificate N κN)
    (D : StoichiometricSourceCoefficientRealizationCertificate C.network C.rates) :
    StoichiometricSourceCoefficientRealizationCertificate N κN where
  network := D.network
  rates := D.rates
  coefficients := C.coefficients.trans D.coefficients
  stoich_eq := C.stoich_eq.trans D.stoich_eq

/-- A property of the final target can therefore be transported across an arbitrarily staged
source-coefficient realization pipeline. -/
theorem hasDynamicallyEquivalentRealizationWith_of_trans
    (C : StoichiometricSourceCoefficientRealizationCertificate N κN)
    (D : StoichiometricSourceCoefficientRealizationCertificate C.network C.rates)
    {P : Network S → Prop} (hP : P D.network) :
    N.HasDynamicallyEquivalentRealizationWith κN P := by
  exact (C.trans D).toStoichiometricMassActionRealization.hasDynamicallyEquivalentRealizationWith hP

end StoichiometricSourceCoefficientRealizationCertificate

end Network
end CRNT
