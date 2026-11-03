import CRNT.Oscillation.Exclusion
import CRNT.Oscillation.ReactionRestriction
import CRNT.Oscillation.KineticBasic

/-!
# Proof-carrying oscillation certificates

A sound general-purpose CRN analyzer cannot promise a total yes/no decision for arbitrary nonlinear
mass-action systems.  The kernel-facing API therefore distinguishes proved exclusion, proved
existence/capacity, and lack of a theorem.

Two levels are kept separate:

* `FixedOscillationCertificate N κ` answers a question about one fixed positive rate vector;
* `OscillationCertificate N` answers the structural, parameter-existential/all-parameter question.

Both have proof-erased status views.  `unknown` is first-class: failure of a sufficient condition is
never converted into evidence for the opposite dynamical conclusion.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Proof-erased three-way oscillation verdict. -/
inductive OscillationStatus
  | excluded
  | capable
  | unknown
  deriving Repr, DecidableEq

/-- Proof-carrying result for one fixed mass-action parameter vector. -/
inductive FixedOscillationCertificate (N : Network S) (κ : N.RateConstants) : Type
  | excluded (proof : ¬ N.HasPositivePeriodicOrbit κ)
  | periodic (orbit : N.PositivePeriodicOrbit κ)
  | unknown

/-- Erase the proof payload of a fixed-parameter certificate. -/
def FixedOscillationCertificate.status {N : Network S} {κ : N.RateConstants} :
    N.FixedOscillationCertificate κ → OscillationStatus
  | .excluded _ => .excluded
  | .periodic _ => .capable
  | .unknown => .unknown

/-- A concrete positive periodic orbit is a fixed-parameter positive certificate. -/
def fixedCertificateOfPeriodicOrbit {N : Network S} {κ : N.RateConstants}
    (P : N.PositivePeriodicOrbit κ) : N.FixedOscillationCertificate κ :=
  .periodic P

/-- An all-parameter exclusion specializes to a fixed-parameter exclusion certificate. -/
def fixedCertificateOfStructuralExclusion {N : Network S} (h : N.NeverPositivePeriodic)
    (κ : N.RateConstants) : N.FixedOscillationCertificate κ :=
  .excluded (h κ)

/-- A fixed exclusion and a concrete fixed periodic orbit are logically incompatible. -/
theorem fixedExclusion_not_periodic {N : Network S} {κ : N.RateConstants}
    (hno : ¬ N.HasPositivePeriodicOrbit κ) (P : N.PositivePeriodicOrbit κ) : False :=
  hno ⟨P⟩

/-- Combine two fixed-parameter certificates. `unknown` is neutral; contradictory proof payloads
are eliminated rather than resolved by an arbitrary priority rule. -/
def FixedOscillationCertificate.combine {N : Network S} {κ : N.RateConstants} :
    N.FixedOscillationCertificate κ → N.FixedOscillationCertificate κ →
      N.FixedOscillationCertificate κ
  | .unknown, c => c
  | c, .unknown => c
  | .excluded h, .excluded _ => .excluded h
  | .periodic P, .periodic _ => .periodic P
  | .excluded hno, .periodic P => False.elim (fixedExclusion_not_periodic hno P)
  | .periodic P, .excluded hno => False.elim (fixedExclusion_not_periodic hno P)

@[simp] theorem FixedOscillationCertificate.combine_unknown_left
    {N : Network S} {κ : N.RateConstants} (c : N.FixedOscillationCertificate κ) :
    (FixedOscillationCertificate.unknown.combine c) = c := by
  rfl

@[simp] theorem FixedOscillationCertificate.combine_unknown_right
    {N : Network S} {κ : N.RateConstants} (c : N.FixedOscillationCertificate κ) :
    (c.combine FixedOscillationCertificate.unknown) = c := by
  cases c <;> rfl

/-- Proof-carrying structural result of an oscillation analysis.

`excluded` is the strong all-positive-parameter statement `NeverPositivePeriodic`; `capable` is the
existential-in-parameters statement `OscillatoryCapacity`. -/
inductive OscillationCertificate (N : Network S) : Type
  | excluded (proof : N.NeverPositivePeriodic)
  | capable (proof : N.OscillatoryCapacity)
  | unknown

/-- Erase the proof payload of a structural oscillation certificate. -/
def OscillationCertificate.status {N : Network S} :
    N.OscillationCertificate → OscillationStatus
  | .excluded _ => .excluded
  | .capable _ => .capable
  | .unknown => .unknown

/-- Structural exclusion and structural capacity cannot both hold. -/
theorem neverPositivePeriodic_not_oscillatoryCapacity {N : Network S}
    (hnever : N.NeverPositivePeriodic) (hcap : N.OscillatoryCapacity) : False := by
  obtain ⟨κ, hκ⟩ := hcap
  exact hnever κ hκ

/-- Promote a fixed-parameter positive witness to structural oscillatory capacity. -/
def OscillationCertificate.ofFixedPeriodic {N : Network S} {κ : N.RateConstants}
    (P : N.PositivePeriodicOrbit κ) : N.OscillationCertificate :=
  .capable ⟨κ, ⟨P⟩⟩

/-- Promote any fixed-parameter `periodic` certificate to structural capacity.  A fixed exclusion is
not an all-parameter exclusion, so it cannot be promoted to `excluded`; it conservatively becomes
`unknown`. -/
def FixedOscillationCertificate.toStructural {N : Network S} {κ : N.RateConstants} :
    N.FixedOscillationCertificate κ → N.OscillationCertificate
  | .periodic P => OscillationCertificate.ofFixedPeriodic P
  | .excluded _ => .unknown
  | .unknown => .unknown

/-- Specialize a structural certificate to one fixed parameter vector.  Structural exclusion remains
an exclusion; structural capacity is existential in parameters and therefore does not imply that this
particular `κ` oscillates. -/
def OscillationCertificate.toFixed {N : Network S}
    (c : N.OscillationCertificate) (κ : N.RateConstants) : N.FixedOscillationCertificate κ :=
  match c with
  | .excluded h => .excluded (h κ)
  | .capable _ => .unknown
  | .unknown => .unknown

/-- Combine two sound structural certificates without weakening either one.

The contradictory `excluded/capable` branches are discharged from their proof payloads, so no
priority convention can hide an inconsistency.  `unknown` is neutral. -/
def OscillationCertificate.combine {N : Network S} :
    N.OscillationCertificate → N.OscillationCertificate → N.OscillationCertificate
  | .unknown, c => c
  | c, .unknown => c
  | .excluded h, .excluded _ => .excluded h
  | .capable h, .capable _ => .capable h
  | .excluded hnever, .capable hcap =>
      False.elim (neverPositivePeriodic_not_oscillatoryCapacity hnever hcap)
  | .capable hcap, .excluded hnever =>
      False.elim (neverPositivePeriodic_not_oscillatoryCapacity hnever hcap)

/-- Combining with `unknown` on the left is identity. -/
@[simp] theorem OscillationCertificate.combine_unknown_left {N : Network S}
    (c : N.OscillationCertificate) :
    (OscillationCertificate.unknown.combine c) = c := by
  rfl

/-- Combining with `unknown` on the right is identity. -/
@[simp] theorem OscillationCertificate.combine_unknown_right {N : Network S}
    (c : N.OscillationCertificate) :
    (c.combine OscillationCertificate.unknown) = c := by
  cases c <;> rfl

/-- Proof-carrying structural result at the broader admissible-kinetics scope. -/
inductive KineticOscillationCertificate (N : Network S) : Type
  | excluded (proof : N.NeverPositiveKineticPeriodic)
  | capable (proof : N.KineticOscillatoryCapacity)
  | unknown

/-- Erase the proof payload of an admissible-kinetics certificate. -/
def KineticOscillationCertificate.status {N : Network S} :
    N.KineticOscillationCertificate → OscillationStatus
  | .excluded _ => .excluded
  | .capable _ => .capable
  | .unknown => .unknown

/-- All-kinetics exclusion and all-kinetics capacity cannot both hold. -/
theorem neverPositiveKineticPeriodic_not_kineticOscillatoryCapacity {N : Network S}
    (hnever : N.NeverPositiveKineticPeriodic) (hcap : N.KineticOscillatoryCapacity) : False := by
  obtain ⟨K, hK⟩ := hcap
  exact hnever K hK

/-- Combine two admissible-kinetics certificates soundly. -/
def KineticOscillationCertificate.combine {N : Network S} :
    N.KineticOscillationCertificate → N.KineticOscillationCertificate →
      N.KineticOscillationCertificate
  | .unknown, c => c
  | c, .unknown => c
  | .excluded h, .excluded _ => .excluded h
  | .capable h, .capable _ => .capable h
  | .excluded hnever, .capable hcap =>
      False.elim (neverPositiveKineticPeriodic_not_kineticOscillatoryCapacity hnever hcap)
  | .capable hcap, .excluded hnever =>
      False.elim (neverPositiveKineticPeriodic_not_kineticOscillatoryCapacity hnever hcap)

/-- A mass-action capacity certificate promotes to the broader admissible-kinetics scope. -/
def OscillationCertificate.toKinetic {N : Network S} :
    N.OscillationCertificate → N.KineticOscillationCertificate
  | .capable h => .capable (kineticOscillatoryCapacity_of_oscillatoryCapacity h)
  | .excluded _ => .unknown
  | .unknown => .unknown

/-- An all-admissible-kinetics exclusion certificate restricts soundly to mass action.  A general
kinetics capacity witness cannot be promoted to mass-action capacity. -/
def KineticOscillationCertificate.toMassAction {N : Network S} :
    N.KineticOscillationCertificate → N.OscillationCertificate
  | .excluded h => .excluded (neverPositivePeriodic_of_neverPositiveKineticPeriodic h)
  | .capable _ => .unknown
  | .unknown => .unknown

/-- Scope-aware summary for arbitrary CRNs.  The constructors intentionally encode what was proved,
not a total classification: `kineticsCapable` need not imply mass-action capacity, while
`massActionExcluded` says nothing about broader kinetics. -/
inductive OscillationScopeCertificate (N : Network S) : Type
  | allKineticsExcluded (proof : N.NeverPositiveKineticPeriodic)
  | massActionExcluded (proof : N.NeverPositivePeriodic)
  | massActionCapable (proof : N.OscillatoryCapacity)
  | kineticsCapable (proof : N.KineticOscillatoryCapacity)
  | unknown

/-- Interpret a scope-aware certificate as a mass-action status.  A broader-kinetics positive witness
is insufficient to assert mass-action capacity, while all-kinetics exclusion does restrict to mass
action. -/
def OscillationScopeCertificate.massActionStatus {N : Network S} :
    N.OscillationScopeCertificate → OscillationStatus
  | .allKineticsExcluded _ => .excluded
  | .massActionExcluded _ => .excluded
  | .massActionCapable _ => .capable
  | .kineticsCapable _ => .unknown
  | .unknown => .unknown

/-- Interpret a scope-aware certificate at the broader admissible-kinetics scope.  Mass-action
capacity is a valid broader-kinetics witness, while mass-action exclusion does not exclude other
admissible kinetics. -/
def OscillationScopeCertificate.kineticStatus {N : Network S} :
    N.OscillationScopeCertificate → OscillationStatus
  | .allKineticsExcluded _ => .excluded
  | .massActionExcluded _ => .unknown
  | .massActionCapable _ => .capable
  | .kineticsCapable _ => .capable
  | .unknown => .unknown

/-- Embed a mass-action certificate into the scope-aware representation. -/
def OscillationCertificate.toScope {N : Network S} :
    N.OscillationCertificate → N.OscillationScopeCertificate
  | .excluded h => .massActionExcluded h
  | .capable h => .massActionCapable h
  | .unknown => .unknown

/-- Embed an admissible-kinetics certificate into the scope-aware representation. -/
def KineticOscillationCertificate.toScope {N : Network S} :
    N.KineticOscillationCertificate → N.OscillationScopeCertificate
  | .excluded h => .allKineticsExcluded h
  | .capable h => .kineticsCapable h
  | .unknown => .unknown

/-- Proof-carrying result for the stronger question of a class-global attracting limit cycle.
`excluded` means only that global oscillatory capacity is impossible; it need not exclude unstable
or nonglobal periodic orbits. -/
inductive GlobalOscillationCertificate (N : Network S) : Type
  | excluded (proof : ¬ N.GlobalOscillatoryCapacity)
  | capable (proof : N.GlobalOscillatoryCapacity)
  | unknown

/-- Proof-erased status for the global-limit-cycle question. -/
def GlobalOscillationCertificate.status {N : Network S} :
    N.GlobalOscillationCertificate → OscillationStatus
  | .excluded _ => .excluded
  | .capable _ => .capable
  | .unknown => .unknown

/-- Global exclusion and global capacity cannot both hold. -/
theorem notGlobalOscillatoryCapacity_not_globalOscillatoryCapacity
    {N : Network S} (hno : ¬ N.GlobalOscillatoryCapacity)
    (hyes : N.GlobalOscillatoryCapacity) : False :=
  hno hyes

/-- Combine global certificates without arbitrary priority. -/
def GlobalOscillationCertificate.combine {N : Network S} :
    N.GlobalOscillationCertificate → N.GlobalOscillationCertificate →
      N.GlobalOscillationCertificate
  | .unknown, c => c
  | c, .unknown => c
  | .excluded h, .excluded _ => .excluded h
  | .capable h, .capable _ => .capable h
  | .excluded hno, .capable hyes =>
      False.elim (notGlobalOscillatoryCapacity_not_globalOscillatoryCapacity hno hyes)
  | .capable hyes, .excluded hno =>
      False.elim (notGlobalOscillatoryCapacity_not_globalOscillatoryCapacity hno hyes)

/-- An ordinary all-parameter exclusion is strong enough to exclude a global limit cycle.  Mere
ordinary capacity is not strong enough to assert global attraction. -/
def OscillationCertificate.toGlobal {N : Network S} :
    N.OscillationCertificate → N.GlobalOscillationCertificate
  | .excluded h => .excluded (not_globalOscillatoryCapacity_of_neverPositivePeriodic h)
  | .capable _ => .unknown
  | .unknown => .unknown

/-- A proved class-global cycle is certainly an ordinary oscillation witness.  Failure of global
attraction does not exclude other periodic orbits, so global exclusion maps to `unknown`. -/
def GlobalOscillationCertificate.toOrdinary {N : Network S} :
    N.GlobalOscillationCertificate → N.OscillationCertificate
  | .capable h => .capable (oscillatoryCapacity_of_globalOscillatoryCapacity h)
  | .excluded _ => .unknown
  | .unknown => .unknown

/-- The deficiency-zero structural theorem produces an exclusion certificate directly. -/
def deficiencyZeroOscillationCertificate (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) : N.OscillationCertificate :=
  .excluded (N.neverPositivePeriodic_of_weaklyReversible_deficiencyZero hwr hδ)

end Network

end CRNT
