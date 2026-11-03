import CRNT.Design.LabeledBufferingStructure
import CRNT.Design.LocalizationDifferential
import CRNT.Design.StrongBufferingFluxRPA

/-!
# Labeled buffering structures as RPA certificates

The labels in a labeled buffering structure identify perturbations.  A response assignment
maps each label to its raw structural response, and generated closure produces the least
output-complete response region.  This module turns that combinatorial object into precise
first-order robustness statements.
-/

namespace CRNT
namespace Network

variable {S P : Type} [DecidableEq S] [Fintype S]
  [DecidableEq P] [Fintype P]

/-- Differential data attached to each perturbation label. -/
structure LabeledSensitivityData (N : Network S) (P : Type)
    [DecidableEq P] [Fintype P] where
  forcing : P → ParameterDerivativeForcing N

/-- The forcing associated with `p` is structurally supported by its generated response. -/
def LabeledSensitivityData.RespectsAssignment {N : Network S}
    (A : StructuralResponseAssignment N P) (D : LabeledSensitivityData N P) : Prop :=
  ∀ p, (D.forcing p).SupportedIn (A.completedResponse p)

/-- Species outside a completed response are robust to perturbation label `p`. -/
def SpeciesRobustToLabel {N : Network S} (A : StructuralResponseAssignment N P)
    (p : P) (s : S) : Prop := s ∉ (A.completedResponse p).species

/-- Reaction rates outside a completed response are robust to perturbation label `p`. -/
def ReactionRobustToLabel {N : Network S} (A : StructuralResponseAssignment N P)
    (p : P) (r : N.R) : Prop := r ∉ (A.completedResponse p).reactions

/-- First-order response certificate for one labeled perturbation. -/
def LabeledResponseCertificate {N : Network S}
    (A : StructuralResponseAssignment N P) (D : LabeledSensitivityData N P)
    (p : P) (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ)) :=
  N.SteadyStateSensitivityCertificate (A.completedResponse p) J (D.forcing p)

/-- **Labeled law of localization.**  A label whose completed response is buffering has
zero concentration sensitivity on every species outside that response and zero total
rate sensitivity on every exterior reaction. -/
theorem labeledBuffering_firstOrder_RPA
    {N : Network S} (A : StructuralResponseAssignment N P)
    (D : LabeledSensitivityData N P) (hD : D.RespectsAssignment A)
    (p : P) (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (hJ : N.RespectsReactantSupport J)
    (hloc : A.IsLocalized p)
    (hinj : Function.Injective
      (N.localSensitivityOperator (A.completedResponse p) J)) :
    ∃! C : N.LabeledResponseCertificate A D p J,
      (∀ s, SpeciesRobustToLabel A p s → C.fullConcentrationDerivative s = 0) ∧
      (∀ r, ReactionRobustToLabel A p r → C.totalRateDerivative r = 0) := by
  simpa [LabeledResponseCertificate, SpeciesRobustToLabel, ReactionRobustToLabel] using
    N.lawOfLocalization_differential hloc hJ hinj (D.forcing p) (hD p)

/-- Same structural response class gives exactly the same robust species set. -/
theorem robustSpecies_eq_of_sameResponse
    {N : Network S} (A : StructuralResponseAssignment N P) {p q : P}
    (h : A.SameResponse p q) :
    (fun s => SpeciesRobustToLabel A p s) =
      (fun s => SpeciesRobustToLabel A q s) := by
  funext s
  simp [SpeciesRobustToLabel, A.completedResponse_eq_of_sameResponse h]

/-- Same structural response class gives exactly the same robust reaction set. -/
theorem robustReactions_eq_of_sameResponse
    {N : Network S} (A : StructuralResponseAssignment N P) {p q : P}
    (h : A.SameResponse p q) :
    (fun r => ReactionRobustToLabel A p r) =
      (fun r => ReactionRobustToLabel A q r) := by
  funext r
  simp [ReactionRobustToLabel, A.completedResponse_eq_of_sameResponse h]

/-- A label is elementary when its nonempty completed response contains no proper nonempty
completed response of another label.  This is the basis-independent combinatorial notion
underlying elementary labeled buffering structures. -/
def StructuralResponseAssignment.IsElementaryLabel
    {N : Network S} (A : StructuralResponseAssignment N P) (p : P) : Prop :=
  ((A.completedResponse p).species.Nonempty ∨
      (A.completedResponse p).reactions.Nonempty) ∧
  ∀ q, ((A.completedResponse q).species ⊆ (A.completedResponse p).species) →
    ((A.completedResponse q).reactions ⊆ (A.completedResponse p).reactions) →
    ((A.completedResponse q).species.Nonempty ∨
      (A.completedResponse q).reactions.Nonempty) →
    A.completedResponse q = A.completedResponse p

/-- Elementary localized labels are elementary labeled buffering structures. -/
theorem elementaryLabel_gives_labeledBuffering
    {N : Network S} (A : StructuralResponseAssignment N P) {p : P}
    (he : A.IsElementaryLabel p) (hloc : A.IsLocalized p) :
    ∃ L : LabeledSubnetwork N P,
      N.IsLabeledBufferingStructure L ∧ p ∈ L.labels := by
  refine ⟨{
    labels := {p}
    response := A.completedResponse p
    addedReactions := ∅
    added_disjoint := by simp
  }, ?_, by simp⟩
  simpa [IsLabeledBufferingStructure, LabeledSubnetwork.completed,
    StructuralResponseAssignment.IsLocalized] using hloc

/-- Strongly localized labels yield global first-order flux RPA: every reaction flux is
insensitive, including reactions inside the buffering structure. -/
theorem stronglyLabeledBuffering_globalFluxRPA
    {N : Network S} (A : StructuralResponseAssignment N P)
    (D : LabeledSensitivityData N P) (hD : D.RespectsAssignment A)
    (p : P) (J : (S → ℝ) →ₗ[ℝ] (N.R → ℝ))
    (hJ : N.RespectsReactantSupport J)
    (hstrong : A.IsStronglyLocalized p)
    (hinj : Function.Injective
      (N.fluxSensitivityOperator (A.completedResponse p) J)) :
    ∃ dx : N.FluxSensitivityDomain (A.completedResponse p),
      N.totalFluxResponse (A.completedResponse p) J dx
        (N.restrictRateForcing (A.completedResponse p) (D.forcing p)) = 0 := by
  have hp := hD p
  let q := N.restrictRateForcing (A.completedResponse p) (D.forcing p)
  rcases N.strongBuffering_fluxRPA_linear hstrong hJ hinj q with ⟨dx, hdx, _⟩
  exact ⟨dx, hdx.2⟩

end Network
end CRNT
