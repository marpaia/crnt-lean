import CRNT.Design.Localization
import CRNT.Design.GeneratedClosure

/-!
# Labeled buffering structures

A labeled buffering structure records not only the response subnetwork but also the
perturbations whose effects are localized there.  The labels are kept abstract: they may
represent reaction parameters, conserved totals, or another finite family of admissible
perturbations.  This avoids baking a numerical nullspace basis into the mathematics.
-/

namespace CRNT
namespace Network

variable {S P : Type} [DecidableEq S] [Fintype S]
  [DecidableEq P] [Fintype P]

/-- A labeled structural response region.  `addedReactions` records reactions required
only to complete the raw response subnetwork to an output-complete one. -/
structure LabeledSubnetwork (N : Network S) (P : Type) [DecidableEq P] [Fintype P] where
  labels : Finset P
  response : StructuralSubnetwork N
  addedReactions : Finset N.R
  added_disjoint : Disjoint addedReactions response.reactions

namespace LabeledSubnetwork

variable {N : Network S}

/-- The output-completed reaction set represented by a labeled response. -/
def completed (L : LabeledSubnetwork N P) : StructuralSubnetwork N where
  species := L.response.species
  reactions := L.response.reactions ∪ L.addedReactions

@[simp] theorem completed_species (L : LabeledSubnetwork N P) :
    L.completed.species = L.response.species := rfl

@[simp] theorem completed_reactions (L : LabeledSubnetwork N P) :
    L.completed.reactions = L.response.reactions ∪ L.addedReactions := rfl

/-- Forget labels and completion provenance. -/
def forget (L : LabeledSubnetwork N P) : StructuralSubnetwork N := L.completed

end LabeledSubnetwork

/-- A labeled buffering structure is a labeled response whose completion is a buffering
structure. -/
def IsLabeledBufferingStructure (N : Network S) (L : LabeledSubnetwork N P) : Prop :=
  N.IsBufferingStructure L.completed

/-- Strong labeled buffering structure. -/
def IsStrongLabeledBufferingStructure (N : Network S)
    (L : LabeledSubnetwork N P) : Prop :=
  N.IsStrongBufferingStructure L.completed

/-- Forgetting the labels of a labeled buffering structure produces an ordinary buffering
structure. -/
theorem IsLabeledBufferingStructure.forget {N : Network S}
    {L : LabeledSubnetwork N P} (h : N.IsLabeledBufferingStructure L) :
    N.IsBufferingStructure L.forget := h

/-- Likewise for strong buffering. -/
theorem IsStrongLabeledBufferingStructure.forget {N : Network S}
    {L : LabeledSubnetwork N P} (h : N.IsStrongLabeledBufferingStructure L) :
    N.IsStrongBufferingStructure L.forget := h

/-- A finite perturbation-response assignment.  `response p` is the raw structural
subnetwork affected by perturbing parameter `p`. -/
structure StructuralResponseAssignment (N : Network S) (P : Type)
    [DecidableEq P] [Fintype P] where
  response : P → StructuralSubnetwork N

namespace StructuralResponseAssignment

variable {N : Network S}

/-- Parameters with identical raw response subnetworks form a structural response class. -/
def SameResponse (A : StructuralResponseAssignment N P) (p q : P) : Prop :=
  A.response p = A.response q

@[refl] theorem sameResponse_refl (A : StructuralResponseAssignment N P) (p : P) :
    A.SameResponse p p := rfl

@[symm] theorem sameResponse_symm (A : StructuralResponseAssignment N P) {p q : P} :
    A.SameResponse p q → A.SameResponse q p := Eq.symm

@[trans] theorem sameResponse_trans (A : StructuralResponseAssignment N P) {p q r : P} :
    A.SameResponse p q → A.SameResponse q r → A.SameResponse p r := Eq.trans

/-- The full label class sharing the response of `p`. -/
noncomputable def responseClass (A : StructuralResponseAssignment N P) (p : P) : Finset P := by
  classical
  exact Finset.univ.filter fun q => A.SameResponse p q

/-- Canonical completed response of a perturbation label. -/
noncomputable def completedResponse (A : StructuralResponseAssignment N P) (p : P) :
    StructuralSubnetwork N := N.generatedClosure (A.response p)

/-- A perturbation is structurally localized when its canonical generated response is a
buffering structure. -/
def IsLocalized (A : StructuralResponseAssignment N P) (p : P) : Prop :=
  N.IsBufferingStructure (A.completedResponse p)

/-- Strong structural localization. -/
def IsStronglyLocalized (A : StructuralResponseAssignment N P) (p : P) : Prop :=
  N.IsStrongBufferingStructure (A.completedResponse p)

/-- Same-response perturbations have the same generated completion. -/
theorem completedResponse_eq_of_sameResponse
    (A : StructuralResponseAssignment N P) {p q : P} (h : A.SameResponse p q) :
    A.completedResponse p = A.completedResponse q := by
  change A.response p = A.response q at h
  exact congrArg N.generatedClosure h

/-- Localization is constant on structural response classes. -/
theorem localized_iff_of_sameResponse
    (A : StructuralResponseAssignment N P) {p q : P} (h : A.SameResponse p q) :
    A.IsLocalized p ↔ A.IsLocalized q := by
  rw [IsLocalized, IsLocalized, A.completedResponse_eq_of_sameResponse h]

end StructuralResponseAssignment

end Network
end CRNT
