import Scaffold.CRNTExpansion.AdvancedDeficiencyClasses
import Scaffold.CRNTExpansion.AdvancedDeficiencyOrientation
import CRNT.Graph.Reachability

/-!
# Extending ADA kernel-row classes from an orientation to all reactions

The published Advanced Deficiency Algorithm defines the row `w_r` directly for reactions in the
orientation `O`.  A reaction outside `O` is the reverse direction of an oriented reaction and is
assigned the same `w`-row.  Consequently the zero class, nonzero colinearity classes, colinkage
sets, signs, and shelves are classes of the **full reaction set**, not merely of `O`.

This file installs that bridge without choosing a basis of `ker L_O`.  Every reaction is assigned a
selected representative: itself if selected, otherwise a selected reverse channel.  The canonical
kernel-coordinate predicates from `AdvancedDeficiencyKernel` are then pulled back along that map.

For networks with parallel channels, the intended use is on `N.mergeParallel`, as in
`ParallelReducedADAOrientation`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace ADAOrientation

variable {N : Network S}

/-- Every reaction has a selected representative: itself, or one selected reverse channel. -/
theorem exists_selectedRepresentative (O : N.ADAOrientation) (r : N.R) :
    ∃ q : N.R, q ∈ O.selected ∧ (q = r ∨ N.ReverseChannels r q) := by
  by_cases hr : r ∈ O.selected
  · exact ⟨r, hr, Or.inl rfl⟩
  · have hrev : N.HasReverseChannel r := by
      by_contra hno
      exact hr (O.irreversible_mem r hno)
    rcases hrev with ⟨q, hrq⟩
    have hq : q ∈ O.selected := by
      rcases O.reverse_mem_or_mem hrq with hr' | hq'
      · exact False.elim (hr hr')
      · exact hq'
    exact ⟨q, hq, Or.inr hrq⟩

/-- A selected representative of a full reaction.  No basis of `ker L_O` is involved. -/
noncomputable def selectedRepresentative (O : N.ADAOrientation) (r : N.R) :
    {q : N.R // q ∈ O.selected} :=
  ⟨Classical.choose (O.exists_selectedRepresentative r),
    (Classical.choose_spec (O.exists_selectedRepresentative r)).1⟩

/-- The representative is either the reaction itself or a selected reverse channel. -/
theorem selectedRepresentative_eq_or_reverse (O : N.ADAOrientation) (r : N.R) :
    (O.selectedRepresentative r).1 = r ∨
      N.ReverseChannels r (O.selectedRepresentative r).1 :=
  (Classical.choose_spec (O.exists_selectedRepresentative r)).2

end ADAOrientation

/-- Full-reaction zero-class membership, obtained by pulling the selected kernel coordinate back
along the orientation representative map. -/
def FullKernelCoordinateZero (N : Network S) (O : N.ADAOrientation) (r : N.R) : Prop :=
  N.KernelCoordinateZero O.selected (O.selectedRepresentative r)

/-- Full-reaction kernel-row colinearity.  This is the basis-free version of the published relation
`w_r = c w_q` after extending `w` from the orientation to all reactions. -/
def FullKernelCoordinateColinear (N : Network S) (O : N.ADAOrientation) (r q : N.R) : Prop :=
  N.KernelCoordinateColinear O.selected (O.selectedRepresentative r)
    (O.selectedRepresentative q)

@[refl] theorem fullKernelCoordinateColinear_refl (N : Network S) (O : N.ADAOrientation)
    (r : N.R) : N.FullKernelCoordinateColinear O r r :=
  N.kernelCoordinateColinear_refl O.selected (O.selectedRepresentative r)

@[symm] theorem fullKernelCoordinateColinear_symm (N : Network S) (O : N.ADAOrientation)
    {r q : N.R} (h : N.FullKernelCoordinateColinear O r q) :
    N.FullKernelCoordinateColinear O q r :=
  N.kernelCoordinateColinear_symm O.selected h

@[trans] theorem fullKernelCoordinateColinear_trans (N : Network S) (O : N.ADAOrientation)
    {r q t : N.R} (hrq : N.FullKernelCoordinateColinear O r q)
    (hqt : N.FullKernelCoordinateColinear O q t) :
    N.FullKernelCoordinateColinear O r t :=
  N.kernelCoordinateColinear_trans O.selected hrq hqt

/-- Full kernel-row colinearity is an equivalence relation on the reaction set. -/
theorem fullKernelCoordinateColinear_equivalence (N : Network S) (O : N.ADAOrientation) :
    Equivalence (N.FullKernelCoordinateColinear O) :=
  ⟨N.fullKernelCoordinateColinear_refl O,
    N.fullKernelCoordinateColinear_symm O,
    N.fullKernelCoordinateColinear_trans O⟩

/-- The corresponding setoid of full ADA colinearity classes. -/
noncomputable def fullKernelCoordinateSetoid (N : Network S) (O : N.ADAOrientation) :
    Setoid N.R where
  r := N.FullKernelCoordinateColinear O
  iseqv := N.fullKernelCoordinateColinear_equivalence O

/-- Full ADA colinearity classes. -/
abbrev FullKernelColinearityClass (N : Network S) (O : N.ADAOrientation) :=
  Quotient (N.fullKernelCoordinateSetoid O)

/-- Zero-class membership is constant on full colinearity classes. -/
theorem fullKernelCoordinateZero_iff_of_colinear
    (N : Network S) (O : N.ADAOrientation) {r q : N.R}
    (h : N.FullKernelCoordinateColinear O r q) :
    N.FullKernelCoordinateZero O r ↔ N.FullKernelCoordinateZero O q :=
  N.kernelCoordinateZero_iff_of_colinear O.selected h

/-! ## Colinkage relations inside a full kernel-row class

These parent-level relations avoid coercion bookkeeping through a reaction-restricted network while
representing exactly the graph obtained by retaining the reactions in one full colinearity class.
-/

/-- One directed reaction step using only reactions in the full kernel-row class of `base`. -/
def ColinearityClassDirectlyReacts (N : Network S) (O : N.ADAOrientation)
    (base : N.R) (c d : Complex S) : Prop :=
  ∃ r : N.R, N.FullKernelCoordinateColinear O base r ∧
    (N.reaction r).source = c ∧ (N.reaction r).target = d

/-- Directed reachability inside one ADA colinearity class. -/
def ColinearityClassReaches (N : Network S) (O : N.ADAOrientation)
    (base : N.R) (c d : Complex S) : Prop :=
  Relation.ReflTransGen (N.ColinearityClassDirectlyReacts O base) c d

/-- Strong colinkage inside one ADA colinearity class. -/
def ColinearityClassStronglyLinked (N : Network S) (O : N.ADAOrientation)
    (base : N.R) (c d : Complex S) : Prop :=
  N.ColinearityClassReaches O base c d ∧ N.ColinearityClassReaches O base d c

/-- The strong colinkage class of `c` is terminal relative to the reaction class of `base`. -/
def IsTerminalStrongColinkage (N : Network S) (O : N.ADAOrientation)
    (base : N.R) (c : Complex S) : Prop :=
  ∀ r : N.R, N.FullKernelCoordinateColinear O base r →
    N.ColinearityClassStronglyLinked O base c (N.reaction r).source →
    N.ColinearityClassStronglyLinked O base c (N.reaction r).target

/-- Strong colinkage is reflexive. -/
@[refl] theorem colinearityClassStronglyLinked_refl
    (N : Network S) (O : N.ADAOrientation) (base : N.R) (c : Complex S) :
    N.ColinearityClassStronglyLinked O base c c :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

end Network
end CRNT
