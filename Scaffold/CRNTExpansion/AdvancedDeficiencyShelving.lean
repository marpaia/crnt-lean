import Scaffold.CRNTExpansion.AdvancedDeficiencySigns
import CRNT.Deficiency.Shelf

/-!
# Reaction shelving inside faithful ADA colinearity classes

Step 9 of the Advanced Deficiency Algorithm shelves **reactions**, not complexes.  The terminality
conditions are relative to the subnetwork formed by one kernel-row colinearity class.  This module
uses the parent-level colinkage relations of `AdvancedDeficiencyFullClasses` to record those rules
without introducing a second network/index coercion layer.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A Step-9 shelving assignment for a fixed orientation and admissible class signing. -/
structure ADAShelving (N : Network S) (O : N.ADAOrientation)
    (σ : N.ADATripletClassSigning O) where
  shelf : N.R → Shelf
  /-- Reactions in a nonterminal strong colinkage class are on the middle shelf. -/
  nonterminal_middle : ∀ r : N.R, (σ.sign r).Nonzero →
    ¬ N.IsTerminalStrongColinkage O r (N.reaction r).source → shelf r = Shelf.middle
  /-- Irreversible reactions are on the middle shelf. -/
  irreversible_middle : ∀ r : N.R, N.IrreversibleChannel r → shelf r = Shelf.middle
  /-- Within a terminal strong colinkage class, reactions belonging to the same ADA class receive
  the same shelf. -/
  terminal_colinkage_constant : ∀ r q : N.R,
    N.FullKernelCoordinateColinear O r q → (σ.sign r).Nonzero →
    N.IsTerminalStrongColinkage O r (N.reaction r).source →
    N.ColinearityClassStronglyLinked O r (N.reaction r).source (N.reaction q).source →
    shelf r = shelf q

namespace ADAShelving

variable {N : Network S} {O : N.ADAOrientation} {σ : N.ADATripletClassSigning O}

/-- Every irreversible reaction in a valid shelving is middle, independently of the colinkage
geometry. -/
@[simp] theorem shelf_eq_middle_of_irreversible
    (d : N.ADAShelving O σ) {r : N.R} (hr : N.IrreversibleChannel r) :
    d.shelf r = Shelf.middle :=
  d.irreversible_middle r hr

end ADAShelving

end Network
end CRNT
