import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen

/-!
# Proper local homeomorphisms onto connected spaces

A proper local homeomorphism has open and closed range.  If the domain is nonempty and the target
is preconnected, the range is therefore the whole target.
-/

namespace CRNT

open Set

/-- A proper local homeomorphism from a nonempty space onto a preconnected space is surjective. -/
theorem surjective_of_isProperMap_isLocalHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [PreconnectedSpace Y] {f : X → Y}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := by
    rw [← Set.image_univ]
    exact hl.isOpenMap _ isOpen_univ
  have hclosed : IsClosed (Set.range f) := by
    rw [← Set.image_univ]
    exact hp.isClosedMap _ isClosed_univ
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  have hne : Set.range f ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp (Set.range_nonempty f)
  have hrange : Set.range f = Set.univ :=
    (isClopen_iff.mp hclopen).resolve_left hne
  exact Set.range_eq_univ.mp hrange

end CRNT
