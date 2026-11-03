import CRNT.Dynamics.Siphon
import CRNT.Graph.WeakReversibility
import CRNT.Graph.LinkageClass

/-!
# Siphons of weakly reversible networks are unions of linkage classes

Say a complex *meets* a species set `P` when some species of `P` occurs in it.

**Theorem (Shiu–Sturmfels 2010).**  In a weakly reversible network, `P` is a siphon iff along
every reaction the source meets `P` exactly when the target does
(`isSiphon_iff_of_weaklyReversible`).  Equivalently, linked complexes either both meet `P` or
both avoid it (`meets_iff_of_linked`): the complexes meeting a siphon form a union of linkage
classes.

The backward direction holds for every network.  For the forward direction, the siphon
condition says exactly that meeting `P` propagates backward along each reaction
(`meets_of_reaches`); weak reversibility returns from each target to its source.

Consequences used in persistence arguments: in a weakly reversible network no reaction leads
from a complex meeting a siphon to a complex avoiding it, and every reaction whose source meets
`P` produces a species of `P`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A complex meets `P` when some species of `P` occurs in it. -/
def Meets (P : Finset S) (c : Complex S) : Prop := ∃ s ∈ P, c s ≠ 0

/-- Under the siphon condition, meeting `P` propagates backward along reactions. -/
theorem meets_source_of_meets_target (N : Network S) {P : Finset S} (hP : N.IsSiphon P)
    (r : N.R) (h : Meets P (N.reaction r).target) : Meets P (N.reaction r).source :=
  hP r h

/-- Under the siphon condition, meeting `P` propagates backward along directed paths. -/
theorem meets_of_reaches (N : Network S) {P : Finset S} (hP : N.IsSiphon P)
    {c d : Complex S} (hcd : N.Reaches c d) (hd : Meets P d) : Meets P c := by
  induction hcd using Relation.ReflTransGen.head_induction_on with
  | refl => exact hd
  | head hstep _ ih =>
    obtain ⟨r, hsrc, htgt⟩ := hstep
    have := N.meets_source_of_meets_target hP r (by rw [htgt]; exact ih)
    rwa [hsrc] at this

/-- **Siphons of weakly reversible networks.** -/
theorem isSiphon_iff_of_weaklyReversible (N : Network S) (hwr : N.WeaklyReversible)
    (P : Finset S) :
    N.IsSiphon P ↔ ∀ r : N.R, Meets P (N.reaction r).source ↔ Meets P (N.reaction r).target := by
  constructor
  · intro hP r
    exact ⟨fun hs => N.meets_of_reaches hP (hwr r) hs, fun ht => N.meets_source_of_meets_target hP r ht⟩
  · intro h r hprod
    exact (h r).mpr hprod

/-- **Linked complexes agree on meeting a siphon** (weakly reversible networks). -/
theorem meets_iff_of_linked (N : Network S) (hwr : N.WeaklyReversible) {P : Finset S}
    (hP : N.IsSiphon P) {c d : Complex S} (hcd : N.Linked c d) : Meets P c ↔ Meets P d := by
  have hstep := (N.isSiphon_iff_of_weaklyReversible hwr P).mp hP
  induction hcd with
  | refl => exact Iff.rfl
  | tail _ hedge ih =>
    refine ih.trans ?_
    rcases hedge with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
    · rw [← hs, ← ht]; exact hstep r
    · rw [← hs, ← ht]; exact (hstep r).symm

end Network
end CRNT
