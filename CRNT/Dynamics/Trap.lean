import CRNT.Dynamics.Siphon
import CRNT.Graph.Reversibility

/-!
# Traps, semilocking sets, and reversible siphon/trap duality

In Petri-net language a siphon (semilocking set) cannot receive a token unless it
already contains one, whereas a trap cannot lose its last token: every reaction
consuming a species in the trap also produces a species in the trap.

For reversible CRNs the two notions coincide.  This gives a useful purely structural
bridge between the siphon language common in CRNT persistence theory and the
siphon/trap language of Petri nets.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `SemilockingSet` is the traditional CRNT synonym for `IsSiphon`. -/
abbrev IsSemilockingSet (N : Network S) (P : Finset S) : Prop := N.IsSiphon P

/-- A trap is a species set such that every reaction consuming a member also produces
some member.  Once a trap contains positive token count in the discrete Petri-net
semantics, reactions cannot remove the last token from the set. -/
def IsTrap (N : Network S) (P : Finset S) : Prop :=
  ∀ r : N.R, (∃ s ∈ P, N.IsReactant r s) → (∃ s ∈ P, N.IsProduct r s)

instance decidableIsTrap (N : Network S) (P : Finset S) : Decidable (N.IsTrap P) :=
  inferInstanceAs (Decidable
    (∀ r : N.R, (∃ s ∈ P, N.IsReactant r s) → (∃ s ∈ P, N.IsProduct r s)))

/-- The empty species set is a trap. -/
theorem empty_isTrap (N : Network S) : N.IsTrap ∅ := by
  intro r h
  rcases h with ⟨s, hs, _⟩
  simp at hs

/-- Traps are closed under union. -/
theorem union_isTrap (N : Network S) {P Q : Finset S}
    (hP : N.IsTrap P) (hQ : N.IsTrap Q) : N.IsTrap (P ∪ Q) := by
  intro r hr
  rcases hr with ⟨s, hs, hreact⟩
  rcases Finset.mem_union.mp hs with hsP | hsQ
  · obtain ⟨t, ht, hprod⟩ := hP r ⟨s, hsP, hreact⟩
    exact ⟨t, Finset.mem_union_left Q ht, hprod⟩
  · obtain ⟨t, ht, hprod⟩ := hQ r ⟨s, hsQ, hreact⟩
    exact ⟨t, Finset.mem_union_right P ht, hprod⟩

/-- A minimal nonempty trap. -/
def IsMinimalTrap (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsTrap P ∧
    ∀ Q ∈ P.powerset, Q.Nonempty → Q ≠ P → ¬ N.IsTrap Q

/-- Finite set of all support-minimal traps. -/
noncomputable def minimalTraps (N : Network S) : Finset (Finset S) := by
  classical
  exact (Finset.univ : Finset S).powerset.filter (fun P => N.IsMinimalTrap P)

@[simp] theorem mem_minimalTraps (N : Network S) (P : Finset S) :
    P ∈ N.minimalTraps ↔ N.IsMinimalTrap P := by
  classical
  simp [minimalTraps]

/-- On a reversible reaction graph, every siphon is a trap. -/
theorem IsSiphon.isTrap_of_reversible {N : Network S} {P : Finset S}
    (hrev : N.Reversible) (hP : N.IsSiphon P) : N.IsTrap P := by
  intro r hr
  rcases hr with ⟨s, hsP, hreact⟩
  rcases hrev r with ⟨r', hsrc, htgt⟩
  have hprod' : N.IsProduct r' s := by
    simp only [IsProduct, IsReactant] at hreact ⊢
    simpa [htgt] using hreact
  obtain ⟨t, htP, hreact'⟩ := hP r' ⟨s, hsP, hprod'⟩
  refine ⟨t, htP, ?_⟩
  simp only [IsReactant, IsProduct] at hreact' ⊢
  simpa [hsrc] using hreact'

/-- On a reversible reaction graph, every trap is a siphon. -/
theorem IsTrap.isSiphon_of_reversible {N : Network S} {P : Finset S}
    (hrev : N.Reversible) (hP : N.IsTrap P) : N.IsSiphon P := by
  intro r hr
  rcases hr with ⟨s, hsP, hprod⟩
  rcases hrev r with ⟨r', hsrc, htgt⟩
  have hreact' : N.IsReactant r' s := by
    simp only [IsReactant, IsProduct] at hprod ⊢
    simpa [hsrc] using hprod
  obtain ⟨t, htP, hprod'⟩ := hP r' ⟨s, hsP, hreact'⟩
  refine ⟨t, htP, ?_⟩
  simp only [IsProduct, IsReactant] at hprod' ⊢
  simpa [htgt] using hprod'

/-- **Reversible siphon/trap equivalence.** -/
theorem siphon_iff_trap_of_reversible (N : Network S) (hrev : N.Reversible)
    (P : Finset S) : N.IsSiphon P ↔ N.IsTrap P :=
  ⟨fun h => IsSiphon.isTrap_of_reversible hrev h,
   fun h => IsTrap.isSiphon_of_reversible hrev h⟩

/-- More directly stated reversible siphon/trap equivalence. -/
theorem reversible_isSiphon_iff_isTrap (N : Network S) (hrev : N.Reversible)
    (P : Finset S) : N.IsSiphon P ↔ N.IsTrap P := by
  constructor
  · exact fun h => IsSiphon.isTrap_of_reversible hrev h
  · exact fun h => IsTrap.isSiphon_of_reversible hrev h

/-- Minimal siphons and minimal traps coincide in reversible networks. -/
theorem reversible_minimalSiphon_iff_minimalTrap (N : Network S)
    (hrev : N.Reversible) (P : Finset S) :
    N.IsMinimalSiphon P ↔ N.IsMinimalTrap P := by
  unfold IsMinimalSiphon IsMinimalTrap
  simp only [N.reversible_isSiphon_iff_isTrap hrev]

end Network
end CRNT
