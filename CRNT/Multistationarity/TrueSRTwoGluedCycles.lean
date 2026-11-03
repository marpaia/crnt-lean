import CRNT.Multistationarity.TrueSRWalkEdges

/-!
# Two cycles glued from a common chord

This is the payoff form of Banaji--Craciun's Lemma 10 (arXiv:0809.1308).  A chord `P` glued to
two edge-disjoint arcs `Q₁`, `Q₂` produces two cycles whose common edges are exactly `P`'s.
If both are even, `hSR.2` forbids it.

The common-edge computation is where `Gluable`'s `edge_disjoint` clause earns its place: a `P`
edge cannot also be a `Q` edge, so the four cases of "common to both glued cycles" collapse to
"is a `P` edge".
-/

namespace CRNT.Network.TrueSREdge

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

theorem SameIncidence.refl (e : N.TrueSREdge) : e.SameIncidence e := ⟨rfl, rfl, rfl⟩

theorem SameIncidence.symm {e f : N.TrueSREdge} (h : e.SameIncidence f) : f.SameIncidence e :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameIncidence.trans {e f g : N.TrueSREdge}
    (h1 : e.SameIncidence f) (h2 : f.SameIncidence g) : e.SameIncidence g :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

end CRNT.Network.TrueSREdge

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

open TrueSRPath TrueSREdge

/-- **Two even cycles glued from a common chord are forbidden.**

`P` is the chord; `Q₁`, `Q₂` are the two arcs, edge-disjoint from each other and (via
`Gluable`) from `P`.  The two glued cycles then intersect exactly in `P`, which is a
species-to-reaction path, so `hSR.2` applies. -/
theorem no_two_glued_cycles_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {i j k : ℕ}
    (P : N.TrueSRPath (2 * j + 1)) (Q₁ : N.TrueSRPath (2 * i + 1))
    (Q₂ : N.TrueSRPath (2 * k + 1))
    (h₁ : Gluable P Q₁) (h₂ : Gluable P Q₂)
    (hQ : ∀ a b, ¬ (Q₁.edge a).SameIncidence (Q₂.edge b))
    (hn₁ : 2 ≤ i + j + 1) (hn₂ : 2 ≤ k + j + 1)
    (hE₁ : (glueCycle P Q₁ h₁ hn₁).Even) (hE₂ : (glueCycle P Q₂ h₂ hn₂).Even) :
    False := by
  refine no_shared_path_of_trueSRCriterion N hSR (glueCycle P Q₁ h₁ hn₁)
    (glueCycle P Q₂ h₂ hn₂) hE₁ hE₂ P ?_ ?_ ?_
  · -- every chord edge lies on the first glued cycle
    intro p
    exact (glueCycle_containsEdge_iff P Q₁ h₁ hn₁ (P.edge p)).mpr
      (Or.inl ⟨p, SameIncidence.refl _⟩)
  · -- and on the second
    intro p
    exact (glueCycle_containsEdge_iff P Q₂ h₂ hn₂ (P.edge p)).mpr
      (Or.inl ⟨p, SameIncidence.refl _⟩)
  · -- the common edges are exactly the chord's
    intro f hf₁ hf₂
    rcases (glueCycle_containsEdge_iff P Q₁ h₁ hn₁ f).mp hf₁ with ⟨p, hp⟩ | ⟨a, ha⟩
    · exact ⟨p, hp⟩
    · rcases (glueCycle_containsEdge_iff P Q₂ h₂ hn₂ f).mp hf₂ with ⟨p, hp⟩ | ⟨b, hb⟩
      · exact absurd (SameIncidence.trans (SameIncidence.symm hp) ha) (h₁.edge_disjoint p a)
      · exact absurd (SameIncidence.trans (SameIncidence.symm ha) hb) (hQ a b)

end CRNT.Network
