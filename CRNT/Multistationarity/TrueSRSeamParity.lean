import CRNT.Multistationarity.TrueSRTwoGluedCycles

/-!
# The seam pigeonhole for the parity argument

Counting c-pairs of a glued cycle: a c-pair sits at each *reaction* vertex, comparing the
endpoint complexes of the two edges meeting there.  For `glueCycle P Q` the reaction vertices
are `P`'s reactions, `Q`'s reactions, and the single shared end reaction, so

  `numCPairs (glueCycle P Q) = c(P) + c(Q) + s(P,Q)`

where `c(·)` is intrinsic to each path and `s(P,Q) ∈ {0,1}` records whether `P`'s last edge and
`Q`'s last edge carry the same endpoint complex.  (The other shared vertex is the start
*species*, at an even walk position, which contributes no c-pair.)

For three paths `P₁, P₂, P₃` with common endpoints this gives, modulo 2,

  `numCPairs C₁₂ + numCPairs C₁₃ + numCPairs C₂₃ ≡ s₁₂ + s₁₃ + s₂₃`,

and the three last edges all meet the same reaction vertex, so their endpoints lie in a
two-element set — whence at least two agree, and the number of agreeing pairs among three
values in a two-set is `3` or `1`, always **odd**.

So in the species-to-reaction case the conclusion is that an **odd number of the three glued
cycles is even** — equivalently, if two are odd the third is even.  This is *not* the same as
Shinar--Feinberg Lemmas A.4/A.5 (arXiv:1203.6560), which concern three paths between two
*reaction* vertices or two *species* vertices; there both shared vertices are of the same kind,
contributing two seam terms rather than one, and the conclusion flips to "if two are even so is
the third".  Worth knowing before porting those lemmas verbatim.

This file supplies the pigeonhole step.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Three values in a two-element set: two of them agree. -/
theorem two_eq_of_three_in_pair {α : Type*} {a b c x y : α}
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) (hc : c = x ∨ c = y) :
    a = b ∨ a = c ∨ b = c := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Or.inl (ha.trans hb.symm)
  · exact Or.inl (ha.trans hb.symm)
  · exact Or.inr (Or.inl (ha.trans hc.symm))
  · exact Or.inr (Or.inr (hb.trans hc.symm))
  · exact Or.inr (Or.inr (hb.trans hc.symm))
  · exact Or.inr (Or.inl (ha.trans hc.symm))
  · exact Or.inl (ha.trans hb.symm)
  · exact Or.inl (ha.trans hb.symm)

/-- Edges of one true reaction have their endpoints among that reaction's two complexes:
the unordered endpoint pair is class-determined. -/
theorem endpoint_pair_of_sameReaction {e f : N.TrueSREdge} (h : e.reaction = f.reaction) :
    (e.endpoint = (N.reaction f.representative).source ∨
      e.endpoint = (N.reaction f.representative).target) := by
  have hs : N.SameTrueReaction e.representative f.representative :=
    Quotient.exact ((e.representative_class).trans (h.trans (f.representative_class).symm))
  rcases e.endpoint_is_source_or_target with he | he
  · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (he.trans h1)
    · exact Or.inr (he.trans h1)
  · rcases hs with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inr (he.trans h2)
    · exact Or.inl (he.trans h2)

/-- **Seam pigeonhole.**  Among three true-SR edges at the same reaction vertex, two carry the
same endpoint complex.  This is what makes the three seam indicators sum to an odd number. -/
theorem two_endpoints_eq_of_three_at_same_reaction {e₁ e₂ e₃ : N.TrueSREdge}
    (h₁ : e₁.reaction = e₃.reaction) (h₂ : e₂.reaction = e₃.reaction) :
    e₁.endpoint = e₂.endpoint ∨ e₁.endpoint = e₃.endpoint ∨ e₂.endpoint = e₃.endpoint :=
  two_eq_of_three_in_pair
    (endpoint_pair_of_sameReaction h₁)
    (endpoint_pair_of_sameReaction h₂)
    (endpoint_pair_of_sameReaction (rfl : e₃.reaction = e₃.reaction))

end CRNT.Network
