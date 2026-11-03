import CRNT.Multistationarity.TrueSRGlueCount

/-!
# The parity ingredients

From `glueCycle_numCPairs_split`, for three paths with common endpoints the intrinsic terms
`c(P₁), c(P₂), c(P₃)` each occur in exactly two of the three sums, so modulo 2 only the three
seam indicators survive.  Each seam indicator compares two of the three paths' **last** edges,
and all three of those are incident to the shared end reaction, so their endpoints lie in a
two-element set.  Two facts are needed and are proved here: the mod-2 count of agreeing pairs
among three values in a two-set is always `1`, and a path's last edge is incident to its end
reaction.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Among three values in a two-element set, the number of agreeing pairs is **odd**. -/
theorem odd_agree_count {α : Type*} [DecidableEq α] {a b c x y : α}
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) (hc : c = x ∨ c = y) :
    ((if a = b then 1 else 0) + (if a = c then 1 else 0)
      + (if b = c then 1 else 0)) % 2 = 1 := by
  by_cases hxy : x = y
  · subst hxy
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      subst ha <;> subst hb <;> subst hc <;> simp
  · rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      subst ha <;> subst hb <;> subst hc <;> simp [hxy, Ne.symm hxy]

namespace TrueSRPath

/-- A path's last edge is incident to its end reaction. -/
theorem last_edge_reaction {j : ℕ} (P : N.TrueSRPath (2 * j + 1))
    (hb : 2 * j < 2 * j + 1) :
    (P.edge ⟨2 * j, hb⟩).reaction = (P.endReaction).1 := by
  have h1 := P.edge_reaction_of_even ⟨2 * j, hb⟩ (by show (2 * j) % 2 = 0; omega)
  have hodd : ((⟨2 * j, hb⟩ : Fin (2 * j + 1)).succ).1 % 2 ≠ 0 := by
    show (2 * j + 1) % 2 ≠ 0
    omega
  have h3 := P.vertex_eq_reactionAt ((⟨2 * j, hb⟩ : Fin (2 * j + 1)).succ) hodd
  have h2 : P.vertex ((⟨2 * j, hb⟩ : Fin (2 * j + 1)).succ) = Sum.inr P.endReaction :=
    (congrArg P.vertex
      (Fin.ext (rfl : ((⟨2 * j, hb⟩ : Fin (2 * j + 1)).succ).1
        = (Fin.last (2 * j + 1)).1))).trans P.vertex_last
  rw [h1]
  exact congrArg Subtype.val (Sum.inr.inj (h3.symm.trans h2))

/-- Two paths sharing an end reaction have last edges at the same reaction vertex. -/
theorem last_edges_same_reaction {j k : ℕ} (P : N.TrueSRPath (2 * j + 1))
    (R : N.TrueSRPath (2 * k + 1)) (hend : P.endReaction = R.endReaction)
    (hb : 2 * j < 2 * j + 1) (hb' : 2 * k < 2 * k + 1) :
    (P.edge ⟨2 * j, hb⟩).reaction = (R.edge ⟨2 * k, hb'⟩).reaction := by
  rw [last_edge_reaction P hb, last_edge_reaction R hb', hend]

end TrueSRPath

end CRNT.Network
