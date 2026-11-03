import CRNT.Multistationarity.TrueSRPathAccessors

/-!
# Seams and cross-regime distinctness for the glue construction

Gluing two species-to-reaction paths into a cycle needs four facts beyond the accessors:

* at the **start seam**, the two paths' position-`0` species agree, so the glued walk closes;
* at the **end seam**, their final reactions agree, so the two halves meet;
* across regimes, a species read off `P` at a nonzero position differs from one read off `Q` at a
  nonzero position — this is what makes the glued cycle's `species` injective;
* likewise for reactions away from the final position.

The last two are exactly the `species_disjoint` / `reaction_disjoint` clauses of `Gluable`,
repackaged in the form the construction uses (an inequality between accessor values rather than
a statement about `InteriorSpecies`).
-/

namespace CRNT.Network.TrueSRPath.Gluable

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L M : ℕ}
  {P : N.TrueSRPath L} {Q : N.TrueSRPath M}

/-- **Start seam**: the two paths agree at position `0`. -/
theorem seam_start (h : Gluable P Q) (hp : ((0 : Fin (L + 1))).1 % 2 = 0)
    (hq : ((0 : Fin (M + 1))).1 % 2 = 0) :
    P.speciesAt 0 hp = Q.speciesAt 0 hq := by
  have h1 := P.startSpecies_eq
  have h2 := Q.startSpecies_eq
  have := h.same_start
  rw [h1, h2] at this
  exact this

/-- **End seam**: the two paths agree at their final position. -/
theorem seam_end (h : Gluable P Q)
    (hp : (Fin.last L).1 % 2 ≠ 0) (hq : (Fin.last M).1 % 2 ≠ 0) :
    P.reactionAt (Fin.last L) hp = Q.reactionAt (Fin.last M) hq := by
  have h1 := P.endReaction_eq
  have h2 := Q.endReaction_eq
  have := h.same_end
  rw [h1, h2] at this
  exact this

/-- **Cross-regime species distinctness.**  A species read off `P` away from position `0`
differs from one read off `Q` away from position `0`. -/
theorem species_ne (h : Gluable P Q) {p : Fin (L + 1)} {q : Fin (M + 1)}
    (hp0 : p.1 ≠ 0) (hq0 : q.1 ≠ 0)
    (hp : p.1 % 2 = 0) (hq : q.1 % 2 = 0) :
    P.speciesAt p hp ≠ Q.speciesAt q hq := by
  intro heq
  refine h.species_disjoint (P.speciesAt p hp) ⟨p, hp0, P.vertex_eq_speciesAt p hp⟩ ?_
  refine ⟨q, hq0, ?_⟩
  rw [Q.vertex_eq_speciesAt q hq, heq]

/-- **Cross-regime reaction distinctness.**  A reaction read off `P` away from its final
position differs from one read off `Q` away from its final position. -/
theorem reaction_ne (h : Gluable P Q) {p : Fin (L + 1)} {q : Fin (M + 1)}
    (hpL : p.1 ≠ L) (hqM : q.1 ≠ M)
    (hp : p.1 % 2 ≠ 0) (hq : q.1 % 2 ≠ 0) :
    P.reactionAt p hp ≠ Q.reactionAt q hq := by
  intro heq
  refine h.reaction_disjoint (P.reactionAt p hp) ⟨p, hpL, P.vertex_eq_reactionAt p hp⟩ ?_
  refine ⟨q, hqM, ?_⟩
  rw [Q.vertex_eq_reactionAt q hq, heq]

/-- The glued cycle's `species` is injective within the `P` regime. -/
theorem speciesAt_inj (P : N.TrueSRPath L) {p p' : Fin (L + 1)}
    (hp : p.1 % 2 = 0) (hp' : p'.1 % 2 = 0)
    (heq : P.speciesAt p hp = P.speciesAt p' hp') : p = p' := by
  apply P.vertex_simple
  rw [P.vertex_eq_speciesAt p hp, P.vertex_eq_speciesAt p' hp', heq]

/-- The glued cycle's `reaction` is injective within the `P` regime. -/
theorem reactionAt_inj (P : N.TrueSRPath L) {p p' : Fin (L + 1)}
    (hp : p.1 % 2 ≠ 0) (hp' : p'.1 % 2 ≠ 0)
    (heq : P.reactionAt p hp = P.reactionAt p' hp') : p = p' := by
  apply P.vertex_simple
  rw [P.vertex_eq_reactionAt p hp, P.vertex_eq_reactionAt p' hp', heq]

end CRNT.Network.TrueSRPath.Gluable
