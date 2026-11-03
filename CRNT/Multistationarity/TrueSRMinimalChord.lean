import CRNT.Multistationarity.TrueSRSegmentEndpoints

/-!
# A minimal chord has interior disjoint from the cycle

Banaji--Craciun's Lemma 10 assumes only that the chord is *edge*-disjoint from the cycle, while
`Gluable` demands interior *vertex*-disjointness.  This file closes that gap by the standard
minimality argument: if a shortest chord had an interior vertex on the cycle, cutting there
would give a shorter chord — an initial cut if that vertex is a reaction, a terminal cut if it
is a species, since a chord must run species-to-reaction.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n L : ℕ}

/-- A species occurring on a cycle. -/
def TrueSRCycle.HasSpecies (C : N.TrueSRCycle n) (s : S) : Prop := ∃ t, C.species t = s

/-- A reaction occurring on a cycle. -/
def TrueSRCycle.HasReaction (C : N.TrueSRCycle n) (ρ : N.TrueReaction) : Prop :=
  ∃ t, C.reaction t = ρ

/-- A vertex lying on a cycle. -/
def TrueSRCycle.HasVertex (C : N.TrueSRCycle n) : N.TrueSRVertex → Prop
  | Sum.inl s => C.HasSpecies s
  | Sum.inr ρ => C.HasReaction ρ.1

/-- A chord of `C`: a species-to-reaction path with both endpoints on `C`, edge-disjoint
from `C`. -/
def TrueSRCycle.IsChord (C : N.TrueSRCycle n) (P : N.TrueSRPath L) : Prop :=
  C.HasSpecies P.startSpecies ∧ C.HasReaction (P.endReaction).1 ∧
    (∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t)) ∧
    (∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t))

namespace TrueSRPath

/-- An initial cut at a reaction vertex of `C` is again a chord. -/
theorem isChord_initialSegment {C : N.TrueSRCycle n} {P : N.TrueSRPath L}
    (hC : C.IsChord P) (m : ℕ) (hm : m ≤ L) (hodd : m % 2 = 1)
    (hv : C.HasReaction (P.reactionAt ⟨m, by omega⟩ (by show m % 2 ≠ 0; omega)).1) :
    C.IsChord (P.initialSegment m hm hodd) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [initialSegment_startSpecies]; exact hC.1
  · rw [initialSegment_endReaction]; exact hv
  · intro p t
    obtain ⟨q, hq⟩ := initialSegment_edge_mem P m hm hodd p
    rw [hq]; exact hC.2.2.1 q t
  · intro p t
    obtain ⟨q, hq⟩ := initialSegment_edge_mem P m hm hodd p
    rw [hq]; exact hC.2.2.2 q t

/-- A terminal cut at a species vertex of `C` is again a chord. -/
theorem isChord_terminalSegment {C : N.TrueSRCycle n} {P : N.TrueSRPath L}
    (hC : C.IsChord P) (m : ℕ) (hm : m < L) (heven : m % 2 = 0)
    (hv : C.HasSpecies (P.speciesAt ⟨m, by omega⟩ heven)) :
    C.IsChord (P.terminalSegment m hm heven) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [terminalSegment_startSpecies]; exact hv
  · rw [terminalSegment_endReaction]; exact hC.2.1
  · intro p t
    obtain ⟨q, hq⟩ := terminalSegment_edge_mem P m hm heven p
    rw [hq]; exact hC.2.2.1 q t
  · intro p t
    obtain ⟨q, hq⟩ := terminalSegment_edge_mem P m hm heven p
    rw [hq]; exact hC.2.2.2 q t

/-- **A shortest chord has interior disjoint from the cycle.** -/
theorem minimal_chord_interior_disjoint {C : N.TrueSRCycle n} {P : N.TrueSRPath L}
    (hC : C.IsChord P)
    (hmin : ∀ (M : ℕ) (R : N.TrueSRPath M), C.IsChord R → L ≤ M)
    (p : Fin (L + 1)) (hp0 : p.1 ≠ 0) (hpL : p.1 ≠ L) :
    ¬ C.HasVertex (P.vertex p) := by
  have hplt := p.isLt
  intro hon
  rcases Nat.even_or_odd p.1 with hev | hod
  · -- a species vertex: cut terminally
    have heven : p.1 % 2 = 0 := Nat.even_iff.mp hev
    have hvs := P.vertex_eq_speciesAt p heven
    have hsp : C.HasSpecies (P.speciesAt p heven) := by
      rw [hvs] at hon; exact hon
    have hlt : p.1 < L := by omega
    have := hmin (L - p.1) (P.terminalSegment p.1 hlt heven)
      (isChord_terminalSegment hC p.1 hlt heven hsp)
    omega
  · -- a reaction vertex: cut initially
    have hoddp : p.1 % 2 = 1 := Nat.odd_iff.mp hod
    have hvr := P.vertex_eq_reactionAt p (by omega)
    have hrx : C.HasReaction (P.reactionAt p (by omega)).1 := by
      rw [hvr] at hon; exact hon
    have := hmin p.1 (P.initialSegment p.1 (by omega) hoddp)
      (isChord_initialSegment hC p.1 (by omega) hoddp hrx)
    omega

/-- Any edge-disjoint chord can be shortened until its interior misses the cycle.  At an
interior reaction use the initial segment; at an interior species use the terminal segment.
Each cut remains a chord and strictly decreases its length, so the process terminates. -/
theorem exists_chord_with_interior_off_cycle {C : N.TrueSRCycle n}
    {P : N.TrueSRPath L} (hC : C.IsChord P) :
    ∃ M : ℕ, ∃ Q : N.TrueSRPath M, C.IsChord Q ∧
      ∀ p : Fin (M + 1), p.1 ≠ 0 → p.1 ≠ M → ¬ C.HasVertex (Q.vertex p) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      classical
      by_cases hclean : ∀ p : Fin (L + 1),
          p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p)
      · exact ⟨L, P, hC, hclean⟩
      · have hhit : ∃ p : Fin (L + 1),
            p.1 ≠ 0 ∧ p.1 ≠ L ∧ C.HasVertex (P.vertex p) := by
          by_contra h
          apply hclean
          intro p hp0 hpL hvertex
          exact h ⟨p, hp0, hpL, hvertex⟩
        obtain ⟨p, hp0, hpL, hvertex⟩ := hhit
        rcases Nat.even_or_odd p.1 with heven | hodd
        · have hpar : p.1 % 2 = 0 := Nat.even_iff.mp heven
          have hlt : p.1 < L := by omega
          have hspecies : C.HasSpecies (P.speciesAt p hpar) := by
            rw [P.vertex_eq_speciesAt p hpar] at hvertex
            exact hvertex
          let Q := P.terminalSegment p.1 hlt hpar
          have hQ : C.IsChord Q := P.isChord_terminalSegment hC p.1 hlt hpar hspecies
          have hshort : L - p.1 < L :=
            terminalSegment_length_lt (by omega) hlt
          exact ih (L - p.1) hshort hQ
        · have hpar : p.1 % 2 = 1 := Nat.odd_iff.mp hodd
          have hreaction : C.HasReaction (P.reactionAt p (by omega)).1 := by
            rw [P.vertex_eq_reactionAt p (by omega)] at hvertex
            exact hvertex
          let Q := P.initialSegment p.1 (by omega) hpar
          have hQ : C.IsChord Q := P.isChord_initialSegment hC p.1 (by omega) hpar hreaction
          exact ih p.1 (by omega) hQ

end TrueSRPath

end CRNT.Network
