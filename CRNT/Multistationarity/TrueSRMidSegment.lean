import CRNT.Multistationarity.TrueSRPathTerminalSegment
import CRNT.Multistationarity.TrueSRPathAccessors

/-!
# Middle segments of a species-to-reaction path, and the odd-gap lemma

Extracting a chord from a walk whose two ends lie on a cycle needs two ingredients, supplied
here.

`midSegment` reads off the piece of a path between an even position `a` (a species vertex) and
a later odd position `b` (a reaction vertex).  It is the composition of the two cuts already
available, `terminalSegment` at `a` followed by `initialSegment` at `b - a`, so its vertices and
edges are literally those of the ambient path, shifted by `a`.

`exists_odd_gap_of_odd` is the counting step.  Mark the positions of a path that lie on the
cycle; positions `0` and `L` are marked, and `L` is odd because a species-to-reaction path has
odd length (`TrueSRPath.odd_length`).  The marked positions cut `[0, L]` into consecutive gaps
whose lengths sum to `L`, so at least one gap is odd.  A gap of odd length runs species-to-
reaction or reaction-to-species, and has no marked position strictly inside it — which is
exactly "interior off the cycle".
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {L : ℕ}

/-- The segment of a path between an even position `a` and a later odd position `b`: a
species-to-reaction path in its own right. -/
def midSegment (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 1)
    (hab : a < b) (hbL : b ≤ L) : N.TrueSRPath (b - a) :=
  (P.terminalSegment a (by omega) ha).initialSegment (b - a) (by omega) (by omega)

@[simp] theorem midSegment_vertex (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 0)
    (hb : b % 2 = 1) (hab : a < b) (hbL : b ≤ L) (p : Fin (b - a + 1)) :
    (P.midSegment a b ha hb hab hbL).vertex p =
      P.vertex ⟨a + p.1, by have := p.isLt; omega⟩ := rfl

@[simp] theorem midSegment_edge (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 0)
    (hb : b % 2 = 1) (hab : a < b) (hbL : b ≤ L) (q : Fin (b - a)) :
    (P.midSegment a b ha hb hab hbL).edge q =
      P.edge ⟨a + q.1, by have := q.isLt; omega⟩ := rfl

/-- A middle segment starts at the species sitting at its left endpoint. -/
theorem midSegment_startSpecies (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 0)
    (hb : b % 2 = 1) (hab : a < b) (hbL : b ≤ L) :
    (P.midSegment a b ha hb hab hbL).startSpecies =
      P.speciesAt ⟨a, by omega⟩ ha := by
  have h1 := (P.midSegment a b ha hb hab hbL).vertex_zero
  rw [midSegment_vertex] at h1
  have h2 : P.vertex ⟨a + ((0 : Fin (b - a + 1))).1, by omega⟩ = P.vertex ⟨a, by omega⟩ :=
    congrArg P.vertex (Fin.ext (by show a + 0 = a; omega))
  rw [h2, P.vertex_eq_speciesAt ⟨a, by omega⟩ ha] at h1
  exact (Sum.inl.inj h1).symm

/-- A middle segment ends at the reaction sitting at its right endpoint. -/
theorem midSegment_endReaction (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 0)
    (hb : b % 2 = 1) (hab : a < b) (hbL : b ≤ L) :
    (P.midSegment a b ha hb hab hbL).endReaction =
      P.reactionAt ⟨b, by omega⟩ (by show b % 2 ≠ 0; omega) := by
  have h1 := (P.midSegment a b ha hb hab hbL).vertex_last
  rw [midSegment_vertex] at h1
  have h2 : P.vertex ⟨a + (Fin.last (b - a)).1, by omega⟩ = P.vertex ⟨b, by omega⟩ :=
    congrArg P.vertex (Fin.ext (by show a + (b - a) = b; omega))
  rw [h2, P.vertex_eq_reactionAt ⟨b, by omega⟩ (by show b % 2 ≠ 0; omega)] at h1
  exact (Sum.inr.inj h1).symm

/-- The piece of a path between an odd position `a` (a reaction vertex) and a later even
position `b` (a species vertex), read **backwards**, so that it is again a species-to-reaction
path.  Half the gaps produced by `exists_odd_gap_of_odd` run this way round. -/
def midSegmentRev (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hab : a < b) (hbL : b ≤ L) : N.TrueSRPath (b - a) where
  length_pos := by omega
  edge := fun q => P.edge ⟨b - 1 - q.1, by have := q.isLt; omega⟩
  vertex := fun p => P.vertex ⟨b - p.1, by have := p.isLt; omega⟩
  connects := by
    intro q
    have hq := q.isLt
    have hc := P.connects ⟨b - 1 - q.1, by omega⟩
    show (P.edge ⟨b - 1 - q.1, by omega⟩).Connects
      (P.vertex ⟨b - q.1, by omega⟩)
      (P.vertex ⟨b - (q.1 + 1), by omega⟩)
    have e1 : (⟨b - q.1, by omega⟩ : Fin (L + 1)) = ⟨b - 1 - q.1 + 1, by omega⟩ :=
      Fin.ext (by show b - q.1 = b - 1 - q.1 + 1; omega)
    have e2 : (⟨b - (q.1 + 1), by omega⟩ : Fin (L + 1)) = ⟨b - 1 - q.1, by omega⟩ :=
      Fin.ext (by show b - (q.1 + 1) = b - 1 - q.1; omega)
    rw [e1, e2]
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  edge_simple := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have h := P.edge_simple hij
    have hv := congrArg Fin.val h
    simp only at hv
    exact Fin.ext (by omega)
  vertex_simple := by
    intro p p' hpp'
    have hp := p.isLt
    have hp' := p'.isLt
    have h := P.vertex_simple hpp'
    have hv := congrArg Fin.val h
    simp only at hv
    exact Fin.ext (by omega)
  starts_at_species := by
    obtain ⟨x, hx⟩ := (P.species_iff_even b (by omega)).mpr (Nat.even_iff.mpr hb)
    refine ⟨x, ?_⟩
    show P.vertex ⟨b - ((0 : Fin (b - a + 1))).1, by omega⟩ = Sum.inl x
    exact (congrArg P.vertex (Fin.ext (by show b - 0 = b; omega))).trans hx
  ends_at_reaction := by
    obtain ⟨ρ, hρ⟩ := P.exists_reaction_of_odd ⟨a, by omega⟩ (by show a % 2 ≠ 0; omega)
    refine ⟨ρ, ?_⟩
    show P.vertex ⟨b - (Fin.last (b - a)).1, by omega⟩ = Sum.inr ρ
    exact (congrArg P.vertex (Fin.ext (by show b - (b - a) = a; omega))).trans hρ

@[simp] theorem midSegmentRev_vertex (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 1)
    (hb : b % 2 = 0) (hab : a < b) (hbL : b ≤ L) (p : Fin (b - a + 1)) :
    (P.midSegmentRev a b ha hb hab hbL).vertex p =
      P.vertex ⟨b - p.1, by have := p.isLt; omega⟩ := rfl

@[simp] theorem midSegmentRev_edge (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 1)
    (hb : b % 2 = 0) (hab : a < b) (hbL : b ≤ L) (q : Fin (b - a)) :
    (P.midSegmentRev a b ha hb hab hbL).edge q =
      P.edge ⟨b - 1 - q.1, by have := q.isLt; omega⟩ := rfl

/-- The reversed segment starts at the species sitting at the right endpoint. -/
theorem midSegmentRev_startSpecies (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 1)
    (hb : b % 2 = 0) (hab : a < b) (hbL : b ≤ L) :
    (P.midSegmentRev a b ha hb hab hbL).startSpecies = P.speciesAt ⟨b, by omega⟩ hb := by
  have h1 := (P.midSegmentRev a b ha hb hab hbL).vertex_zero
  rw [midSegmentRev_vertex] at h1
  have h2 : P.vertex ⟨b - ((0 : Fin (b - a + 1))).1, by omega⟩ = P.vertex ⟨b, by omega⟩ :=
    congrArg P.vertex (Fin.ext (by show b - 0 = b; omega))
  rw [h2, P.vertex_eq_speciesAt ⟨b, by omega⟩ hb] at h1
  exact (Sum.inl.inj h1).symm

/-- The reversed segment ends at the reaction sitting at the left endpoint. -/
theorem midSegmentRev_endReaction (P : N.TrueSRPath L) (a b : ℕ) (ha : a % 2 = 1)
    (hb : b % 2 = 0) (hab : a < b) (hbL : b ≤ L) :
    (P.midSegmentRev a b ha hb hab hbL).endReaction =
      P.reactionAt ⟨a, by omega⟩ (by show a % 2 ≠ 0; omega) := by
  have h1 := (P.midSegmentRev a b ha hb hab hbL).vertex_last
  rw [midSegmentRev_vertex] at h1
  have h2 : P.vertex ⟨b - (Fin.last (b - a)).1, by omega⟩ = P.vertex ⟨a, by omega⟩ :=
    congrArg P.vertex (Fin.ext (by show b - (b - a) = a; omega))
  rw [h2, P.vertex_eq_reactionAt ⟨a, by omega⟩ (by show a % 2 ≠ 0; omega)] at h1
  exact (Sum.inr.inj h1).symm

end CRNT.Network.TrueSRPath

namespace CRNT

/-- **The odd-gap lemma.**  If `0` and `L` are marked, and `L` is odd, then two consecutive
marked positions are an odd distance apart.

This is the counting step behind chord extraction: marking the positions of a path that lie on
a cycle, some gap between consecutive marked positions has odd length, hence runs
species-to-reaction or reaction-to-species, and contains no marked position in its interior. -/
theorem exists_odd_gap_of_odd (M : ℕ → Prop) [DecidablePred M] (L : ℕ)
    (hM0 : M 0) (hML : M L) (hLodd : L % 2 = 1) :
    ∃ a b : ℕ, a < b ∧ b ≤ L ∧ M a ∧ M b ∧ (b - a) % 2 = 1 ∧
      ∀ d, a < d → d < b → ¬ M d := by
  classical
  -- Strengthened statement, proved by strong induction on the distance to `L`.
  have key : ∀ k : ℕ, ∀ a : ℕ, L - a = k → M a → a < L → (L - a) % 2 = 1 →
      ∃ a' b : ℕ, a' < b ∧ b ≤ L ∧ M a' ∧ M b ∧ (b - a') % 2 = 1 ∧
        ∀ d, a' < d → d < b → ¬ M d := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro a hak hMa haL hodd
      -- the least marked position strictly above `a`
      have hex : ∃ j : ℕ, M (a + 1 + j) := ⟨L - a - 1, by
        have : a + 1 + (L - a - 1) = L := by omega
        rw [this]; exact hML⟩
      set j := Nat.find hex with hj
      have hMj : M (a + 1 + j) := Nat.find_spec hex
      have hjle : a + 1 + j ≤ L := by
        by_contra hgt
        have hlt : L - a - 1 < j := by omega
        exact absurd (Nat.find_le (p := fun j => M (a + 1 + j)) (h := hex)
          (show M (a + 1 + (L - a - 1)) by
            have he : a + 1 + (L - a - 1) = L := by omega
            rw [he]; exact hML)) (by omega)
      have hmin : ∀ d, a < d → d < a + 1 + j → ¬ M d := by
        intro d hd1 hd2 hMd
        have hlt : d - a - 1 < j := by omega
        have := Nat.find_le (p := fun j => M (a + 1 + j)) (h := hex)
          (show M (a + 1 + (d - a - 1)) by
            have he : a + 1 + (d - a - 1) = d := by omega
            rw [he]; exact hMd)
        omega
      set b := a + 1 + j with hb
      by_cases hpar : (b - a) % 2 = 1
      · exact ⟨a, b, by omega, hjle, hMa, hMj, hpar, hmin⟩
      · -- an even gap: the remaining distance stays odd, so recurse from `b`
        have hbL : b < L := by
          rcases Nat.lt_or_ge b L with h | h
          · exact h
          · have hbeq : b = L := by omega
            rw [hbeq] at hpar
            omega
        refine ih (L - b) (by omega) b rfl hMj hbL ?_
        omega
  exact key (L - 0) 0 rfl hM0 (by omega) (by simpa using hLodd)

end CRNT
