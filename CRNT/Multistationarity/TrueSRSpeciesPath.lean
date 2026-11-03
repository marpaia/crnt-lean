import CRNT.Multistationarity.TrueSRPathAccessors
import CRNT.Multistationarity.TrueSRCycleSplit

/-!
# Species-to-species paths in the true-SR graph

`TrueSRPath` is species-to-reaction by construction, which is what the second conjunct of
`TrueSRStrongCriterion` quantifies over. The remaining case of the true-SR theorem is a chord
with *two species* endpoints, and that is not a `TrueSRPath` at all. This file introduces the
type, with the one structural fact needed to work with it: such a path has **even** length.

The parity argument does not repeat the alternation induction of `TrueSRPath.species_iff_even`.
A single application of `connects` at the last edge shows the penultimate vertex is a reaction
vertex, so dropping the last edge gives a genuine `TrueSRPath`, whose length is odd by
`TrueSRPath.odd_length`. Length one is impossible for the same reason: the two endpoints of a
single edge cannot both be species vertices.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- A simple species-to-species path in the true-SR graph: a vertex-injective alternating edge
sequence with a species vertex at each end. -/
structure TrueSRSSPath (N : Network S) (L : ℕ) where
  length_pos : 0 < L
  edge : Fin L → N.TrueSREdge
  vertex : Fin (L + 1) → N.TrueSRVertex
  connects : ∀ i, (edge i).Connects (vertex (Fin.castSucc i)) (vertex i.succ)
  edge_simple : ∀ {i j}, (edge i).SameIncidence (edge j) → i = j
  vertex_simple : Function.Injective vertex
  starts_at_species : ∃ s : S, vertex 0 = Sum.inl s
  ends_at_species : ∃ s : S, vertex (Fin.last L) = Sum.inl s

namespace TrueSRSSPath

variable {L : ℕ}

/-- The vertex just before the end is a reaction vertex: the last edge joins it to the final
species vertex. -/
theorem reaction_at_pred (P : N.TrueSRSSPath L) :
    ∃ ρ : N.InternalTrueReaction, P.vertex ⟨L - 1, by have := P.length_pos; omega⟩
      = Sum.inr ρ := by
  have hL := P.length_pos
  obtain ⟨x, hx⟩ := P.ends_at_species
  have hlast : (Fin.last L) = (⟨L, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rw [hlast] at hx
  have hc := P.connects ⟨L - 1, by omega⟩
  have hsu : ((⟨L - 1, by omega⟩ : Fin L).succ) = (⟨L, by omega⟩ : Fin (L + 1)) :=
    Fin.ext (by show L - 1 + 1 = L; omega)
  have hcs : (Fin.castSucc (⟨L - 1, by omega⟩ : Fin L))
      = (⟨L - 1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rw [hsu, hcs] at hc
  rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hx] at hv
    exact absurd hv (by simp)
  · exact ⟨_, hu⟩

/-- A species-to-species path has length at least two: a single edge cannot have species
vertices at both ends. -/
theorem two_le_length (P : N.TrueSRSSPath L) : 2 ≤ L := by
  have hL := P.length_pos
  rcases Nat.lt_or_ge L 2 with hlt | hge
  · exfalso
    have hL1 : L = 1 := by omega
    obtain ⟨ρ, hρ⟩ := P.reaction_at_pred
    obtain ⟨x, hx⟩ := P.starts_at_species
    have h0 : (0 : Fin (L + 1)) = (⟨L - 1, by omega⟩ : Fin (L + 1)) :=
      Fin.ext (by show (0 : ℕ) = L - 1; omega)
    rw [h0, hρ] at hx
    exact absurd hx (by simp)
  · exact hge

/-- Dropping the last edge of a species-to-species path leaves a species-to-reaction path. -/
def toPath (P : N.TrueSRSSPath L) : N.TrueSRPath (L - 1) where
  length_pos := by have := P.two_le_length; omega
  edge := fun q => P.edge ⟨q.1, by have := q.isLt; omega⟩
  vertex := fun p => P.vertex ⟨p.1, by have := p.isLt; have := P.two_le_length; omega⟩
  connects := by
    intro q
    exact P.connects ⟨q.1, by have := q.isLt; omega⟩
  edge_simple := by
    intro i j hij
    have := P.edge_simple hij
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  vertex_simple := by
    intro p p' hpp'
    have := P.vertex_simple hpp'
    exact Fin.ext (by have := congrArg Fin.val this; simpa using this)
  starts_at_species := by
    obtain ⟨x, hx⟩ := P.starts_at_species
    refine ⟨x, ?_⟩
    show P.vertex ⟨((0 : Fin (L - 1 + 1))).1, _⟩ = Sum.inl x
    exact (congrArg P.vertex (Fin.ext (rfl : (0 : ℕ) = ((0 : Fin (L + 1))).1))).trans hx
  ends_at_reaction := by
    obtain ⟨ρ, hρ⟩ := P.reaction_at_pred
    refine ⟨ρ, ?_⟩
    show P.vertex ⟨(Fin.last (L - 1)).1, _⟩ = Sum.inr ρ
    exact (congrArg P.vertex (Fin.ext (rfl : (L - 1) = (⟨L - 1, _⟩ : Fin (L + 1)).1))).trans hρ

@[simp] theorem toPath_edge (P : N.TrueSRSSPath L) (q : Fin (L - 1)) :
    P.toPath.edge q = P.edge ⟨q.1, by have := q.isLt; omega⟩ := rfl

@[simp] theorem toPath_vertex (P : N.TrueSRSSPath L) (p : Fin (L - 1 + 1)) :
    P.toPath.vertex p =
      P.vertex ⟨p.1, by have := p.isLt; have := P.two_le_length; omega⟩ := rfl

/-- **A species-to-species path has even length.** -/
theorem even_length (P : N.TrueSRSSPath L) : Even L := by
  have h2 := P.two_le_length
  obtain ⟨k, hk⟩ := P.toPath.odd_length
  refine ⟨L / 2, ?_⟩
  omega

/-! ### Parity and accessors -/

/-- A vertex of a species-to-species path is a species vertex exactly at even positions.
Inherited from `TrueSRPath.species_iff_even` through `toPath` below the last position, and from
`ends_at_species` together with `even_length` at the last. -/
theorem species_iff_even (P : N.TrueSRSSPath L) (m : ℕ) (hm : m ≤ L) :
    (∃ x : S, P.vertex ⟨m, by omega⟩ = Sum.inl x) ↔ Even m := by
  have h2 := P.two_le_length
  rcases Nat.lt_or_ge m L with hlt | hge
  · have h := P.toPath.species_iff_even m (by omega)
    have hv : P.toPath.vertex ⟨m, by omega⟩ = P.vertex ⟨m, by omega⟩ := rfl
    rw [hv] at h
    exact h
  · have hmL : m = L := by omega
    subst hmL
    obtain ⟨x, hx⟩ := P.ends_at_species
    have hlast : (Fin.last m) = (⟨m, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hlast] at hx
    exact ⟨fun _ => P.even_length, fun _ => ⟨x, hx⟩⟩

theorem exists_species_of_even (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) :
    ∃ x : S, P.vertex p = Sum.inl x := by
  have hlt := p.isLt
  obtain ⟨x, hx⟩ := (P.species_iff_even p.1 (by omega)).mpr (Nat.even_iff.mpr hp)
  exact ⟨x, (congrArg P.vertex (Fin.ext rfl)).trans hx⟩

theorem exists_reaction_of_odd (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    ∃ ρ : N.InternalTrueReaction, P.vertex p = Sum.inr ρ := by
  have hlt := p.isLt
  have hns : ¬ ∃ x : S, P.vertex ⟨p.1, by omega⟩ = Sum.inl x := by
    intro h
    exact absurd ((P.species_iff_even p.1 (by omega)).mp h) (by
      rw [Nat.even_iff]; omega)
  cases hv : P.vertex p with
  | inl x =>
    exact absurd ⟨x, (congrArg P.vertex (Fin.ext rfl)).trans hv⟩ hns
  | inr ρ => exact ⟨ρ, rfl⟩

/-- The species at an even position. -/
noncomputable def speciesAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) : S :=
  (P.exists_species_of_even p hp).choose

theorem vertex_eq_speciesAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 = 0) :
    P.vertex p = Sum.inl (P.speciesAt p hp) :=
  (P.exists_species_of_even p hp).choose_spec

/-- The reaction at an odd position. -/
noncomputable def reactionAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    N.InternalTrueReaction :=
  (P.exists_reaction_of_odd p hp).choose

theorem vertex_eq_reactionAt (P : N.TrueSRSSPath L) (p : Fin (L + 1)) (hp : p.1 % 2 ≠ 0) :
    P.vertex p = Sum.inr (P.reactionAt p hp) :=
  (P.exists_reaction_of_odd p hp).choose_spec

/-- An even-position edge carries the species at its own position. -/
theorem edge_species_of_even (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 = 0) :
    (P.edge q).species = P.speciesAt ⟨q.1, by have := q.isLt; omega⟩ hq := by
  have hq' := q.isLt
  have hv := P.vertex_eq_speciesAt ⟨q.1, by omega⟩ hq
  have hcs : (Fin.castSucc q) = (⟨q.1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rcases P.connects q with ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [hcs, hv] at hu
    exact (Sum.inl.inj hu).symm
  · rw [hcs, hv] at hu
    exact absurd hu (by simp)

/-- An even-position edge carries the reaction at the next position. -/
theorem edge_reaction_of_even (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 = 0) :
    (P.edge q).reaction =
      (P.reactionAt ⟨q.1 + 1, by have := q.isLt; omega⟩
        (by show (q.1 + 1) % 2 ≠ 0; omega)).1 := by
  have hq' := q.isLt
  have hv := P.vertex_eq_reactionAt ⟨q.1 + 1, by omega⟩ (by show (q.1 + 1) % 2 ≠ 0; omega)
  have hsu : (q.succ) = (⟨q.1 + 1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rcases P.connects q with ⟨_, hw⟩ | ⟨_, hw⟩
  · rw [hsu, hv] at hw
    exact (congrArg Subtype.val (Sum.inr.inj hw)).symm
  · rw [hsu, hv] at hw
    exact absurd hw (by simp)

/-- An odd-position edge carries the reaction at its own position. -/
theorem edge_reaction_of_odd (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) :
    (P.edge q).reaction = (P.reactionAt ⟨q.1, by have := q.isLt; omega⟩ hq).1 := by
  have hq' := q.isLt
  have hv := P.vertex_eq_reactionAt ⟨q.1, by omega⟩ hq
  have hcs : (Fin.castSucc q) = (⟨q.1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rcases P.connects q with ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [hcs, hv] at hu
    exact absurd hu (by simp)
  · rw [hcs, hv] at hu
    exact (congrArg Subtype.val (Sum.inr.inj hu)).symm

/-- An odd-position edge carries the species at the next position. -/
theorem edge_species_of_odd (P : N.TrueSRSSPath L) (q : Fin L) (hq : q.1 % 2 ≠ 0) :
    (P.edge q).species =
      P.speciesAt ⟨q.1 + 1, by have := q.isLt; omega⟩
        (by show (q.1 + 1) % 2 = 0; omega) := by
  have hq' := q.isLt
  have hv := P.vertex_eq_speciesAt ⟨q.1 + 1, by omega⟩ (by show (q.1 + 1) % 2 = 0; omega)
  have hsu : (q.succ) = (⟨q.1 + 1, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
  rcases P.connects q with ⟨_, hw⟩ | ⟨_, hw⟩
  · rw [hsu, hv] at hw
    exact absurd hw (by simp)
  · rw [hsu, hv] at hw
    exact (Sum.inl.inj hw).symm

/-! ### Extending by one edge at the far end

A species-to-species path `Q` of length `M` followed by one further edge at its terminal
species is a species-to-reaction path of length `M + 1`.  This is what lets the
species-to-species glue reuse `glueCycle`: a cycle built from two species-to-species paths
`P`, `Q` with the same endpoints is also the glue of the two species-to-**reaction** paths
`P.toPath` (drop `P`'s last edge) and `Q.extend` (append that edge to `Q`), whose common
junctions are `P`'s start species and `P`'s last reaction vertex. -/

theorem even_mod (P : N.TrueSRSSPath L) : L % 2 = 0 := Nat.even_iff.mp P.even_length

/-- Append one edge at the terminal species of a species-to-species path. -/
noncomputable def extend (Q : N.TrueSRSSPath L) (e : N.TrueSREdge)
    (hes : e.species = Q.speciesAt ⟨L, by omega⟩ Q.even_mod)
    (hnew : ∀ p : Fin (L + 1),
      Q.vertex p ≠ Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction))
    (hedge : ∀ q : Fin L, ¬ e.SameIncidence (Q.edge q)) :
    N.TrueSRPath (L + 1) where
  length_pos := by omega
  edge := fun q => if h : q.1 < L then Q.edge ⟨q.1, h⟩ else e
  vertex := fun p =>
    if h : p.1 < L + 1 then Q.vertex ⟨p.1, h⟩
    else Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction)
  connects := by
    intro q
    have hq := q.isLt
    have hcs : (Fin.castSucc q).1 = q.1 := rfl
    have hsu : (q.succ).1 = q.1 + 1 := rfl
    by_cases hlt : q.1 < L
    · have h1 : (if h : (Fin.castSucc q).1 < L + 1 then Q.vertex ⟨(Fin.castSucc q).1, h⟩
          else Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction))
            = Q.vertex (Fin.castSucc ⟨q.1, hlt⟩) := by
        rw [dif_pos (show (Fin.castSucc q).1 < L + 1 by rw [hcs]; omega)]
        exact congrArg Q.vertex (Fin.ext rfl)
      have h2 : (if h : (q.succ).1 < L + 1 then Q.vertex ⟨(q.succ).1, h⟩
          else Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction))
            = Q.vertex ((⟨q.1, hlt⟩ : Fin L).succ) := by
        rw [dif_pos (show (q.succ).1 < L + 1 by rw [hsu]; omega)]
        exact congrArg Q.vertex (Fin.ext rfl)
      show ((if h : q.1 < L then Q.edge ⟨q.1, h⟩ else e)).Connects _ _
      rw [dif_pos hlt, h1, h2]
      exact Q.connects ⟨q.1, hlt⟩
    · have hqL : q.1 = L := by omega
      have h1 : (if h : (Fin.castSucc q).1 < L + 1 then Q.vertex ⟨(Fin.castSucc q).1, h⟩
          else Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction))
            = Q.vertex ⟨L, by omega⟩ := by
        rw [dif_pos (show (Fin.castSucc q).1 < L + 1 by rw [hcs]; omega)]
        exact congrArg Q.vertex (Fin.ext (by rw [hcs]; exact hqL))
      have h2 : (if h : (q.succ).1 < L + 1 then Q.vertex ⟨(q.succ).1, h⟩
          else Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction))
            = Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction) := by
        rw [dif_neg (show ¬ (q.succ).1 < L + 1 by rw [hsu]; omega)]
      show ((if h : q.1 < L then Q.edge ⟨q.1, h⟩ else e)).Connects _ _
      rw [dif_neg hlt, h1, h2]
      refine Or.inl ⟨?_, rfl⟩
      rw [Q.vertex_eq_speciesAt ⟨L, by omega⟩ Q.even_mod, hes]
  edge_simple := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases hla : a.1 < L <;> by_cases hlb : b.1 < L
    · rw [dif_pos hla, dif_pos hlb] at hab
      have h := Q.edge_simple hab
      have hv := congrArg Fin.val h
      exact Fin.ext hv
    · rw [dif_pos hla, dif_neg hlb] at hab
      exact absurd (TrueSREdge.SameIncidence.symm hab) (hedge ⟨a.1, hla⟩)
    · rw [dif_neg hla, dif_pos hlb] at hab
      exact absurd hab (hedge ⟨b.1, hlb⟩)
    · exact Fin.ext (by omega)
  vertex_simple := by
    intro a b hab
    simp only at hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases hla : a.1 < L + 1 <;> by_cases hlb : b.1 < L + 1
    · rw [dif_pos hla, dif_pos hlb] at hab
      have h := Q.vertex_simple hab
      have hv := congrArg Fin.val h
      exact Fin.ext hv
    · rw [dif_pos hla, dif_neg hlb] at hab
      exact absurd hab (hnew ⟨a.1, hla⟩)
    · rw [dif_neg hla, dif_pos hlb] at hab
      exact absurd hab.symm (hnew ⟨b.1, hlb⟩)
    · exact Fin.ext (by omega)
  starts_at_species := by
    obtain ⟨x, hx⟩ := Q.starts_at_species
    refine ⟨x, ?_⟩
    show (if h : ((0 : Fin (L + 1 + 1))).1 < L + 1 then Q.vertex ⟨_, h⟩ else _) = Sum.inl x
    rw [dif_pos (show ((0 : Fin (L + 1 + 1))).1 < L + 1 by simp)]
    exact (congrArg Q.vertex (Fin.ext rfl)).trans hx
  ends_at_reaction := by
    refine ⟨⟨e.reaction, e.internal⟩, ?_⟩
    show (if h : (Fin.last (L + 1)).1 < L + 1 then Q.vertex ⟨_, h⟩ else _) = _
    rw [dif_neg (show ¬ (Fin.last (L + 1)).1 < L + 1 by
      show ¬ L + 1 < L + 1
      omega)]

@[simp] theorem extend_edge_lt (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge)
    (q : Fin (L + 1)) (h : q.1 < L) :
    (Q.extend e hes hnew hedge).edge q = Q.edge ⟨q.1, h⟩ := dif_pos h

@[simp] theorem extend_edge_last (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge)
    (q : Fin (L + 1)) (h : ¬ q.1 < L) :
    (Q.extend e hes hnew hedge).edge q = e := dif_neg h

@[simp] theorem extend_vertex_lt (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge)
    (p : Fin (L + 1 + 1)) (h : p.1 < L + 1) :
    (Q.extend e hes hnew hedge).vertex p = Q.vertex ⟨p.1, h⟩ := dif_pos h

@[simp] theorem extend_vertex_last (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge)
    (p : Fin (L + 1 + 1)) (h : ¬ p.1 < L + 1) :
    (Q.extend e hes hnew hedge).vertex p =
      Sum.inr (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction) := dif_neg h

/-! ### Endpoints of `toPath` and `extend` -/

theorem toPath_startSpecies (P : N.TrueSRSSPath L) :
    P.toPath.startSpecies = P.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega) := by
  have h2 := P.two_le_length
  have h1 := P.toPath.vertex_zero
  have hv : P.toPath.vertex 0 = P.vertex ⟨0, by omega⟩ := by
    rw [toPath_vertex]
    exact congrArg P.vertex (Fin.ext rfl)
  rw [hv, P.vertex_eq_speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)] at h1
  exact (Sum.inl.inj h1).symm

theorem toPath_endReaction (P : N.TrueSRSSPath L) :
    P.toPath.endReaction =
      P.reactionAt ⟨L - 1, by have := P.length_pos; omega⟩
        (by have := P.even_mod; have := P.two_le_length; show (L - 1) % 2 ≠ 0; omega) := by
  have h2 := P.two_le_length
  have h1 := P.toPath.vertex_last
  have hv : P.toPath.vertex (Fin.last (L - 1)) = P.vertex ⟨L - 1, by omega⟩ := by
    rw [toPath_vertex]
    exact congrArg P.vertex (Fin.ext rfl)
  rw [hv, P.vertex_eq_reactionAt ⟨L - 1, by omega⟩
    (by have := P.even_mod; show (L - 1) % 2 ≠ 0; omega)] at h1
  exact (Sum.inr.inj h1).symm

theorem extend_startSpecies (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge) :
    (Q.extend e hes hnew hedge).startSpecies =
      Q.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega) := by
  have h1 := (Q.extend e hes hnew hedge).vertex_zero
  have hv : (Q.extend e hes hnew hedge).vertex 0 = Q.vertex ⟨0, by omega⟩ := by
    rw [extend_vertex_lt Q e hes hnew hedge 0 (by simp)]
    exact congrArg Q.vertex (Fin.ext rfl)
  rw [hv, Q.vertex_eq_speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)] at h1
  exact (Sum.inl.inj h1).symm

theorem extend_endReaction (Q : N.TrueSRSSPath L) (e : N.TrueSREdge) (hes hnew hedge) :
    (Q.extend e hes hnew hedge).endReaction =
      (⟨e.reaction, e.internal⟩ : N.InternalTrueReaction) := by
  have h1 := (Q.extend e hes hnew hedge).vertex_last
  rw [extend_vertex_last Q e hes hnew hedge (Fin.last (L + 1))
    (by show ¬ L + 1 < L + 1; omega)] at h1
  exact (Sum.inr.inj h1).symm

/-! ### Interiors, and when two species-to-species paths glue -/

/-- A species vertex strictly inside a species-to-species path. -/
def InteriorSpecies (P : N.TrueSRSSPath L) (x : S) : Prop :=
  ∃ p : Fin (L + 1), p.1 ≠ 0 ∧ p.1 ≠ L ∧ P.vertex p = Sum.inl x

/-- Every reaction vertex of a species-to-species path is interior. -/
def InteriorReaction (P : N.TrueSRSSPath L) (ρ : N.InternalTrueReaction) : Prop :=
  ∃ p : Fin (L + 1), P.vertex p = Sum.inr ρ

/-- **When two species-to-species paths glue to a cycle**: same two species endpoints,
disjoint interiors, no shared edge. -/
structure SSGluable {L M : ℕ} (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M) : Prop where
  same_start : P.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)
    = Q.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)
  same_end : P.speciesAt ⟨L, by omega⟩ P.even_mod = Q.speciesAt ⟨M, by omega⟩ Q.even_mod
  species_disjoint : ∀ x : S, P.InteriorSpecies x → Q.InteriorSpecies x → False
  reaction_disjoint : ∀ ρ : N.InternalTrueReaction,
    P.InteriorReaction ρ → Q.InteriorReaction ρ → False
  edge_disjoint : ∀ a b, ¬ (P.edge a).SameIncidence (Q.edge b)

/-! ### Reducing the species-to-species glue to the species-to-reaction glue -/

theorem speciesAt_congr (P : N.TrueSRSSPath L) {p p' : Fin (L + 1)}
    (hp : p.1 % 2 = 0) (hp' : p'.1 % 2 = 0) (hpp' : p = p') :
    P.speciesAt p hp = P.speciesAt p' hp' := by
  subst hpp'
  rfl

theorem reactionAt_congr (P : N.TrueSRSSPath L) {p p' : Fin (L + 1)}
    (hp : p.1 % 2 ≠ 0) (hp' : p'.1 % 2 ≠ 0) (hpp' : p = p') :
    P.reactionAt p hp = P.reactionAt p' hp' := by
  subst hpp'
  rfl

/-- The last edge of a species-to-species path. -/
noncomputable def lastEdge (P : N.TrueSRSSPath L) : N.TrueSREdge :=
  P.edge ⟨L - 1, by have := P.length_pos; omega⟩

private theorem pred_odd (P : N.TrueSRSSPath L) : (L - 1) % 2 ≠ 0 := by
  have := P.even_mod
  have := P.two_le_length
  omega

theorem lastEdge_species (P : N.TrueSRSSPath L) :
    P.lastEdge.species = P.speciesAt ⟨L, by omega⟩ P.even_mod := by
  have h2 := P.two_le_length
  rw [lastEdge, P.edge_species_of_odd ⟨L - 1, by omega⟩ P.pred_odd]
  exact P.speciesAt_congr _ _ (Fin.ext (by show L - 1 + 1 = L; omega))

theorem lastEdge_reaction (P : N.TrueSRSSPath L) :
    (⟨P.lastEdge.reaction, P.lastEdge.internal⟩ : N.InternalTrueReaction) =
      P.reactionAt ⟨L - 1, by have := P.length_pos; omega⟩ P.pred_odd := by
  have h2 := P.two_le_length
  apply Subtype.ext
  exact P.edge_reaction_of_odd ⟨L - 1, by omega⟩ P.pred_odd

end TrueSRSSPath

namespace TrueSRSSPath

variable {L M : ℕ}

theorem extend_hes (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M) (h : SSGluable P Q) :
    P.lastEdge.species = Q.speciesAt ⟨M, by omega⟩ Q.even_mod :=
  P.lastEdge_species.trans h.same_end

theorem extend_hnew (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M) (h : SSGluable P Q) :
    ∀ p : Fin (M + 1),
      Q.vertex p ≠ Sum.inr (⟨P.lastEdge.reaction, P.lastEdge.internal⟩ :
        N.InternalTrueReaction) := by
  intro p hp
  refine h.reaction_disjoint _ ?_ ⟨p, hp⟩
  refine ⟨⟨L - 1, by have := P.length_pos; omega⟩, ?_⟩
  rw [P.vertex_eq_reactionAt ⟨L - 1, by have := P.length_pos; omega⟩ P.pred_odd]
  exact congrArg Sum.inr P.lastEdge_reaction.symm

theorem extend_hedge (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M) (h : SSGluable P Q) :
    ∀ q : Fin M, ¬ P.lastEdge.SameIncidence (Q.edge q) :=
  fun q => h.edge_disjoint ⟨L - 1, by have := P.length_pos; omega⟩ q

/-- The species-to-reaction partner of `Q` in the reduction: `Q` with `P`'s last edge appended.
-/
noncomputable def partner (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M) (h : SSGluable P Q) :
    N.TrueSRPath (M + 1) :=
  Q.extend P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)

/-- **The species-to-species glue reduces to the species-to-reaction glue.**  Dropping `P`'s
last edge and appending it to `Q` turns two gluable species-to-species paths into two gluable
species-to-reaction paths with the same union, so `glueCycle` and all of its c-pair bookkeeping
apply unchanged. -/
theorem gluable_of_ssGluable (P : N.TrueSRSSPath L) (Q : N.TrueSRSSPath M)
    (h : SSGluable P Q) : TrueSRPath.Gluable P.toPath (partner P Q h) where
  same_start := by
    rw [P.toPath_startSpecies, partner, extend_startSpecies]
    exact h.same_start
  same_end := by
    rw [P.toPath_endReaction, partner, extend_endReaction]
    exact P.lastEdge_reaction.symm
  species_disjoint := by
    intro x hP hQ
    have h2 := P.two_le_length
    obtain ⟨p, hp0, hpv⟩ := hP
    rw [toPath_vertex] at hpv
    have hplt := p.isLt
    have hPint : P.InteriorSpecies x :=
      ⟨⟨p.1, by omega⟩, by simpa using hp0, by show p.1 ≠ L; omega, hpv⟩
    obtain ⟨r, hr0, hrv⟩ := hQ
    have hrlt' := r.isLt
    rw [partner] at hrv
    by_cases hrlt : r.1 < M + 1
    · rw [extend_vertex_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h)
        (extend_hedge P Q h) r hrlt] at hrv
      by_cases hrM : r.1 = M
      · -- `x` is the shared terminal species, which cannot also be interior to `P`
        obtain ⟨u, hu0, huL, huv⟩ := hPint
        have hxQ : Q.vertex ⟨M, by omega⟩ = Sum.inl x := by
          rw [← hrv]
          exact congrArg Q.vertex (Fin.ext hrM.symm)
        rw [Q.vertex_eq_speciesAt ⟨M, by omega⟩ Q.even_mod] at hxQ
        have hxP : P.vertex ⟨L, by omega⟩ = Sum.inl x := by
          rw [P.vertex_eq_speciesAt ⟨L, by omega⟩ P.even_mod, h.same_end]
          exact hxQ
        have : u = ⟨L, by omega⟩ := P.vertex_simple (huv.trans hxP.symm)
        exact huL (congrArg Fin.val this)
      · exact h.species_disjoint x hPint ⟨⟨r.1, hrlt⟩, by simpa using hr0, hrM, hrv⟩
    · rw [extend_vertex_last Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h)
        (extend_hedge P Q h) r hrlt] at hrv
      exact absurd hrv (by simp)
  reaction_disjoint := by
    intro ρ hP hQ
    have h2 := P.two_le_length
    obtain ⟨p, hpL, hpv⟩ := hP
    rw [toPath_vertex] at hpv
    have hplt := p.isLt
    obtain ⟨r, hrL, hrv⟩ := hQ
    have hrlt' := r.isLt
    have hrlt : r.1 < M + 1 := by
      have : r.1 ≠ M + 1 := by simpa using hrL
      omega
    rw [partner, extend_vertex_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h)
      (extend_hedge P Q h) r hrlt] at hrv
    exact h.reaction_disjoint ρ ⟨⟨p.1, by omega⟩, hpv⟩ ⟨⟨r.1, hrlt⟩, hrv⟩
  edge_disjoint := by
    intro a b hab
    have h2 := P.two_le_length
    have halt := a.isLt
    rw [toPath_edge] at hab
    by_cases hb : b.1 < M
    · rw [partner, extend_edge_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h)
        (extend_hedge P Q h) b hb] at hab
      exact h.edge_disjoint _ _ hab
    · rw [partner, extend_edge_last Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h)
        (extend_hedge P Q h) b hb, lastEdge] at hab
      have hz := P.edge_simple hab
      have hv := congrArg Fin.val hz
      simp only at hv
      omega


/-- **The cycle glued from two species-to-species paths.**  Lengths are parametrised as
`2j+2` and `2i+2` so that the reduction lands exactly on `glueCycle`'s `2·+1` form: dropping
`P`'s last edge gives a path of length `2j+1`, appending it to `Q` gives one of length
`2(i+1)+1`, and the resulting cycle has length `(i+1) + j + 1`, which is the number of species
on `P ∪ Q`.

Because the glue is literally a `glueCycle`, everything in `TrueSRGlueCPairs.lean`,
`TrueSRGlueCount.lean` and `TrueSRParityLemma.lean` applies to it unchanged. -/
noncomputable def ssGlueCycle {i j : ℕ} (P : N.TrueSRSSPath (2 * j + 2))
    (Q : N.TrueSRSSPath (2 * i + 2)) (h : SSGluable P Q) :
    N.TrueSRCycle (i + 1 + j + 1) :=
  TrueSRPath.glueCycle P.toPath (partner P Q h) (gluable_of_ssGluable P Q h) (by omega)

/-- The glue is literally a `glueCycle`, so every lemma about `glueCycle` rewrites into it. -/
theorem ssGlueCycle_eq {i j : ℕ} (P : N.TrueSRSSPath (2 * j + 2))
    (Q : N.TrueSRSSPath (2 * i + 2)) (h : SSGluable P Q) :
    ssGlueCycle P Q h =
      TrueSRPath.glueCycle P.toPath (partner P Q h) (gluable_of_ssGluable P Q h)
        (by omega) := rfl


/-! ### Edge-disjointness from interior-off-cycle, for species-to-species paths -/

private theorem hasEnds_of_left {n : ℕ} (C : N.TrueSRCycle n) {e : N.TrueSREdge} {t : Fin n}
    (h : e.SameIncidence (C.leftEdge t)) :
    C.HasSpecies e.species ∧ C.HasReaction e.reaction := by
  refine ⟨⟨t, ?_⟩, ⟨t, ?_⟩⟩
  · rw [← C.left_species t]; exact h.1.symm
  · rw [← C.left_reaction t]; exact h.2.1.symm

private theorem hasEnds_of_right {n : ℕ} (C : N.TrueSRCycle n) {e : N.TrueSREdge} {t : Fin n}
    (h : e.SameIncidence (C.rightEdge t)) :
    C.HasSpecies e.species ∧ C.HasReaction e.reaction := by
  refine ⟨⟨⟨(t.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩, ?_⟩, ⟨t, ?_⟩⟩
  · rw [← C.right_species t]; exact h.1.symm
  · rw [← C.right_reaction t]; exact h.2.1.symm

/-- **A species-to-species path whose interior misses the cycle traverses no cycle edge.**
Unconditional, because such a path has length at least two (`two_le_length`), so every edge has
an interior endpoint — and a cycle edge would put cycle vertices at both of its endpoints. -/
theorem ss_edges_off_cycle {n L : ℕ} (C : N.TrueSRCycle n) (P : N.TrueSRSSPath L)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p)) :
    (∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t)) ∧
      (∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t)) := by
  have h2 := P.two_le_length
  have key : ∀ (p : Fin L), C.HasSpecies (P.edge p).species →
      C.HasReaction (P.edge p).reaction → False := by
    intro p hsp hrx
    have hp := p.isLt
    have hends : C.HasVertex (P.vertex (Fin.castSucc p)) ∧ C.HasVertex (P.vertex p.succ) := by
      rcases P.connects p with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [hu, hv]; exact ⟨hsp, hrx⟩
      · rw [hu, hv]; exact ⟨hrx, hsp⟩
    rcases Nat.eq_zero_or_pos p.1 with hp0 | hppos
    · exact hint p.succ (by show p.1 + 1 ≠ 0; omega) (by show p.1 + 1 ≠ L; omega) hends.2
    · exact hint (Fin.castSucc p) (by show p.1 ≠ 0; omega) (by show p.1 ≠ L; omega) hends.1
  refine ⟨?_, ?_⟩
  · intro p t hsame
    obtain ⟨hsp, hrx⟩ := hasEnds_of_left C hsame
    exact key p hsp hrx
  · intro p t hsame
    obtain ⟨hsp, hrx⟩ := hasEnds_of_right C hsame
    exact key p hsp hrx

end TrueSRSSPath

namespace TrueSRCycle

variable {n : ℕ}

private theorem sarcIdx {m n q : ℕ} (hm : m < n) (hq : q < 2 * m + 1) : q / 2 < n := by omega

section SpeciesArc

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m)

/-- Edges of the species-to-species arc: left edge at even positions, right edge at odd. -/
private noncomputable def sarcEdge (q : Fin (2 * m)) : N.TrueSREdge :=
  if q.1 % 2 = 0 then C.leftEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩
  else C.rightEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩

/-- Vertices of the species-to-species arc: species at even positions, reactions at odd. -/
private noncomputable def sarcVertex (p : Fin (2 * m + 1)) : N.TrueSRVertex :=
  if p.1 % 2 = 0 then Sum.inl (C.species ⟨p.1 / 2, sarcIdx hm p.isLt⟩)
  else Sum.inr ⟨C.reaction ⟨p.1 / 2, sarcIdx hm p.isLt⟩,
    C.reaction_internal ⟨p.1 / 2, sarcIdx hm p.isLt⟩⟩

private theorem sarcEdge_even {q : Fin (2 * m)} (h : q.1 % 2 = 0) :
    sarcEdge C m hm q = C.leftEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩ :=
  if_pos h

private theorem sarcEdge_odd {q : Fin (2 * m)} (h : q.1 % 2 ≠ 0) :
    sarcEdge C m hm q = C.rightEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩ :=
  if_neg h

private theorem sarcVertex_even {p : Fin (2 * m + 1)} (h : p.1 % 2 = 0) :
    sarcVertex C m hm p = Sum.inl (C.species ⟨p.1 / 2, sarcIdx hm p.isLt⟩) :=
  if_pos h

private theorem sarcVertex_odd {p : Fin (2 * m + 1)} (h : p.1 % 2 ≠ 0) :
    sarcVertex C m hm p = Sum.inr ⟨C.reaction ⟨p.1 / 2, sarcIdx hm p.isLt⟩,
      C.reaction_internal ⟨p.1 / 2, sarcIdx hm p.isLt⟩⟩ :=
  if_neg h

/-- **The arc of a cycle from species `x₀` to species `x_m`**, as a species-to-species path. -/
noncomputable def speciesArc : N.TrueSRSSPath (2 * m) where
  length_pos := by omega
  edge := sarcEdge C m hm
  vertex := sarcVertex C m hm
  connects := by
    intro q
    have hq := q.isLt
    have hcs : (Fin.castSucc q).1 = q.1 := rfl
    have hsu : (q.succ).1 = q.1 + 1 := rfl
    by_cases hpar : q.1 % 2 = 0
    · refine Or.inl ⟨?_, ?_⟩
      · rw [sarcVertex_even C m hm (by rw [hcs]; exact hpar), sarcEdge_even C m hm hpar]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (C.left_species _).symm
        exact congrArg C.species (Fin.ext (by show (Fin.castSucc q).1 / 2 = q.1 / 2; rfl))
      · rw [sarcVertex_odd C m hm (by rw [hsu]; omega), sarcEdge_even C m hm hpar]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (C.left_reaction _).symm
        exact congrArg C.reaction (Fin.ext (by show (q.1 + 1) / 2 = q.1 / 2; omega))
    · refine Or.inr ⟨?_, ?_⟩
      · rw [sarcVertex_odd C m hm (by rw [hcs]; exact hpar), sarcEdge_odd C m hm hpar]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (C.right_reaction _).symm
        exact congrArg C.reaction (Fin.ext (by show (Fin.castSucc q).1 / 2 = q.1 / 2; rfl))
      · rw [sarcVertex_even C m hm (by rw [hsu]; omega), sarcEdge_odd C m hm hpar]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (C.right_species _).symm
        refine congrArg C.species (Fin.ext ?_)
        show (q.1 + 1) / 2 = (q.1 / 2 + 1) % n
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
  edge_simple := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    by_cases hpi : i.1 % 2 = 0 <;> by_cases hpj : j.1 % 2 = 0
    · rw [sarcEdge_even C m hm hpi, sarcEdge_even C m hm hpj] at hij
      have := C.sameIncidence_leftEdge_iff _ _ hij
      have hv := congrArg Fin.val this
      exact Fin.ext (by simp only at hv; omega)
    · rw [sarcEdge_even C m hm hpi, sarcEdge_odd C m hm hpj] at hij
      exact absurd hij (C.not_sameIncidence_left_right _ _)
    · rw [sarcEdge_odd C m hm hpi, sarcEdge_even C m hm hpj] at hij
      exact absurd (TrueSREdge.SameIncidence.symm hij) (C.not_sameIncidence_left_right _ _)
    · rw [sarcEdge_odd C m hm hpi, sarcEdge_odd C m hm hpj] at hij
      have := C.sameIncidence_rightEdge_iff _ _ hij
      have hv := congrArg Fin.val this
      exact Fin.ext (by simp only at hv; omega)
  vertex_simple := by
    intro p p' hpp'
    have hp := p.isLt
    have hp' := p'.isLt
    by_cases hpi : p.1 % 2 = 0 <;> by_cases hpj : p'.1 % 2 = 0
    · rw [sarcVertex_even C m hm hpi, sarcVertex_even C m hm hpj] at hpp'
      have := C.species_injective (Sum.inl.inj hpp')
      have hv := congrArg Fin.val this
      exact Fin.ext (by simp only at hv; omega)
    · rw [sarcVertex_even C m hm hpi, sarcVertex_odd C m hm hpj] at hpp'
      exact absurd hpp' (by simp)
    · rw [sarcVertex_odd C m hm hpi, sarcVertex_even C m hm hpj] at hpp'
      exact absurd hpp' (by simp)
    · rw [sarcVertex_odd C m hm hpi, sarcVertex_odd C m hm hpj] at hpp'
      have := C.reaction_injective (congrArg Subtype.val (Sum.inr.inj hpp'))
      have hv := congrArg Fin.val this
      exact Fin.ext (by simp only at hv; omega)
  starts_at_species := by
    refine ⟨C.species ⟨0, by omega⟩, ?_⟩
    rw [sarcVertex_even C m hm (by simp)]
    refine congrArg Sum.inl (congrArg C.species (Fin.ext ?_))
    show ((0 : Fin (2 * m + 1))).1 / 2 = 0
    simp
  ends_at_species := by
    refine ⟨C.species ⟨m, hm⟩, ?_⟩
    rw [sarcVertex_even C m hm (by show (2 * m) % 2 = 0; omega)]
    refine congrArg Sum.inl (congrArg C.species (Fin.ext ?_))
    show (Fin.last (2 * m)).1 / 2 = m
    show (2 * m) / 2 = m
    omega

theorem speciesArc_edge_even (q : Fin (2 * m)) (h : q.1 % 2 = 0) :
    (C.speciesArc m hm hmpos).edge q =
      C.leftEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩ :=
  sarcEdge_even C m hm h

theorem speciesArc_edge_odd (q : Fin (2 * m)) (h : q.1 % 2 ≠ 0) :
    (C.speciesArc m hm hmpos).edge q =
      C.rightEdge ⟨q.1 / 2, sarcIdx hm (Nat.lt_succ_of_lt q.isLt)⟩ :=
  sarcEdge_odd C m hm h

theorem speciesArc_vertex_even (p : Fin (2 * m + 1)) (h : p.1 % 2 = 0) :
    (C.speciesArc m hm hmpos).vertex p = Sum.inl (C.species ⟨p.1 / 2, sarcIdx hm p.isLt⟩) :=
  sarcVertex_even C m hm h

theorem speciesArc_vertex_odd (p : Fin (2 * m + 1)) (h : p.1 % 2 ≠ 0) :
    (C.speciesArc m hm hmpos).vertex p =
      Sum.inr ⟨C.reaction ⟨p.1 / 2, sarcIdx hm p.isLt⟩,
        C.reaction_internal ⟨p.1 / 2, sarcIdx hm p.isLt⟩⟩ :=
  sarcVertex_odd C m hm h

theorem speciesArc_vertex_zero :
    (C.speciesArc m hm hmpos).vertex ⟨0, by omega⟩ = Sum.inl (C.species ⟨0, by omega⟩) := by
  rw [speciesArc_vertex_even C m hm hmpos ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)]
  exact congrArg Sum.inl (congrArg C.species (Fin.ext (by show (0 : ℕ) / 2 = 0; omega)))

theorem speciesArc_vertex_last :
    (C.speciesArc m hm hmpos).vertex ⟨2 * m, by omega⟩ = Sum.inl (C.species ⟨m, hm⟩) := by
  rw [speciesArc_vertex_even C m hm hmpos ⟨2 * m, by omega⟩ (by show (2 * m) % 2 = 0; omega)]
  exact congrArg Sum.inl (congrArg C.species (Fin.ext (by show (2 * m) / 2 = m; omega)))

/-- The complementary arc, from species `x₀` round the other way to species `x_m`. -/
noncomputable def speciesArcBwd : N.TrueSRSSPath (2 * (n - m)) :=
  (C.reverse).speciesArc (n - m) (by omega) (by omega)

theorem speciesArcBwd_vertex_zero :
    (C.speciesArcBwd m hm hmpos).vertex ⟨0, by omega⟩ =
      Sum.inl (C.species ⟨0, by omega⟩) := by
  rw [speciesArcBwd, speciesArc_vertex_zero, reverse_species']
  refine congrArg Sum.inl (congrArg C.species (Fin.ext ?_))
  show (n - 0) % n = 0
  simp

theorem speciesArcBwd_vertex_last :
    (C.speciesArcBwd m hm hmpos).vertex ⟨2 * (n - m), by omega⟩ =
      Sum.inl (C.species ⟨m, hm⟩) := by
  rw [speciesArcBwd, speciesArc_vertex_last, reverse_species']
  refine congrArg Sum.inl (congrArg C.species (Fin.ext ?_))
  show (n - (n - m)) % n = m
  rw [show n - (n - m) = m by omega, Nat.mod_eq_of_lt hm]

theorem speciesArcBwd_edge_even (q : Fin (2 * (n - m))) (h : q.1 % 2 = 0) :
    (C.speciesArcBwd m hm hmpos).edge q =
      C.rightEdge (revPerm n ⟨q.1 / 2, sarcIdx (show n - m < n by omega)
        (Nat.lt_succ_of_lt q.isLt)⟩) :=
  speciesArc_edge_even (C.reverse) (n - m) (by omega) (by omega) q h

theorem speciesArcBwd_edge_odd (q : Fin (2 * (n - m))) (h : q.1 % 2 ≠ 0) :
    (C.speciesArcBwd m hm hmpos).edge q =
      C.leftEdge (revPerm n ⟨q.1 / 2, sarcIdx (show n - m < n by omega)
        (Nat.lt_succ_of_lt q.isLt)⟩) :=
  speciesArc_edge_odd (C.reverse) (n - m) (by omega) (by omega) q h


/-! ### Interiors and endpoints of the two species-arcs -/

theorem speciesArc_speciesAt_zero :
    (C.speciesArc m hm hmpos).speciesAt ⟨0, by omega⟩
      (by show (0 : ℕ) % 2 = 0; omega) = C.species ⟨0, by omega⟩ := by
  have h1 := (C.speciesArc m hm hmpos).vertex_eq_speciesAt ⟨0, by omega⟩
    (by show (0 : ℕ) % 2 = 0; omega)
  rw [speciesArc_vertex_zero] at h1
  exact (Sum.inl.inj h1).symm

theorem speciesArc_speciesAt_last :
    (C.speciesArc m hm hmpos).speciesAt ⟨2 * m, by omega⟩
      (C.speciesArc m hm hmpos).even_mod = C.species ⟨m, hm⟩ := by
  have h1 := (C.speciesArc m hm hmpos).vertex_eq_speciesAt ⟨2 * m, by omega⟩
    (C.speciesArc m hm hmpos).even_mod
  rw [speciesArc_vertex_last] at h1
  exact (Sum.inl.inj h1).symm

theorem speciesArc_interiorSpecies {x : S}
    (h : (C.speciesArc m hm hmpos).InteriorSpecies x) :
    ∃ k : Fin n, 0 < k.1 ∧ k.1 < m ∧ x = C.species k := by
  obtain ⟨p, hp0, hpL, hpv⟩ := h
  have hplt := p.isLt
  by_cases hpar : p.1 % 2 = 0
  · rw [speciesArc_vertex_even C m hm hmpos p hpar] at hpv
    refine ⟨⟨p.1 / 2, by omega⟩, ?_, ?_, (Sum.inl.inj hpv).symm⟩
    · show 0 < p.1 / 2
      have : p.1 ≠ 0 := by simpa using hp0
      omega
    · show p.1 / 2 < m
      have : p.1 ≠ 2 * m := by simpa using hpL
      omega
  · rw [speciesArc_vertex_odd C m hm hmpos p hpar] at hpv
    exact absurd hpv (by simp)

theorem speciesArc_interiorReaction {ρ : N.InternalTrueReaction}
    (h : (C.speciesArc m hm hmpos).InteriorReaction ρ) :
    ∃ k : Fin n, k.1 < m ∧ ρ.1 = C.reaction k := by
  obtain ⟨p, hpv⟩ := h
  have hplt := p.isLt
  by_cases hpar : p.1 % 2 = 0
  · rw [speciesArc_vertex_even C m hm hmpos p hpar] at hpv
    exact absurd hpv (by simp)
  · rw [speciesArc_vertex_odd C m hm hmpos p hpar] at hpv
    refine ⟨⟨p.1 / 2, by omega⟩, ?_, ?_⟩
    · show p.1 / 2 < m
      omega
    · exact congrArg Subtype.val (Sum.inr.inj hpv).symm

theorem speciesArcBwd_speciesAt_zero :
    (C.speciesArcBwd m hm hmpos).speciesAt ⟨0, by omega⟩
      (by show (0 : ℕ) % 2 = 0; omega) = C.species ⟨0, by omega⟩ := by
  have h1 := (C.speciesArcBwd m hm hmpos).vertex_eq_speciesAt ⟨0, by omega⟩
    (by show (0 : ℕ) % 2 = 0; omega)
  rw [speciesArcBwd_vertex_zero] at h1
  exact (Sum.inl.inj h1).symm

theorem speciesArcBwd_speciesAt_last :
    (C.speciesArcBwd m hm hmpos).speciesAt ⟨2 * (n - m), by omega⟩
      (C.speciesArcBwd m hm hmpos).even_mod = C.species ⟨m, hm⟩ := by
  have h1 := (C.speciesArcBwd m hm hmpos).vertex_eq_speciesAt ⟨2 * (n - m), by omega⟩
    (C.speciesArcBwd m hm hmpos).even_mod
  rw [speciesArcBwd_vertex_last] at h1
  exact (Sum.inl.inj h1).symm

theorem speciesArcBwd_interiorSpecies {x : S}
    (h : (C.speciesArcBwd m hm hmpos).InteriorSpecies x) :
    ∃ k : Fin n, m < k.1 ∧ x = C.species k := by
  have hn := C.nontrivial
  obtain ⟨k', hk'0, hk'lt, hxk'⟩ :=
    speciesArc_interiorSpecies (C.reverse) (n - m) (by omega) (by omega) h
  have hk'ltn := k'.isLt
  refine ⟨⟨(n - k'.1) % n, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
  · show m < (n - k'.1) % n
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hxk', reverse_species']

theorem speciesArcBwd_interiorReaction {ρ : N.InternalTrueReaction}
    (h : (C.speciesArcBwd m hm hmpos).InteriorReaction ρ) :
    ∃ k : Fin n, m ≤ k.1 ∧ ρ.1 = C.reaction k := by
  have hn := C.nontrivial
  obtain ⟨k', hk'lt, hρk'⟩ :=
    speciesArc_interiorReaction (C.reverse) (n - m) (by omega) (by omega) h
  have hk'ltn := k'.isLt
  refine ⟨revPerm n k', ?_, ?_⟩
  · show m ≤ n - 1 - k'.1
    omega
  · rw [hρk']
    rfl

theorem speciesArc_edge_cases (q : Fin (2 * m)) :
    (∃ k : Fin n, k.1 < m ∧ (C.speciesArc m hm hmpos).edge q = C.leftEdge k) ∨
      (∃ k : Fin n, k.1 < m ∧ (C.speciesArc m hm hmpos).edge q = C.rightEdge k) := by
  have hq := q.isLt
  by_cases hpar : q.1 % 2 = 0
  · exact Or.inl ⟨⟨q.1 / 2, by omega⟩, by show q.1 / 2 < m; omega,
      speciesArc_edge_even C m hm hmpos q hpar⟩
  · exact Or.inr ⟨⟨q.1 / 2, by omega⟩, by show q.1 / 2 < m; omega,
      speciesArc_edge_odd C m hm hmpos q hpar⟩

theorem speciesArcBwd_edge_cases (q : Fin (2 * (n - m))) :
    (∃ k : Fin n, m ≤ k.1 ∧ (C.speciesArcBwd m hm hmpos).edge q = C.leftEdge k) ∨
      (∃ k : Fin n, m ≤ k.1 ∧ (C.speciesArcBwd m hm hmpos).edge q = C.rightEdge k) := by
  have hn := C.nontrivial
  have hq := q.isLt
  by_cases hpar : q.1 % 2 = 0
  · refine Or.inr ⟨revPerm n ⟨q.1 / 2, by omega⟩, by show m ≤ n - 1 - q.1 / 2; omega, ?_⟩
    exact speciesArc_edge_even (C.reverse) (n - m) (by omega) (by omega) q hpar
  · refine Or.inl ⟨revPerm n ⟨q.1 / 2, by omega⟩, by show m ≤ n - 1 - q.1 / 2; omega, ?_⟩
    exact speciesArc_edge_odd (C.reverse) (n - m) (by omega) (by omega) q hpar

/-- **The two species-arcs of a cycle glue back to it.**  This is the species-to-species
counterpart of `gluable_arcs`: between species vertex `0` and species vertex `m`, a cycle is
two species-to-species paths with those endpoints and disjoint interiors. -/
theorem ss_gluable_arcs :
    TrueSRSSPath.SSGluable (C.speciesArc m hm hmpos) (C.speciesArcBwd m hm hmpos) where
  same_start := by
    rw [speciesArc_speciesAt_zero, speciesArcBwd_speciesAt_zero]
  same_end := by
    rw [speciesArc_speciesAt_last, speciesArcBwd_speciesAt_last]
  species_disjoint := by
    intro x hF hB
    obtain ⟨k, _, hk, hxk⟩ := speciesArc_interiorSpecies C m hm hmpos hF
    obtain ⟨l, hl, hxl⟩ := speciesArcBwd_interiorSpecies C m hm hmpos hB
    have : k = l := C.species_injective (hxk.symm.trans hxl)
    rw [this] at hk
    omega
  reaction_disjoint := by
    intro ρ hF hB
    obtain ⟨k, hk, hρk⟩ := speciesArc_interiorReaction C m hm hmpos hF
    obtain ⟨l, hl, hρl⟩ := speciesArcBwd_interiorReaction C m hm hmpos hB
    have : k = l := C.reaction_injective (hρk.symm.trans hρl)
    rw [this] at hk
    omega
  edge_disjoint := by
    intro a b hsame
    rcases speciesArc_edge_cases C m hm hmpos a with ⟨k, hk, hea⟩ | ⟨k, hk, hea⟩ <;>
      rcases speciesArcBwd_edge_cases C m hm hmpos b with ⟨l, hl, heb⟩ | ⟨l, hl, heb⟩ <;>
        rw [hea, heb] at hsame
    · have := C.sameIncidence_leftEdge_iff k l hsame
      rw [this] at hk
      omega
    · exact C.not_sameIncidence_left_right k l hsame
    · exact C.not_sameIncidence_left_right l k (TrueSREdge.SameIncidence.symm hsame)
    · have := C.sameIncidence_rightEdge_iff k l hsame
      rw [this] at hk
      omega


/-! ### An even chord glues to each species-arc -/

private theorem ss_reaction_pos_odd {L : ℕ} (P : N.TrueSRSSPath L) (p : Fin (L + 1))
    {ρ : N.InternalTrueReaction} (hpv : P.vertex p = Sum.inr ρ) : p.1 % 2 ≠ 0 := by
  intro hpar
  obtain ⟨x, hx⟩ := P.exists_species_of_even p hpar
  rw [hpv] at hx
  exact absurd hx (by simp)

theorem ssGluable_chord_arcFwd {L : ℕ} (P : N.TrueSRSSPath L)
    (hstart : P.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)
      = C.species ⟨0, by omega⟩)
    (hend : P.speciesAt ⟨L, by omega⟩ P.even_mod = C.species ⟨m, hm⟩)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t)) :
    TrueSRSSPath.SSGluable P (C.speciesArc m hm hmpos) where
  same_start := by rw [hstart, speciesArc_speciesAt_zero]
  same_end := by rw [hend, speciesArc_speciesAt_last]
  species_disjoint := by
    intro x hP hA
    obtain ⟨p, hp0, hpL, hpv⟩ := hP
    obtain ⟨k, _, _, hxk⟩ := speciesArc_interiorSpecies C m hm hmpos hA
    refine hint p hp0 hpL ?_
    rw [hpv]
    exact ⟨k, hxk.symm⟩
  reaction_disjoint := by
    intro ρ hP hA
    obtain ⟨p, hpv⟩ := hP
    obtain ⟨k, _, hρk⟩ := speciesArc_interiorReaction C m hm hmpos hA
    have hodd := ss_reaction_pos_odd P p hpv
    have hplt := p.isLt
    have hLeven := P.even_mod
    refine hint p (by omega) (by omega) ?_
    rw [hpv]
    exact ⟨k, hρk.symm⟩
  edge_disjoint := by
    intro a b hsame
    rcases speciesArc_edge_cases C m hm hmpos b with ⟨k, _, heb⟩ | ⟨k, _, heb⟩ <;>
      rw [heb] at hsame
    · exact hedgeL a k hsame
    · exact hedgeR a k hsame

theorem ssGluable_chord_arcBwd {L : ℕ} (P : N.TrueSRSSPath L)
    (hstart : P.speciesAt ⟨0, by omega⟩ (by show (0 : ℕ) % 2 = 0; omega)
      = C.species ⟨0, by omega⟩)
    (hend : P.speciesAt ⟨L, by omega⟩ P.even_mod = C.species ⟨m, hm⟩)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t)) :
    TrueSRSSPath.SSGluable P (C.speciesArcBwd m hm hmpos) where
  same_start := by rw [hstart, speciesArcBwd_speciesAt_zero]
  same_end := by rw [hend, speciesArcBwd_speciesAt_last]
  species_disjoint := by
    intro x hP hA
    obtain ⟨p, hp0, hpL, hpv⟩ := hP
    obtain ⟨k, _, hxk⟩ := speciesArcBwd_interiorSpecies C m hm hmpos hA
    refine hint p hp0 hpL ?_
    rw [hpv]
    exact ⟨k, hxk.symm⟩
  reaction_disjoint := by
    intro ρ hP hA
    obtain ⟨p, hpv⟩ := hP
    obtain ⟨k, _, hρk⟩ := speciesArcBwd_interiorReaction C m hm hmpos hA
    have hodd := ss_reaction_pos_odd P p hpv
    have hplt := p.isLt
    have hLeven := P.even_mod
    refine hint p (by omega) (by omega) ?_
    rw [hpv]
    exact ⟨k, hρk.symm⟩
  edge_disjoint := by
    intro a b hsame
    rcases speciesArcBwd_edge_cases C m hm hmpos b with ⟨k, _, heb⟩ | ⟨k, _, heb⟩ <;>
      rw [heb] at hsame
    · exact hedgeL a k hsame
    · exact hedgeR a k hsame

end SpeciesArc

end TrueSRCycle

end CRNT.Network
