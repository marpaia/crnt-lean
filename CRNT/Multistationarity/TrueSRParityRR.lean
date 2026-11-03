import CRNT.Multistationarity.TrueSRParityLemma

/-!
# The R-to-R three-path parity lemma (Shinar--Feinberg, Lemma A.4)

Shinar--Feinberg, *Concordant Chemical Reaction Networks and the Species-Reaction Graph*
(arXiv:1203.6560), Appendix A.2, Lemma A.4 (p. 52): distinct reactions `R*` and `R**` joined by
three edge-disjoint (not-necessarily-directed) paths `R*AR**`, `R*BR**`, `R*CR**` — if the cycles
`R*BR**AR*` and `R*CR**BR*` are both even, so is `R*CR**AR*`.

This is the reaction-to-reaction counterpart of the two parity steps already in the repository:
the S-to-R `three_glued_parity` (`TrueSRParityLemma.lean`) and the S-to-S
`ss_three_glued_even_of_two` (`TrueChemistrySRCriterion.lean`).  As there, path data are
hypotheses: nothing here constructs paths, and no Menger-type existence statement is needed.

## How the lemma is formalised

A reaction-to-reaction path (`TrueSRPathRR`) is a first edge leaving the start reaction followed
by an ordinary species-to-reaction `TrueSRPath` tail.  Gluing two of them, `A` and `B`, into the
cycle `R*BR**AR*` uses the repository's `glueCycle` on the pair

* `A.tail` — from `A`'s first species to `R**`, and
* `glueArc A B` — `A`'s first edge followed by all of `B`'s edges, again from `A`'s first
  species to `R**`,

so the glued walk runs along `A` to `R**`, back along `B`, and closes across `A`'s first edge at
`R*`.  The c-pair count then splits (`rrGluedCycle_numCPairs`) as

  `numCPairs (A ∪ B) = c(A) + s**(A,B) + s*(A,B) + c(B)`

where `c(·)` is intrinsic to each path, `s**` compares the two last edges (both incident to the
shared end reaction `R**`) and `s*` compares the two first edges (both incident to the shared
start reaction `R*`).

Summing over the three pairs, every intrinsic term occurs twice, while the three `s*` indicators
are the three pairwise comparisons of the paths' first edges — three values in the two-element
complex set of `R*`, whose number of agreeing pairs is odd (`odd_agree_count`) — and likewise for
`s**` at `R**`.  The total is `≡ 1 + 1 = 0 (mod 2)`, so an even number of the three cycles is
odd: two even cycles force the third to be even.

## Relation to the paper's proof

The paper's proof is a case analysis over the distribution of c-pairs at `R*` and `R**`
(Fig. 5a–g).  The counting identity above is that case analysis compressed into one equation:
each figure is one assignment of the six edge labels, and the two `odd_agree_count` applications
are exactly the observation that each of `R*`, `R**` carries at least one c-pair, since only two
complex labels are available per reaction.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **A reaction-to-reaction path in the true-SR graph.**  The parameter `j` is the number of
interior reactions of the tail, so the whole path has `2 * j + 2` edges (even, as alternation
forces) and runs from a start reaction through interior vertices to an end reaction. -/
structure TrueSRPathRR (N : Network S) (j : ℕ) where
  /-- The edge leaving the start reaction. -/
  first : N.TrueSREdge
  /-- The remainder of the path, a species-to-reaction path ending at the end reaction. -/
  tail : N.TrueSRPath (2 * j + 1)
  /-- The first edge lands on the tail's start species. -/
  first_species : Sum.inl first.species = tail.vertex ⟨0, by omega⟩
  /-- The first edge is not reused inside the tail. -/
  first_ne_tail_edge : ∀ i : Fin (2 * j + 1), ¬ first.SameIncidence (tail.edge i)
  /-- The start reaction does not recur inside the tail. -/
  first_ne_tail_vertex : ∀ i : Fin (2 * j + 1 + 1),
    Sum.inr ⟨first.reaction, first.internal⟩ ≠ tail.vertex i

namespace TrueSRPathRR

open CRNT.Network.TrueSRPath

variable {j : ℕ}

/-- The reaction the path starts at. -/
def startReaction (A : N.TrueSRPathRR j) : N.InternalTrueReaction :=
  ⟨A.first.reaction, A.first.internal⟩

/-- The reaction the path ends at. -/
noncomputable def endReaction (A : N.TrueSRPathRR j) : N.InternalTrueReaction :=
  A.tail.endReaction

/-- The vertex at position `k`, for `k : Fin (2 * j + 3)`.  Position `0` is the start reaction;
positions `1 … 2 * j + 2` are the tail's vertices shifted by one. -/
noncomputable def vertexAt (A : N.TrueSRPathRR j) (k : Fin (2 * j + 3)) : N.TrueSRVertex :=
  if k.1 = 0 then Sum.inr A.startReaction
  else A.tail.vertex ⟨k.1 - 1, by have := k.isLt; omega⟩

/-- The edge at position `k`, for `k : Fin (2 * j + 2)`.  Position `0` is the first edge;
positions `1 … 2 * j + 1` are the tail's edges shifted by one. -/
noncomputable def edgeAt (A : N.TrueSRPathRR j) (k : Fin (2 * j + 2)) : N.TrueSREdge :=
  if k.1 = 0 then A.first
  else A.tail.edge ⟨k.1 - 1, by have := k.isLt; omega⟩

@[simp] theorem vertexAt_zero (A : N.TrueSRPathRR j) :
    A.vertexAt ⟨0, by omega⟩ = Sum.inr A.startReaction := by
  rw [vertexAt]
  exact if_pos rfl

@[simp] theorem edgeAt_zero (A : N.TrueSRPathRR j) :
    A.edgeAt ⟨0, by omega⟩ = A.first := by
  rw [edgeAt]
  exact if_pos rfl

/-- A nonzero position of the path carries the tail's edge. -/
@[simp] theorem edgeAt_pos (A : N.TrueSRPathRR j) (k : Fin (2 * j + 2)) (hk : 0 < k.1) :
    A.edgeAt k = A.tail.edge ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
  if_neg (by omega)

/-- Position `k + 1` of the path is position `k` of the tail. -/
@[simp] theorem vertexAt_succ (A : N.TrueSRPathRR j) (k : Fin (2 * j + 2)) :
    A.vertexAt ⟨k.1 + 1, by omega⟩ = A.tail.vertex k := by
  rw [vertexAt]
  rw [if_neg (by show ¬ (k.1 + 1) = 0; omega)]
  exact congrArg A.tail.vertex (Fin.ext rfl)

/-- Edge `k + 1` of the path is edge `k` of the tail. -/
@[simp] theorem edgeAt_succ (A : N.TrueSRPathRR j) (k : Fin (2 * j + 1)) :
    A.edgeAt ⟨k.1 + 1, by omega⟩ = A.tail.edge k := by
  rw [edgeAt]
  rw [if_neg (by show ¬ (k.1 + 1) = 0; omega)]
  exact congrArg A.tail.edge (Fin.ext rfl)

/-- The tail's vertex at position `k` sits at position `k + 1` of the path. -/
theorem tail_vertex (A : N.TrueSRPathRR j) (k : Fin (2 * j + 2)) :
    A.tail.vertex k = A.vertexAt ⟨k.1 + 1, by omega⟩ :=
  (vertexAt_succ A k).symm

/-- The tail's edge at position `k` sits at position `k + 1` of the path. -/
theorem tail_edge (A : N.TrueSRPathRR j) (k : Fin (2 * j + 1)) :
    A.tail.edge k = A.edgeAt ⟨k.1 + 1, by omega⟩ :=
  (edgeAt_succ A k).symm

/-- The tail's start species is the first edge's species. -/
theorem tail_startSpecies (A : N.TrueSRPathRR j) :
    A.tail.startSpecies = A.first.species :=
  Sum.inl.inj ((A.first_species.trans (vertex_at_zero A.tail (by omega))).symm)

/-- **Consecutive positions are joined by the corresponding edge**: positions `m`, `m + 1`,
`m + 2` (indices into `2 * j + 2`, `2 * j + 3`, `2 * j + 3`) are joined by the path's edge at
`m` — the first edge when `m = 0`, a tail edge otherwise. -/
theorem connects_at (A : N.TrueSRPathRR j) (m : Fin (2 * j + 2)) :
    (A.edgeAt ⟨m.1, by omega⟩).Connects (A.vertexAt ⟨m.1, by omega⟩)
      (A.vertexAt ⟨m.1 + 1, by omega⟩) := by
  by_cases hm : m.1 = 0
  · have he : A.edgeAt ⟨m.1, by omega⟩ = A.first := by
      rw [edgeAt]
      rw [if_pos hm]
    have hv1 : A.vertexAt ⟨m.1, by omega⟩ = Sum.inr A.startReaction := by
      rw [vertexAt]
      rw [if_pos hm]
    have hv2 : A.vertexAt ⟨m.1 + 1, by omega⟩ = Sum.inl A.first.species := by
      rw [vertexAt]
      rw [if_neg (by show ¬ (m.1 + 1) = 0; omega)]
      rw [show (⟨m.1 + 1 - 1, by omega⟩ : Fin (2 * j + 2)) = (⟨0, by omega⟩ : Fin (2 * j + 2))
          from Fin.ext (by show m.1 + 1 - 1 = 0; omega)]
      rw [vertex_at_zero A.tail (by omega)]
      exact congrArg Sum.inl A.tail_startSpecies
    rw [he, hv1, hv2]
    exact Or.inr ⟨rfl, rfl⟩
  · have hne : ¬ (m.1 = 0) := hm
    have he : A.edgeAt ⟨m.1, by omega⟩
        = A.tail.edge ⟨m.1 - 1, by have := m.isLt; omega⟩ := by
      rw [edgeAt]
      rw [if_neg hne]
    have hv1 : A.vertexAt ⟨m.1, by omega⟩
        = A.tail.vertex ⟨m.1 - 1, by have := m.isLt; omega⟩ := by
      rw [vertexAt]
      rw [if_neg hne]
    have hv2 : A.vertexAt ⟨m.1 + 1, by omega⟩
        = A.tail.vertex ⟨m.1 + 1 - 1, by have := m.isLt; omega⟩ := by
      rw [vertexAt]
      rw [if_neg (by show ¬ (m.1 + 1) = 0; omega)]
    rw [he, hv1, hv2]
    have h1 : (⟨m.1 - 1, by have := m.isLt; omega⟩ : Fin (2 * j + 2))
        = Fin.castSucc (⟨m.1 - 1, by have := m.isLt; omega⟩ : Fin (2 * j + 1)) := Fin.ext rfl
    have h2 : (⟨m.1 + 1 - 1, by have := m.isLt; omega⟩ : Fin (2 * j + 2))
        = (⟨m.1 - 1, by have := m.isLt; omega⟩ : Fin (2 * j + 1)).succ := by
      apply Fin.ext
      show m.1 + 1 - 1 = m.1 - 1 + 1
      omega
    rw [h1, h2]
    exact A.tail.connects ⟨m.1 - 1, by have := m.isLt; omega⟩

/-- The vertex map is injective: the start reaction does not recur, and the tail is injective. -/
theorem vertexAt_injective (A : N.TrueSRPathRR j) :
    Function.Injective A.vertexAt := by
  intro k k' heq
  have hk : A.vertexAt k
      = if k.1 = 0 then Sum.inr A.startReaction
        else A.tail.vertex ⟨k.1 - 1, by have := k.isLt; omega⟩ := rfl
  have hk' : A.vertexAt k'
      = if k'.1 = 0 then Sum.inr A.startReaction
        else A.tail.vertex ⟨k'.1 - 1, by have := k'.isLt; omega⟩ := rfl
  rcases Nat.eq_zero_or_pos k.1 with h0 | hp
  · rcases Nat.eq_zero_or_pos k'.1 with h0' | hp'
    · exact Fin.ext (by omega)
    · exfalso
      rw [hk, hk', if_pos h0, if_neg (by omega)] at heq
      exact A.first_ne_tail_vertex ⟨k'.1 - 1, by have := k'.isLt; omega⟩ heq
  · rcases Nat.eq_zero_or_pos k'.1 with h0' | hp'
    · exfalso
      rw [hk, hk', if_neg (by omega), if_pos h0'] at heq
      exact A.first_ne_tail_vertex ⟨k.1 - 1, by have := k.isLt; omega⟩ heq.symm
    · rw [hk, hk', if_neg (by omega), if_neg (by omega)] at heq
      have h := A.tail.vertex_simple heq
      have hval : k.1 - 1 = k'.1 - 1 := congrArg Fin.val h
      exact Fin.ext (by omega)

/-- Edge positions are distinguished by incidence: the first edge differs from every tail edge,
and tail edges are pairwise distinct. -/
theorem edgeAt_simple (A : N.TrueSRPathRR j) {k k' : Fin (2 * j + 2)}
    (h : (A.edgeAt k).SameIncidence (A.edgeAt k')) : k = k' := by
  have hk : A.edgeAt k
      = if k.1 = 0 then A.first
        else A.tail.edge ⟨k.1 - 1, by have := k.isLt; omega⟩ := rfl
  have hk' : A.edgeAt k'
      = if k'.1 = 0 then A.first
        else A.tail.edge ⟨k'.1 - 1, by have := k'.isLt; omega⟩ := rfl
  rcases Nat.eq_zero_or_pos k.1 with h0 | hp
  · rcases Nat.eq_zero_or_pos k'.1 with h0' | hp'
    · exact Fin.ext (by omega)
    · exfalso
      rw [hk, hk', if_pos h0, if_neg (by omega)] at h
      exact A.first_ne_tail_edge ⟨k'.1 - 1, by have := k'.isLt; omega⟩ h
  · rcases Nat.eq_zero_or_pos k'.1 with h0' | hp'
    · exfalso
      rw [hk, hk', if_neg (by omega), if_pos h0'] at h
      exact A.first_ne_tail_edge ⟨k.1 - 1, by have := k.isLt; omega⟩
        (TrueSREdge.SameIncidence.symm h)
    · rw [hk, hk', if_neg (by omega), if_neg (by omega)] at h
      have hh := A.tail.edge_simple h
      have hval : k.1 - 1 = k'.1 - 1 := congrArg Fin.val hh
      exact Fin.ext (by omega)

/-- A species vertex of the path. -/
def HasSpecies (A : N.TrueSRPathRR j) (s : S) : Prop :=
  ∃ k : Fin (2 * j + 3), A.vertexAt k = Sum.inl s

/-- A reaction vertex of the path. -/
def HasReaction (A : N.TrueSRPathRR j) (ρ : N.InternalTrueReaction) : Prop :=
  ∃ k : Fin (2 * j + 3), A.vertexAt k = Sum.inr ρ

/-- The first edge's species lies on the path. -/
theorem hasSpecies_first (A : N.TrueSRPathRR j) :
    A.HasSpecies A.first.species := by
  refine ⟨⟨1, by omega⟩, ?_⟩
  have h1 : A.vertexAt ⟨1, by omega⟩ = A.tail.vertex ⟨0, by omega⟩ := by
    rw [vertexAt]
    rw [if_neg (by show ¬ (1 : ℕ) = 0; omega)]
    exact congrArg A.tail.vertex (Fin.ext rfl)
  rw [h1, vertex_at_zero A.tail (by omega)]
  exact congrArg Sum.inl A.tail_startSpecies

/-- **Two reaction-to-reaction paths glue to a cycle**: they share both endpoint reactions,
their vertex sets meet only in those endpoints, and they share no edge.  This is the
reaction-to-reaction counterpart of `TrueSRPath.Gluable` (and of `TrueSRSSPath.SSGluable`):
the interior-disjointness clauses are what makes the glued walk vertex-simple. -/
structure RRGluable {a b : ℕ} (A : N.TrueSRPathRR a) (B : N.TrueSRPathRR b) : Prop where
  /-- The paths leave the same start reaction `R*`. -/
  same_start : A.startReaction = B.startReaction
  /-- The paths end at the same end reaction `R**`. -/
  same_end : A.endReaction = B.endReaction
  /-- The paths share no species vertex (their endpoints are reactions). -/
  species_disjoint : ∀ s : S, A.HasSpecies s → B.HasSpecies s → False
  /-- The only reaction vertices the paths share are the two endpoints. -/
  reaction_disjoint : ∀ ρ : N.InternalTrueReaction, A.HasReaction ρ → B.HasReaction ρ →
    ρ = A.startReaction ∨ ρ = A.endReaction
  /-- The paths share no edge. -/
  edge_disjoint : ∀ i : Fin (2 * a + 2), ∀ k : Fin (2 * b + 2),
    ¬ (A.edgeAt i).SameIncidence (B.edgeAt k)

/-- Prepend an edge to a reaction-to-reaction path: the resulting species-to-reaction path
starts at the edge's species, crosses the edge, and then runs along all of `A`'s edges. -/
private noncomputable def prepend {j : ℕ} (e : N.TrueSREdge) (A : N.TrueSRPathRR j)
    (hstart : A.startReaction = ⟨e.reaction, e.internal⟩)
    (hne : ∀ k : Fin (2 * j + 2), ¬ e.SameIncidence (A.edgeAt k))
    (hsp : ∀ k : Fin (2 * j + 3), A.vertexAt k ≠ Sum.inl e.species) :
    N.TrueSRPath (2 * (j + 1) + 1) where
  length_pos := by omega
  edge := fun q => if 0 < q.1 then A.edgeAt ⟨q.1 - 1, by have := q.isLt; omega⟩ else e
  vertex := fun p => if 0 < p.1 then A.vertexAt ⟨p.1 - 1, by have := p.isLt; omega⟩
    else Sum.inl e.species
  connects := by
    intro i
    show (if 0 < i.1 then A.edgeAt ⟨i.1 - 1, by have := i.isLt; omega⟩ else e).Connects
      (if 0 < (Fin.castSucc i).1 then
          A.vertexAt ⟨(Fin.castSucc i).1 - 1, by have := (Fin.castSucc i).isLt; omega⟩
        else Sum.inl e.species)
      (if 0 < (i.succ).1 then
          A.vertexAt ⟨(i.succ).1 - 1, by have := (i.succ).isLt; omega⟩
        else Sum.inl e.species)
    by_cases hi : 0 < i.1
    · have hc1 : 0 < (Fin.castSucc i).1 := hi
      have hc2 : 0 < (i.succ).1 := by show 0 < i.1 + 1; omega
      rw [if_pos hi, if_pos hc1, if_pos hc2]
      have h1 : (⟨(Fin.castSucc i).1 - 1, by have := (Fin.castSucc i).isLt; omega⟩
          : Fin (2 * j + 3)) = (⟨i.1 - 1, by have := i.isLt; omega⟩ : Fin (2 * j + 3)) :=
        Fin.ext rfl
      have h2 : (⟨(i.succ).1 - 1, by have := (i.succ).isLt; omega⟩ : Fin (2 * j + 3))
          = (⟨i.1 - 1 + 1, by have := i.isLt; omega⟩ : Fin (2 * j + 3)) := by
        apply Fin.ext
        show (i.succ).1 - 1 = i.1 - 1 + 1
        have hs : (i.succ).1 = i.1 + 1 := rfl
        rw [hs]
        omega
      rw [h1, h2]
      exact A.connects_at ⟨i.1 - 1, by have := i.isLt; omega⟩
    · have hne1 : ¬ (0 < (Fin.castSucc i).1) := by show ¬ 0 < i.1; exact hi
      have hc2 : 0 < (i.succ).1 := by show 0 < i.1 + 1; omega
      rw [if_neg hi, if_neg hne1, if_pos hc2]
      have hz : (⟨(i.succ).1 - 1, by have := (i.succ).isLt; omega⟩ : Fin (2 * j + 3))
          = (⟨0, by omega⟩ : Fin (2 * j + 3)) := by
        apply Fin.ext
        show (i.succ).1 - 1 = 0
        have hs : (i.succ).1 = i.1 + 1 := rfl
        rw [hs]
        omega
      rw [hz, vertexAt_zero A]
      refine Or.inl ⟨rfl, ?_⟩
      rw [hstart]
  edge_simple := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases hla : 0 < a.1 <;> by_cases hlb : 0 < b.1
    · rw [if_pos hla, if_pos hlb] at hab
      have h := A.edgeAt_simple hab
      have hval : a.1 - 1 = b.1 - 1 := congrArg Fin.val h
      exact Fin.ext (by omega)
    · rw [if_pos hla, if_neg hlb] at hab
      exact absurd (TrueSREdge.SameIncidence.symm hab) (hne ⟨a.1 - 1, by omega⟩)
    · rw [if_neg hla, if_pos hlb] at hab
      exact absurd hab (hne ⟨b.1 - 1, by omega⟩)
    · rw [if_neg hla, if_neg hlb] at hab
      exact Fin.ext (by omega)
  vertex_simple := by
    intro a b hab
    simp only at hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases hla : 0 < a.1 <;> by_cases hlb : 0 < b.1
    · rw [if_pos hla, if_pos hlb] at hab
      have h := A.vertexAt_injective hab
      have hval : a.1 - 1 = b.1 - 1 := congrArg Fin.val h
      exact Fin.ext (by omega)
    · rw [if_pos hla, if_neg hlb] at hab
      exact absurd hab (hsp ⟨a.1 - 1, by omega⟩)
    · rw [if_neg hla, if_pos hlb] at hab
      exact absurd hab.symm (hsp ⟨b.1 - 1, by omega⟩)
    · rw [if_neg hla, if_neg hlb] at hab
      exact Fin.ext (by omega)
  starts_at_species := by
    refine ⟨e.species, ?_⟩
    show (if 0 < (0 : Fin (2 * (j + 1) + 1 + 1)).1 then
        A.vertexAt ⟨(0 : Fin (2 * (j + 1) + 1 + 1)).1 - 1, by omega⟩
      else Sum.inl e.species) = Sum.inl e.species
    exact if_neg (by show ¬ (0 : ℕ) < 0; omega)
  ends_at_reaction := by
    refine ⟨A.endReaction, ?_⟩
    show (if 0 < (Fin.last (2 * (j + 1) + 1)).1 then
        A.vertexAt ⟨(Fin.last (2 * (j + 1) + 1)).1 - 1,
          by have := (Fin.last (2 * (j + 1) + 1)).isLt; omega⟩
      else Sum.inl e.species) = Sum.inr A.endReaction
    rw [if_pos (by show 0 < 2 * (j + 1) + 1; omega)]
    have hz : (⟨(Fin.last (2 * (j + 1) + 1)).1 - 1,
        by have := (Fin.last (2 * (j + 1) + 1)).isLt; omega⟩ : Fin (2 * j + 3))
        = (⟨2 * j + 2, by omega⟩ : Fin (2 * j + 3)) := by
      apply Fin.ext
      show (2 * (j + 1) + 1) - 1 = 2 * j + 2
      omega
    rw [hz]
    rw [vertexAt]
    rw [if_neg (by show ¬ (2 * j + 2) = 0; omega)]
    have hidx : (⟨↑(⟨2 * j + 2, by omega⟩ : Fin (2 * j + 3)) - 1,
        by have := (⟨2 * j + 2, by omega⟩ : Fin (2 * j + 3)).isLt; omega⟩ : Fin (2 * j + 2))
        = (⟨2 * j + 1, by omega⟩ : Fin (2 * j + 2)) := by
      apply Fin.ext
      show (2 * j + 2) - 1 = 2 * j + 1
      omega
    rw [hidx, vertex_at_last A.tail (by omega)]
    rfl

/-- **The glued arc**: `X`'s first edge followed by all of `Y`'s edges — a species-to-reaction
path from `X`'s first-edge species to `Y`'s end reaction.  Together with `X.tail` it forms the
two halves of the cycle `R* Y R** X R*`. -/
noncomputable def glueArc {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) : N.TrueSRPath (2 * (y + 1) + 1) :=
  prepend X.first Y h.same_start.symm
    (fun k => h.edge_disjoint ⟨0, by omega⟩ k)
    (fun k hk => h.species_disjoint X.first.species X.hasSpecies_first ⟨k, hk⟩)

/-- The zeroth edge of a glued arc is `X`'s first edge. -/
@[simp] theorem glueArc_edge_zero {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) (q : Fin (2 * (y + 1) + 1)) (hq : ¬ 0 < q.1) :
    (glueArc X Y h).edge q = X.first :=
  if_neg hq

/-- A positive edge position of a glued arc is `Y`'s corresponding edge. -/
@[simp] theorem glueArc_edge_pos {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) (q : Fin (2 * (y + 1) + 1)) (hq : 0 < q.1) :
    (glueArc X Y h).edge q = Y.edgeAt ⟨q.1 - 1, by have := q.isLt; omega⟩ :=
  if_pos hq

/-- The zeroth vertex of a glued arc is `X`'s first-edge species. -/
@[simp] theorem glueArc_vertex_zero {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) (q : Fin (2 * (y + 1) + 1 + 1)) (hq : ¬ 0 < q.1) :
    (glueArc X Y h).vertex q = Sum.inl X.first.species :=
  if_neg hq

/-- A positive vertex position of a glued arc is `Y`'s corresponding vertex. -/
@[simp] theorem glueArc_vertex_pos {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) (q : Fin (2 * (y + 1) + 1 + 1)) (hq : 0 < q.1) :
    (glueArc X Y h).vertex q = Y.vertexAt ⟨q.1 - 1, by have := q.isLt; omega⟩ :=
  if_pos hq

/-- The glued arc ends at `Y`'s end reaction. -/
theorem glueArc_vertex_last {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) :
    (glueArc X Y h).vertex (Fin.last (2 * (y + 1) + 1)) = Sum.inr Y.endReaction := by
  rw [glueArc_vertex_pos X Y h _ (by show 0 < 2 * (y + 1) + 1; omega)]
  have hz : (⟨↑(Fin.last (2 * (y + 1) + 1)) - 1,
      by have := (Fin.last (2 * (y + 1) + 1)).isLt; omega⟩ : Fin (2 * y + 3))
      = (⟨2 * y + 2, by omega⟩ : Fin (2 * y + 3)) := by
    apply Fin.ext
    show (2 * (y + 1) + 1) - 1 = 2 * y + 2
    omega
  rw [hz, vertexAt]
  rw [if_neg (by show ¬ (2 * y + 2) = 0; omega)]
  have hidx : (⟨↑(⟨2 * y + 2, by omega⟩ : Fin (2 * y + 3)) - 1,
      by have := (⟨2 * y + 2, by omega⟩ : Fin (2 * y + 3)).isLt; omega⟩ : Fin (2 * y + 2))
      = (⟨2 * y + 1, by omega⟩ : Fin (2 * y + 2)) := by
    apply Fin.ext
    show (2 * y + 2) - 1 = 2 * y + 1
    omega
  rw [hidx, vertex_at_last Y.tail (by omega)]
  rfl

/-- **The two arcs of the glued cycle**: `X.tail` and `glueArc X Y h`, both from `X`'s first
species to the shared end reaction. -/
theorem gluable_of_RRGluable {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) : Gluable X.tail (glueArc X Y h) where
  same_start := by
    have h0 : (glueArc X Y h).vertex 0 = Sum.inl X.first.species :=
      glueArc_vertex_zero X Y h 0 (by show ¬ (0 : ℕ) < 0; omega)
    exact X.tail_startSpecies.trans
      (Sum.inl.inj ((glueArc X Y h).vertex_zero.symm.trans h0)).symm
  same_end := by
    have hlast : (glueArc X Y h).vertex (Fin.last (2 * (y + 1) + 1))
        = Sum.inr Y.endReaction := glueArc_vertex_last X Y h
    have hv : (glueArc X Y h).vertex (Fin.last (2 * (y + 1) + 1))
        = Sum.inr (glueArc X Y h).endReaction := (glueArc X Y h).vertex_last
    exact h.same_end.trans (Sum.inr.inj (hlast.symm.trans hv))
  species_disjoint := by
    intro s hp hq
    obtain ⟨p, hp0, hpv⟩ := hp
    obtain ⟨q, hq0, hqv⟩ := hq
    refine h.species_disjoint s ⟨⟨p.1 + 1, by omega⟩, ?_⟩ ⟨⟨q.1 - 1, by omega⟩, ?_⟩
    · rw [← X.tail_vertex p]
      exact hpv
    · have hqv' : (glueArc X Y h).vertex q
          = if 0 < q.1 then Y.vertexAt ⟨q.1 - 1, by have := q.isLt; omega⟩
            else Sum.inl X.first.species := rfl
      rw [hqv'] at hqv
      rw [if_pos (by omega)] at hqv
      exact hqv
  reaction_disjoint := by
    intro ρ hp hq
    obtain ⟨p, hpl, hpv⟩ := hp
    obtain ⟨q, hql, hqv⟩ := hq
    have hX : X.HasReaction ρ := ⟨⟨p.1 + 1, by omega⟩, by rw [← X.tail_vertex p]; exact hpv⟩
    have hY : Y.HasReaction ρ := by
      have hqv' : (glueArc X Y h).vertex q
          = if 0 < q.1 then Y.vertexAt ⟨q.1 - 1, by have := q.isLt; omega⟩
            else Sum.inl X.first.species := rfl
      rw [hqv'] at hqv
      rcases Nat.eq_zero_or_pos q.1 with h0 | hpq
      · rw [if_neg (by omega)] at hqv
        exact absurd hqv (by simp)
      · rw [if_pos hpq] at hqv
        exact ⟨⟨q.1 - 1, by omega⟩, hqv⟩
    rcases h.reaction_disjoint ρ hX hY with hρ | hρ
    · exfalso
      have hpv' : X.tail.vertex p
          = Sum.inr ⟨X.first.reaction, X.first.internal⟩ :=
        hpv.trans (congrArg Sum.inr hρ)
      exact X.first_ne_tail_vertex p hpv'.symm
    · exfalso
      have hpv' : X.tail.vertex p = Sum.inr X.endReaction :=
        hpv.trans (congrArg Sum.inr hρ)
      have hlast : X.tail.vertex (Fin.last (2 * x + 1)) = Sum.inr X.endReaction :=
        X.tail.vertex_last
      have hlk : (Fin.last (2 * x + 1))
          = (⟨2 * x + 1, by omega⟩ : Fin (2 * x + 1 + 1)) := Fin.ext rfl
      have hpp : (⟨p.1, by have := p.isLt; omega⟩ : Fin (2 * x + 1 + 1))
          = (⟨2 * x + 1, by omega⟩ : Fin (2 * x + 1 + 1)) := by
        rw [← hlk]
        exact X.tail.vertex_simple (hpv'.trans hlast.symm)
      have hval : p.1 = 2 * x + 1 := congrArg Fin.val hpp
      exact hpl hval
  edge_disjoint := by
    intro i q hiq
    have harc : (glueArc X Y h).edge q
        = if 0 < q.1 then Y.edgeAt ⟨q.1 - 1, by have := q.isLt; omega⟩ else X.first := rfl
    rw [harc] at hiq
    rcases Nat.eq_zero_or_pos q.1 with h0 | hpq
    · rw [if_neg (by omega)] at hiq
      exact X.first_ne_tail_edge i (TrueSREdge.SameIncidence.symm hiq)
    · rw [if_pos hpq] at hiq
      rw [X.tail_edge i] at hiq
      exact h.edge_disjoint ⟨i.1 + 1, by have := i.isLt; omega⟩
        ⟨q.1 - 1, by have := q.isLt; omega⟩ hiq

/-- **The glued cycle `R* Y R** X R*`** of two reaction-to-reaction paths: along `X` to the
shared end reaction, back along `Y`, and closing across `X`'s first edge at the shared start
reaction.  This is `R* X Y R**` in the notation of Shinar--Feinberg Lemma A.4. -/
noncomputable def rrGluedCycle {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) : N.TrueSRCycle (y + 1 + x + 1) :=
  TrueSRPath.glueCycle (i := y + 1) (j := x) X.tail (glueArc X Y h)
    (gluable_of_RRGluable X Y h) (by omega)

/-- The glue is literally a `glueCycle`, so every lemma about `glueCycle` rewrites into it. -/
theorem rrGluedCycle_eq {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) :
    rrGluedCycle X Y h =
      TrueSRPath.glueCycle (i := y + 1) (j := x) X.tail (glueArc X Y h)
        (gluable_of_RRGluable X Y h) (by omega) :=
  rfl

/-- The number of c-pairs internal to a reaction-to-reaction path: those at its tail's
interior reactions. -/
noncomputable def rrNumCPairs {j : ℕ} (A : N.TrueSRPathRR j) : ℕ := by
  classical
  exact (Finset.univ.filter (TrueSRPath.CPairAt A.tail)).card

private theorem glueArc_cpair_iff {x y : ℕ} {X : N.TrueSRPathRR x} {Y : N.TrueSRPathRR y}
    {h : RRGluable X Y} (r : Fin (y + 1)) (hr : 0 < r.1) :
    TrueSRPath.CPairAt (glueArc X Y h) r ↔
      TrueSRPath.CPairAt Y.tail ⟨r.1 - 1, by have := r.isLt; omega⟩ := by
  rw [TrueSRPath.CPairAt, TrueSRPath.CPairAt]
  have e0 : (glueArc X Y h).edge ⟨2 * r.1, by have := r.isLt; omega⟩
      = Y.tail.edge ⟨2 * r.1 - 2, by have := r.isLt; omega⟩ := by
    rw [glueArc_edge_pos X Y h ⟨2 * r.1, by have := r.isLt; omega⟩
      (by show 0 < 2 * r.1; omega)]
    show Y.edgeAt ⟨2 * r.1 - 1, by omega⟩ = Y.tail.edge ⟨2 * r.1 - 2, by omega⟩
    rw [edgeAt_pos Y ⟨2 * r.1 - 1, by have := r.isLt; omega⟩
      (by show 0 < 2 * r.1 - 1; omega)]
    have hidx : (⟨(⟨2 * r.1 - 1, by omega⟩ : Fin (2 * y + 2)).1 - 1, by omega⟩
        : Fin (2 * y + 1)) = ⟨2 * r.1 - 2, by omega⟩ := by
      apply Fin.ext
      show (2 * r.1 - 1) - 1 = 2 * r.1 - 2
      omega
    rw [hidx]
  have e1 : (glueArc X Y h).edge ⟨2 * r.1 + 1, by have := r.isLt; omega⟩
      = Y.tail.edge ⟨2 * r.1 - 1, by have := r.isLt; omega⟩ := by
    rw [glueArc_edge_pos X Y h ⟨2 * r.1 + 1, by have := r.isLt; omega⟩
      (by show 0 < 2 * r.1 + 1; omega)]
    show Y.edgeAt ⟨2 * r.1, by omega⟩ = Y.tail.edge ⟨2 * r.1 - 1, by omega⟩
    rw [edgeAt_pos Y ⟨2 * r.1, by have := r.isLt; omega⟩ (by show 0 < 2 * r.1; omega)]
  rw [e0, e1]
  have h0' : (⟨2 * r.1 - 2, by have := r.isLt; omega⟩ : Fin (2 * y + 1))
      = ⟨2 * (r.1 - 1), by have := r.isLt; omega⟩ := by
    apply Fin.ext
    show 2 * r.1 - 2 = 2 * (r.1 - 1)
    omega
  have h1' : (⟨2 * r.1 - 1, by have := r.isLt; omega⟩ : Fin (2 * y + 1))
      = ⟨2 * (r.1 - 1) + 1, by have := r.isLt; omega⟩ := by
    apply Fin.ext
    show 2 * r.1 - 1 = 2 * (r.1 - 1) + 1
    omega
  rw [h0', h1']

/-- Two `if … then 1 else 0` indicators of the same proposition agree, whatever their
`Decidable` instances — the bridge between statement-level and proof-level instances. -/
private theorem ite_one_zero_congr (p q : Prop) (h : p ↔ q)
    (d1 : Decidable p) (d2 : Decidable q) :
    @ite ℕ p d1 1 0 = @ite ℕ q d2 1 0 := by
  cases d1 with
  | isTrue hp =>
    rw [if_pos (c := p) hp, if_pos (c := q) (h.mp hp)]
  | isFalse hp =>
    rw [if_neg (c := p) hp, if_neg (c := q) (fun hq => hp (h.mpr hq))]

/-- The seam indicator of a proposition: `1` if it holds, `0` otherwise, with the classical
decidability instance pinned.  Stating seam terms via `seamInd` keeps statements free of
`Decidable` instance choices, so they match under any proof-level `classical`. -/
noncomputable def seamInd (p : Prop) : ℕ :=
  @ite ℕ p (Classical.propDecidable p) 1 0

theorem seamInd_congr {p q : Prop} (h : p ↔ q) : seamInd p = seamInd q := by
  unfold seamInd
  exact ite_one_zero_congr p q h _ _

theorem seamInd_of_ite (p : Prop) [Decidable p] : seamInd p = (if p then 1 else 0) :=
  ite_one_zero_congr p p Iff.rfl (Classical.propDecidable p) _

/-- The zeroth c-pair indicator of a glued arc compares the two first edges. -/
theorem glueArc_CPairAt_zero {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) :
    TrueSRPath.CPairAt (glueArc X Y h) ⟨0, by omega⟩ ↔ X.first.endpoint = Y.first.endpoint := by
  rw [TrueSRPath.CPairAt]
  show ((glueArc X Y h).edge ⟨0, by omega⟩).endpoint
      = ((glueArc X Y h).edge ⟨1, by omega⟩).endpoint
      ↔ X.first.endpoint = Y.first.endpoint
  have h0 : (glueArc X Y h).edge ⟨0, by omega⟩ = X.first :=
    glueArc_edge_zero X Y h ⟨0, by omega⟩ (by show ¬ (0 : ℕ) < 0; omega)
  have h1 : (glueArc X Y h).edge ⟨1, by omega⟩ = Y.first := by
    rw [glueArc_edge_pos X Y h ⟨1, by omega⟩ (by show 0 < (1 : ℕ); omega)]
    show Y.edgeAt ⟨0, by omega⟩ = Y.first
    rw [edgeAt_zero Y]
  rw [h0, h1]

private theorem glueArc_numCPairs {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) [DecidablePred (TrueSRPath.CPairAt (glueArc X Y h))]
    [DecidablePred (TrueSRPath.CPairAt Y.tail)] :
    (Finset.univ.filter (TrueSRPath.CPairAt (glueArc X Y h))).card
      = (if TrueSRPath.CPairAt (glueArc X Y h) ⟨0, by omega⟩ then 1 else 0)
        + (Finset.univ.filter (TrueSRPath.CPairAt Y.tail)).card := by
  have hpart :
      (Finset.univ.filter (TrueSRPath.CPairAt (glueArc X Y h)))
        = (((Finset.univ.filter (fun r : Fin (y + 1) => r.1 = 0)).filter
              (TrueSRPath.CPairAt (glueArc X Y h)))
          ∪ ((Finset.univ.filter (fun r : Fin (y + 1) => 0 < r.1)).filter
              (TrueSRPath.CPairAt (glueArc X Y h)))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro hr
      rcases Nat.eq_zero_or_pos r.1 with h0 | hp
      · exact Or.inl ⟨h0, hr⟩
      · exact Or.inr ⟨hp, hr⟩
    · rintro (⟨_, hr⟩ | ⟨_, hr⟩) <;> exact hr
  have hdisj : Disjoint
      ((Finset.univ.filter (fun r : Fin (y + 1) => r.1 = 0)).filter
        (TrueSRPath.CPairAt (glueArc X Y h)))
      ((Finset.univ.filter (fun r : Fin (y + 1) => 0 < r.1)).filter
        (TrueSRPath.CPairAt (glueArc X Y h))) := by
    refine Finset.disjoint_left.mpr ?_
    intro r hr1 hr2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
    omega
  have hz : (((Finset.univ.filter (fun r : Fin (y + 1) => r.1 = 0)).filter
        (TrueSRPath.CPairAt (glueArc X Y h)))).card
      = (if TrueSRPath.CPairAt (glueArc X Y h) ⟨0, by omega⟩ then 1 else 0) := by
    have hsing : (Finset.univ.filter (fun r : Fin (y + 1) => r.1 = 0))
        = {⟨0, by omega⟩} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hr => Fin.ext hr, fun hr => by rw [hr]⟩
    rw [hsing, Finset.filter_singleton]
    split <;> simp
  have hp : (((Finset.univ.filter (fun r : Fin (y + 1) => 0 < r.1)).filter
        (TrueSRPath.CPairAt (glueArc X Y h)))).card
      = (Finset.univ.filter (TrueSRPath.CPairAt Y.tail)).card := by
    rcases Nat.eq_zero_or_pos y with hy0 | hyp
    · -- `y = 0`: the source has no positive position and the target type is empty
      rcases hy0 with rfl
      have hs0 : (((Finset.univ.filter (fun r : Fin (0 + 1) => 0 < r.1)).filter
          (TrueSRPath.CPairAt (glueArc X Y h)))).card = 0 := by
        rw [Finset.card_eq_zero]
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hpos, _⟩
          exact absurd hpos (by omega)
        · intro h
          exact False.elim (Finset.notMem_empty a h)
      have ht0 : (Finset.univ.filter (TrueSRPath.CPairAt Y.tail)).card = 0 := by
        rw [Finset.card_eq_zero]
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro _
          exact absurd a.isLt (by omega)
        · intro h
          exact False.elim (Finset.notMem_empty a h)
      rw [hs0, ht0]
    · refine Finset.card_bij (fun r _ => (⟨r.1 - 1, by have := r.isLt; omega⟩ : Fin y)) ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        obtain ⟨hpos, hcp⟩ := hr
        exact (glueArc_cpair_iff r hpos).mp hcp
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have hval : a.1 - 1 = b.1 - 1 := congrArg Fin.val hab
        exact Fin.ext (by omega)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        refine ⟨⟨r.1 + 1, by have := r.isLt; omega⟩, ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · omega
          · exact (glueArc_cpair_iff ⟨r.1 + 1, by have := r.isLt; omega⟩
              (by show 0 < r.1 + 1; omega)).mpr hr
        · exact Fin.ext (by show r.1 + 1 - 1 = r.1; omega)
  rw [hpart, Finset.card_union_of_disjoint hdisj, hz, hp]

/-- **The c-pair count of the glued cycle splits**: `c(X)` intrinsic to `X`, one seam
comparing the two last edges (both at `R**`), one seam comparing the two first edges (both at
`R*`), and `c(Y)` intrinsic to `Y`. -/
theorem rrGluedCycle_numCPairs {x y : ℕ} (X : N.TrueSRPathRR x) (Y : N.TrueSRPathRR y)
    (h : RRGluable X Y) :
    (rrGluedCycle X Y h).numCPairs
      = rrNumCPairs X
        + seamInd ((X.tail.edge ⟨2 * x, by omega⟩).endpoint
            = (Y.tail.edge ⟨2 * y, by omega⟩).endpoint)
        + seamInd (X.first.endpoint = Y.first.endpoint)
        + rrNumCPairs Y := by
  classical
  -- bridge the two classically-defined counts to their `Finset` forms
  have hnum : (rrGluedCycle X Y h).numCPairs
      = (Finset.univ.filter (rrGluedCycle X Y h).isCPair).card := by
    unfold TrueSRCycle.numCPairs
    rfl
  have hX : rrNumCPairs X = (Finset.univ.filter (TrueSRPath.CPairAt X.tail)).card := by
    unfold rrNumCPairs
    rfl
  have hY : rrNumCPairs Y = (Finset.univ.filter (TrueSRPath.CPairAt Y.tail)).card := by
    unfold rrNumCPairs
    rfl
  have hsplit := TrueSRPath.glueCycle_numCPairs_split (i := y + 1) (j := x) X.tail
    (glueArc X Y h) (gluable_of_RRGluable X Y h) (by omega) (by omega)
  have hg : (glueArc X Y h).edge ⟨2 * (y + 1), by omega⟩ = Y.tail.edge ⟨2 * y, by omega⟩ := by
    rw [glueArc_edge_pos X Y h ⟨2 * (y + 1), by omega⟩ (by show 0 < 2 * (y + 1); omega)]
    show Y.edgeAt ⟨2 * (y + 1) - 1, by omega⟩ = Y.tail.edge ⟨2 * y, by omega⟩
    rw [edgeAt_pos Y ⟨2 * (y + 1) - 1, by omega⟩ (by show 0 < 2 * (y + 1) - 1; omega)]
    have hidx : (⟨(⟨2 * (y + 1) - 1, by omega⟩ : Fin (2 * y + 2)).1 - 1, by omega⟩
        : Fin (2 * y + 1)) = ⟨2 * y, by omega⟩ := by
      apply Fin.ext
      show (2 * (y + 1) - 1) - 1 = 2 * y
      omega
    rw [hidx]
  have hseam : (if (TrueSRPath.glueCycle (i := y + 1) (j := x) X.tail (glueArc X Y h)
        (gluable_of_RRGluable X Y h) (by omega)).isCPair ⟨x, by omega⟩ then 1 else 0)
      = seamInd ((X.tail.edge ⟨2 * x, by omega⟩).endpoint
          = (Y.tail.edge ⟨2 * y, by omega⟩).endpoint) := by
    have hiff : (TrueSRPath.glueCycle (i := y + 1) (j := x) X.tail (glueArc X Y h)
          (gluable_of_RRGluable X Y h) (by omega)).isCPair ⟨x, by omega⟩
        ↔ (X.tail.edge ⟨2 * x, by omega⟩).endpoint
            = (Y.tail.edge ⟨2 * y, by omega⟩).endpoint := by
      rw [TrueSRPath.glueCycle_isCPair_seam (i := y + 1) (j := x) X.tail (glueArc X Y h)
        (gluable_of_RRGluable X Y h) (by omega) (by omega)]
      rw [hg]
    exact (ite_one_zero_congr _ _ hiff _ _).trans (seamInd_of_ite _).symm
  have harc : (if TrueSRPath.CPairAt (glueArc X Y h) ⟨0, by omega⟩ then 1 else 0)
      = seamInd (X.first.endpoint = Y.first.endpoint) :=
    (ite_one_zero_congr _ _ (glueArc_CPairAt_zero X Y h) _ _).trans (seamInd_of_ite _).symm
  have hurl : (Finset.univ.filter (rrGluedCycle X Y h).isCPair)
      = (Finset.univ.filter
          (TrueSRPath.glueCycle (i := y + 1) (j := x) X.tail (glueArc X Y h)
            (gluable_of_RRGluable X Y h) (by omega)).isCPair) := by
    rw [rrGluedCycle_eq]
  have hcount : (Finset.univ.filter (rrGluedCycle X Y h).isCPair).card
      = (Finset.univ.filter (TrueSRPath.CPairAt X.tail)).card
        + seamInd ((X.tail.edge ⟨2 * x, by omega⟩).endpoint
            = (Y.tail.edge ⟨2 * y, by omega⟩).endpoint)
        + (seamInd (X.first.endpoint = Y.first.endpoint)
          + (Finset.univ.filter (TrueSRPath.CPairAt Y.tail)).card) := by
    rw [hurl, hsplit, hseam]
    rw [glueArc_numCPairs X Y h, harc]
  rw [hnum, hX, hY, hcount]
  omega

/-- **Shinar--Feinberg Lemma A.4** (arXiv:1203.6560, Appendix A.2): three pairwise gluable
reaction-to-reaction paths `R*AR**`, `R*BR**`, `R*CR**` between distinct reactions `R*` and
`R**` — if the cycles `R*BR**AR*` and `R*CR**BR*` are both even, then so is the cycle
`R*CR**AR*`.

The three glued cycles' c-pair counts sum to twice the intrinsic counts plus the six seam
indicators; the three seams at `R*` compare the paths' first edges and those at `R**` compare
their last edges, each triple lying in the two-element complex set of the shared reaction, so
each triple contributes an odd sum (`odd_agree_count`).  Hence the total is even, the number of
odd cycles is even, and two even cycles force the third. -/
theorem rr_three_glued_even_of_two {a b c : ℕ}
    (A : N.TrueSRPathRR a) (B : N.TrueSRPathRR b) (C : N.TrueSRPathRR c)
    (hAB : RRGluable A B) (hAC : RRGluable A C) (hBC : RRGluable B C)
    (hABeven : (rrGluedCycle A B hAB).Even)
    (hBCEven : (rrGluedCycle B C hBC).Even) :
    (rrGluedCycle A C hAC).Even := by
  change Even (rrGluedCycle A B hAB).numCPairs at hABeven
  change Even (rrGluedCycle B C hBC).numCPairs at hBCEven
  change Even (rrGluedCycle A C hAC).numCPairs
  rw [Nat.even_iff] at hABeven hBCEven
  rw [Nat.even_iff]
  have h1 := rrGluedCycle_numCPairs A B hAB
  have h2 := rrGluedCycle_numCPairs B C hBC
  have h3 := rrGluedCycle_numCPairs A C hAC
  -- the three first edges all sit at the shared start reaction `R*`
  have hrAB : A.first.reaction = B.first.reaction := congrArg Subtype.val hAB.same_start
  have hrAC : A.first.reaction = C.first.reaction := congrArg Subtype.val hAC.same_start
  have hseamR : (seamInd (A.first.endpoint = B.first.endpoint)
      + seamInd (A.first.endpoint = C.first.endpoint)
      + seamInd (B.first.endpoint = C.first.endpoint)) % 2 = 1 := by
    have key := odd_agree_count
      (endpoint_pair_of_sameReaction (rfl : A.first.reaction = A.first.reaction))
      (endpoint_pair_of_sameReaction hrAB.symm)
      (endpoint_pair_of_sameReaction hrAC.symm)
    rw [← seamInd_of_ite, ← seamInd_of_ite, ← seamInd_of_ite] at key
    exact key
  -- the three last edges all sit at the shared end reaction `R**`
  have hLA : (A.tail.edge ⟨2 * a, by omega⟩).reaction = A.endReaction.1 :=
    last_edge_reaction A.tail (by omega)
  have hLB : (B.tail.edge ⟨2 * b, by omega⟩).reaction = B.endReaction.1 :=
    last_edge_reaction B.tail (by omega)
  have hLC : (C.tail.edge ⟨2 * c, by omega⟩).reaction = C.endReaction.1 :=
    last_edge_reaction C.tail (by omega)
  have hABend : A.endReaction = B.endReaction := hAB.same_end
  have hACend : A.endReaction = C.endReaction := hAC.same_end
  have hseamS : ((seamInd ((A.tail.edge ⟨2 * a, by omega⟩).endpoint
          = (B.tail.edge ⟨2 * b, by omega⟩).endpoint))
      + (seamInd ((A.tail.edge ⟨2 * a, by omega⟩).endpoint
          = (C.tail.edge ⟨2 * c, by omega⟩).endpoint))
      + (seamInd ((B.tail.edge ⟨2 * b, by omega⟩).endpoint
          = (C.tail.edge ⟨2 * c, by omega⟩).endpoint))) % 2 = 1 := by
    have key := odd_agree_count
      (endpoint_pair_of_sameReaction
        (hLA.trans ((congrArg Subtype.val hABend).trans hLB.symm)))
      (endpoint_pair_of_sameReaction
        (rfl : (B.tail.edge ⟨2 * b, by omega⟩).reaction
          = (B.tail.edge ⟨2 * b, by omega⟩).reaction))
      (endpoint_pair_of_sameReaction
        ((hLC.trans ((congrArg Subtype.val hACend).symm.trans
          (congrArg Subtype.val hABend))).trans hLB.symm))
    rw [← seamInd_of_ite, ← seamInd_of_ite, ← seamInd_of_ite] at key
    exact key
  rw [h1] at hABeven
  rw [h2] at hBCEven
  have htot : ((rrGluedCycle A B hAB).numCPairs + (rrGluedCycle B C hBC).numCPairs
      + (rrGluedCycle A C hAC).numCPairs) % 2 = 0 := by
    rw [h1, h2, h3]
    omega
  rw [h1, h2, h3] at htot
  rw [h3]
  omega

end TrueSRPathRR

end CRNT.Network
