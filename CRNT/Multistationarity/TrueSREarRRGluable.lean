import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRCycleSplit
import CRNT.Multistationarity.TrueSRRotate

/-!
# Reaction-to-reaction arcs of a true-SR cycle (the `RR` flavour)

The species flavour of "cut a cycle into two arcs" exists in the tree
(`TrueSRCycle.speciesArc` / `speciesArcBwd` in `TrueSRSpeciesPath.lean`, `arcFwd` / `arcBwd` in
`TrueSRCycleSplit.lean`, with `ss_gluable_arcs` making the two species-arcs glue for free).
**The reaction flavour does not.**  `CRNT/Multistationarity/TrueSRParityRR.lean` provides
`TrueSRPathRR`, `RRGluable`, `glueArc` and `rrGluedCycle`, but there is no way to read an arc of
a `TrueSRCycle` off as a `TrueSRPathRR`.  `rrGluedCycle` needs two RR paths and only `glueArc`
(the *closing* arc of an already-given pair) can produce one, so nothing can supply the first
path.  Every Shinar--Feinberg Lemma A.6 Case 2 application is written in terms of `rrGluedCycle`
and is blocked on exactly this.

This file supplies it.

## What is built here

* `TrueSRCycle.reactionArcFwd i j (hij : i.1 < j.1) : N.TrueSRPathRR (j.1 - i.1 - 1)` — the arc of
  `C` that leaves the reaction vertex `C.reaction i` through its right edge, runs *with* the cycle
  orientation through the species and reaction vertices strictly between `i` and `j`, and arrives
  at `C.reaction j` through that reaction's left edge.  The length parameter is the number of
  *interior* reaction vertices, `j.1 - i.1 - 1`.
* Accessors: the start reaction, the end reaction, the edge cases, "every edge is a cycle edge",
  and the vertex cases.
* `rrGluable_reactionArcFwd` — the ear-extraction step of the surviving Hole B route.  An
  off-cycle reaction-to-reaction path whose endpoints are `C.reaction i` and `C.reaction j` and
  which meets `C` nowhere else satisfies `RRGluable (reactionArcFwd C i j hij) A`, so
  `rrGluedCycle` yields the new cycle carrying the ear.  Per `research/DEAD-ENDS.md` B-12 that ear
  must close in `hSR.2`, never through the `hnd` clause of B-1.

## Three notes on the formalisation

* This module deliberately does **not** import `CRNT.Multistationarity.TrueChemistrySRCriterion`;
  that module contains the Hole B `sorry`, and importing it would put `sorryAx` in this file's
  axiom footprint and couple it to the file being closed.  Only hole-free modules are imported.
* The construction is *direct* — a `TrueSRPathRR` is a first edge plus a species-to-reaction tail —
  so it deliberately does **not** go through `TrueSRPathRR.prepend`, which is `private` in
  `TrueSRParityRR.lean:276` and unreachable from another module.
* A wrapping arc (one that passes index `n - 1`) is not built here.  It is obtained by rotating:
  `(C.rotate r).reactionArcFwd i' j'`, whose endpoints are the reactions of `C` at
  `((i'.1 + r) % n)` and `((j'.1 + r) % n)`.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

namespace TrueSRCycle

variable (C : N.TrueSRCycle n)

/-- **The reaction-to-reaction arc from `C.reaction i` to `C.reaction j`, with the orientation.**
Takes `i.1 < j.1`, so the arc does not wrap. -/
noncomputable def reactionArcFwd (i j : Fin n) (hij : i.1 < j.1) : N.TrueSRPathRR (j.1 - i.1 - 1)
    where
  first := C.rightEdge i
  tail := (C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1)
    (by have := C.nontrivial; omega)
  first_species := by
    have hzero := (C.rotate (i.1 + 1)).initialArcPath_vertex_even (j.1 - i.1 - 1)
      (by have := C.nontrivial; omega) ⟨0, by omega⟩ rfl
    rw [hzero]
    refine congrArg Sum.inl ?_
    rw [C.right_species i, C.rotate_species]
    refine congrArg C.species (Fin.ext ?_)
    simp
  first_ne_tail_edge := by
    intro q hsame
    have hn := C.nontrivial
    have hk : j.1 - i.1 - 1 < n := by omega
    have hq := q.isLt
    have hq2 : q.1 / 2 ≤ j.1 - i.1 - 1 := by omega
    have hlt : q.1 / 2 + (i.1 + 1) < n := by have := j.isLt; omega
    by_cases hpar : q.1 % 2 = 0
    · have he := (C.rotate (i.1 + 1)).initialArcPath_edge_even (j.1 - i.1 - 1) hk q hpar
      rw [C.rotate_leftEdge] at he
      rw [he] at hsame
      exact C.not_sameIncidence_left_right _ i hsame.symm
    · have he := (C.rotate (i.1 + 1)).initialArcPath_edge_odd (j.1 - i.1 - 1) hk q hpar
      rw [C.rotate_rightEdge] at he
      rw [he] at hsame
      have hb := C.sameIncidence_rightEdge_iff i _ hsame
      have hbv : i.1 = (q.1 / 2 + (i.1 + 1)) % n := congrArg Fin.val hb
      have hmod : (q.1 / 2 + (i.1 + 1)) % n = q.1 / 2 + (i.1 + 1) := Nat.mod_eq_of_lt hlt
      have hne : i.1 = q.1 / 2 + (i.1 + 1) := hbv.trans hmod
      omega
  first_ne_tail_vertex := by
    intro p heq
    have hn := C.nontrivial
    have hk : j.1 - i.1 - 1 < n := by omega
    have hp := p.isLt
    have hp2 : p.1 / 2 ≤ j.1 - i.1 - 1 := by omega
    have hlt : p.1 / 2 + (i.1 + 1) < n := by have := j.isLt; omega
    by_cases hpar : p.1 % 2 = 0
    · have hv := (C.rotate (i.1 + 1)).initialArcPath_vertex_even (j.1 - i.1 - 1) hk p hpar
      rw [hv] at heq
      exact Sum.inr_ne_inl heq
    · have hv : ((C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1) hk).vertex p
          = Sum.inr ⟨C.reaction ⟨(p.1 / 2 + (i.1 + 1)) % n, Nat.mod_lt _ (by omega)⟩,
              C.reaction_internal ⟨(p.1 / 2 + (i.1 + 1)) % n, Nat.mod_lt _ (by omega)⟩⟩ := by
        rw [(C.rotate (i.1 + 1)).initialArcPath_vertex_odd (j.1 - i.1 - 1) hk p hpar]
        exact congrArg Sum.inr (Subtype.ext rfl)
      rw [hv] at heq
      have hval : C.reaction i
          = C.reaction ⟨(p.1 / 2 + (i.1 + 1)) % n, Nat.mod_lt _ (by omega)⟩ := by
        rw [← C.right_reaction i]
        exact congrArg Subtype.val (Sum.inr.inj heq)
      have hinj : i = ⟨(p.1 / 2 + (i.1 + 1)) % n, Nat.mod_lt _ (by omega)⟩ :=
        C.reaction_injective hval
      have hmod : (p.1 / 2 + (i.1 + 1)) % n = p.1 / 2 + (i.1 + 1) := Nat.mod_eq_of_lt hlt
      have hne : i.1 = p.1 / 2 + (i.1 + 1) := (congrArg Fin.val hinj).trans hmod
      omega

/-- The arc leaves `C.reaction i`. -/
theorem reactionArcFwd_startReaction (i j : Fin n) (hij : i.1 < j.1) :
    ((reactionArcFwd C i j hij).startReaction : N.InternalTrueReaction).1 = C.reaction i := by
  have hs : ((reactionArcFwd C i j hij).startReaction : N.InternalTrueReaction).1
      = (reactionArcFwd C i j hij).first.reaction := rfl
  have hfirst : (reactionArcFwd C i j hij).first = C.rightEdge i := rfl
  rw [hs, hfirst, C.right_reaction i]

/-- The arc arrives at `C.reaction j`. -/
theorem reactionArcFwd_endReaction (i j : Fin n) (hij : i.1 < j.1) :
    ((reactionArcFwd C i j hij).endReaction : N.InternalTrueReaction).1 = C.reaction j := by
  have hn := C.nontrivial
  have hk : j.1 - i.1 - 1 < n := by omega
  have hlt : j.1 - i.1 - 1 + (i.1 + 1) < n := by have := j.isLt; omega
  have hed : (reactionArcFwd C i j hij).endReaction
      = ((C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1) hk).endReaction := rfl
  have hb := (C.rotate (i.1 + 1)).initialArcPath_endReaction (j.1 - i.1 - 1) hk
  have hb1 : (((C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1) hk).endReaction :
      N.InternalTrueReaction).1 = (C.rotate (i.1 + 1)).reaction ⟨j.1 - i.1 - 1, hk⟩ :=
    congrArg Subtype.val hb
  rw [hed, hb1]
  refine congrArg C.reaction (Fin.ext ?_)
  have heq : ((⟨j.1 - i.1 - 1, hk⟩ : Fin n).1 + (i.1 + 1)) % n = j.1 := by
    rw [Nat.mod_eq_of_lt hlt]
    omega
  exact heq

/-- **Edges of the reaction arc.**  Position `0` is the leaving edge `C.rightEdge i`; the
remaining positions are left and right edges of `C` at indices strictly after `i` and at most
`j`. -/
theorem reactionArcFwd_edge_cases (i j : Fin n) (hij : i.1 < j.1)
    (k : Fin (2 * (j.1 - i.1 - 1) + 2)) :
    ((reactionArcFwd C i j hij).edgeAt k = C.rightEdge i ∧ k.1 = 0) ∨
      (∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).edgeAt k = C.leftEdge t) ∨
      (∃ t : Fin n, i.1 < t.1 ∧ t.1 < j.1 ∧
        (reactionArcFwd C i j hij).edgeAt k = C.rightEdge t) := by
  have hn := C.nontrivial
  have hk : j.1 - i.1 - 1 < n := by omega
  rcases Nat.eq_zero_or_pos k.1 with h0 | hp
  · have hk0 : k = (⟨0, by omega⟩ : Fin (2 * (j.1 - i.1 - 1) + 2)) := Fin.ext h0
    rw [hk0]
    exact Or.inl ⟨TrueSRPathRR.edgeAt_zero (reactionArcFwd C i j hij), rfl⟩
  · have hed : (reactionArcFwd C i j hij).edgeAt k
        = ((C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1) hk).edge
          ⟨k.1 - 1, by have := k.isLt; omega⟩ := by
      rw [TrueSRPathRR.edgeAt_pos (reactionArcFwd C i j hij) k hp]
      rfl
    rw [hed]
    let q : Fin (2 * (j.1 - i.1 - 1) + 1) := ⟨k.1 - 1, by have := k.isLt; omega⟩
    have hq2 : q.1 / 2 ≤ j.1 - i.1 - 1 := by have := q.isLt; omega
    have hlt : q.1 / 2 + (i.1 + 1) < n := by have := j.isLt; omega
    by_cases hpar : q.1 % 2 = 0
    · refine Or.inr (Or.inl ⟨⟨q.1 / 2 + (i.1 + 1), hlt⟩, ?_, ?_, ?_⟩)
      · show i.1 < q.1 / 2 + (i.1 + 1); omega
      · show q.1 / 2 + (i.1 + 1) ≤ j.1; omega
      · have he := (C.rotate (i.1 + 1)).initialArcPath_edge_even (j.1 - i.1 - 1) hk q hpar
        rw [C.rotate_leftEdge] at he
        rw [he]
        refine congrArg C.leftEdge (Fin.ext ?_)
        show (q.1 / 2 + (i.1 + 1)) % n = q.1 / 2 + (i.1 + 1)
        rw [Nat.mod_eq_of_lt hlt]
    · refine Or.inr (Or.inr ⟨⟨q.1 / 2 + (i.1 + 1), hlt⟩, ?_, ?_, ?_⟩)
      · show i.1 < q.1 / 2 + (i.1 + 1); omega
      · show q.1 / 2 + (i.1 + 1) < j.1; omega
      · have he := (C.rotate (i.1 + 1)).initialArcPath_edge_odd (j.1 - i.1 - 1) hk q hpar
        rw [C.rotate_rightEdge] at he
        rw [he]
        refine congrArg C.rightEdge (Fin.ext ?_)
        show (q.1 / 2 + (i.1 + 1)) % n = q.1 / 2 + (i.1 + 1)
        rw [Nat.mod_eq_of_lt hlt]

/-- **Every edge of the reaction arc is an edge of the cycle.** -/
theorem reactionArcFwd_edge_on_cycle (i j : Fin n) (hij : i.1 < j.1)
    (k : Fin (2 * (j.1 - i.1 - 1) + 2)) :
    C.ContainsEdge ((reactionArcFwd C i j hij).edgeAt k) := by
  rcases C.reactionArcFwd_edge_cases i j hij k with ⟨h, _⟩ | ⟨t, _, _, h⟩ | ⟨t, _, _, h⟩
  · rw [h]
    exact Or.inr ⟨i, ⟨rfl, rfl, rfl⟩⟩
  · rw [h]
    exact Or.inl ⟨t, ⟨rfl, rfl, rfl⟩⟩
  · rw [h]
    exact Or.inr ⟨t, ⟨rfl, rfl, rfl⟩⟩

/-- **Vertices of the reaction arc.**  Position `0` is the reaction `C.reaction i`; every later
vertex is `C.species t` or `C.reaction t` for `i.1 < t.1 ≤ j.1`. -/
theorem reactionArcFwd_vertex_cases (i j : Fin n) (hij : i.1 < j.1)
    (p : Fin (2 * (j.1 - i.1 - 1) + 3)) :
    (∃ (h : TrueReaction.Internal N (C.reaction i)), p.1 = 0 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inr ⟨C.reaction i, h⟩) ∨
      (∃ (t : Fin n), i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inl (C.species t)) ∨
      (∃ (t : Fin n) (h : TrueReaction.Internal N (C.reaction t)), i.1 < t.1 ∧ t.1 ≤ j.1 ∧
        (reactionArcFwd C i j hij).vertexAt p = Sum.inr ⟨C.reaction t, h⟩) := by
  have hn := C.nontrivial
  have hk : j.1 - i.1 - 1 < n := by omega
  rcases Nat.eq_zero_or_pos p.1 with h0 | hp
  · have hp0 : p = (⟨0, by omega⟩ : Fin (2 * (j.1 - i.1 - 1) + 3)) := Fin.ext h0
    rw [hp0]
    refine Or.inl ?_
    refine Exists.intro (C.reaction_internal i : TrueReaction.Internal N (C.reaction i)) ?_
    refine And.intro rfl ?_
    rw [TrueSRPathRR.vertexAt_zero]
    have hs : ((reactionArcFwd C i j hij).startReaction : N.InternalTrueReaction).1
        = (C.rightEdge i).reaction := rfl
    apply congrArg Sum.inr
    apply Subtype.ext
    exact hs.trans (C.right_reaction i)
  · have hvv : (reactionArcFwd C i j hij).vertexAt p
        = ((C.rotate (i.1 + 1)).initialArcPath (j.1 - i.1 - 1) hk).vertex
          ⟨p.1 - 1, by have := p.isLt; omega⟩ := by
      rw [TrueSRPathRR.vertexAt, if_neg (by omega : ¬ (p.1 = 0))]
      rfl
    let q : Fin (2 * (j.1 - i.1 - 1) + 2) := ⟨p.1 - 1, by have := p.isLt; omega⟩
    have hq2 : q.1 / 2 ≤ j.1 - i.1 - 1 := by have := q.isLt; omega
    have hlt : q.1 / 2 + (i.1 + 1) < n := by have := j.isLt; omega
    have hsum : q.1 / 2 + (i.1 + 1) ≤ j.1 := by omega
    by_cases hpar : q.1 % 2 = 0
    · have hv0 := (C.rotate (i.1 + 1)).initialArcPath_vertex_even (j.1 - i.1 - 1) hk q hpar
      have hlt1 : i.1 < q.1 / 2 + (i.1 + 1) := by omega
      have hgoal : (reactionArcFwd C i j hij).vertexAt p
          = Sum.inl (C.species ⟨q.1 / 2 + (i.1 + 1), hlt⟩) := by
        rw [hvv, hv0, C.rotate_species]
        apply congrArg Sum.inl
        apply congrArg C.species
        apply Fin.ext
        show (q.1 / 2 + (i.1 + 1)) % n = q.1 / 2 + (i.1 + 1)
        rw [Nat.mod_eq_of_lt hlt]
      exact Or.inr (Or.inl ⟨⟨q.1 / 2 + (i.1 + 1), hlt⟩, hlt1, hsum, hgoal⟩)
    · have hv0 := (C.rotate (i.1 + 1)).initialArcPath_vertex_odd (j.1 - i.1 - 1) hk q hpar
      have hlt1 : i.1 < q.1 / 2 + (i.1 + 1) := by omega
      have hgoal : (reactionArcFwd C i j hij).vertexAt p
          = Sum.inr ⟨C.reaction ⟨q.1 / 2 + (i.1 + 1), hlt⟩,
              C.reaction_internal ⟨q.1 / 2 + (i.1 + 1), hlt⟩⟩ := by
        rw [hvv, hv0]
        apply congrArg Sum.inr
        apply Subtype.ext
        show C.reaction ⟨(q.1 / 2 + (i.1 + 1)) % n, Nat.mod_lt _ (by omega)⟩
          = C.reaction ⟨q.1 / 2 + (i.1 + 1), hlt⟩
        apply congrArg C.reaction
        apply Fin.ext
        show (q.1 / 2 + (i.1 + 1)) % n = q.1 / 2 + (i.1 + 1)
        rw [Nat.mod_eq_of_lt hlt]
      exact Or.inr (Or.inr ⟨⟨q.1 / 2 + (i.1 + 1), hlt⟩,
        C.reaction_internal ⟨q.1 / 2 + (i.1 + 1), hlt⟩, hlt1, hsum, hgoal⟩)

/-- **Species vertices of the reaction arc are exactly the cycle species strictly after `i`.** -/
theorem reactionArcFwd_species (i j : Fin n) (hij : i.1 < j.1) {x : S}
    (h : (reactionArcFwd C i j hij).HasSpecies x) :
    ∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧ x = C.species t := by
  obtain ⟨p, hp⟩ := h
  rcases C.reactionArcFwd_vertex_cases i j hij p with
    ⟨hi, _, hv⟩ | ⟨t, hlt1, hlt2, ht⟩ | ⟨t, hi, hlt1, hlt2, ht⟩
  · exact absurd (hv.symm.trans hp) (by simp)
  · exact ⟨t, hlt1, hlt2, Sum.inl.inj (hp.symm.trans ht)⟩
  · exact absurd (ht.symm.trans hp) (by simp)

/-- **Reaction vertices of the reaction arc are `C.reaction i` and the cycle reactions strictly
after it, up to `C.reaction j`.** -/
theorem reactionArcFwd_reaction (i j : Fin n) (hij : i.1 < j.1)
    {ρ : N.InternalTrueReaction} (h : (reactionArcFwd C i j hij).HasReaction ρ) :
    ρ.1 = C.reaction i ∨ (∃ t : Fin n, i.1 < t.1 ∧ t.1 ≤ j.1 ∧ ρ.1 = C.reaction t) := by
  obtain ⟨p, hp⟩ := h
  rcases C.reactionArcFwd_vertex_cases i j hij p with
    ⟨hi, _, hv⟩ | ⟨t, hlt1, hlt2, ht⟩ | ⟨t, hi, hlt1, hlt2, ht⟩
  · rw [hv] at hp
    exact Or.inl (congrArg Subtype.val (Sum.inr.inj hp)).symm
  · exact absurd (ht.symm.trans hp) (by simp)
  · rw [ht] at hp
    exact Or.inr ⟨t, hlt1, hlt2, (congrArg Subtype.val (Sum.inr.inj hp)).symm⟩

/-- **Ear extraction, step 1 (DEAD-ENDS B-12).**  An off-cycle reaction-to-reaction path whose
endpoints are `C.reaction i` and `C.reaction j`, and which meets `C` nowhere except at its start
reaction and at no species of `C`, glues to the reaction arc of `C` between those two reactions.
`rrGluedCycle` then produces the cycle that carries the ear; that cycle is the object the
Shinar--Feinberg Lemma A.6 Case 2 discharge (`lemmaA6_case2_*`) consumes, and it closes in
`hSR.2` rather than through the unsatisfiable `hnd` clause recorded in DEAD-ENDS B-1. -/
theorem rrGluable_reactionArcFwd (i j : Fin n) (hij : i.1 < j.1) {L : ℕ}
    (A : N.TrueSRPathRR L)
    (hstart : (A.startReaction : N.InternalTrueReaction).1 = C.reaction i)
    (hend : (A.endReaction : N.InternalTrueReaction).1 = C.reaction j)
    (hspec : ∀ s : S, A.HasSpecies s → ¬ C.HasSpecies s)
    (hint : ∀ p : Fin (2 * L + 3), p.1 ≠ 0 → ¬ C.HasVertex (A.vertexAt p))
    (hedge : ∀ l : Fin (2 * L + 2), ¬ C.ContainsEdge (A.edgeAt l)) :
    TrueSRPathRR.RRGluable (reactionArcFwd C i j hij) A where
  same_start := by
    have hs := C.reactionArcFwd_startReaction i j hij
    exact Subtype.ext (hstart.trans hs.symm).symm
  same_end := by
    have he := C.reactionArcFwd_endReaction i j hij
    exact Subtype.ext (hend.trans he.symm).symm
  species_disjoint := by
    intro s hA hE
    obtain ⟨t, _, _, hst⟩ := C.reactionArcFwd_species i j hij hA
    rw [hst] at hE
    exact hspec _ hE ⟨t, rfl⟩
  reaction_disjoint := by
    intro ρ hA hE
    obtain ⟨p, hp⟩ := hE
    by_cases hp0 : p.1 = 0
    · have hpv : (⟨0, by omega⟩ : Fin (2 * L + 3)) = p := Fin.ext hp0.symm
      rw [← hpv, TrueSRPathRR.vertexAt_zero] at hp
      have hρ : ρ.1 = (A.startReaction : N.InternalTrueReaction).1 :=
        (congrArg Subtype.val (Sum.inr.inj hp)).symm
      have hs := C.reactionArcFwd_startReaction i j hij
      have hstartArc := C.reactionArcFwd_startReaction i j hij
      exact Or.inl (Subtype.ext ((hρ.trans hstart).trans hstartArc.symm))
    · refine Or.inr ?_
      have hcontra : C.HasVertex (A.vertexAt p) := by
        rcases C.reactionArcFwd_reaction i j hij hA with hρ | ⟨t, _, _, hρ⟩
        · rw [hp]
          exact ⟨i, hρ.symm⟩
        · rw [hp]
          exact ⟨t, hρ.symm⟩
      exact absurd hcontra (hint p hp0)
  edge_disjoint := by
    intro k l hsame
    rcases C.reactionArcFwd_edge_cases i j hij k with ⟨h, _⟩ | ⟨t, _, _, h⟩ | ⟨t, _, _, h⟩
    · rw [h] at hsame
      exact hedge l (Or.inr ⟨i, hsame.symm⟩)
    · rw [h] at hsame
      exact hedge l (Or.inl ⟨t, hsame.symm⟩)
    · rw [h] at hsame
      exact hedge l (Or.inr ⟨t, hsame.symm⟩)

end TrueSRCycle

end CRNT.Network
