import CRNT.Multistationarity.TrueSRMinimalChord
import CRNT.Multistationarity.TrueSRChordParity
import CRNT.Multistationarity.TrueSRCycleReverse
import CRNT.Multistationarity.TrueSRArc
import CRNT.Multistationarity.TrueSRPathAccessors

/-!
# Splitting a true-SR cycle into its two arcs, and the chord exclusion

`TrueSRGlueInterface.lean` fixes the abstraction that **a cycle is exactly two
species-to-reaction paths with the same two endpoints and disjoint interiors**, and builds the
gluing direction (`glueCycle`).  This file builds the splitting direction, which is what
Banaji--Craciun's Lemma 10 (arXiv:0809.1308) consumes.

Between the species vertex `0` and the reaction vertex `m` of a cycle `C` there are two arcs:
`arcFwd`, read off with the cycle's orientation (`initialArcPath`), and `arcBwd`, read off
against it (`initialArcPath` of `C.reverse`).  `gluable_arcs` proves they satisfy `Gluable`, and
`glueCycle_arcs_isCPair` shows the glue reindexes c-pairs by the identity, so
`glueCycle_arcs_even` transports evenness from `C` to the reglued cycle.

With that, `no_chord_of_trueSRCriterion` is Lemma 10 for the true-chemistry SR graph: an even
cycle admits no species-to-reaction chord whose interior misses the cycle and none of whose
edges is a cycle edge.  The chord glues to each arc; the three c-pair counts sum to an odd
number (`three_glued_parity`), so one of the two glued cycles is even and shares a whole
species-to-reaction arc with `C`, which the second conjunct of `TrueSRStrongCriterion` forbids.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

open TrueSRPath

@[simp] theorem reverse_species' (C : N.TrueSRCycle n) (j : Fin n) :
    (C.reverse).species j =
      C.species ⟨(n - j.1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

@[simp] theorem reverse_reaction' (C : N.TrueSRCycle n) (j : Fin n) :
    (C.reverse).reaction j = C.reaction (revPerm n j) := rfl

/-! ### Edge identity along a cycle -/

theorem sameIncidence_leftEdge_iff (C : N.TrueSRCycle n) (a b : Fin n)
    (h : (C.leftEdge a).SameIncidence (C.leftEdge b)) : a = b := by
  apply C.reaction_injective
  have h2 := h.2.1
  rw [C.left_reaction a, C.left_reaction b] at h2
  exact h2

theorem sameIncidence_rightEdge_iff (C : N.TrueSRCycle n) (a b : Fin n)
    (h : (C.rightEdge a).SameIncidence (C.rightEdge b)) : a = b := by
  apply C.reaction_injective
  have h2 := h.2.1
  rw [C.right_reaction a, C.right_reaction b] at h2
  exact h2

theorem not_sameIncidence_left_right (C : N.TrueSRCycle n) (a b : Fin n) :
    ¬ (C.leftEdge a).SameIncidence (C.rightEdge b) := by
  intro h
  have hr : a = b := by
    apply C.reaction_injective
    have h2 := h.2.1
    rw [C.left_reaction a, C.right_reaction b] at h2
    exact h2
  have hs := h.1
  rw [C.left_species a, C.right_species b, ← hr] at hs
  have := C.species_injective hs
  have hv := congrArg Fin.val this
  have hn := C.nontrivial
  have ha := a.isLt
  simp only at hv
  rcases Nat.lt_or_ge (a.1 + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have : a.1 + 1 = n := by omega
    rw [this, Nat.mod_self] at hv
    omega

/-! ### The two arcs of a cycle between species `0` and reaction `m` -/

section Split

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)

/-- The forward arc of `C`: species `0` to reaction `m`, travelling with the orientation. -/
noncomputable def arcFwd : N.TrueSRPath (2 * m + 1) := C.initialArcPath m hm

/-- The backward arc of `C`: species `0` to reaction `m`, travelling against the orientation. -/
noncomputable def arcBwd : N.TrueSRPath (2 * (n - 1 - m) + 1) :=
  (C.reverse).initialArcPath (n - 1 - m) (by have := C.nontrivial; omega)

theorem arcFwd_startSpecies :
    (C.arcFwd m hm).startSpecies = C.species ⟨0, by omega⟩ :=
  C.initialArcPath_startSpecies m hm

theorem arcFwd_endReaction :
    ((C.arcFwd m hm).endReaction : N.InternalTrueReaction).1 = C.reaction ⟨m, hm⟩ :=
  congrArg (fun ρ : N.InternalTrueReaction => ρ.1) (C.initialArcPath_endReaction m hm)

theorem arcBwd_startSpecies :
    (C.arcBwd m hm).startSpecies = C.species ⟨0, by omega⟩ := by
  have h := (C.reverse).initialArcPath_startSpecies (n - 1 - m)
    (by have := C.nontrivial; omega)
  rw [arcBwd, h, reverse_species']
  refine congrArg C.species (Fin.ext ?_)
  have := C.nontrivial
  show (n - 0) % n = 0
  simp

theorem arcBwd_endReaction :
    ((C.arcBwd m hm).endReaction : N.InternalTrueReaction).1 = C.reaction ⟨m, hm⟩ := by
  let mr : Fin n := ⟨n - 1 - m, by have := C.nontrivial; omega⟩
  have h := (C.reverse).initialArcPath_endReaction (n - 1 - m)
    (by have := C.nontrivial; omega)
  have hval := congrArg (fun ρ : N.InternalTrueReaction => ρ.1) h
  change ((C.reverse).initialArcPath (n - 1 - m) (by have := C.nontrivial; omega)).endReaction.1 = _
  calc
    _ = (C.reverse).reaction mr := by simpa [mr] using hval
    _ = C.reaction ⟨m, hm⟩ := by
      rw [reverse_reaction']
      congr 1
      apply Fin.ext
      dsimp [mr]
      have := C.nontrivial
      omega

end Split

/-! ### Interiors of the two arcs -/

theorem arcFwd_interiorSpecies (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) {x : S}
    (h : (C.arcFwd m hm).InteriorSpecies x) :
    ∃ i : Fin n, 0 < i.1 ∧ i.1 ≤ m ∧ x = C.species i := by
  obtain ⟨p, hp0, hpv⟩ := h
  have hplt := p.isLt
  by_cases hpar : p.1 % 2 = 0
  · rw [arcFwd, C.initialArcPath_vertex_even m hm p hpar] at hpv
    refine ⟨⟨p.1 / 2, by omega⟩, ?_, ?_, ?_⟩
    · show 0 < p.1 / 2
      have : p.1 ≠ 0 := by simpa using hp0
      omega
    · show p.1 / 2 ≤ m
      omega
    · exact (Sum.inl.inj hpv).symm
  · rw [arcFwd, C.initialArcPath_vertex_odd m hm p hpar] at hpv
    exact absurd hpv (by simp)

theorem arcBwd_interiorSpecies (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) {x : S}
    (h : (C.arcBwd m hm).InteriorSpecies x) :
    ∃ i : Fin n, m < i.1 ∧ x = C.species i := by
  have hn := C.nontrivial
  obtain ⟨p, hp0, hpv⟩ := h
  have hplt := p.isLt
  have hp0' : p.1 ≠ 0 := by simpa using hp0
  by_cases hpar : p.1 % 2 = 0
  · rw [arcBwd, (C.reverse).initialArcPath_vertex_even (n - 1 - m) (by omega) p hpar,
      reverse_species'] at hpv
    refine ⟨⟨(n - p.1 / 2) % n, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · show m < (n - p.1 / 2) % n
      have h1 : 0 < p.1 / 2 := by omega
      have h2 : p.1 / 2 ≤ n - 1 - m := by omega
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · exact (Sum.inl.inj hpv).symm
  · rw [arcBwd, (C.reverse).initialArcPath_vertex_odd (n - 1 - m) (by omega) p hpar] at hpv
    exact absurd hpv (by simp)

theorem arcFwd_interiorReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    {ρ : N.InternalTrueReaction} (h : (C.arcFwd m hm).InteriorReaction ρ) :
    ∃ i : Fin n, i.1 < m ∧ ρ.1 = C.reaction i := by
  obtain ⟨p, hpL, hpv⟩ := h
  have hplt := p.isLt
  have hpL' : p.1 ≠ 2 * m + 1 := by simpa using hpL
  by_cases hpar : p.1 % 2 = 0
  · rw [arcFwd, C.initialArcPath_vertex_even m hm p hpar] at hpv
    exact absurd hpv (by simp)
  · rw [arcFwd, C.initialArcPath_vertex_odd m hm p hpar] at hpv
    refine ⟨⟨p.1 / 2, by omega⟩, ?_, ?_⟩
    · show p.1 / 2 < m
      omega
    · exact congrArg Subtype.val (Sum.inr.inj hpv).symm

theorem arcBwd_interiorReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    {ρ : N.InternalTrueReaction} (h : (C.arcBwd m hm).InteriorReaction ρ) :
    ∃ i : Fin n, m < i.1 ∧ ρ.1 = C.reaction i := by
  have hn := C.nontrivial
  obtain ⟨p, hpL, hpv⟩ := h
  have hplt := p.isLt
  have hpL' : p.1 ≠ 2 * (n - 1 - m) + 1 := by simpa using hpL
  by_cases hpar : p.1 % 2 = 0
  · rw [arcBwd, (C.reverse).initialArcPath_vertex_even (n - 1 - m) (by omega) p hpar] at hpv
    exact absurd hpv (by simp)
  · rw [arcBwd, (C.reverse).initialArcPath_vertex_odd (n - 1 - m) (by omega) p hpar] at hpv
    have hval : ρ.1 = (C.reverse).reaction ⟨p.1 / 2, by omega⟩ :=
      congrArg Subtype.val (Sum.inr.inj hpv).symm
    refine ⟨revPerm n ⟨p.1 / 2, by omega⟩, ?_, ?_⟩
    · show m < n - 1 - p.1 / 2
      omega
    · rw [hval]; rfl

/-! ### Edges of the two arcs -/

theorem arcFwd_edge_cases (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (q : Fin (2 * m + 1)) :
    (∃ i : Fin n, i.1 ≤ m ∧ (C.arcFwd m hm).edge q = C.leftEdge i) ∨
      (∃ i : Fin n, i.1 < m ∧ (C.arcFwd m hm).edge q = C.rightEdge i) := by
  have hq := q.isLt
  by_cases hpar : q.1 % 2 = 0
  · exact Or.inl ⟨⟨q.1 / 2, by omega⟩, by show q.1 / 2 ≤ m; omega,
      C.initialArcPath_edge_even m hm q hpar⟩
  · exact Or.inr ⟨⟨q.1 / 2, by omega⟩, by show q.1 / 2 < m; omega,
      C.initialArcPath_edge_odd m hm q hpar⟩

theorem arcBwd_edge_cases (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (q : Fin (2 * (n - 1 - m) + 1)) :
    (∃ i : Fin n, m < i.1 ∧ (C.arcBwd m hm).edge q = C.leftEdge i) ∨
      (∃ i : Fin n, m ≤ i.1 ∧ (C.arcBwd m hm).edge q = C.rightEdge i) := by
  have hn := C.nontrivial
  have hq := q.isLt
  by_cases hpar : q.1 % 2 = 0
  · refine Or.inr ⟨revPerm n ⟨q.1 / 2, by omega⟩, by show m ≤ n - 1 - q.1 / 2; omega, ?_⟩
    exact (C.reverse).initialArcPath_edge_even (n - 1 - m) (by omega) q hpar
  · refine Or.inl ⟨revPerm n ⟨q.1 / 2, by omega⟩, by show m < n - 1 - q.1 / 2; omega, ?_⟩
    exact (C.reverse).initialArcPath_edge_odd (n - 1 - m) (by omega) q hpar

/-- Every edge of the forward arc is an edge of the cycle. -/
theorem arcFwd_edge_on_cycle (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (q : Fin (2 * m + 1)) :
    (∃ i : Fin n, (C.arcFwd m hm).edge q = C.leftEdge i) ∨
      (∃ i : Fin n, (C.arcFwd m hm).edge q = C.rightEdge i) := by
  rcases C.arcFwd_edge_cases m hm q with ⟨i, _, h⟩ | ⟨i, _, h⟩
  · exact Or.inl ⟨i, h⟩
  · exact Or.inr ⟨i, h⟩

/-- Every edge of the backward arc is an edge of the cycle. -/
theorem arcBwd_edge_on_cycle (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (q : Fin (2 * (n - 1 - m) + 1)) :
    (∃ i : Fin n, (C.arcBwd m hm).edge q = C.leftEdge i) ∨
      (∃ i : Fin n, (C.arcBwd m hm).edge q = C.rightEdge i) := by
  rcases C.arcBwd_edge_cases m hm q with ⟨i, _, h⟩ | ⟨i, _, h⟩
  · exact Or.inl ⟨i, h⟩
  · exact Or.inr ⟨i, h⟩

/-- The two arcs of a cycle share no edge. -/
theorem arcs_edge_disjoint (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (a : Fin (2 * m + 1)) (b : Fin (2 * (n - 1 - m) + 1)) :
    ¬ ((C.arcFwd m hm).edge a).SameIncidence ((C.arcBwd m hm).edge b) := by
  intro hsame
  rcases C.arcFwd_edge_cases m hm a with ⟨i, hi, hea⟩ | ⟨i, hi, hea⟩ <;>
    rcases C.arcBwd_edge_cases m hm b with ⟨j, hj, heb⟩ | ⟨j, hj, heb⟩ <;>
      rw [hea, heb] at hsame
  · have := C.sameIncidence_leftEdge_iff i j hsame
    rw [this] at hi
    omega
  · exact C.not_sameIncidence_left_right i j hsame
  · exact C.not_sameIncidence_left_right j i (TrueSREdge.SameIncidence.symm hsame)
  · have := C.sameIncidence_rightEdge_iff i j hsame
    rw [this] at hi
    omega

/-- **The two arcs of a cycle glue back to it.**  Between the species vertex `0` and the
reaction vertex `m`, a simple cycle is exactly two species-to-reaction paths with those
endpoints and disjoint interiors. -/
theorem gluable_arcs (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) :
    Gluable (C.arcFwd m hm) (C.arcBwd m hm) where
  same_start := by rw [C.arcFwd_startSpecies m hm, C.arcBwd_startSpecies m hm]
  same_end := by
    apply Subtype.ext
    rw [C.arcFwd_endReaction m hm, C.arcBwd_endReaction m hm]
  species_disjoint := by
    intro x hF hB
    obtain ⟨i, _, hi, hxi⟩ := C.arcFwd_interiorSpecies m hm hF
    obtain ⟨j, hj, hxj⟩ := C.arcBwd_interiorSpecies m hm hB
    have : i = j := C.species_injective (hxi.symm.trans hxj)
    rw [this] at hi
    omega
  reaction_disjoint := by
    intro ρ hF hB
    obtain ⟨i, hi, hρi⟩ := C.arcFwd_interiorReaction m hm hF
    obtain ⟨j, hj, hρj⟩ := C.arcBwd_interiorReaction m hm hB
    have : i = j := C.reaction_injective (hρi.symm.trans hρj)
    rw [this] at hi
    omega
  edge_disjoint := C.arcs_edge_disjoint m hm

/-! ### The glued arcs have the cycle's c-pairs -/

section Even

variable (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)

private theorem arcFwd_edge_even_eq (q : ℕ) (hq : q < 2 * m + 1) (hpar : q % 2 = 0)
    (i : Fin n) (hi : i.1 = q / 2) :
    (C.arcFwd m hm).edge ⟨q, hq⟩ = C.leftEdge i := by
  rw [arcFwd, C.initialArcPath_edge_even m hm ⟨q, hq⟩ hpar]
  refine congrArg C.leftEdge (Fin.ext ?_)
  show q / 2 = i.1
  omega

private theorem arcFwd_edge_odd_eq (q : ℕ) (hq : q < 2 * m + 1) (hpar : q % 2 ≠ 0)
    (i : Fin n) (hi : i.1 = q / 2) :
    (C.arcFwd m hm).edge ⟨q, hq⟩ = C.rightEdge i := by
  rw [arcFwd, C.initialArcPath_edge_odd m hm ⟨q, hq⟩ hpar]
  refine congrArg C.rightEdge (Fin.ext ?_)
  show q / 2 = i.1
  omega

private theorem arcBwd_edge_even_eq (q : ℕ) (hq : q < 2 * (n - 1 - m) + 1) (hpar : q % 2 = 0)
    (i : Fin n) (hi : i.1 = n - 1 - q / 2) :
    (C.arcBwd m hm).edge ⟨q, hq⟩ = C.rightEdge i := by
  have hn := C.nontrivial
  rw [arcBwd, (C.reverse).initialArcPath_edge_even (n - 1 - m) (by omega) ⟨q, hq⟩ hpar,
    reverse_leftEdge]
  refine congrArg C.rightEdge (Fin.ext ?_)
  show n - 1 - q / 2 = i.1
  omega

private theorem arcBwd_edge_odd_eq (q : ℕ) (hq : q < 2 * (n - 1 - m) + 1) (hpar : q % 2 ≠ 0)
    (i : Fin n) (hi : i.1 = n - 1 - q / 2) :
    (C.arcBwd m hm).edge ⟨q, hq⟩ = C.leftEdge i := by
  have hn := C.nontrivial
  rw [arcBwd, (C.reverse).initialArcPath_edge_odd (n - 1 - m) (by omega) ⟨q, hq⟩ hpar,
    reverse_rightEdge]
  refine congrArg C.leftEdge (Fin.ext ?_)
  show n - 1 - q / 2 = i.1
  omega

/-- **Gluing the two arcs back together reproduces the cycle's c-pair pattern.**  Position `t`
of the glued cycle is a c-pair exactly when position `t` of `C` is. -/
theorem glueCycle_arcs_isCPair (hn2 : 2 ≤ (n - 1 - m) + m + 1)
    (t : Fin ((n - 1 - m) + m + 1)) :
    (glueCycle (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2).isCPair t ↔
      C.isCPair ⟨t.1, by have := t.isLt; omega⟩ := by
  have hn := C.nontrivial
  have htl := t.isLt
  rcases lt_trichotomy t.1 m with hlt | heq | hgt
  · rw [glueCycle_isCPair_below (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2 t hlt,
      C.arcFwd_edge_even_eq m hm (2 * t.1) (by omega) (by omega) ⟨t.1, by omega⟩ (by simp),
      C.arcFwd_edge_odd_eq m hm (2 * t.1 + 1) (by omega) (by omega) ⟨t.1, by omega⟩
        (by simp; omega)]
    rfl
  · have ht : t = ⟨m, by omega⟩ := Fin.ext heq
    rw [ht, glueCycle_isCPair_seam (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2
        (by omega),
      C.arcFwd_edge_even_eq m hm (2 * m) (by omega) (by omega) ⟨m, by omega⟩ (by simp),
      C.arcBwd_edge_even_eq m hm (2 * (n - 1 - m)) (by omega) (by omega) ⟨m, by omega⟩
        (by simp; omega)]
    rfl
  · rw [glueCycle_isCPair_above (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2 t hgt,
      C.arcBwd_edge_odd_eq m hm (2 * (n - 1 - m) + 2 * m - 2 * t.1 + 1) (by omega) (by omega)
        ⟨t.1, by omega⟩ (by simp; omega),
      C.arcBwd_edge_even_eq m hm (2 * (n - 1 - m) + 2 * m - 2 * t.1) (by omega) (by omega)
        ⟨t.1, by omega⟩ (by simp; omega)]
    rfl

/-- **The two arcs of an even cycle glue back to an even cycle.** -/
theorem glueCycle_arcs_even (hn2 : 2 ≤ (n - 1 - m) + m + 1) (hC : C.Even) :
    (glueCycle (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2).Even := by
  classical
  have hn := C.nontrivial
  unfold TrueSRCycle.Even TrueSRCycle.numCPairs at hC ⊢
  have hcard :
      (Finset.univ.filter
          (glueCycle (C.arcFwd m hm) (C.arcBwd m hm) (C.gluable_arcs m hm) hn2).isCPair).card
        = (Finset.univ.filter C.isCPair).card := by
    apply Finset.card_bij (fun t _ => (⟨t.1, by have := t.isLt; omega⟩ : Fin n))
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact (C.glueCycle_arcs_isCPair m hm hn2 t).mp ht
    · intro a ha b hb hab
      have hv := congrArg Fin.val hab
      exact Fin.ext hv
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      refine ⟨⟨i.1, by have := i.isLt; omega⟩, ?_, ?_⟩
      · refine (C.glueCycle_arcs_isCPair m hm hn2 ⟨i.1, by have := i.isLt; omega⟩).mpr ?_
        exact hi
      · exact Fin.ext rfl
  rw [hcard]
  exact hC

end Even


end CRNT.Network.TrueSRCycle

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

open TrueSRPath TrueSRCycle

/-! ### Rotating a cycle -/

private theorem rot_inv {n : ℕ} (hn : 0 < n) {r : ℕ} (hr : r < n) {j : ℕ} (hj : j < n) :
    (((j + (n - r)) % n) + r) % n = j := by
  rcases Nat.lt_or_ge (j + (n - r)) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    have he : j + (n - r) + r = j + n := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · have h2 : j + (n - r) - n < n := by omega
    have h3 : (j + (n - r)) % n = j + (n - r) - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h2]
    rw [h3]
    have he : j + (n - r) - n + r = j := by omega
    rw [he, Nat.mod_eq_of_lt hj]

namespace TrueSRCycle

theorem rotate_hasSpecies (C : N.TrueSRCycle n) {r : ℕ} (hr : r < n) (x : S) :
    (C.rotate r).HasSpecies x ↔ C.HasSpecies x := by
  have hn : 0 < n := by have := C.nontrivial; omega
  constructor
  · rintro ⟨i, hi⟩
    rw [C.rotate_species r i] at hi
    exact ⟨_, hi⟩
  · rintro ⟨j, hj⟩
    refine ⟨⟨(j.1 + (n - r)) % n, Nat.mod_lt _ hn⟩, ?_⟩
    rw [C.rotate_species r]
    refine Eq.trans (congrArg C.species (Fin.ext ?_)) hj
    exact rot_inv hn hr j.isLt

theorem rotate_hasReaction (C : N.TrueSRCycle n) {r : ℕ} (hr : r < n) (ρ : N.TrueReaction) :
    (C.rotate r).HasReaction ρ ↔ C.HasReaction ρ := by
  have hn : 0 < n := by have := C.nontrivial; omega
  constructor
  · rintro ⟨i, hi⟩
    rw [C.rotate_reaction r i] at hi
    exact ⟨_, hi⟩
  · rintro ⟨j, hj⟩
    refine ⟨⟨(j.1 + (n - r)) % n, Nat.mod_lt _ hn⟩, ?_⟩
    rw [C.rotate_reaction r]
    refine Eq.trans (congrArg C.reaction (Fin.ext ?_)) hj
    exact rot_inv hn hr j.isLt

theorem rotate_hasVertex (C : N.TrueSRCycle n) {r : ℕ} (hr : r < n)
    (v : N.TrueSRVertex) : (C.rotate r).HasVertex v ↔ C.HasVertex v := by
  cases v with
  | inl x => exact C.rotate_hasSpecies hr x
  | inr ρ => exact C.rotate_hasReaction hr ρ.1

end TrueSRCycle

/-- A chord glues to the forward arc. -/
theorem gluable_chord_arcFwd {L m : ℕ} (C : N.TrueSRCycle n) (hm : m < n)
    (P : N.TrueSRPath L)
    (hstart : P.startSpecies = C.species ⟨0, by have := C.nontrivial; omega⟩)
    (hend : (P.endReaction).1 = C.reaction ⟨m, hm⟩)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t)) :
    Gluable P (C.arcFwd m hm) where
  same_start := by rw [hstart, C.arcFwd_startSpecies m hm]
  same_end := by
    apply Subtype.ext
    rw [hend, C.arcFwd_endReaction m hm]
  species_disjoint := by
    intro x hP hA
    obtain ⟨p, hp0, hpv⟩ := hP
    obtain ⟨i, _, _, hxi⟩ := C.arcFwd_interiorSpecies m hm hA
    have hpL : p.1 ≠ L := by
      intro h
      have hlast : P.vertex ⟨L, by omega⟩ = Sum.inr P.endReaction := by
        have := P.vertex_last
        rwa [show (Fin.last L) = (⟨L, by omega⟩ : Fin (L + 1)) from Fin.ext rfl] at this
      have hp : p = ⟨L, by omega⟩ := Fin.ext h
      rw [hp, hlast] at hpv
      exact absurd hpv (by simp)
    refine hint p (by simpa using hp0) hpL ?_
    rw [hpv]
    exact ⟨i, hxi.symm⟩
  reaction_disjoint := by
    intro ρ hP hA
    obtain ⟨p, hpL, hpv⟩ := hP
    obtain ⟨i, _, hρi⟩ := C.arcFwd_interiorReaction m hm hA
    have hp0 : p.1 ≠ 0 := by
      intro h
      have hzero : P.vertex ⟨0, by omega⟩ = Sum.inl P.startSpecies := by
        have := P.vertex_zero
        rwa [show (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin (L + 1)) from Fin.ext rfl] at this
      have hp : p = ⟨0, by omega⟩ := Fin.ext h
      rw [hp, hzero] at hpv
      exact absurd hpv (by simp)
    refine hint p hp0 (by simpa using hpL) ?_
    rw [hpv]
    exact ⟨i, hρi.symm⟩
  edge_disjoint := by
    intro p q hsame
    rcases C.arcFwd_edge_on_cycle m hm q with ⟨i, hq⟩ | ⟨i, hq⟩
    · rw [hq] at hsame; exact hedgeL p i hsame
    · rw [hq] at hsame; exact hedgeR p i hsame

/-- A chord glues to the backward arc. -/
theorem gluable_chord_arcBwd {L m : ℕ} (C : N.TrueSRCycle n) (hm : m < n)
    (P : N.TrueSRPath L)
    (hstart : P.startSpecies = C.species ⟨0, by have := C.nontrivial; omega⟩)
    (hend : (P.endReaction).1 = C.reaction ⟨m, hm⟩)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t)) :
    Gluable P (C.arcBwd m hm) where
  same_start := by rw [hstart, C.arcBwd_startSpecies m hm]
  same_end := by
    apply Subtype.ext
    rw [hend, C.arcBwd_endReaction m hm]
  species_disjoint := by
    intro x hP hA
    obtain ⟨p, hp0, hpv⟩ := hP
    obtain ⟨i, _, hxi⟩ := C.arcBwd_interiorSpecies m hm hA
    have hpL : p.1 ≠ L := by
      intro h
      have hlast : P.vertex ⟨L, by omega⟩ = Sum.inr P.endReaction := by
        have := P.vertex_last
        rwa [show (Fin.last L) = (⟨L, by omega⟩ : Fin (L + 1)) from Fin.ext rfl] at this
      have hp : p = ⟨L, by omega⟩ := Fin.ext h
      rw [hp, hlast] at hpv
      exact absurd hpv (by simp)
    refine hint p (by simpa using hp0) hpL ?_
    rw [hpv]
    exact ⟨i, hxi.symm⟩
  reaction_disjoint := by
    intro ρ hP hA
    obtain ⟨p, hpL, hpv⟩ := hP
    obtain ⟨i, _, hρi⟩ := C.arcBwd_interiorReaction m hm hA
    have hp0 : p.1 ≠ 0 := by
      intro h
      have hzero : P.vertex ⟨0, by omega⟩ = Sum.inl P.startSpecies := by
        have := P.vertex_zero
        rwa [show (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin (L + 1)) from Fin.ext rfl] at this
      have hp : p = ⟨0, by omega⟩ := Fin.ext h
      rw [hp, hzero] at hpv
      exact absurd hpv (by simp)
    refine hint p hp0 (by simpa using hpL) ?_
    rw [hpv]
    exact ⟨i, hρi.symm⟩
  edge_disjoint := by
    intro p q hsame
    rcases C.arcBwd_edge_on_cycle m hm q with ⟨i, hq⟩ | ⟨i, hq⟩
    · rw [hq] at hsame; exact hedgeL p i hsame
    · rw [hq] at hsame; exact hedgeR p i hsame


/-- **Banaji--Craciun Lemma 10, for the true-chemistry SR graph.**

An even true-SR cycle admits no species-to-reaction chord: no path from a species vertex of the
cycle to a reaction vertex of the cycle whose interior vertices miss the cycle and none of whose
edges is a cycle edge.

The chord splits the cycle into its two arcs; gluing the chord to each arc gives two cycles
whose c-pair counts, together with the original cycle's, sum to an odd number, so one of the two
is even and shares a whole species-to-reaction arc with the original -- which the second
conjunct of `TrueSRStrongCriterion` forbids.

The hypothesis `hnd` is the degenerate exclusion: a single-edge chord must not land on the
reaction vertex immediately before or after its species vertex, since then one of the two glued
"cycles" would have length one. -/
theorem no_chord_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion) {L m : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even) (hm : m < n) (P : N.TrueSRPath L)
    (hstart : P.startSpecies = C.species ⟨0, by have := C.nontrivial; omega⟩)
    (hend : (P.endReaction).1 = C.reaction ⟨m, hm⟩)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t))
    (hnd : L = 1 → 0 < m ∧ m + 1 < n) :
    False := by
  have hn := C.nontrivial
  have hPF := gluable_chord_arcFwd C hm P hstart hend hint hedgeL hedgeR
  have hPB := gluable_chord_arcBwd C hm P hstart hend hint hedgeL hedgeR
  have hAB := C.gluable_arcs m hm
  obtain ⟨j, hjraw⟩ := P.odd_length
  have hj : L = 2 * j + 1 := by omega
  subst hj
  have hnd' : 2 * j + 1 = 1 → 0 < m ∧ m + 1 < n := hnd
  have h1 : 2 ≤ m + j + 1 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · have := hnd' (by omega); omega
    · omega
  have h2 : 2 ≤ (n - 1 - m) + j + 1 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · have := hnd' (by omega); omega
    · omega
  have h0 : 2 ≤ (n - 1 - m) + m + 1 := by omega
  exact no_edge_disjoint_sToR_chord_of_trueSRCriterion hSR P (C.arcFwd m hm) (C.arcBwd m hm)
    hPF hPB hAB h1 h2 h0 (C.glueCycle_arcs_even m hm h0 hC)



/-- **Lemma 10 in general position.**  The chord may attach at any species vertex `a` and any
reaction vertex `m` of the cycle; rotating the cycle brings `a` to position `0`.

`hnd` is again only the degenerate exclusion for a one-edge chord: measured from `a`, the
reaction vertex `m` must not be the cycle neighbour on either side. -/
theorem no_chord_at_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion) {L : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even) (a m : Fin n) (P : N.TrueSRPath L)
    (hstart : P.startSpecies = C.species a)
    (hend : (P.endReaction).1 = C.reaction m)
    (hint : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L → ¬ C.HasVertex (P.vertex p))
    (hedgeL : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.leftEdge t))
    (hedgeR : ∀ (p : Fin L) (t : Fin n), ¬ (P.edge p).SameIncidence (C.rightEdge t))
    (hnd : L = 1 → 0 < (m.1 + (n - a.1)) % n ∧ (m.1 + (n - a.1)) % n + 1 < n) :
    False := by
  have hn : 0 < n := by have := C.nontrivial; omega
  have hm'lt : (m.1 + (n - a.1)) % n < n := Nat.mod_lt _ hn
  refine no_chord_of_trueSRCriterion hSR (C.rotate a.1)
    (C.rotate_even a.1 hC) hm'lt P ?_ ?_ ?_ ?_ ?_ hnd
  · rw [hstart, C.rotate_species]
    exact (congrArg C.species (Fin.ext (by simp [Nat.mod_eq_of_lt a.isLt]))).symm
  · rw [hend, C.rotate_reaction]
    exact (congrArg C.reaction (Fin.ext (rot_inv hn a.isLt m.isLt))).symm
  · intro p hp0 hpL hv
    exact hint p hp0 hpL ((C.rotate_hasVertex a.isLt (P.vertex p)).mp hv)
  · intro p t hsame
    rw [C.rotate_leftEdge] at hsame
    exact hedgeL p _ hsame
  · intro p t hsame
    rw [C.rotate_rightEdge] at hsame
    exact hedgeR p _ hsame


/-- Both endpoints of a cycle edge are cycle vertices. -/
private theorem hasVertex_of_sameIncidence_left (C : N.TrueSRCycle n) {e : N.TrueSREdge}
    {t : Fin n} (h : e.SameIncidence (C.leftEdge t)) :
    C.HasSpecies e.species ∧ C.HasReaction e.reaction := by
  refine ⟨⟨t, ?_⟩, ⟨t, ?_⟩⟩
  · rw [← C.left_species t]; exact h.1.symm
  · rw [← C.left_reaction t]; exact h.2.1.symm

private theorem hasVertex_of_sameIncidence_right (C : N.TrueSRCycle n) {e : N.TrueSREdge}
    {t : Fin n} (h : e.SameIncidence (C.rightEdge t)) :
    C.HasSpecies e.species ∧ C.HasReaction e.reaction := by
  refine ⟨⟨⟨(t.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩, ?_⟩, ⟨t, ?_⟩⟩
  · rw [← C.right_species t]; exact h.1.symm
  · rw [← C.right_reaction t]; exact h.2.1.symm

/-- If a path's edge lies on the cycle, then both of that edge's endpoint positions carry
cycle vertices. -/
private theorem hasVertex_endpoints_of_cycle_edge {L : ℕ} (C : N.TrueSRCycle n)
    (P : N.TrueSRPath L) (p : Fin L)
    (hsp : C.HasSpecies (P.edge p).species) (hrx : C.HasReaction (P.edge p).reaction) :
    C.HasVertex (P.vertex (Fin.castSucc p)) ∧ C.HasVertex (P.vertex p.succ) := by
  rcases P.connects p with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv]; exact ⟨hsp, hrx⟩
  · rw [hu, hv]; exact ⟨hrx, hsp⟩

/-- **Interior off the cycle is enough.**  A species-to-reaction path of length at least three
whose two endpoints lie on an even cycle and whose interior vertices do not is automatically
edge-disjoint from the cycle, hence a chord -- which the true-SR criterion forbids.

The edge-disjointness is free: an edge lying on the cycle would put cycle vertices at both of
its endpoint positions, and for length at least three at least one of those two positions is
interior. -/
theorem no_offCycle_interior_path_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion) {K : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even) (P : N.TrueSRPath K)
    (hstart : C.HasSpecies P.startSpecies) (hend : C.HasReaction (P.endReaction).1)
    (hint : ∀ p : Fin (K + 1), p.1 ≠ 0 → p.1 ≠ K → ¬ C.HasVertex (P.vertex p))
    (hK : 3 ≤ K) : False := by
  obtain ⟨aIdx, haIdx⟩ := hstart
  obtain ⟨mIdx, hmIdx⟩ := hend
  have hedge : ∀ (p : Fin K),
      C.HasSpecies (P.edge p).species → C.HasReaction (P.edge p).reaction → False := by
    intro p hsp hrx
    have hp := p.isLt
    obtain ⟨hu, hv⟩ := hasVertex_endpoints_of_cycle_edge C P p hsp hrx
    rcases Nat.eq_zero_or_pos p.1 with hp0 | hppos
    · exact hint p.succ (by show p.1 + 1 ≠ 0; omega) (by show p.1 + 1 ≠ K; omega) hv
    · exact hint (Fin.castSucc p) (by show p.1 ≠ 0; omega) (by show p.1 ≠ K; omega) hu
  refine no_chord_at_of_trueSRCriterion hSR C hC aIdx mIdx P haIdx.symm hmIdx.symm hint
    ?_ ?_ (fun h => absurd h (by omega))
  · intro p t hsame
    obtain ⟨hsp, hrx⟩ := hasVertex_of_sameIncidence_left C hsame
    exact hedge p hsp hrx
  · intro p t hsame
    obtain ⟨hsp, hrx⟩ := hasVertex_of_sameIncidence_right C hsame
    exact hedge p hsp hrx

end CRNT.Network
