import CRNT.Multistationarity.TrueSRParityRR
import CRNT.Multistationarity.TrueSRCycleSplit

/-!
# Reaction-to-reaction arcs of a cycle

`TrueSRSpeciesPath.lean` builds the **species** flavour of a cycle arc: between species vertex
`0` and species vertex `m`, a cycle is two species-to-species paths (`speciesArc`,
`speciesArcBwd`) with those endpoints and disjoint interiors.  The **reaction** flavour has no
builder on `holes`, and `TrueSRPathRR` — the object Shinar--Feinberg's Lemma A.4 three-path
parity argument consumes, and hence the object
`exists_second_evenCycle_of_offCycle_escape` must produce — cannot be built at all without it.

This file supplies that builder.

## The combinatorial content

A `TrueSRCycle n` carries `leftEdge i : S_i — R_i` and `rightEdge i : R_i — S_{i+1 mod n}`, so the
graph is the chain

```
R_0 — S_1 — R_1 — S_2 — R_2 — … — S_m — R_m
```

**Lemma (uniqueness of the forward route).**  From `R_0` there is exactly one simple route to
`R_m` running forward: `rightEdge 0, leftEdge 1, rightEdge 1, …, rightEdge (m-1), leftEdge m`,
of length `2m`.

*Proof.*  `R_0`'s only neighbours are `S_0` (via `leftEdge 0`) and `S_1` (via `rightEdge 0`); a
path using `S_0` runs *backwards*.  On the forward side `S_i`'s only neighbours are `R_{i-1}`
(`rightEdge (i-1)`) and `R_i` (`leftEdge i`), so from `S_i` the route must take `leftEdge i`.
Induction. ∎

**Parity.**  The true-SR graph is bipartite (species against reactions — `TrueSREdge.Connects`
only ever pairs `Sum.inl` with `Sum.inr`), so every reaction-to-reaction path has even length;
`2m` is even.

`TrueSRPathRR j` records a reaction-to-reaction path of `2j+2` edges as a first edge plus a
`TrueSRPath (2j+1)` tail.  Splitting off `rightEdge 0` gives `j = m - 1`:

* `first = rightEdge 0`, joining `R_0` to `S_1`;
* `tail : TrueSRPath (2 * (m - 1) + 1)` running `S_1 — R_1 — S_2 — … — S_m — R_m`.

`m > 0` is required (a zero-length reaction arc would be a bare reaction vertex) and `m < n` keeps
every species and reaction index inside the cycle.

## Implementation note

The tail's index type is `Fin (2 * (m - 1) + 1)`, which Lean does not defeq-reduce to
`Fin (2 * m - 1)`.  The helper definitions are therefore indexed by `ℕ` with an explicit bound,
and the `Fin` index is recovered at each use site by `omega`.  Indexing by `Fin` directly turns
every bound proof into a normalisation fight.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- Every vertex index used by the reaction arc, of the form `p / 2 + 1` with `p < 2 * m`, stays
inside the cycle. -/
private theorem arcIdx {m : ℕ} (hm : m < n) {p : ℕ} (hp : p < 2 * m) : p / 2 + 1 < n := by
  have h1 : p / 2 < m := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  omega

/-- **The species index two steps along an *odd* edge position** is `p / 2 + 2`, and it is still
inside the cycle.  Oddness matters: an odd `p < 2 * m - 1` satisfies `p ≤ 2 * m - 3`, hence
`p / 2 + 2 ≤ m < n`. -/
private theorem arcIdxSucc {m : ℕ} (hm : m < n) {p : ℕ} (hp : p < 2 * m - 1)
    (hod : p % 2 ≠ 0) : p / 2 + 2 < n := by
  rcases Nat.even_or_odd p with heven | hod'
  · exact absurd hod (by rw [Nat.even_iff.mp heven]; simp)
  · obtain ⟨r, hr⟩ := hod'
    rw [hr] at hp ⊢
    have h1 : r ≤ m - 2 := by omega
    omega


/-- Edge at position `q` of the reaction arc's tail: `leftEdge (q / 2 + 1)` when `q` is even and
`rightEdge (q / 2 + 1)` when `q` is odd. -/
private noncomputable def rarcEdge (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (q : ℕ) (hq : q < 2 * m - 1) : N.TrueSREdge :=
  if q % 2 = 0 then C.leftEdge ⟨q / 2 + 1, arcIdx hm (by omega)⟩
  else C.rightEdge ⟨q / 2 + 1, arcIdx hm (by omega)⟩

/-- Vertex at position `p` of the reaction arc's tail: the species `S_{p / 2 + 1}` when `p` is
even and the reaction `R_{p / 2 + 1}` when `p` is odd.  So `p = 0` is `S_1` and `p = 2m - 1` is
`R_m`. -/
private noncomputable def rarcVertex (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (p : ℕ) (hp : p < 2 * m) : N.TrueSRVertex :=
  if p % 2 = 0 then Sum.inl (C.species ⟨p / 2 + 1, arcIdx hm (by omega)⟩)
  else Sum.inr ⟨C.reaction ⟨p / 2 + 1, arcIdx hm (by omega)⟩,
    C.reaction_internal ⟨p / 2 + 1, arcIdx hm (by omega)⟩⟩

@[simp] theorem rarcEdge_even (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (q : ℕ)
    (hq : q < 2 * m - 1) (h : q % 2 = 0) :
    rarcEdge C m hm q hq = C.leftEdge ⟨q / 2 + 1, arcIdx hm (by omega)⟩ := by
  rw [rarcEdge, ite_eq_left h]

@[simp] theorem rarcEdge_odd (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (q : ℕ)
    (hq : q < 2 * m - 1) (h : q % 2 ≠ 0) :
    rarcEdge C m hm q hq = C.rightEdge ⟨q / 2 + 1, arcIdx hm (by omega)⟩ := by
  rw [rarcEdge, ite_eq_right h]

@[simp] theorem rarcVertex_even (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (p : ℕ)
    (hp : p < 2 * m) (h : p % 2 = 0) :
    rarcVertex C m hm p hp = Sum.inl (C.species ⟨p / 2 + 1, arcIdx hm (by omega)⟩) := by
  rw [rarcVertex, ite_eq_left h]

@[simp] theorem rarcVertex_odd (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (p : ℕ)
    (hp : p < 2 * m) (h : p % 2 ≠ 0) :
    rarcVertex C m hm p hp =
      Sum.inr ⟨C.reaction ⟨p / 2 + 1, arcIdx hm (by omega)⟩,
        C.reaction_internal ⟨p / 2 + 1, arcIdx hm (by omega)⟩⟩ := by
  rw [rarcVertex, ite_eq_right h]

/-- **The forward reaction arc of a cycle**, from the reaction vertex `R_0` to the reaction
vertex `R_m`.  This is the reaction-to-reaction counterpart of `speciesArc`: the walk

```
R_0 —rightEdge 0— S_1 —leftEdge 1— R_1 —rightEdge 1— S_2 — … — S_m —leftEdge m— R_m
```

with its first edge `rightEdge 0` split off into `TrueSRPathRR.first` and the remaining
`2 * m - 1` edges forming `TrueSRPathRR.tail`.  The parameter is `j = m - 1`, so the whole arc
has `2 * (m - 1) + 2 = 2 * m` edges: even, as the bipartition of the true-SR graph forces. -/
noncomputable def reactionArc (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    N.TrueSRPathRR (m - 1) where
  first := C.rightEdge ⟨0, by omega⟩
  tail := by
    have hn := C.nontrivial
    refine
      { length_pos := by omega
        edge := fun q => rarcEdge C m hm q.1 (by omega)
        vertex := fun p => rarcVertex C m hm p.1 (by omega)
        connects := by
          intro q
          have hq := q.isLt
          have hcs : (Fin.castSucc q).1 = q.1 := rfl
          have hsu : (q.succ).1 = q.1 + 1 := rfl
          have hqlt : q.1 < 2 * m - 1 := by omega
          have hcast : (Fin.castSucc q).1 < 2 * m := by rw [hcs]; omega
          have hsucc : (q.succ).1 < 2 * m := by rw [hsu]; omega
          by_cases h0 : q.1 % 2 = 0
          · -- `leftEdge (q / 2 + 1)`
            have hsuccOdd : ¬ (q.succ).1 % 2 = 0 := by rw [hsu]; omega
            have hidx : (q.succ).1 / 2 + 1 = q.1 / 2 + 1 := by rw [hsu]; omega
            simp only [rarcEdge_even C m hm q.1 hqlt h0]
            refine Or.inl ⟨?_, ?_⟩
            · simp only [rarcVertex_even C m hm (Fin.castSucc q).1 hcast h0, C.left_species]
              exact congrArg Sum.inl (congrArg C.species (Fin.ext rfl))
            · simp only [rarcVertex_odd C m hm (q.succ).1 hsucc hsuccOdd, hidx, C.left_reaction]
          · -- `rightEdge (q / 2 + 1)`
            have hcastOdd : ¬ (Fin.castSucc q).1 % 2 = 0 := by rw [hcs]; exact h0
            have hidx : (q.succ).1 / 2 + 1 = q.1 / 2 + 2 := by rw [hsu]; omega
            have hlt0 : q.1 / 2 + 2 < n := by omega
            have hlt1 : (q.1 / 2 + 1 + 1) % n = q.1 / 2 + 2 := Nat.mod_eq_of_lt hlt0
            simp only [rarcEdge_odd C m hm q.1 hqlt h0]
            refine Or.inr ⟨?_, ?_⟩
            · simp only [rarcVertex_odd C m hm (Fin.castSucc q).1 hcast hcastOdd,
                C.right_reaction]
              exact congrArg Sum.inr (Subtype.ext rfl)
            · have hsuccEven : (q.succ).1 % 2 = 0 := by rw [hsu]; omega
              simp only [rarcVertex_even C m hm (q.succ).1 hsucc hsuccEven, hidx,
                C.right_species, hlt1]
        edge_simple := by
          intro i j hij
          have hi := i.isLt
          have hj := j.isLt
          have hil : i.1 < 2 * m - 1 := by omega
          have hjl : j.1 < 2 * m - 1 := by omega
          by_cases hpi : i.1 % 2 = 0 <;> by_cases hpj : j.1 % 2 = 0
          · simp only [rarcEdge_even C m hm i.1 hil hpi, rarcEdge_even C m hm j.1 hjl hpj] at hij
            have h := C.sameIncidence_leftEdge_iff _ _ hij
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
          · simp only [rarcEdge_even C m hm i.1 hil hpi, rarcEdge_odd C m hm j.1 hjl hpj] at hij
            exact absurd hij (C.not_sameIncidence_left_right _ _)
          · simp only [rarcEdge_odd C m hm i.1 hil hpi, rarcEdge_even C m hm j.1 hjl hpj] at hij
            exact absurd (TrueSREdge.SameIncidence.symm hij)
              (C.not_sameIncidence_left_right _ _)
          · simp only [rarcEdge_odd C m hm i.1 hil hpi, rarcEdge_odd C m hm j.1 hjl hpj] at hij
            have h := C.sameIncidence_rightEdge_iff _ _ hij
            have hv := congrArg Fin.val h
            exact Fin.ext (by simp only at hv; omega)
        vertex_simple := by
          intro p p' hpp'
          have hp := p.isLt
          have hp' := p'.isLt
          have hpl : p.1 < 2 * m := by omega
          have hp'l : p'.1 < 2 * m := by omega
          by_cases hpi : p.1 % 2 = 0 <;> by_cases hpj : p'.1 % 2 = 0
          · simp only [rarcVertex_even C m hm p.1 hpl hpi,
              rarcVertex_even C m hm p'.1 hp'l hpj] at hpp'
            have h := C.species_injective (Sum.inl.inj hpp')
            exact Fin.ext (by have hv := congrArg Fin.val h; simp only at hv; omega)
          · simp only [rarcVertex_even C m hm p.1 hpl hpi,
              rarcVertex_odd C m hm p'.1 hp'l hpj] at hpp'
            exact absurd hpp' (by simp)
          · simp only [rarcVertex_odd C m hm p.1 hpl hpi,
              rarcVertex_even C m hm p'.1 hp'l hpj] at hpp'
            exact absurd hpp' (by simp)
          · simp only [rarcVertex_odd C m hm p.1 hpl hpi,
              rarcVertex_odd C m hm p'.1 hp'l hpj] at hpp'
            have h := C.reaction_injective (congrArg Subtype.val (Sum.inr.inj hpp'))
            exact Fin.ext (by have hv := congrArg Fin.val h; simp only at hv; omega)
        starts_at_species := by
          have hz : (0 : ℕ) < 2 * m := by omega
          refine ⟨C.species ⟨1, by omega⟩, ?_⟩
          show rarcVertex C m hm 0 _ = Sum.inl (C.species ⟨1, _⟩)
          rw [rarcVertex_even C m hm 0 hz (by simp)]

        ends_at_reaction := by
          refine ⟨⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩, ?_⟩
          have hlast : (Fin.last (2 * (m - 1) + 1)).1 = 2 * (m - 1) + 1 := rfl
          have hz : (Fin.last (2 * (m - 1) + 1)).1 < 2 * m := by omega
          have hodd : ¬ (Fin.last (2 * (m - 1) + 1)).1 % 2 = 0 := by rw [hlast]; omega
          have hidx : ((Fin.last (2 * (m - 1) + 1)).1 / 2 + 1 : ℕ) = m := by rw [hlast]; omega
          show rarcVertex C m hm (Fin.last (2 * (m - 1) + 1)).1 _
            = Sum.inr ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩
          simp only [rarcVertex_odd C m hm (Fin.last (2 * (m - 1) + 1)).1 hz hodd, hidx]
      }
  first_species := by
    have hn := C.nontrivial
    have hz : (0 : ℕ) < 2 * m := by omega
    have hlt : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    simp only [rarcVertex_even C m hm 0 hz (by simp), C.right_species]
    exact congrArg Sum.inl
      (congrArg C.species (Fin.ext (by show (0 + 1) % n = 0 / 2 + 1; omega)))
  first_ne_tail_edge := by
    intro i
    have hi := i.isLt
    have hz : i.1 < 2 * m - 1 := by omega
    have hidx : 0 < i.1 / 2 + 1 := by omega
    by_cases hpi : i.1 % 2 = 0
    · simp only [rarcEdge_even C m hm i.1 hz hpi]
      intro h
      exact C.not_sameIncidence_left_right _ _ h.symm
    · simp only [rarcEdge_odd C m hm i.1 hz hpi]
      intro h
      have hne := C.sameIncidence_rightEdge_iff _ _ h
      have hv := congrArg Fin.val hne
      simp only at hv
      omega
  first_ne_tail_vertex := by
    intro i
    have hi := i.isLt
    by_cases hpi : i.1 % 2 = 0
    · have hz : i.1 < 2 * m := by omega
      simp only [rarcVertex_even C m hm i.1 hz hpi]
      simp
    · have hz : i.1 < 2 * m := by omega
      have hidx : 0 < i.1 / 2 + 1 := by omega
      simp only [rarcVertex_odd C m hm i.1 hz hpi, C.right_reaction]
      intro hcon
      have hval := congrArg Subtype.val (Sum.inr.inj hcon)
      have hne : C.reaction ⟨0, by omega⟩ ≠ C.reaction ⟨i.1 / 2 + 1, by omega⟩ := by
        intro hh
        have hv := congrArg Fin.val (C.reaction_injective hh)
        simp only at hv
        omega
      exact absurd hval hne


/-- **The arc starts at `R_0`.** -/
theorem reactionArc_startReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    ((C.reactionArc m hm hmpos).startReaction : N.InternalTrueReaction).1
      = C.reaction ⟨0, by omega⟩ := by
  show (C.reactionArc m hm hmpos).first.reaction = C.reaction ⟨0, by omega⟩
  exact C.right_reaction ⟨0, by omega⟩

/-- **The arc ends at `R_m`.** -/
theorem reactionArc_endReaction (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n) (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).endReaction
      = ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩ := by
  have hlast := (C.reactionArc m hm hmpos).tail.vertex_last
  have hlz : (Fin.last (2 * (m - 1) + 1)).1 = 2 * (m - 1) + 1 := rfl
  have hz : (Fin.last (2 * (m - 1) + 1)).1 < 2 * m := by omega
  have hodd : ¬ (Fin.last (2 * (m - 1) + 1)).1 % 2 = 0 := by rw [hlz]; omega
  have hidx : ((Fin.last (2 * (m - 1) + 1)).1 / 2 + 1 : ℕ) = m := by rw [hlz]; omega
  have hv : (C.reactionArc m hm hmpos).tail.vertex (Fin.last (2 * (m - 1) + 1))
      = Sum.inr ⟨C.reaction ⟨m, hm⟩, C.reaction_internal ⟨m, hm⟩⟩ := by
    show rarcVertex C m hm (Fin.last (2 * (m - 1) + 1)).1
        (by have := (Fin.last (2 * (m - 1) + 1)).isLt; omega) = _
    simp only [rarcVertex_odd C m hm (Fin.last (2 * (m - 1) + 1)).1 hz hodd, hidx]
  exact Sum.inr.inj (hlast.symm.trans hv)

/-- **The arc's tail starts at `S_1`.** -/
theorem reactionArc_tail_startSpecies (C : N.TrueSRCycle n) (m : ℕ) (hm : m < n)
    (hmpos : 0 < m) :
    (C.reactionArc m hm hmpos).tail.startSpecies = C.species ⟨1, by omega⟩ := by
  have hz : (0 : ℕ) < 2 * m := by omega
  have hv : (C.reactionArc m hm hmpos).tail.vertex 0
      = Sum.inl (C.species ⟨1, by omega⟩) := by
    show rarcVertex C m hm 0 (by omega) = _
    rw [rarcVertex_even C m hm 0 hz (by simp)]

  exact Sum.inl.inj ((C.reactionArc m hm hmpos).tail.vertex_zero.symm.trans hv)

/-- **The arc is even-length, as the bipartition forces**: `2 * (m - 1) + 2 = 2 * m`. -/
theorem reactionArc_length (_C : N.TrueSRCycle n) (m : ℕ) (_hm : m < n) (_hmpos : 0 < m) :
    2 * (m - 1) + 2 = 2 * m := by omega

end CRNT.Network.TrueSRCycle