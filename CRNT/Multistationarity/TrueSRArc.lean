import CRNT.Multistationarity.TrueSRPath

/-!
# Arcs of a cycle are species-to-reaction paths

Both producer lemmas for `hSR.2` splice an arc of a cycle with a chord:

* Banaji--Craciun (arXiv:0809.1308, Lemma 10) forms two cycles from a chord plus each of the two
  arcs of a cycle between the chord's endpoints;
* Shinar--Feinberg (arXiv:1203.6560, Lemmas A.4/A.5) work with three edge-disjoint paths between
  two vertices.

This file supplies the arc half: read off from position `0`, an arc of a `TrueSRCycle` is a
`TrueSRPath`.  Starting at `0` avoids modular arithmetic — `right_species` is phrased with an
explicit `% n`, and for `t < k < n` the successor does not wrap.  A general starting position
follows by rotating the cycle, not done here.

The arc through species `x₀ … x_k` and reactions `ρ₀ … ρ_k` has `2k+1` edges, odd as
`TrueSRPath.odd_length` requires.

Representation note: `edge` and `vertex` are defined by a parity test, but every proof goes
through the four `rfl`-level accessor lemmas below rather than unfolding the `ite` inline.  An
earlier attempt that mixed `simp only` with `rw [if_pos]` inside the field proofs did not
compile.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- Internality of a cycle's reaction vertex, transported from its left edge. -/
theorem reaction_internal (C : N.TrueSRCycle n) (i : Fin n) :
    (C.reaction i).Internal N := by
  have h := (C.leftEdge i).internal
  rwa [C.left_reaction i] at h

section Arc

variable (C : N.TrueSRCycle n) (k : ℕ) (hk : k < n)

private theorem arcIdx' {k n : ℕ} (hk : k < n) {m : ℕ} (hm : m < 2 * k + 2) :
    m / 2 < n := by omega

/-- Edges of the arc: left edge at even positions, right edge at odd ones. -/
private noncomputable def arcEdge (q : Fin (2 * k + 1)) : N.TrueSREdge :=
  if q.1 % 2 = 0 then C.leftEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩
  else C.rightEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩

/-- Vertices of the arc: species at even positions, reactions at odd ones. -/
private noncomputable def arcVertex (p : Fin (2 * k + 2)) : N.TrueSRVertex :=
  if p.1 % 2 = 0 then Sum.inl (C.species ⟨p.1 / 2, arcIdx' hk p.isLt⟩)
  else Sum.inr ⟨C.reaction ⟨p.1 / 2, arcIdx' hk p.isLt⟩,
    C.reaction_internal ⟨p.1 / 2, arcIdx' hk p.isLt⟩⟩

private theorem arcEdge_even {q : Fin (2 * k + 1)} (h : q.1 % 2 = 0) :
    arcEdge C k hk q = C.leftEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩ :=
  if_pos h

private theorem arcEdge_odd {q : Fin (2 * k + 1)} (h : q.1 % 2 ≠ 0) :
    arcEdge C k hk q = C.rightEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩ :=
  if_neg h

private theorem arcVertex_even {p : Fin (2 * k + 2)} (h : p.1 % 2 = 0) :
    arcVertex C k hk p = Sum.inl (C.species ⟨p.1 / 2, arcIdx' hk p.isLt⟩) :=
  if_pos h

private theorem arcVertex_odd {p : Fin (2 * k + 2)} (h : p.1 % 2 ≠ 0) :
    arcVertex C k hk p = Sum.inr ⟨C.reaction ⟨p.1 / 2, arcIdx' hk p.isLt⟩,
      C.reaction_internal ⟨p.1 / 2, arcIdx' hk p.isLt⟩⟩ :=
  if_neg h

/-- **The arc of a cycle from species `x₀` to reaction `ρ_k`, as a path.** -/
noncomputable def initialArcPath : N.TrueSRPath (2 * k + 1) where
  length_pos := by omega
  edge := arcEdge C k hk
  vertex := arcVertex C k hk
  connects := by
    intro q
    have hq := q.isLt
    have hcs : (Fin.castSucc q).1 = q.1 := rfl
    have hsu : (q.succ).1 = q.1 + 1 := rfl
    rcases Nat.even_or_odd q.1 with hev | hod
    · have h0 : q.1 % 2 = 0 := Nat.even_iff.mp hev
      have h1 : (q.1 + 1) % 2 ≠ 0 := by omega
      refine Or.inl ⟨?_, ?_⟩
      · rw [arcVertex_even C k hk (by rw [hcs]; exact h0), arcEdge_even C k hk h0]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (C.left_species _).symm
        exact congrArg C.species (Fin.ext (by show (Fin.castSucc q).1 / 2 = q.1 / 2; rfl))
      · rw [arcVertex_odd C k hk (by rw [hsu]; exact h1), arcEdge_even C k hk h0]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (C.left_reaction _).symm
        exact congrArg C.reaction (Fin.ext (by show (q.succ).1 / 2 = q.1 / 2; show (q.1 + 1) / 2 = q.1 / 2; omega))
    · have h0 : q.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hod; omega
      have h1 : (q.1 + 1) % 2 = 0 := by have := Nat.odd_iff.mp hod; omega
      refine Or.inr ⟨?_, ?_⟩
      · rw [arcVertex_odd C k hk (by rw [hcs]; exact h0), arcEdge_odd C k hk h0]
        refine congrArg Sum.inr (Subtype.ext ?_)
        refine Eq.trans ?_ (C.right_reaction _).symm
        exact congrArg C.reaction (Fin.ext (by show (Fin.castSucc q).1 / 2 = q.1 / 2; rfl))
      · rw [arcVertex_even C k hk (by rw [hsu]; exact h1), arcEdge_odd C k hk h0]
        refine congrArg Sum.inl ?_
        refine Eq.trans ?_ (C.right_species _).symm
        have hodd := Nat.odd_iff.mp hod
        have hlt : q.1 / 2 + 1 < n := by omega
        refine congrArg C.species (Fin.ext ?_)
        show (q.succ).1 / 2 = (q.1 / 2 + 1) % n
        show (q.1 + 1) / 2 = (q.1 / 2 + 1) % n
        rw [Nat.mod_eq_of_lt hlt]
        omega
  edge_simple := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    obtain ⟨hsp, hrx, -⟩ := hij
    rcases Nat.even_or_odd i.1 with hei | hoi <;> rcases Nat.even_or_odd j.1 with hej | hoj
    · have h1 : i.1 % 2 = 0 := Nat.even_iff.mp hei
      have h2 : j.1 % 2 = 0 := Nat.even_iff.mp hej
      rw [arcEdge_even C k hk h1, arcEdge_even C k hk h2, C.left_species,
        C.left_species] at hsp
      have hv := congrArg Fin.val (C.species_injective hsp)
      apply Fin.ext
      simp only at hv
      omega
    · have h1 : i.1 % 2 = 0 := Nat.even_iff.mp hei
      have h2 : j.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoj; omega
      rw [arcEdge_even C k hk h1, arcEdge_odd C k hk h2, C.left_reaction,
        C.right_reaction] at hrx
      rw [arcEdge_even C k hk h1, arcEdge_odd C k hk h2, C.left_species,
        C.right_species] at hsp
      have hv := congrArg Fin.val (C.reaction_injective hrx)
      have hv2 := congrArg Fin.val (C.species_injective hsp)
      simp only at hv hv2
      have hlt : j.1 / 2 + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hv2
      exfalso
      omega
    · have h1 : i.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoi; omega
      have h2 : j.1 % 2 = 0 := Nat.even_iff.mp hej
      rw [arcEdge_odd C k hk h1, arcEdge_even C k hk h2, C.right_reaction,
        C.left_reaction] at hrx
      rw [arcEdge_odd C k hk h1, arcEdge_even C k hk h2, C.right_species,
        C.left_species] at hsp
      have hv := congrArg Fin.val (C.reaction_injective hrx)
      have hv2 := congrArg Fin.val (C.species_injective hsp)
      simp only at hv hv2
      have hlt : i.1 / 2 + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hlt] at hv2
      exfalso
      omega
    · have h1 : i.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoi; omega
      have h2 : j.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoj; omega
      rw [arcEdge_odd C k hk h1, arcEdge_odd C k hk h2, C.right_reaction,
        C.right_reaction] at hrx
      have hv := congrArg Fin.val (C.reaction_injective hrx)
      apply Fin.ext
      simp only at hv
      omega
  vertex_simple := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    rcases Nat.even_or_odd a.1 with hea | hoa <;> rcases Nat.even_or_odd b.1 with heb | hob
    · have h1 : a.1 % 2 = 0 := Nat.even_iff.mp hea
      have h2 : b.1 % 2 = 0 := Nat.even_iff.mp heb
      rw [arcVertex_even C k hk h1, arcVertex_even C k hk h2] at hab
      have hv := congrArg Fin.val (C.species_injective (Sum.inl.inj hab))
      apply Fin.ext
      simp only at hv
      omega
    · have h1 : a.1 % 2 = 0 := Nat.even_iff.mp hea
      have h2 : b.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hob; omega
      rw [arcVertex_even C k hk h1, arcVertex_odd C k hk h2] at hab
      exact absurd hab (by simp)
    · have h1 : a.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoa; omega
      have h2 : b.1 % 2 = 0 := Nat.even_iff.mp heb
      rw [arcVertex_odd C k hk h1, arcVertex_even C k hk h2] at hab
      exact absurd hab (by simp)
    · have h1 : a.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hoa; omega
      have h2 : b.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp hob; omega
      rw [arcVertex_odd C k hk h1, arcVertex_odd C k hk h2] at hab
      have hv := congrArg Fin.val
        (C.reaction_injective (Subtype.ext_iff.mp (Sum.inr.inj hab)))
      apply Fin.ext
      simp only at hv
      omega
  starts_at_species := by
    refine ⟨C.species ⟨0, by omega⟩, ?_⟩
    have h0 : ((0 : Fin (2 * k + 2))).1 % 2 = 0 := by simp
    rw [arcVertex_even C k hk h0]
    refine congrArg Sum.inl ?_
    congr 1
    apply Fin.ext
    simp
  ends_at_reaction := by
    refine ⟨⟨C.reaction ⟨k, hk⟩, C.reaction_internal ⟨k, hk⟩⟩, ?_⟩
    have hl : (Fin.last (2 * k + 1)).1 = 2 * k + 1 := rfl
    have h1 : (Fin.last (2 * k + 1)).1 % 2 ≠ 0 := by rw [hl]; omega
    rw [arcVertex_odd C k hk h1]
    refine congrArg Sum.inr (Subtype.ext ?_)
    refine congrArg C.reaction (Fin.ext ?_)
    show (Fin.last (2 * k + 1)).1 / 2 = k
    rw [hl]
    omega

/-- An even-position vertex of the initial arc is the cycle's species at half the position. -/
theorem initialArcPath_vertex_even (p : Fin (2 * k + 2)) (h : p.1 % 2 = 0) :
    (C.initialArcPath k hk).vertex p = Sum.inl (C.species ⟨p.1 / 2, by omega⟩) :=
  arcVertex_even C k hk h

/-- An odd-position vertex of the initial arc is the cycle's reaction at half the position. -/
theorem initialArcPath_vertex_odd (p : Fin (2 * k + 2)) (h : p.1 % 2 ≠ 0) :
    (C.initialArcPath k hk).vertex p =
      Sum.inr ⟨C.reaction ⟨p.1 / 2, by omega⟩,
        C.reaction_internal ⟨p.1 / 2, by omega⟩⟩ :=
  arcVertex_odd C k hk h

/-- An even-position edge of the initial arc is the cycle's left edge. -/
theorem initialArcPath_edge_even (q : Fin (2 * k + 1)) (h : q.1 % 2 = 0) :
    (C.initialArcPath k hk).edge q =
      C.leftEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩ :=
  arcEdge_even C k hk h

/-- An odd-position edge of the initial arc is the cycle's right edge. -/
theorem initialArcPath_edge_odd (q : Fin (2 * k + 1)) (h : q.1 % 2 ≠ 0) :
    (C.initialArcPath k hk).edge q =
      C.rightEdge ⟨q.1 / 2, arcIdx' hk (by have := q.isLt; omega)⟩ :=
  arcEdge_odd C k hk h

end Arc

end CRNT.Network.TrueSRCycle
