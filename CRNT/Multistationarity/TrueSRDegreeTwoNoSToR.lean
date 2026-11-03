import CRNT.Multistationarity.TrueSRCPairThirdEdge

/-!
# Degree-two reaction vertices make an S-to-R intersection impossible

An S-to-R intersection requires a component of the common-edge subgraph to *end* at a reaction
vertex.  A reaction vertex on a cycle carries both of that cycle's edges there, so if the vertex
has SR-degree two — no third edge — then any cycle through it uses exactly its two edges, both
cycles through it share both, and the component cannot stop there: it runs through.

This is the formal content of the "degree-two species/reaction obstruction" that appears twice in
the true-SR development:

* it is why `TrueSRStrongCriterion`'s second conjunct holds vacuously for networks all of whose
  reactions touch only two species, which is what `netV` in
  `CRNT/Examples/TrueSRFirstConjunctWitness.lean` needs;
* it is why the second conjunct is vacuous relative to the distinguished causal cycle in the open
  branch of hole 1 (see `HANDOFF_hole1_reaction_start.md`): every shared segment there runs
  through rather than terminating.

The hypothesis is stated relative to `C`: every SR edge at a reaction of `C` is one of `C`'s two
edges there.  That is exactly "the reactions of `C` have SR-degree two", and it is checkable by
finite case analysis for a concrete network.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {m k : ℕ}

/-- `SameIncidence` is transitive: it is a conjunction of equalities. -/
private theorem sameIncidence_trans {e f g : N.TrueSREdge}
    (h1 : e.SameIncidence f) (h2 : f.SameIncidence g) : e.SameIncidence g :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

private theorem sameIncidence_symm {e f : N.TrueSREdge} (h : e.SameIncidence f) :
    f.SameIncidence e := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- The two cycle edges at one index have distinct species. -/
theorem left_right_species_ne (C : N.TrueSRCycle m) (i : Fin m) :
    (C.leftEdge i).species ≠ (C.rightEdge i).species := by
  have hm := C.nontrivial
  rw [C.left_species i, C.right_species i]
  intro h
  -- the type ascription forces `Fin.mk.val` to reduce, so `rw` acts on a plain `ℕ` equation
  -- instead of inside a dependent `Fin.mk` (where the motive is not type correct)
  have hv : i.1 = (i.1 + 1) % m := congrArg Fin.val (C.species_injective h)
  have hi := i.isLt
  rcases Nat.lt_or_ge (i.1 + 1) m with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have he : i.1 + 1 = m := by omega
    rw [he, Nat.mod_self] at hv; omega

/-- Hence they are not the same graph edge. -/
theorem left_not_sameIncidence_right (C : N.TrueSRCycle m) (i : Fin m) :
    ¬ (C.leftEdge i).SameIncidence (C.rightEdge i) := fun h =>
  left_right_species_ne C i h.1

/-- **Degree two at the reactions of `C` forbids an S-to-R intersection with any cycle.** -/
theorem no_sToRIntersection_of_degree_two (C : N.TrueSRCycle m) (D : N.TrueSRCycle k)
    (hdeg : ∀ (e : N.TrueSREdge) (i : Fin m), e.reaction = C.reaction i →
      e.SameIncidence (C.leftEdge i) ∨ e.SameIncidence (C.rightEdge i)) :
    ¬ Nonempty (C.SToRIntersection D) := by
  rintro ⟨T⟩
  obtain ⟨c⟩ : Nonempty (Fin T.componentCount) := ⟨⟨0, T.componentCount_pos⟩⟩
  obtain ⟨ρ, hρ⟩ := T.ends_at_reaction c
  set L := T.componentLength c with hLdef
  have hLpos : 0 < L := T.componentLength_pos c
  -- any edge of the component whose reaction is `ρ` sits at the final position
  have hpos : ∀ j : Fin L, (T.edge c j).reaction = ρ.1 → j.1 = L - 1 := by
    intro j hj
    have hjr : (⟨(T.edge c j).reaction, (T.edge c j).internal⟩ : N.InternalTrueReaction) = ρ :=
      Subtype.ext hj
    rcases T.connects c j with ⟨_, hv⟩ | ⟨hv, _⟩
    · rw [hjr] at hv
      have := T.vertex_simple c (hv.trans hρ.symm)
      have hj1 := congrArg Fin.val this
      have := j.isLt
      simp only [Fin.val_succ, Fin.val_last] at hj1
      omega
    · rw [hjr] at hv
      have := T.vertex_simple c (hv.trans hρ.symm)
      have hj1 := congrArg Fin.val this
      have := j.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hj1
      omega
  -- the last edge has reaction `ρ` and lies on both cycles
  have hlastIdx : (L - 1) < L := by omega
  set e0 := T.edge c ⟨L - 1, hlastIdx⟩ with he0
  have he0r : e0.reaction = ρ.1 := by
    have hsucc : (⟨L - 1, hlastIdx⟩ : Fin L).succ = Fin.last L := Fin.ext (by simp; omega)
    rcases T.connects c ⟨L - 1, hlastIdx⟩ with ⟨_, hv⟩ | ⟨_, hv⟩
    · rw [hsucc, hρ] at hv
      exact (congrArg Subtype.val (Sum.inr.inj hv)).symm
    · -- this orientation puts a species vertex at the final position, contradicting `hρ`
      exfalso
      rw [hsucc, hρ] at hv
      exact Sum.inr_ne_inl hv

  -- `e0` is one of `C`'s two edges at some index `i`, so `ρ = C.reaction i`
  obtain ⟨i, hi⟩ : ∃ i : Fin m, e0.reaction = C.reaction i := by
    rcases T.edge_on_C c ⟨L - 1, hlastIdx⟩ with ⟨i, hsame⟩ | ⟨i, hsame⟩
    · exact ⟨i, by rw [hsame.2.1, C.left_reaction i]⟩
    · exact ⟨i, by rw [hsame.2.1, C.right_reaction i]⟩
  -- `D` also has a reaction vertex there; degree two identifies its two edges with `C`'s
  obtain ⟨j, hj⟩ : ∃ j : Fin k, e0.reaction = D.reaction j := by
    rcases T.edge_on_D c ⟨L - 1, hlastIdx⟩ with ⟨j, hsame⟩ | ⟨j, hsame⟩
    · exact ⟨j, by rw [hsame.2.1, D.left_reaction j]⟩
    · exact ⟨j, by rw [hsame.2.1, D.right_reaction j]⟩
  have hDl : (D.leftEdge j).reaction = C.reaction i := by
    rw [D.left_reaction j, ← hj, hi]
  have hDr : (D.rightEdge j).reaction = C.reaction i := by
    rw [D.right_reaction j, ← hj, hi]
  -- both of `C`'s edges at `i` are common to `C` and `D`
  have hCl_onD : D.ContainsEdge (C.leftEdge i) := by
    rcases hdeg (D.leftEdge j) i hDl with h | h
    · exact Or.inl ⟨j, sameIncidence_symm h⟩
    · rcases hdeg (D.rightEdge j) i hDr with h' | h'
      · exact Or.inr ⟨j, sameIncidence_symm h'⟩
      · exact absurd (sameIncidence_trans h (sameIncidence_symm h'))
          (left_not_sameIncidence_right D j)
  have hCr_onD : D.ContainsEdge (C.rightEdge i) := by
    rcases hdeg (D.leftEdge j) i hDl with h | h
    · rcases hdeg (D.rightEdge j) i hDr with h' | h'
      · exact absurd (sameIncidence_trans h (sameIncidence_symm h'))
          (left_not_sameIncidence_right D j)
      · exact Or.inr ⟨j, sameIncidence_symm h'⟩
    · exact Or.inl ⟨j, sameIncidence_symm h⟩
  -- both are covered by the listed components, and both must land on `e0`
  have hcover : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      f.reaction = ρ.1 → f.SameIncidence e0 := by
    intro f hfC hfD hfr
    obtain ⟨c', j', hsame⟩ := T.covers_common f hfC hfD
    have hc' : c' = c := by
      by_contra hne
      refine T.components_separated hne j' ⟨L - 1, hlastIdx⟩ ?_
      exact Or.inr (by rw [← hsame.2.1, hfr, ← he0r])
    -- `subst` eliminates `c` in favour of `c'`, so everything below names `c'`
    subst hc'
    have hj'r : (T.edge c' j').reaction = ρ.1 := by rw [← hsame.2.1, hfr]
    have := hpos j' hj'r
    have hj'eq : j' = (⟨L - 1, hlastIdx⟩ : Fin L) := Fin.ext this
    rw [hj'eq] at hsame
    exact hsame
  have h1 : (C.leftEdge i).SameIncidence e0 :=
    hcover _ (Or.inl ⟨i, ⟨rfl, rfl, rfl⟩⟩) hCl_onD (by rw [C.left_reaction i, ← hi, he0r])
  have h2 : (C.rightEdge i).SameIncidence e0 :=
    hcover _ (Or.inr ⟨i, ⟨rfl, rfl, rfl⟩⟩) hCr_onD (by rw [C.right_reaction i, ← hi, he0r])
  exact left_not_sameIncidence_right C i (sameIncidence_trans h1 (sameIncidence_symm h2))

end CRNT.Network
