import CRNT.Multistationarity.TrueSRChordParity
import CRNT.Multistationarity.TrueSRMinimalChord
import CRNT.Multistationarity.TrueSREdgePath
import CRNT.Multistationarity.TrueSRGlueCPairs
import CRNT.Multistationarity.TrueSRWalkEdges
import CRNT.Multistationarity.TrueSRCycleReverse

namespace CRNT.Network

open TrueSRPath TrueSREdge

theorem no_arc_chord_of_trueSRCriterion
    {S : Type} [DecidableEq S] [Fintype S] {N : Network S}
    (hSR : N.TrueSRStrongCriterion) {k L : ℕ}
    (C : N.TrueSRCycle (k + 2)) (hC : C.Even)
    (P : N.TrueSRPath L)
    (hchord : C.IsChord P)
    (hclean : ∀ p : Fin (L + 1), p.1 ≠ 0 → p.1 ≠ L →
      ¬ C.HasVertex (P.vertex p))
    (hstart : P.startSpecies = C.species ⟨0, by omega⟩)
    (hend : P.endReaction.1 = C.reaction (Fin.last (k + 1)))
    (hpathLarge : 2 ≤ L) : False := by
  classical
  obtain ⟨ell, hodd⟩ := P.odd_length
  have hell : 1 ≤ ell := by rw [hodd] at hpathLarge; omega
  subst L
  let j : ℕ := k + 1
  have hj : j < k + 2 := by dsimp [j]; omega
  let last : Fin (k + 2) := Fin.last (k + 1)
  let Q₁ : N.TrueSRPath (2 * j + 1) := C.initialArcPath j hj
  let Q₂ : N.TrueSRPath 1 := (C.rightEdge last).toPath
  have hidxZero :
      (⟨(last.1 + 1) % (k + 2), Nat.mod_lt _ (by omega)⟩ : Fin (k + 2)) =
        ⟨0, by omega⟩ := by
    apply Fin.ext
    simp [last]
  have hQ₁start : Q₁.startSpecies = C.species ⟨0, by omega⟩ := by
    simpa [Q₁] using C.initialArcPath_startSpecies j hj
  have hjlast : (⟨j, hj⟩ : Fin (k + 2)) = last := by
    apply Fin.ext
    rfl
  have hQ₁end : Q₁.endReaction =
      ⟨C.reaction last, C.reaction_internal last⟩ := by
    change (C.initialArcPath j hj).endReaction = _
    rw [C.initialArcPath_endReaction j hj, hjlast]
  have hQ₂start : Q₂.startSpecies = C.species ⟨0, by omega⟩ := by
    change (C.rightEdge last).toPath.startSpecies = _
    rw [TrueSREdge.toPath_startSpecies]
    change (C.rightEdge last).species = C.species ⟨0, by omega⟩
    rw [C.right_species last, hidxZero]
  have hQ₂end : Q₂.endReaction =
      ⟨C.reaction last, C.reaction_internal last⟩ := by
    change (C.rightEdge last).toPath.endReaction = _
    rw [TrueSREdge.toPath_endReaction]
    exact Subtype.ext (C.right_reaction last)
  have hQ₁Q₂ : Gluable Q₁ Q₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hQ₁start, hQ₂start]
    · rw [hQ₁end, hQ₂end]
    · intro s h₁ h₂
      exact (TrueSREdge.toPath_no_interior_species (C.rightEdge last) s) h₂
    · intro ρ h₁ h₂
      exact (TrueSREdge.toPath_no_interior_reaction (C.rightEdge last) ρ) h₂
    · intro a b hab
      have hb : b = 0 := Fin.ext (by have := b.isLt; omega)
      subst b
      by_cases he : a.1 % 2 = 0
      · let idx : Fin (k + 2) := ⟨a.1 / 2, by have := a.isLt; omega⟩
        have hArc : Q₁.edge a = C.leftEdge idx := by
          simpa [Q₁, idx] using C.initialArcPath_edge_even j hj a he
        have hsame : (C.leftEdge idx).SameIncidence (C.rightEdge last) := by
          rw [hArc] at hab
          change (C.leftEdge idx).SameIncidence (C.rightEdge last) at hab
          exact hab
        have hr : C.reaction idx = C.reaction last := by
          calc
            C.reaction idx = (C.leftEdge idx).reaction := (C.left_reaction idx).symm
            _ = (C.rightEdge last).reaction := hsame.2.1
            _ = C.reaction last := C.right_reaction last
        have hidx : idx = last := C.reaction_injective hr
        have hs : C.species idx = C.species ⟨0, by omega⟩ := by
          have hs := hsame.1
          rw [C.left_species, C.right_species last, hidxZero] at hs
          exact hs
        have hz : idx = ⟨0, by omega⟩ := C.species_injective hs
        have hbad := congrArg Fin.val (hidx.symm.trans hz)
        simp [last] at hbad
      · let idx : Fin (k + 2) := ⟨a.1 / 2, by have := a.isLt; omega⟩
        have hArc : Q₁.edge a = C.rightEdge idx := by
          simpa [Q₁, idx] using C.initialArcPath_edge_odd j hj a he
        have hsame : (C.rightEdge idx).SameIncidence (C.rightEdge last) := by
          rw [hArc] at hab
          change (C.rightEdge idx).SameIncidence (C.rightEdge last) at hab
          exact hab
        have hr : C.reaction idx = C.reaction last := by
          calc
            C.reaction idx = (C.rightEdge idx).reaction := (C.right_reaction idx).symm
            _ = (C.rightEdge last).reaction := hsame.2.1
            _ = C.reaction last := C.right_reaction last
        have hidx : idx = last := C.reaction_injective hr
        have hsmall : idx.1 < k + 1 := by
          have ha := a.isLt
          have ho : a.1 % 2 = 1 := by omega
          dsimp [idx]
          omega
        have hval := congrArg Fin.val hidx
        simp [last] at hval
        omega
  have hQ₁OnCycle : ∀ p : Fin (2 * j + 2), C.HasVertex (Q₁.vertex p) := by
    intro p
    rcases Nat.even_or_odd p.1 with he | ho
    · have he' : p.1 % 2 = 0 := Nat.even_iff.mp he
      have hvertex : Q₁.vertex p = Sum.inl (C.species ⟨p.1 / 2,
          by have := p.isLt; dsimp [j]; omega⟩) := by
        simpa [Q₁] using C.initialArcPath_vertex_even j hj p he'
      rw [hvertex]
      change C.HasSpecies (C.species ⟨p.1 / 2, by have := p.isLt; dsimp [j]; omega⟩)
      exact ⟨⟨p.1 / 2, by have := p.isLt; dsimp [j]; omega⟩, rfl⟩
    · have ho' : p.1 % 2 ≠ 0 := by have := Nat.odd_iff.mp ho; omega
      have hvertex : Q₁.vertex p = Sum.inr ⟨C.reaction ⟨p.1 / 2,
          by have := p.isLt; dsimp [j]; omega⟩,
          C.reaction_internal ⟨p.1 / 2, by have := p.isLt; dsimp [j]; omega⟩⟩ := by
        simpa [Q₁] using C.initialArcPath_vertex_odd j hj p ho'
      rw [hvertex]
      change C.HasReaction (C.reaction ⟨p.1 / 2, by have := p.isLt; dsimp [j]; omega⟩)
      exact ⟨⟨p.1 / 2, by have := p.isLt; dsimp [j]; omega⟩, rfl⟩
  have hPQ₁ : Gluable P Q₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hstart, hQ₁start]
    · apply Subtype.ext
      calc
        P.endReaction.1 = C.reaction last := hend
        _ = Q₁.endReaction.1 := by rw [hQ₁end]
    · intro s hP hQ
      obtain ⟨p, hp0, hp⟩ := hP
      obtain ⟨q, hq0, hq⟩ := hQ
      have hpL : p.1 ≠ 2 * ell + 1 := by
        intro heq
        have hqv := P.vertex_last
        have hpeq : p = Fin.last (2 * ell + 1) := Fin.ext heq
        rw [hpeq, hqv] at hp
        simp at hp
      have heq : P.vertex p = Q₁.vertex q := by rw [hp, hq]
      have hCq := hQ₁OnCycle q
      rw [← heq] at hCq
      exact hclean p hp0 hpL hCq
    · intro ρ hP hQ
      obtain ⟨p, hpL, hp⟩ := hP
      obtain ⟨q, hq0, hq⟩ := hQ
      have hp0 : p.1 ≠ 0 := by
        intro heq
        have hqv := P.vertex_zero
        have hpeq : p = 0 := Fin.ext heq
        rw [hpeq, hqv] at hp
        simp at hp
      have heq : P.vertex p = Q₁.vertex q := by rw [hp, hq]
      have hCq := hQ₁OnCycle q
      rw [← heq] at hCq
      exact hclean p hp0 hpL hCq
    · intro a b hab
      by_cases he : b.1 % 2 = 0
      · let idx : Fin (k + 2) := ⟨b.1 / 2, by have := b.isLt; dsimp [j]; omega⟩
        have hb : Q₁.edge b = C.leftEdge idx := by
          simpa [Q₁, idx] using C.initialArcPath_edge_even j hj b he
        rw [hb] at hab
        exact hchord.2.2.1 a idx hab
      · let idx : Fin (k + 2) := ⟨b.1 / 2, by have := b.isLt; dsimp [j]; omega⟩
        have hb : Q₁.edge b = C.rightEdge idx := by
          simpa [Q₁, idx] using C.initialArcPath_edge_odd j hj b he
        rw [hb] at hab
        exact hchord.2.2.2 a idx hab
  have hPQ₂ : Gluable P Q₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hstart, hQ₂start]
    · apply Subtype.ext
      calc
        P.endReaction.1 = C.reaction last := hend
        _ = Q₂.endReaction.1 := by rw [hQ₂end]
    · intro s hP hQ
      exact (TrueSREdge.toPath_no_interior_species (C.rightEdge last) s) hQ
    · intro ρ hP hQ
      exact (TrueSREdge.toPath_no_interior_reaction (C.rightEdge last) ρ) hQ
    · intro a b hab
      have hb : b = 0 := Fin.ext (by have := b.isLt; omega)
      subst b
      have hsame : (P.edge a).SameIncidence (C.rightEdge last) := by
        change (P.edge a).SameIncidence ((C.rightEdge last).toPath.edge 0) at hab
        simpa using hab
      exact hchord.2.2.2 a last hsame
  let G := TrueSRPath.glueCycle (i := j) (j := 0) Q₂ Q₁ hQ₁Q₂.symm
    (by dsimp [j]; omega)
  have hGleft : ∀ t : Fin (k + 2), G.leftEdge t = C.reverse.leftEdge t := by
    intro t
    dsimp [G]
    rw [glueCycle_leftEdge]
    by_cases ht : t.1 = 0
    · have ht0 : t = 0 := Fin.ext ht
      subst t
      rw [glueEdge_left (i := j) (j := 0) (P := Q₂) (Q := Q₁) (by simp [evenPos])]
      change (C.rightEdge last).toPath.edge 0 = C.reverse.leftEdge 0
      rw [TrueSREdge.toPath_edge, TrueSRCycle.reverse_leftEdge]
      have hrev : (TrueSRCycle.revPerm (k + 2) (0 : Fin (k + 2))) = last := by
        apply Fin.ext
        simp [last]
      rw [hrev]
    · have htpos : 0 < t.1 := Nat.pos_of_ne_zero ht
      have hnotle : ¬ (evenPos t).1 ≤ 0 := by
        rw [evenPos_val]
        omega
      rw [glueEdge_right (i := j) (j := 0) (P := Q₂) (Q := Q₁) hnotle]
      let q : Fin (2 * j + 1) := ⟨2 * (j - t.1) + 1, by have := t.isLt; dsimp [j]; omega⟩
      have hqOdd : q.1 % 2 ≠ 0 := by simp [q]
      have hq : Q₁.edge q = C.rightEdge ⟨j - t.1, by have := t.isLt; dsimp [j]; omega⟩ := by
        change (C.initialArcPath j hj).edge q = _
        rw [C.initialArcPath_edge_odd j hj q hqOdd]
        congr 1
        apply Fin.ext
        dsimp [q]
        omega
      have hqidx :
          (⟨2 * j + 1 - (evenPos t).1, by have := t.isLt; rw [evenPos_val]; dsimp [j]; omega⟩ :
            Fin (2 * j + 1)) = q := by
        apply Fin.ext
        change 2 * j + 1 - 2 * t.1 = 2 * (j - t.1) + 1
        omega
      change Q₁.edge ⟨2 * j + 1 - (evenPos t).1, by have := t.isLt; rw [evenPos_val]; dsimp [j]; omega⟩ = _
      rw [hqidx, hq]
      have hidx : (⟨j - t.1, by have := t.isLt; dsimp [j]; omega⟩ : Fin (k + 2)) =
          TrueSRCycle.revPerm (k + 2) t := by
        apply Fin.ext
        simp [TrueSRCycle.revPerm, j]
      rw [hidx]
  have hGright : ∀ t : Fin (k + 2), G.rightEdge t = C.reverse.rightEdge t := by
    intro t
    dsimp [G]
    rw [glueCycle_rightEdge]
    have hm := walkSucc_evenPos_val t
    have hnotle : ¬ (walkSucc (evenPos t)).1 ≤ 0 := by
      rw [hm]
      omega
    rw [glueEdge_right (i := j) (j := 0) (P := Q₂) (Q := Q₁) hnotle]
    let q : Fin (2 * j + 1) := ⟨2 * (j - t.1), by have := t.isLt; dsimp [j]; omega⟩
    have hqEven : q.1 % 2 = 0 := by simp [q]
    have hq : Q₁.edge q = C.leftEdge ⟨j - t.1, by have := t.isLt; dsimp [j]; omega⟩ := by
      change (C.initialArcPath j hj).edge q = _
      rw [C.initialArcPath_edge_even j hj q hqEven]
      congr 1
      apply Fin.ext
      dsimp [q]
      omega
    have hqidx :
        (⟨2 * j + 1 - (walkSucc (evenPos t)).1,
          by have := t.isLt; rw [hm]; dsimp [j]; omega⟩ : Fin (2 * j + 1)) = q := by
      apply Fin.ext
      change 2 * j + 1 - (walkSucc (evenPos t)).1 = 2 * (j - t.1)
      calc
        2 * j + 1 - (walkSucc (evenPos t)).1 = 2 * j + 1 - (2 * t.1 + 1) := by rw [hm]
        _ = 2 * (j - t.1) := by omega
    change Q₁.edge ⟨2 * j + 1 - (walkSucc (evenPos t)).1,
      by have := t.isLt; rw [hm]; dsimp [j]; omega⟩ = _
    rw [hqidx, hq]
    have hidx : (⟨j - t.1, by have := t.isLt; dsimp [j]; omega⟩ : Fin (k + 2)) =
        TrueSRCycle.revPerm (k + 2) t := by
      apply Fin.ext
      simp [TrueSRCycle.revPerm, j]
    rw [hidx]
  have hpair (t : Fin (k + 2)) : G.isCPair t ↔ C.reverse.isCPair t := by
    unfold TrueSRCycle.isCPair
    rw [hGleft t, hGright t]
  have hset : (Finset.univ.filter G.isCPair) = Finset.univ.filter C.reverse.isCPair := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpair t
  have hnum : G.numCPairs = C.reverse.numCPairs := by
    unfold TrueSRCycle.numCPairs
    rw [hset]
  have hGEven : G.Even := by
    unfold TrueSRCycle.Even at hC ⊢
    rw [hnum, TrueSRCycle.reverse_numCPairs]
    exact hC
  exact no_edge_disjoint_sToR_chord_of_trueSRCriterion (i := 0) (j := ell) (k := j)
    hSR P Q₂ Q₁ hPQ₂ hPQ₁ hQ₁Q₂.symm
    (by omega) (by omega) (by dsimp [j]; omega) (by simpa [G, j] using hGEven)

end CRNT.Network
