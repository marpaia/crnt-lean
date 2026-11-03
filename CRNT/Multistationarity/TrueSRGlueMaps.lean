import CRNT.Multistationarity.TrueSRGlueIndex

/-!
# The glue maps

For `P : TrueSRPath (2j+1)` and `Q : TrueSRPath (2i+1)` sharing their endpoints, the glued
closed walk on `n = i+j+1` cycle positions (so `2n = 2i+2j+2` walk positions) is

  `glueVertex m = if m ≤ 2j+1 then P.vertex m else Q.vertex (2i+2j+2 - m)`
  `glueEdge   m = if m ≤ 2j   then P.edge   m else Q.edge   (2i+2j+1 - m)`

Both seams fall out of the same formula: `glueEdge (2j+1) = Q.edge (2i)` joins the halves and
`glueEdge (2n-1) = Q.edge 0` closes the walk.

This file defines the two maps, their branch equations, and the two parity fields of
`TrueSRClosedWalk`.  Dependent `if` is used so each branch's proof obligation has the branch
condition in scope.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}

/-- Vertices of the glued closed walk. -/
noncomputable def glueVertex (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
    (m : Fin (2 * (i + j + 1))) : N.TrueSRVertex :=
  if h : m.1 ≤ 2 * j + 1 then P.vertex ⟨m.1, by omega⟩
  else Q.vertex ⟨2 * i + 2 * j + 2 - m.1, by have := m.isLt; omega⟩

/-- Edges of the glued closed walk. -/
noncomputable def glueEdge (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
    (m : Fin (2 * (i + j + 1))) : N.TrueSREdge :=
  if h : m.1 ≤ 2 * j then P.edge ⟨m.1, by omega⟩
  else Q.edge ⟨2 * i + 2 * j + 1 - m.1, by have := m.isLt; omega⟩

variable (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))

theorem glueVertex_left {m : Fin (2 * (i + j + 1))} (h : m.1 ≤ 2 * j + 1) :
    glueVertex P Q m = P.vertex ⟨m.1, by omega⟩ := dif_pos h

theorem glueVertex_right {m : Fin (2 * (i + j + 1))} (h : ¬ m.1 ≤ 2 * j + 1) :
    glueVertex P Q m = Q.vertex ⟨2 * i + 2 * j + 2 - m.1, by have := m.isLt; omega⟩ :=
  dif_neg h

theorem glueEdge_left {m : Fin (2 * (i + j + 1))} (h : m.1 ≤ 2 * j) :
    glueEdge P Q m = P.edge ⟨m.1, by omega⟩ := dif_pos h

theorem glueEdge_right {m : Fin (2 * (i + j + 1))} (h : ¬ m.1 ≤ 2 * j) :
    glueEdge P Q m = Q.edge ⟨2 * i + 2 * j + 1 - m.1, by have := m.isLt; omega⟩ :=
  dif_neg h

/-- **Even walk positions carry species.** -/
theorem glueVertex_even (m : Fin (2 * (i + j + 1))) (hm : m.1 % 2 = 0) :
    ∃ s : S, glueVertex P Q m = Sum.inl s := by
  have hlt := m.isLt
  by_cases h : m.1 ≤ 2 * j + 1
  · rw [glueVertex_left P Q h]
    exact (P.species_iff_even m.1 (by omega)).mpr (Nat.even_iff.mpr hm)
  · rw [glueVertex_right P Q h]
    refine (Q.species_iff_even (2 * i + 2 * j + 2 - m.1) (by omega)).mpr ?_
    exact Nat.even_iff.mpr (by omega)

/-- **Odd walk positions carry reactions.** -/
theorem glueVertex_odd (m : Fin (2 * (i + j + 1))) (hm : m.1 % 2 ≠ 0) :
    ∃ ρ : N.InternalTrueReaction, glueVertex P Q m = Sum.inr ρ := by
  have hlt := m.isLt
  by_cases h : m.1 ≤ 2 * j + 1
  · rw [glueVertex_left P Q h]
    exact P.exists_reaction_of_odd ⟨m.1, by omega⟩ (by simpa using hm)
  · rw [glueVertex_right P Q h]
    refine Q.exists_reaction_of_odd ⟨2 * i + 2 * j + 2 - m.1, by omega⟩ ?_
    show (2 * i + 2 * j + 2 - m.1) % 2 ≠ 0
    omega

/-! ### Value-indexed branch equations

Stating each branch with the target index given as a *numeral* keeps the `Fin.mk` proof
components out of the rewriting, so the `Connects` facts from `P.connects` / `Q.connects` match
by defeq. -/

theorem glueVertex_left_val {m : Fin (2 * (i + j + 1))} (a : ℕ) (ha : m.1 = a)
    (h : a ≤ 2 * j + 1) (hb : a < 2 * j + 1 + 1) :
    glueVertex P Q m = P.vertex ⟨a, hb⟩ := by
  rw [glueVertex_left P Q (by omega)]
  exact congrArg P.vertex (Fin.ext ha)

theorem glueVertex_right_val {m : Fin (2 * (i + j + 1))} (a : ℕ)
    (h : ¬ m.1 ≤ 2 * j + 1) (ha : 2 * i + 2 * j + 2 - m.1 = a) (hb : a < 2 * i + 1 + 1) :
    glueVertex P Q m = Q.vertex ⟨a, hb⟩ := by
  rw [glueVertex_right P Q h]
  exact congrArg Q.vertex (Fin.ext ha)

theorem glueEdge_left_val {m : Fin (2 * (i + j + 1))} (a : ℕ) (ha : m.1 = a)
    (h : a ≤ 2 * j) (hb : a < 2 * j + 1) :
    glueEdge P Q m = P.edge ⟨a, hb⟩ := by
  rw [glueEdge_left P Q (by omega)]
  exact congrArg P.edge (Fin.ext ha)

theorem glueEdge_right_val {m : Fin (2 * (i + j + 1))} (a : ℕ)
    (h : ¬ m.1 ≤ 2 * j) (ha : 2 * i + 2 * j + 1 - m.1 = a) (hb : a < 2 * i + 1) :
    glueEdge P Q m = Q.edge ⟨a, hb⟩ := by
  rw [glueEdge_right P Q h]
  exact congrArg Q.edge (Fin.ext ha)

/-! ### Endpoint values, bridged without rewriting a `Fin.mk` -/

theorem vertex_at_last {L : ℕ} (R : N.TrueSRPath L) (hb : L < L + 1) :
    R.vertex ⟨L, hb⟩ = Sum.inr R.endReaction :=
  (congrArg R.vertex (Fin.ext (rfl : (L : ℕ) = (Fin.last L).1))).trans R.vertex_last

theorem vertex_at_zero {L : ℕ} (R : N.TrueSRPath L) (hb : 0 < L + 1) :
    R.vertex ⟨0, hb⟩ = Sum.inl R.startSpecies :=
  (congrArg R.vertex (Fin.ext (rfl : (0 : ℕ) = ((0 : Fin (L + 1))).1))).trans R.vertex_zero

/-- **Consecutive glued-walk vertices are joined by the corresponding glue edge.** -/
theorem glueEdge_connects (h : Gluable P Q) (m : Fin (2 * (i + j + 1))) :
    (glueEdge P Q m).Connects (glueVertex P Q m) (glueVertex P Q (walkSucc m)) := by
  have hlt := m.isLt
  have hws : (walkSucc m).1 = (m.1 + 1) % (2 * (i + j + 1)) := rfl
  have hseamE : P.vertex ⟨2 * j + 1, by omega⟩ = Q.vertex ⟨2 * i + 1, by omega⟩ := by
    rw [vertex_at_last P (by omega), vertex_at_last Q (by omega), h.same_end]
  have hseamS : P.vertex ⟨0, by omega⟩ = Q.vertex ⟨0, by omega⟩ := by
    rw [vertex_at_zero P (by omega), vertex_at_zero Q (by omega), h.same_start]
  by_cases hA : m.1 ≤ 2 * j
  · have hsucc : (walkSucc m).1 = m.1 + 1 := by rw [hws, Nat.mod_eq_of_lt (by omega)]
    rw [glueEdge_left_val P Q m.1 rfl hA (by omega),
      glueVertex_left_val P Q m.1 rfl (by omega) (by omega),
      glueVertex_left_val P Q (m.1 + 1) hsucc (by omega) (by omega)]
    exact P.connects ⟨m.1, by omega⟩
  · by_cases hC : m.1 = 2 * (i + j + 1) - 1
    · -- closing seam
      have hsucc : (walkSucc m).1 = 0 := by
        rw [hws, hC]
        have he : 2 * (i + j + 1) - 1 + 1 = 2 * (i + j + 1) := by omega
        rw [he, Nat.mod_self]
      by_cases hL : m.1 ≤ 2 * j + 1
      · -- degenerate `i = 0`: `Q` is a single edge, both seams needed at once
        have hi0 : i = 0 := by omega
        subst hi0
        rw [glueEdge_right_val P Q 0 hA (by omega) (by omega),
          glueVertex_left_val P Q (2 * j + 1) (by omega) (by omega) (by omega),
          glueVertex_left_val P Q 0 hsucc (by omega) (by omega),
          hseamE, hseamS]
        exact (Q.connects ⟨0, by omega⟩).symm
      · rw [glueEdge_right_val P Q 0 hA (by omega) (by omega),
          glueVertex_right_val P Q 1 hL (by omega) (by omega),
          glueVertex_left_val P Q 0 hsucc (by omega) (by omega),
          hseamS]
        exact (Q.connects ⟨0, by omega⟩).symm
    · by_cases hB : m.1 = 2 * j + 1
      · have hsucc : (walkSucc m).1 = 2 * j + 2 := by
          rw [hws, hB, Nat.mod_eq_of_lt (by omega)]
        rw [glueEdge_right_val P Q (2 * i) hA (by omega) (by omega),
          glueVertex_left_val P Q (2 * j + 1) hB (by omega) (by omega),
          glueVertex_right_val P Q (2 * i) (by omega) (by rw [hsucc]; omega) (by omega),
          hseamE]
        exact (Q.connects ⟨2 * i, by omega⟩).symm
      · have hsucc : (walkSucc m).1 = m.1 + 1 := by rw [hws, Nat.mod_eq_of_lt (by omega)]
        rw [glueEdge_right_val P Q (2 * i + 2 * j + 1 - m.1) hA rfl (by omega),
          glueVertex_right_val P Q (2 * i + 2 * j + 1 - m.1 + 1) (by omega) (by omega)
            (by omega),
          glueVertex_right_val P Q (2 * i + 2 * j + 1 - m.1) (by omega)
            (by rw [hsucc]; omega) (by omega)]
        exact (Q.connects ⟨2 * i + 2 * j + 1 - m.1, by omega⟩).symm

/-! ### Injectivity of the glued vertex map -/

/-- The cross-regime case: a `P` vertex and a `Q` vertex at an interior `Q` position cannot
coincide.  No parity analysis is needed — `InteriorSpecies` only asks for a nonzero position. -/
private theorem glue_mixed_absurd (h : Gluable P Q) {a b : ℕ}
    (hab : a < 2 * j + 1 + 1) (hbb : b < 2 * i + 1 + 1) (hb1 : 1 ≤ b) (hb2 : b ≤ 2 * i)
    (heq : P.vertex ⟨a, hab⟩ = Q.vertex ⟨b, hbb⟩) : False := by
  cases hva : P.vertex ⟨a, hab⟩ with
  | inl s =>
    have hqb : Q.vertex ⟨b, hbb⟩ = Sum.inl s := heq.symm.trans hva
    by_cases ha0 : a = 0
    · have hp0 : P.vertex ⟨a, hab⟩ = Sum.inl P.startSpecies := by
        subst ha0; exact vertex_at_zero P hab
      have hs : s = Q.startSpecies := by
        have := hva.symm.trans hp0
        rw [h.same_start] at this
        exact Sum.inl.inj this
      have hq0 : Q.vertex ⟨0, by omega⟩ = Sum.inl Q.startSpecies := vertex_at_zero Q (by omega)
      have : Q.vertex ⟨b, hbb⟩ = Q.vertex ⟨0, by omega⟩ := by rw [hqb, hq0, hs]
      have := congrArg Fin.val (Q.vertex_simple this)
      simp only at this
      omega
    · exact h.species_disjoint s ⟨⟨a, hab⟩, by simpa using ha0, hva⟩
        ⟨⟨b, hbb⟩, by simpa using (by omega : b ≠ 0), hqb⟩
  | inr ρ =>
    have hqb : Q.vertex ⟨b, hbb⟩ = Sum.inr ρ := heq.symm.trans hva
    by_cases haL : a = 2 * j + 1
    · have hpL : P.vertex ⟨a, hab⟩ = Sum.inr P.endReaction := by
        subst haL; exact vertex_at_last P hab
      have hs : ρ = Q.endReaction := by
        have := hva.symm.trans hpL
        rw [h.same_end] at this
        exact Sum.inr.inj this
      have hqL : Q.vertex ⟨2 * i + 1, by omega⟩ = Sum.inr Q.endReaction :=
        vertex_at_last Q (by omega)
      have : Q.vertex ⟨b, hbb⟩ = Q.vertex ⟨2 * i + 1, by omega⟩ := by rw [hqb, hqL, hs]
      have := congrArg Fin.val (Q.vertex_simple this)
      simp only at this
      omega
    · exact h.reaction_disjoint ρ ⟨⟨a, hab⟩, by simpa using haL, hva⟩
        ⟨⟨b, hbb⟩, by simpa using (by omega : b ≠ 2 * i + 1), hqb⟩

/-- **The glued vertex map is injective.** -/
theorem glueVertex_injective (h : Gluable P Q) :
    Function.Injective (glueVertex P Q) := by
  intro m m' heq
  have hm := m.isLt
  have hm' := m'.isLt
  by_cases hL : m.1 ≤ 2 * j + 1 <;> by_cases hL' : m'.1 ≤ 2 * j + 1
  · rw [glueVertex_left P Q hL, glueVertex_left P Q hL'] at heq
    have := congrArg Fin.val (P.vertex_simple heq)
    simp only at this
    exact Fin.ext this
  · rw [glueVertex_left P Q hL, glueVertex_right P Q hL'] at heq
    exact absurd heq (fun hc => glue_mixed_absurd P Q h (by omega) (by omega)
      (by omega) (by omega) hc)
  · rw [glueVertex_right P Q hL, glueVertex_left P Q hL'] at heq
    exact absurd heq.symm (fun hc => glue_mixed_absurd P Q h (by omega) (by omega)
      (by omega) (by omega) hc)
  · rw [glueVertex_right P Q hL, glueVertex_right P Q hL'] at heq
    have := congrArg Fin.val (Q.vertex_simple heq)
    simp only at this
    exact Fin.ext (by omega)

/-! ### Assembly -/

/-- **Two gluable paths form a closed alternating walk.** -/
noncomputable def glueWalk (h : Gluable P Q) (hn : 2 ≤ i + j + 1) :
    N.TrueSRClosedWalk (i + j + 1) where
  nontrivial := hn
  vertex := glueVertex P Q
  edge := glueEdge P Q
  connects := glueEdge_connects P Q h
  vertex_simple := glueVertex_injective P Q h
  even_species := glueVertex_even P Q
  odd_reaction := glueVertex_odd P Q

/-- **Two gluable species-to-reaction paths form a true-SR cycle.**  This is the construction
Banaji--Craciun's Lemma 10 needs: a chord glued to each arc of a cycle. -/
noncomputable def glueCycle (h : Gluable P Q) (hn : 2 ≤ i + j + 1) :
    N.TrueSRCycle (i + j + 1) :=
  (glueWalk P Q h hn).toCycle

end CRNT.Network.TrueSRPath
