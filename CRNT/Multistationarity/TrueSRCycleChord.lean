import Mathlib.Logic.Equiv.Fin.Rotate
import CRNT.Multistationarity.TrueSRRotate
import CRNT.Multistationarity.TrueSRSingleSharedEdge

/-!
# Closing an arc of a simple true-SR cycle with a chord

Given a cycle, an edge from its initial species to a reaction vertex later on the cycle closes
the initial arc into another simple cycle.  This is the elementary cycle construction needed by
the chord arguments that use the no-S-to-R-intersection hypothesis.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

private def prefixIndex (n k : ℕ) (hk : k < n) (i : Fin (k + 1)) : Fin n :=
  ⟨i.1, by have := i.isLt; omega⟩

/-- Close the arc from `species 0` through `reaction k` with an extra edge back to `species 0`.
The condition `0 < k` ensures the resulting cycle is nontrivial. -/
noncomputable def closeInitialArcWithChord (C : N.TrueSRCycle n) (k : ℕ) (hk : k < n)
    (hkpos : 0 < k) (e : N.TrueSREdge)
    (hes : e.species = C.species (⟨0, by omega⟩ : Fin n))
    (her : e.reaction = C.reaction ⟨k, hk⟩) : N.TrueSRCycle (k + 1) := by
  let idx := prefixIndex n k hk
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (k + 1) := ⟨by omega⟩
  exact {
    nontrivial := by omega
    species := fun i => C.species (idx i)
    reaction := fun i => C.reaction (idx i)
    leftEdge := fun i => C.leftEdge (idx i)
    rightEdge := fun i => if i.1 < k then C.rightEdge (idx i) else e
    left_species := by
      intro i
      exact C.left_species (idx i)
    left_reaction := by
      intro i
      exact C.left_reaction (idx i)
    right_species := by
      intro i
      change (if i.1 < k then C.rightEdge (idx i) else e).species =
        C.species (idx ⟨(i.1 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩)
      by_cases hi : i.1 < k
      · have inext : i.1 + 1 < k + 1 := by omega
        have hmodSmall : (i.1 + 1) % (k + 1) = i.1 + 1 :=
          Nat.mod_eq_of_lt inext
        have hidxSmall :
            (⟨(i.1 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
              ⟨i.1 + 1, inext⟩ := by
          apply Fin.ext
          exact hmodSmall
        simp only [hi, ↓reduceIte]
        rw [hidxSmall]
        simpa [idx, prefixIndex, Nat.mod_eq_of_lt (show i.1 + 1 < n by omega)] using
          C.right_species (idx i)
      · have hiEq : i.1 = k := by have := i.isLt; omega
        have hmodLast : (i.1 + 1) % (k + 1) = 0 := by rw [hiEq]; simp
        have hidxMod :
            (⟨(i.1 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
              ⟨0, by omega⟩ := by
          apply Fin.ext
          exact hmodLast
        simp only [hi, ↓reduceIte]
        rw [hidxMod]
        have hidxZero : idx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin n) := by
          apply Fin.ext
          rfl
        rw [hidxZero]
        exact hes
    right_reaction := by
      intro i
      by_cases hi : i.1 < k
      · simpa [hi, idx] using C.right_reaction (idx i)
      · have hiEq : i.1 = k := by have := i.isLt; omega
        have hidxLast : idx i = ⟨k, hk⟩ := by
          apply Fin.ext
          exact hiEq
        simp only [hi, ↓reduceIte, hidxLast]
        exact her
    species_injective := by
      intro i j hij
      have hidx : idx i = idx j := C.species_injective hij
      apply Fin.ext
      simpa [idx, prefixIndex] using congrArg Fin.val hidx
    reaction_injective := by
      intro i j hij
      have hidx : idx i = idx j := C.reaction_injective hij
      apply Fin.ext
      simpa [idx, prefixIndex] using congrArg Fin.val hidx
  }

@[simp] theorem closeInitialArcWithChord_species (C : N.TrueSRCycle n) (k : ℕ)
    (hk : k < n) (hkpos : 0 < k) (e : N.TrueSREdge)
    (hes : e.species = C.species (⟨0, by omega⟩ : Fin n))
    (her : e.reaction = C.reaction ⟨k, hk⟩) (i : Fin (k + 1)) :
    (C.closeInitialArcWithChord k hk hkpos e hes her).species i =
      C.species ⟨i.1, by omega⟩ := by
  apply congrArg C.species
  apply Fin.ext
  rfl

@[simp] theorem closeInitialArcWithChord_leftEdge (C : N.TrueSRCycle n) (k : ℕ)
    (hk : k < n) (hkpos : 0 < k) (e : N.TrueSREdge)
    (hes : e.species = C.species (⟨0, by omega⟩ : Fin n))
    (her : e.reaction = C.reaction ⟨k, hk⟩) (i : Fin (k + 1)) :
    (C.closeInitialArcWithChord k hk hkpos e hes her).leftEdge i =
      C.leftEdge ⟨i.1, by omega⟩ := by
  apply congrArg C.leftEdge
  apply Fin.ext
  rfl

@[simp] theorem closeInitialArcWithChord_rightEdge (C : N.TrueSRCycle n) (k : ℕ)
    (hk : k < n) (hkpos : 0 < k) (e : N.TrueSREdge)
    (hes : e.species = C.species (⟨0, by omega⟩ : Fin n))
    (her : e.reaction = C.reaction ⟨k, hk⟩) (i : Fin (k + 1)) :
    (C.closeInitialArcWithChord k hk hkpos e hes her).rightEdge i =
      if i.1 < k then C.rightEdge ⟨i.1, by omega⟩ else e := rfl

/-- Close an initial cycle arc with a reaction vertex outside the original cycle.  The first
`k` reaction vertices follow `C`; the final reaction is incident to the arc's terminal species
and initial species through `eTail` and `eHead`, respectively. -/
noncomputable def closeInitialArcWithReturnReaction (C : N.TrueSRCycle n) (k : ℕ)
    (hk : k < n) (hkpos : 0 < k) (eTail eHead : N.TrueSREdge)
    (hTailSpecies : eTail.species = C.species ⟨k, hk⟩)
    (hHeadSpecies : eHead.species = C.species ⟨0, by omega⟩)
    (hSameReaction : eTail.reaction = eHead.reaction)
    (hOffCycle : ∀ j, C.reaction j ≠ eTail.reaction) : N.TrueSRCycle (k + 1) := by
  let idx : Fin (k + 1) → Fin n := prefixIndex n k hk
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero (k + 1) := ⟨by omega⟩
  exact {
    nontrivial := by omega
    species := fun i => C.species (idx i)
    reaction := fun i => if i.1 < k then C.reaction (idx i) else eTail.reaction
    leftEdge := fun i => if i.1 < k then C.leftEdge (idx i) else eTail
    rightEdge := fun i => if i.1 < k then C.rightEdge (idx i) else eHead
    left_species := by
      intro i
      by_cases hi : i.1 < k
      · simp only [hi, ↓reduceIte]
        exact C.left_species (idx i)
      · have hieq : i.1 = k := by have := i.isLt; omega
        have hidxk : idx i = ⟨k, hk⟩ := by
          apply Fin.ext
          simpa [idx, prefixIndex] using hieq
        simp only [hi, ↓reduceIte]
        rw [hidxk]
        exact hTailSpecies
    left_reaction := by
      intro i
      by_cases hi : i.1 < k
      · simpa [hi, idx] using C.left_reaction (idx i)
      · simp only [hi, ↓reduceIte]
    right_species := by
      intro i
      by_cases hi : i.1 < k
      · have hnext : (i.1 + 1) % (k + 1) = i.1 + 1 :=
          Nat.mod_eq_of_lt (by omega)
        have hidxNext : idx ⟨(i.1 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ =
            ⟨i.1 + 1, by omega⟩ := by
          apply Fin.ext
          simp [idx, prefixIndex, hnext]
        simp only [hi, ↓reduceIte]
        rw [hidxNext]
        have hnextN : (i.1 + 1) % n = i.1 + 1 := Nat.mod_eq_of_lt (by omega)
        simpa [idx, prefixIndex, hnextN] using C.right_species (idx i)
      · have hieq : i.1 = k := by have := i.isLt; omega
        have hnext : (i.1 + 1) % (k + 1) = 0 := by rw [hieq]; simp
        have hzero : (⟨(i.1 + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
            ⟨0, by omega⟩ := by
          apply Fin.ext
          exact hnext
        simp only [hi, ↓reduceIte]
        rw [hzero]
        have hidxZero : idx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin n) := by
          apply Fin.ext
          rfl
        rw [hidxZero]
        exact hHeadSpecies
    right_reaction := by
      intro i
      by_cases hi : i.1 < k
      · simpa [hi, idx] using C.right_reaction (idx i)
      · simpa [hi] using hSameReaction.symm
    species_injective := by
      intro i j hij
      have hidx : idx i = idx j := C.species_injective hij
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [idx, prefixIndex] using hv
    reaction_injective := by
      intro i j hij
      by_cases hi : i.1 < k
      · by_cases hj : j.1 < k
        · have hidx : idx i = idx j := by
            apply C.reaction_injective
            simpa [hi, hj, idx] using hij
          apply Fin.ext
          have hv := congrArg Fin.val hidx
          simpa [idx, prefixIndex] using hv
        · have hbad : C.reaction (idx i) = eTail.reaction := by
            simpa only [if_pos hi, if_neg hj] using hij
          exact (hOffCycle (idx i) hbad).elim
      · by_cases hj : j.1 < k
        · have hbad : eTail.reaction = C.reaction (idx j) := by
            simpa only [if_neg hi, if_pos hj] using hij
          exact (hOffCycle (idx j) hbad.symm).elim
        · have hieq : i.1 = k := by have := i.isLt; omega
          have hjeq : j.1 = k := by have := j.isLt; omega
          apply Fin.ext
          omega
  }

@[simp] theorem closeInitialArcWithReturnReaction_species
    (C : N.TrueSRCycle n) (k : ℕ) (hk : k < n) (hkpos : 0 < k)
    (eTail eHead : N.TrueSREdge)
    (hTailSpecies : eTail.species = C.species ⟨k, hk⟩)
    (hHeadSpecies : eHead.species = C.species ⟨0, by omega⟩)
    (hSameReaction : eTail.reaction = eHead.reaction)
    (hOffCycle : ∀ j, C.reaction j ≠ eTail.reaction) (i : Fin (k + 1)) :
    (C.closeInitialArcWithReturnReaction k hk hkpos eTail eHead
      hTailSpecies hHeadSpecies hSameReaction hOffCycle).species i =
      C.species ⟨i.1, by omega⟩ := by
  apply congrArg C.species
  apply Fin.ext
  rfl

@[simp] theorem closeInitialArcWithReturnReaction_leftEdge
    (C : N.TrueSRCycle n) (k : ℕ) (hk : k < n) (hkpos : 0 < k)
    (eTail eHead : N.TrueSREdge)
    (hTailSpecies : eTail.species = C.species ⟨k, hk⟩)
    (hHeadSpecies : eHead.species = C.species ⟨0, by omega⟩)
    (hSameReaction : eTail.reaction = eHead.reaction)
    (hOffCycle : ∀ j, C.reaction j ≠ eTail.reaction) (i : Fin (k + 1)) :
    (C.closeInitialArcWithReturnReaction k hk hkpos eTail eHead
      hTailSpecies hHeadSpecies hSameReaction hOffCycle).leftEdge i =
      if i.1 < k then C.leftEdge ⟨i.1, by omega⟩ else eTail := rfl

@[simp] theorem closeInitialArcWithReturnReaction_rightEdge
    (C : N.TrueSRCycle n) (k : ℕ) (hk : k < n) (hkpos : 0 < k)
    (eTail eHead : N.TrueSREdge)
    (hTailSpecies : eTail.species = C.species ⟨k, hk⟩)
    (hHeadSpecies : eHead.species = C.species ⟨0, by omega⟩)
    (hSameReaction : eTail.reaction = eHead.reaction)
    (hOffCycle : ∀ j, C.reaction j ≠ eTail.reaction) (i : Fin (k + 1)) :
    (C.closeInitialArcWithReturnReaction k hk hkpos eTail eHead
      hTailSpecies hHeadSpecies hSameReaction hOffCycle).rightEdge i =
      if i.1 < k then C.rightEdge ⟨i.1, by omega⟩ else eHead := rfl

/-- Closing a proper initial arc of an even cycle with an extra incidence edge creates a second
even cycle sharing that entire species-to-reaction arc. The strong true-SR criterion forbids
this, so no such chord can occur. -/
theorem no_close_arc_chord_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {n : ℕ} (C : N.TrueSRCycle n) (hC : C.Even)
    (k : ℕ) (hk : k < n) (hkpos : 0 < k) (e : N.TrueSREdge)
    (hes : e.species = C.species (⟨0, by omega⟩ : Fin n))
    (her : e.reaction = C.reaction ⟨k, hk⟩) (hnot : ¬ C.ContainsEdge e)
    (hD : (C.closeInitialArcWithChord k hk hkpos e hes her).Even) : False := by
  classical
  let D := C.closeInitialArcWithChord k hk hkpos e hes her
  let P := C.initialArcPath k hk
  have hlen : 0 < 2 * k + 1 := by omega
  apply N.no_single_shared_path_of_trueSRCriterion hSR C D hC hD (2 * k + 1) hlen
    P.edge P.vertex
  · intro i
    have hlt := i.isLt
    by_cases heven : i.1 % 2 = 0
    · rw [C.initialArcPath_edge_even k hk i heven]
      exact Or.inl ⟨⟨i.1 / 2, by omega⟩, ⟨rfl, rfl, rfl⟩⟩
    · have hodd : i.1 % 2 ≠ 0 := heven
      rw [C.initialArcPath_edge_odd k hk i hodd]
      exact Or.inr ⟨⟨i.1 / 2, by omega⟩, ⟨rfl, rfl, rfl⟩⟩
  · intro i
    have hlt := i.isLt
    by_cases heven : i.1 % 2 = 0
    · let j : Fin (k + 1) := ⟨i.1 / 2, by omega⟩
      rw [C.initialArcPath_edge_even k hk i heven]
      refine Or.inl ⟨j, ?_⟩
      rw [closeInitialArcWithChord_leftEdge]
      exact ⟨rfl, rfl, rfl⟩
    · have hodd : i.1 % 2 ≠ 0 := heven
      let j : Fin (k + 1) := ⟨i.1 / 2, by omega⟩
      have hoddVal : i.1 % 2 = 1 := by omega
      have hdecomp := Nat.mod_add_div i.1 2
      have hjval : j.1 = i.1 / 2 := rfl
      have hiEq : i.1 = 2 * (i.1 / 2) + 1 := by
        have h := hdecomp
        rw [hoddVal] at h
        omega
      have hjlt : j.1 < k := by rw [hjval]; omega
      rw [C.initialArcPath_edge_odd k hk i hodd]
      refine Or.inr ⟨j, ?_⟩
      rw [closeInitialArcWithChord_rightEdge, if_pos hjlt]
      exact ⟨rfl, rfl, rfl⟩
  · exact P.connects
  · exact P.edge_simple
  · exact P.vertex_simple
  · exact P.starts_at_species
  · exact P.ends_at_reaction
  · intro f hfC hfD
    rcases hfD with ⟨j, hleft⟩ | ⟨j, hright⟩
    · let q : Fin (2 * k + 1) := ⟨2 * j.1, by have := j.isLt; omega⟩
      have hqeven : q.1 % 2 = 0 := by simp [q]
      let cidx : Fin n := ⟨j.1, by have := j.isLt; omega⟩
      have hqedge : P.edge q = C.leftEdge cidx := by
        rw [C.initialArcPath_edge_even k hk q hqeven]
        apply congrArg C.leftEdge
        apply Fin.ext
        simp [q, cidx]
      have hDleft : D.leftEdge j = C.leftEdge cidx := by
        simp [D, cidx]
      have hcommon : f.SameIncidence (C.leftEdge cidx) := by
        simpa [hDleft] using hleft
      refine ⟨q, ?_⟩
      simpa [hqedge] using hcommon
    · by_cases hjlt : j.1 < k
      · let q : Fin (2 * k + 1) := ⟨2 * j.1 + 1, by omega⟩
        have hqodd : q.1 % 2 ≠ 0 := by simp [q]
        let cidx : Fin n := ⟨j.1, by have := j.isLt; omega⟩
        have hqedge : P.edge q = C.rightEdge cidx := by
          rw [C.initialArcPath_edge_odd k hk q hqodd]
          apply congrArg C.rightEdge
          apply Fin.ext
          change (2 * j.1 + 1) / 2 = j.1
          omega
        have hDright : D.rightEdge j = C.rightEdge cidx := by
          simp [D, closeInitialArcWithChord_rightEdge, cidx, hjlt]
        have hcommon : f.SameIncidence (C.rightEdge cidx) := by
          simpa [hDright] using hright
        refine ⟨q, ?_⟩
        simpa [hqedge] using hcommon
      · have hjk : j.1 = k := by have := j.isLt; omega
        have hj : j = ⟨k, by omega⟩ := by apply Fin.ext; exact hjk
        have heq : D.rightEdge j = e := by
          rw [hj]
          simp [D, closeInitialArcWithChord_rightEdge]
        have hfe : f.SameIncidence e := by
          simpa [heq] using hright
        have hcontainsE : C.ContainsEdge e := by
          rcases hfC with ⟨a, hfa⟩ | ⟨a, hfa⟩
          · apply Or.inl
            refine ⟨a, ?_⟩
            rcases hfe with ⟨hs1, hr1, he1⟩
            rcases hfa with ⟨hs2, hr2, he2⟩
            exact ⟨hs1.symm.trans hs2, hr1.symm.trans hr2, he1.symm.trans he2⟩
          · apply Or.inr
            refine ⟨a, ?_⟩
            rcases hfe with ⟨hs1, hr1, he1⟩
            rcases hfa with ⟨hs2, hr2, he2⟩
            exact ⟨hs1.symm.trans hs2, hr1.symm.trans hr2, he1.symm.trans he2⟩
        exact (hnot hcontainsE).elim

end CRNT.Network.TrueSRCycle
