import Mathlib.Logic.Equiv.Fin.Rotate
import CRNT.Multistationarity.TrueSRArc

/-!
# Rotating a cycle, and arcs from an arbitrary position

`TrueSRCycle.initialArcPath` reads an arc off a cycle starting at position `0`, which keeps
`right_species`' explicit `% n` from ever wrapping.  Splicing needs *both* arcs of a cycle
between two vertices, and the second one necessarily wraps.  Rotating the cycle moves any
starting position to `0`, so `rotate` plus `initialArcPath` gives arcs from anywhere.

The abstraction splicing wants is this: **a cycle is exactly two species-to-reaction paths with
the same two endpoints and disjoint interiors.**  Banaji--Craciun's Lemma 10 then reads: a chord
`P` from a species vertex of `C` to a reaction vertex of `C` glues to each of the two arcs of
`C` between those vertices, giving two cycles whose common edges are exactly `P` — which is what
`no_shared_path_of_trueSRCriterion` consumes.  The glue lemma itself is not built here.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- Shifting a residue by a constant is injective on `Fin n`. -/
private theorem rot_inj (hn : 0 < n) (r : ℕ) {a b : Fin n}
    (h : (a.1 + r) % n = (b.1 + r) % n) : a = b := by
  apply Fin.ext
  have hmod : a.1 ≡ b.1 [MOD n] := by
    have h' : (a.1 + r) ≡ (b.1 + r) [MOD n] := h
    exact Nat.ModEq.add_right_cancel' r h'
  exact Nat.ModEq.eq_of_lt_of_lt hmod a.isLt b.isLt

/-- Successor commutes with rotation. -/
private theorem rot_succ (hn : 0 < n) (r : ℕ) (i : Fin n) :
    (((i.1 + r) % n) + 1) % n = (((i.1 + 1) % n) + r) % n := by
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

/-- **Rotate a cycle by `r` positions.** -/
def rotate (C : N.TrueSRCycle n) (r : ℕ) : N.TrueSRCycle n where
  nontrivial := C.nontrivial
  species := fun i =>
    C.species ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  reaction := fun i =>
    C.reaction ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  leftEdge := fun i =>
    C.leftEdge ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  rightEdge := fun i =>
    C.rightEdge ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  left_species := fun i => C.left_species _
  left_reaction := fun i => C.left_reaction _
  right_species := by
    intro i
    rw [C.right_species]
    refine congrArg C.species (Fin.ext ?_)
    exact rot_succ (by have := C.nontrivial; omega) r i
  right_reaction := fun i => C.right_reaction _
  species_injective := by
    intro a b hab
    have h := C.species_injective hab
    exact rot_inj (by have := C.nontrivial; omega) r (congrArg Fin.val h)
  reaction_injective := by
    intro a b hab
    have h := C.reaction_injective hab
    exact rot_inj (by have := C.nontrivial; omega) r (congrArg Fin.val h)

@[simp] theorem rotate_species (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (C.rotate r).species i =
      C.species ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

@[simp] theorem rotate_leftEdge (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (C.rotate r).leftEdge i =
      C.leftEdge ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

@[simp] theorem rotate_rightEdge (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (C.rotate r).rightEdge i =
      C.rightEdge ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

@[simp] theorem rotate_reaction (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (C.rotate r).reaction i =
      C.reaction ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

@[simp] theorem rotate_isCPair (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (C.rotate r).isCPair i =
      C.isCPair ⟨(i.1 + r) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := rfl

/-- Rotating the cycle index and then taking its successor agrees with taking the successor first
and rotating that index. -/
theorem rotateIndex_successor (C : N.TrueSRCycle n) (r : ℕ) (i : Fin n) :
    (⟨((finRotate n i).1 + r) % n,
      Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ : Fin n) =
      finRotate n ⟨(i.1 + r) % n,
        Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ := by
  have hn : 0 < n := by have := C.nontrivial; omega
  apply Fin.ext
  have hleft : (finRotate n i).1 = (i.1 + 1) % n := by
    have h := congrArg Fin.val (finRotate_apply i)
    simpa [Fin.add_def] using h
  have hright :
      (finRotate n ⟨(i.1 + r) % n,
        Nat.mod_lt _ (by have := C.nontrivial; omega)⟩).1 =
        (((i.1 + r) % n) + 1) % n := by
    have h := congrArg Fin.val
      (finRotate_apply (⟨(i.1 + r) % n,
        Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ : Fin n))
    simpa [Fin.add_def] using h
  rw [hleft, hright]
  exact (rot_succ hn r i).symm

private noncomputable def rotateIndexEquiv (n r : ℕ) (hn : 0 < n) : Fin n ≃ Fin n := by
  letI : NeZero n := ⟨by omega⟩
  exact {
    toFun := fun i => i + ⟨r % n, Nat.mod_lt _ hn⟩
    invFun := fun i => i - ⟨r % n, Nat.mod_lt _ hn⟩
    left_inv := by intro i; exact add_sub_cancel_right i ⟨r % n, Nat.mod_lt _ hn⟩
    right_inv := by intro i; exact sub_add_cancel i ⟨r % n, Nat.mod_lt _ hn⟩
  }

private theorem rotateIndexEquiv_apply {n r : ℕ} (hn : 0 < n) (i : Fin n) :
    (rotateIndexEquiv n r hn i).1 = (i.1 + r) % n := by
  simp [rotateIndexEquiv, Fin.add_def]

/-- Rotating a simple cycle only changes where its cyclic indexing begins, so it preserves the
number of c-pairs. -/
theorem rotate_numCPairs (C : N.TrueSRCycle n) (r : ℕ) :
    (C.rotate r).numCPairs = C.numCPairs := by
  classical
  let hn : 0 < n := by have := C.nontrivial; omega
  let e := rotateIndexEquiv n r hn
  have hpair (i : Fin n) : (C.rotate r).isCPair i ↔ C.isCPair (e i) := by
    unfold TrueSRCycle.isCPair
    rw [rotate_leftEdge, rotate_rightEdge]
    have hi : e i = ⟨(i.1 + r) % n, Nat.mod_lt _ hn⟩ := by
      apply Fin.ext
      exact rotateIndexEquiv_apply hn i
    rw [hi]
  have hset : (Finset.univ.filter (C.rotate r).isCPair) =
      (Finset.univ.filter C.isCPair).image e.symm := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨e i, (hpair i).mp hi, e.symm_apply_apply i⟩
    · rintro ⟨j, hj, hji⟩
      have hje : j = e i := by
        have := congrArg e hji
        simpa using this
      rw [hpair i, ← hje]
      exact hj
  unfold TrueSRCycle.numCPairs
  rw [hset, Finset.card_image_of_injective _ e.symm.injective]

/-- Evenness of an e-cycle is unchanged by cyclically rotating its indexing. -/
theorem rotate_even (C : N.TrueSRCycle n) (r : ℕ) (hE : C.Even) :
    (C.rotate r).Even := by
  unfold TrueSRCycle.Even at hE ⊢
  rw [rotate_numCPairs]
  exact hE

/-- **An arc of a cycle starting at an arbitrary position**, obtained by rotating first. -/
noncomputable def arcPathFrom (C : N.TrueSRCycle n) (r : ℕ) (k : ℕ) (hk : k < n) :
    N.TrueSRPath (2 * k + 1) :=
  (C.rotate r).initialArcPath k hk

end CRNT.Network.TrueSRCycle
