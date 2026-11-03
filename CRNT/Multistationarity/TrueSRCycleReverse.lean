import CRNT.Multistationarity.TrueChemistrySRGraph

/-!
# Reversing a true-SR cycle

`no_degree_two_causal_cycle` requires the cycle's *incoming* reaction at a species to be causal
for that species and the *outgoing* one to oppose it.  The causal-orbit constructor
`trueSRCycleOfPeriodicCausalOrbit` supplies the mirror image (see
`CRNT/Multistationarity/TrueSRCausalCycleFacts.lean`).  Reversing the traversal exchanges the
two roles, so this file builds the reversal and shows it preserves everything the endgame needs:
evenness, the net s-cycle identity, and the shared-representative condition.

Indexing.  With `C` having species `x₀ … x_{n-1}`, reactions `ρ₀ … ρ_{n-1}`,
`leftEdge i = (xᵢ, ρᵢ)` and `rightEdge i = (x_{i+1}, ρᵢ)`, the reversal takes

* `species' j = x_{(n-j) % n}`,
* `reaction' j = ρ_{n-1-j}`,
* `leftEdge' j = C.rightEdge (n-1-j)`,
* `rightEdge' j = C.leftEdge (n-1-j)`.

Each cycle edge is reused, with its left/right role swapped, which is exactly what flips the
causal/opposing orientation.
-/

namespace CRNT.Network.TrueSRCycle

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-! ### Index arithmetic -/

/-- Reversal of positions, `j ↦ n-1-j`, as a permutation of `Fin n`. -/
def revPerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun j := ⟨n - 1 - j.1, by have := j.isLt; omega⟩
  invFun j := ⟨n - 1 - j.1, by have := j.isLt; omega⟩
  left_inv j := by apply Fin.ext; have := j.isLt; simp; omega
  right_inv j := by apply Fin.ext; have := j.isLt; simp; omega

@[simp] theorem revPerm_apply (n : ℕ) (j : Fin n) : (revPerm n j).1 = n - 1 - j.1 := rfl

theorem rev_succ_idx (hn : 2 ≤ n) (j : Fin n) :
    ((n - 1 - j.1) + 1) % n = (n - j.1) % n := by
  have hj := j.isLt
  have h : (n - 1 - j.1) + 1 = n - j.1 := by omega
  rw [h]

theorem rev_pred_idx (hn : 2 ≤ n) (j : Fin n) :
    (n - ((j.1 + 1) % n)) % n = n - 1 - j.1 := by
  have hj := j.isLt
  rcases Nat.lt_or_ge (j.1 + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hjn : j.1 + 1 = n := by omega
    rw [hjn, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    omega

/-! ### The reversed cycle -/

/-- Traverse a true-SR cycle in the opposite direction. -/
def reverse (C : N.TrueSRCycle n) : N.TrueSRCycle n where
  nontrivial := C.nontrivial
  species := fun j =>
    C.species ⟨(n - j.1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  reaction := fun j => C.reaction (revPerm n j)
  leftEdge := fun j => C.rightEdge (revPerm n j)
  rightEdge := fun j => C.leftEdge (revPerm n j)
  left_species := by
    intro j
    rw [C.right_species (revPerm n j)]
    congr 1
    apply Fin.ext
    simpa using rev_succ_idx C.nontrivial j
  left_reaction := by intro j; exact C.right_reaction (revPerm n j)
  right_species := by
    intro j
    rw [C.left_species (revPerm n j)]
    congr 1
    apply Fin.ext
    simpa using (rev_pred_idx C.nontrivial j).symm
  right_reaction := by intro j; exact C.left_reaction (revPerm n j)
  species_injective := by
    intro a b hab
    have h := C.species_injective hab
    have hv := congrArg Fin.val h
    have ha := a.isLt
    have hb := b.isLt
    have hn := C.nontrivial
    apply Fin.ext
    simp only at hv
    rcases Nat.eq_zero_or_pos a.1 with ha0 | ha0
    · rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · omega
      · rw [ha0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hv
        omega
    · rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · rw [hb0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hv
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
  reaction_injective := by
    intro a b hab
    exact (revPerm n).injective (C.reaction_injective hab)

/-! ### Everything the endgame needs is preserved -/

@[simp] theorem reverse_leftEdge (C : N.TrueSRCycle n) (j : Fin n) :
    (C.reverse).leftEdge j = C.rightEdge (revPerm n j) := rfl

@[simp] theorem reverse_rightEdge (C : N.TrueSRCycle n) (j : Fin n) :
    (C.reverse).rightEdge j = C.leftEdge (revPerm n j) := rfl

/-- A position is a c-pair for the reversal exactly when its mirror is one for the original. -/
theorem reverse_isCPair (C : N.TrueSRCycle n) (j : Fin n) :
    (C.reverse).isCPair j ↔ C.isCPair (revPerm n j) := by
  unfold TrueSRCycle.isCPair
  simp only [reverse_leftEdge, reverse_rightEdge]
  exact eq_comm

theorem reverse_numCPairs (C : N.TrueSRCycle n) :
    (C.reverse).numCPairs = C.numCPairs := by
  classical
  unfold TrueSRCycle.numCPairs
  have hinv : ∀ j : Fin n, revPerm n (revPerm n j) = j := by
    intro j
    apply Fin.ext
    simp only [revPerm_apply]
    have := j.isLt
    omega
  have hset : (Finset.univ.filter (C.reverse).isCPair)
      = (Finset.univ.filter C.isCPair).image (revPerm n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      refine ⟨revPerm n j, ?_, hinv j⟩
      exact (reverse_isCPair C j).mp hj
    · rintro ⟨i, hi, hij⟩
      rw [reverse_isCPair]
      rw [← hij, hinv]
      exact hi
  rw [hset, Finset.card_image_of_injective _ (revPerm n).injective]

/-- **Evenness is preserved.** -/
theorem reverse_even (C : N.TrueSRCycle n) (hE : C.Even) : (C.reverse).Even := by
  unfold TrueSRCycle.Even at hE ⊢
  rw [reverse_numCPairs]
  exact hE

/-- **The net s-cycle identity is preserved**: reversal swaps the two products, and the
identity is an equality. -/
theorem reverse_sCycleNet (C : N.TrueSRCycle n) (h : C.SCycleNet) : (C.reverse).SCycleNet := by
  unfold TrueSRCycle.SCycleNet at h ⊢
  have hL : (∏ j, ((C.reverse).leftEdge j).netCoeff)
      = ∏ i, (C.rightEdge i).netCoeff := by
    simp only [reverse_leftEdge]
    exact Equiv.prod_comp (revPerm n) (fun i => (C.rightEdge i).netCoeff)
  have hR : (∏ j, ((C.reverse).rightEdge j).netCoeff)
      = ∏ i, (C.leftEdge i).netCoeff := by
    simp only [reverse_rightEdge]
    exact Equiv.prod_comp (revPerm n) (fun i => (C.leftEdge i).netCoeff)
  rw [hL, hR]
  exact h.symm

/-- **The label s-cycle identity is preserved** too, by the same swap. -/
theorem reverse_sCycle (C : N.TrueSRCycle n) (h : C.SCycle) : (C.reverse).SCycle := by
  unfold TrueSRCycle.SCycle at h ⊢
  have hL : (∏ j, ((C.reverse).leftEdge j).coeff) = ∏ i, (C.rightEdge i).coeff := by
    simp only [reverse_leftEdge]
    exact Equiv.prod_comp (revPerm n) (fun i => (C.rightEdge i).coeff)
  have hR : (∏ j, ((C.reverse).rightEdge j).coeff) = ∏ i, (C.leftEdge i).coeff := by
    simp only [reverse_rightEdge]
    exact Equiv.prod_comp (revPerm n) (fun i => (C.leftEdge i).coeff)
  rw [hL, hR]
  exact h.symm

/-- **The shared-representative condition is preserved.** -/
theorem reverse_rep (C : N.TrueSRCycle n)
    (hrep : ∀ i, (C.leftEdge i).representative = (C.rightEdge i).representative) :
    ∀ j, ((C.reverse).leftEdge j).representative = ((C.reverse).rightEdge j).representative := by
  intro j
  simp only [reverse_leftEdge, reverse_rightEdge]
  exact (hrep (revPerm n j)).symm

end CRNT.Network.TrueSRCycle
