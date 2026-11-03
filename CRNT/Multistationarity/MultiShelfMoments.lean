import CRNT.Multistationarity.MultiShelfConverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormDet

/-!
# The multi-shelf converse under three independent moments

This module continues the work of `CRNT.Multistationarity.MultiShelfConverse` (leaf M7) on the
**shelf** construction of Feinberg's *Deficiency One Algorithm* (DOA, 1995b) and of the
*Advanced Deficiency Algorithm* (ADA) of Ellison (1998) and Ji (2003).

A **shelf** is a part of the reaction set whose reactions are *pairing-constant* at the
log-ratio `μ`: all the sources of the shelf pair equally with `μ`.  A network is *ADA feasible*
when its reaction set is partitioned into shelves, each carrying a **shelf-wise confluence
vector** — a strictly positive flux supported on the shelf which balances the shelf at the lower
state `1` and at the upper state `e^{μ}`.  `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`
proves that an ADA-feasible network has the capacity for multiple positive steady states.

## The two-value argument and its sharpness

The *converse* direction — decomposing a balanced flux into shelf-wise confluence vectors — is
governed by the **two-value argument** `shelf_recursion`: if a balanced collection of reactions
splits into two pairing-constant parts with *distinct* pairing values, then each part balances on
its own.  Applied to the whole reaction set this is the **two-shelf decomposition**
`twoShelf_decomposition`, and it yields the capacity (`twoShelf_hasMultistationarityCapacity`).

The argument is **sharp**: a shelf produced this way is pairing-constant and hence cannot be split
again with distinct values (`twoShelf_cannot_iterate`), and with three pairing values the two
global balances leave a one-parameter family of partial balances (`threeShelf_freedom`).

## The rank obstruction

The reason is a **rank obstruction**, not a gap in the proof.  The two global flux balances give
exactly two moment relations on the partial balances `L i = ∑_{r ∈ sh_i} α_r (y'_r − y_r)`:

    (1)  ∑_i L i = 0                    for every s
    (2)  ∑_i e^{c_i} L i = 0            for every s

(`partialBalance_moments`).  For `k = 2` the resulting `2 × 2` matrix is nonsingular, so the
shelf balances follow; for `k ≥ 3` the kernel is at least `(k−2)`-dimensional, so the individual
shelf balances are **not** forced by the balances alone.  In this module the obstruction is made
explicit:

* `twoMomentRelations_haveNonzeroSolution` — the two moment relations always admit a nonzero
  solution, i.e. the rank of the moment system is at most two;
* `twoMomentKernel` — the explicit nonzero solution (the "circulation" of the two moments);
* `threeShelf_momentSystem_nontrivial_of_dependent` — if the third moment is a linear combination
  of the two balance moments, the *full* three-moment system still has a nonzero solution, so the
  shelf balances are still not forced.

## The correct way out: a third independent moment supplied as data

The correct way out of the obstruction is not to iterate the two-value argument, but to supply the
missing moment **as additional data**.  This module formalizes that:

* `shelfMomentMatrix` — the **moment matrix** of a three-shelf partition: the moment with which
  each shelf enters the partial balances (the plain count `1`, the exponential moment `e^{c_i}`
  from the upper balance, and the third moment `w_i`);
* `threeShelf_decomposition` — **the three-shelf converse under three independent moments**: if
  the reaction set is partitioned into three pairing-constant shelves, the flux balances the whole
  network at the lower and at the upper state, the partial balances satisfy the third moment
  relation with weights `w`, and the moment matrix `shelfMomentMatrix c w` is **nonsingular**,
  then *every* partial balance vanishes: the flux decomposes into three shelf-wise confluence
  vectors, the network is ADA feasible, and it has the capacity for multiple positive steady
  states;
* `shelfMomentMatrix_det_ne_zero_iff` — the criterion, in linear-algebraic form: the moment
  matrix is nonsingular exactly when the three moments `1`, `e^{c}` and `w` are linearly
  independent;
* `shelfMomentMatrix_det` — the explicit value of the determinant,
  `(e^{c_2} − e^{c_1}) w_0 + (e^{c_0} − e^{c_2}) w_1 + (e^{c_1} − e^{c_0}) w_2`;
* `shelfMomentMatrix_det_eq_zero_of_dependent` and
  `shelfMomentMatrix_det_ne_zero_of_independent` — the criterion in concrete terms: the third
  moment must be *independent* of the two balance moments, i.e. it must not be of the form
  `w i = a + b e^{c_i}`.

Note that the third moment is an **additional hypothesis**, not a conclusion: the statement is
not circular.  It is exactly the content that a genuine multi-shelf construction (Feinberg's or
Ellison's) has to establish.

## A concrete instance

`CRNT.Network.ThreeShelfExample` is a network with six species `{X i, Y i}` (`i = 0, 1, 2`) and
six reactions, grouped into three **modules**: the module `i` consists of the two reactions
`2 X i + Y i → 3 X i` and `X i → Y i`, whose reaction vectors are `+1` on `X i` and `-1` on
`Y i` and its opposite.  Each module therefore balances on its own.  The log-ratio
`μ (X i) = c i`, `μ (Y i) = -c i` puts the three modules at the three distinct levels
`c 0 = 1`, `c 1 = 2`, `c 2 = 3`; the sign-compatible stoichiometric vector is `σ = μ`, which lies
in the stoichiometric subspace as `σ = v₁ + 2 v₄ + 3 v₇`.  With the third moment
`w = (1, 0, 0)` — which is *independent* of the two balance moments, so that the moment matrix is
nonsingular — the three-shelf decomposition theorem applies and the network has the capacity for
multiple positive steady states (`ThreeShelfExample.hasCapacity`).

## What is *not* proved here

* **The third moment is not constructed from the combinatorics of the network.**  Nothing here
  shows that a network which admits a multi-shelf decomposition automatically admits a third
  independent moment; that remains Feinberg's *structural* analysis of the shelves (and the
  outstanding item of leaf M8).  What is proved here is the *converse* direction of such a
  construction: whenever the third moment is available and the moment matrix is nonsingular, the
  shelf balances follow automatically, exactly as the two-value argument does for two shelves.
* The **numerical version** of the algorithms.
* The **endotacticity** of the shelves, which is kept separate here as in
  `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`.

Depends on: `CRNT.Multistationarity.MultiShelfConverse`,
`CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Finset
open scoped Matrix

section General

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! ### The moment matrix of a three-shelf partition -/

/-- **The moment matrix of a three-shelf partition.**  The `i`-th row records the moment with
which the `i`-th shelf enters the partial balances: the plain count, the exponential moment
`e^{c_i}` coming from the upper balance, and a third moment `w_i`. -/
noncomputable def shelfMomentMatrix (c : Fin 3 → ℝ) (w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match j with
    | 0 => 1
    | 1 => Real.exp (c i)
    | 2 => w i

@[simp] theorem shelfMomentMatrix_zero (c w : Fin 3 → ℝ) (i : Fin 3) :
    shelfMomentMatrix c w i 0 = 1 := rfl

@[simp] theorem shelfMomentMatrix_one (c w : Fin 3 → ℝ) (i : Fin 3) :
    shelfMomentMatrix c w i 1 = Real.exp (c i) := rfl

@[simp] theorem shelfMomentMatrix_two (c w : Fin 3 → ℝ) (i : Fin 3) :
    shelfMomentMatrix c w i 2 = w i := rfl

/-- The moment matrix of a three-shelf partition, as a matrix literal. -/
theorem shelfMomentMatrix_eq (c w : Fin 3 → ℝ) :
    shelfMomentMatrix c w =
      !![1, Real.exp (c 0), w 0; 1, Real.exp (c 1), w 1; 1, Real.exp (c 2), w 2] := by
  ext i j
  fin_cases j <;> fin_cases i <;> rfl

/-! ### The three shelves -/

/-- The three shelves, as a function of the shelf index: `threeShelf sh0 sh1 sh2 0 = sh0`,
`threeShelf sh0 sh1 sh2 1 = sh1` and `threeShelf sh0 sh1 sh2 2 = sh2`. -/
def threeShelf (sh0 sh1 sh2 : Finset N.R) (i : Fin 3) : Finset N.R :=
  if i = 0 then sh0 else if i = 1 then sh1 else sh2

/-- **The three cases of `Fin 3`.** -/
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

@[simp] theorem threeShelf_zero (sh0 sh1 sh2 : Finset N.R) : threeShelf sh0 sh1 sh2 0 = sh0 := by
  simp [threeShelf]

@[simp] theorem threeShelf_one (sh0 sh1 sh2 : Finset N.R) : threeShelf sh0 sh1 sh2 1 = sh1 := by
  simp [threeShelf]

@[simp] theorem threeShelf_two (sh0 sh1 sh2 : Finset N.R) : threeShelf sh0 sh1 sh2 2 = sh2 := by
  simp [threeShelf]

/-- **Two distinct shelves are disjoint.** -/
theorem threeShelf_inter_eq_empty {sh0 sh1 sh2 : Finset N.R}
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅)
    (i j : Fin 3) (hij : i ≠ j) : threeShelf sh0 sh1 sh2 i ∩ threeShelf sh0 sh1 sh2 j = ∅ := by
  rcases fin3_cases i with hi | hi | hi
  · subst hi
    rcases fin3_cases j with hj | hj | hj
    · subst hj; exact absurd rfl hij
    · subst hj; simpa using hdisj.1
    · subst hj; simpa using hdisj.2.1
  · subst hi
    rcases fin3_cases j with hj | hj | hj
    · subst hj; simpa [Finset.inter_comm] using hdisj.1
    · subst hj; exact absurd rfl hij
    · subst hj; simpa using hdisj.2.2
  · subst hi
    rcases fin3_cases j with hj | hj | hj
    · subst hj; simpa [Finset.inter_comm] using hdisj.2.1
    · subst hj; simpa [Finset.inter_comm] using hdisj.2.2
    · subst hj; exact absurd rfl hij

/-- **The shelf decomposition of a three-shelf partition.** -/
def threeShelfDecomposition {N : Network S} (sh0 sh1 sh2 : Finset N.R)
    (hcover : sh0 ∪ sh1 ∪ sh2 = (Finset.univ : Finset N.R))
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅) : N.ADAShelfDecomposition where
  shelves := {sh0, sh1, sh2}
  cover := by
    intro r
    have hr : r ∈ sh0 ∪ sh1 ∪ sh2 := by
      rw [hcover]; exact Finset.mem_univ r
    rcases Finset.mem_union.mp hr with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨sh0, Finset.mem_insert_self _ _, h⟩
      · exact ⟨sh1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨sh2, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), h⟩
  disjoint := by
    intro sh hsh sh' hsh' hne
    have hcases : sh = sh0 ∨ sh = sh1 ∨ sh = sh2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsh
      exact hsh
    have hcases' : sh' = sh0 ∨ sh' = sh1 ∨ sh' = sh2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsh'
      exact hsh'
    rcases hcases with h1 | h1 | h1
    · rcases hcases' with h2 | h2 | h2
      · rw [h1, h2]; exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]; exact hdisj.1
      · rw [h1, h2]; exact hdisj.2.1
    · rcases hcases' with h2 | h2 | h2
      · rw [h1, h2]; exact (Finset.inter_comm sh1 sh0).symm ▸ hdisj.1
      · rw [h1, h2]; exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]; exact hdisj.2.2
    · rcases hcases' with h2 | h2 | h2
      · rw [h1, h2]; exact (Finset.inter_comm sh2 sh0).symm ▸ hdisj.2.1
      · rw [h1, h2]; exact (Finset.inter_comm sh2 sh1).symm ▸ hdisj.2.2
      · rw [h1, h2]; exact absurd (h1.trans h2.symm) hne

/-- **The shelf-wise confluence vectors of a three-shelf partition.** -/
def threeShelfConfluences {N : Network S} (sh0 sh1 sh2 : Finset N.R)
    (hcover : sh0 ∪ sh1 ∪ sh2 = (Finset.univ : Finset N.R))
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅)
    (μ : S → ℝ) (α : N.R → ℝ) (hα : ∀ r, 0 < α r)
    (hbal : ∀ i : Fin 3, ∀ s,
      ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * N.reactionVector r s = 0)
    (hupp : ∀ i : Fin 3, ∀ s,
      ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) :
    N.ADAConfluences (threeShelfDecomposition sh0 sh1 sh2 hcover hdisj) where
  μ := μ
  flux := fun sh r => if r ∈ sh then α r else 0
  support := by
    intro sh hsh r hr
    simp [hr]
  positive := by
    intro sh hsh r hr
    simp [hr]
    exact hα r
  lower_balance := by
    intro sh hsh s
    have hcases : sh = sh0 ∨ sh = sh1 ∨ sh = sh2 := by
      have hsh' : sh ∈ ({sh0, sh1, sh2} : Finset (Finset N.R)) := hsh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsh'
      exact hsh'
    rcases hcases with h1 | h1 | h1
    · rw [h1]
      calc ∑ r ∈ sh0, (if r ∈ sh0 then α r else 0) * N.reactionVector r s
          = ∑ r ∈ sh0, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hbal 0 s
    · rw [h1]
      calc ∑ r ∈ sh1, (if r ∈ sh1 then α r else 0) * N.reactionVector r s
          = ∑ r ∈ sh1, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hbal 1 s
    · rw [h1]
      calc ∑ r ∈ sh2, (if r ∈ sh2 then α r else 0) * N.reactionVector r s
          = ∑ r ∈ sh2, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hbal 2 s
  upper_balance := by
    intro sh hsh s
    have hcases : sh = sh0 ∨ sh = sh1 ∨ sh = sh2 := by
      have hsh' : sh ∈ ({sh0, sh1, sh2} : Finset (Finset N.R)) := hsh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsh'
      exact hsh'
    rcases hcases with h1 | h1 | h1
    · rw [h1]
      calc ∑ r ∈ sh0, (if r ∈ sh0 then α r else 0) * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s
          = ∑ r ∈ sh0, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hupp 0 s
    · rw [h1]
      calc ∑ r ∈ sh1, (if r ∈ sh1 then α r else 0) * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s
          = ∑ r ∈ sh1, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hupp 1 s
    · rw [h1]
      calc ∑ r ∈ sh2, (if r ∈ sh2 then α r else 0) * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s
          = ∑ r ∈ sh2, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hupp 2 s

/-! ### The three-shelf converse under three independent moments -/

/-- **The shelf balances follow from three independent moments.**  This is the analytic core of
the three-shelf converse: the two global balances supply the moments `1` and `e^{c}`, the third
moment relation supplies the moment `w`, and the nonsingularity of the moment matrix
`shelfMomentMatrix c w` forces every partial balance to vanish. -/
theorem threeShelf_shelfBalances
    (μ : S → ℝ) (α : N.R → ℝ)
    (sh0 sh1 sh2 : Finset N.R) (c : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (hcover : sh0 ∪ sh1 ∪ sh2 = (Finset.univ : Finset N.R))
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅)
    (hconst : ∀ (i : Fin 3) (r : N.R), r ∈ threeShelf sh0 sh1 sh2 i →
        sourcePairing N μ r = c i)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (hmom : ∀ s, ∑ (i : Fin 3), w i * (∑ r ∈ threeShelf sh0 sh1 sh2 i,
        α r * N.reactionVector r s) = 0)
    (hdet : (shelfMomentMatrix c w).det ≠ 0) :
    (∀ i : Fin 3, ∀ s,
        ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * N.reactionVector r s = 0) ∧
      (∀ i : Fin 3, ∀ s,
        ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s = 0) := by
  classical
  have hcover' : ∀ r : N.R, ∃ i, r ∈ threeShelf sh0 sh1 sh2 i := by
    intro r
    have hr : r ∈ sh0 ∪ sh1 ∪ sh2 := by
      rw [hcover]; exact Finset.mem_univ r
    rcases Finset.mem_union.mp hr with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  have hdisj' : ∀ i j : Fin 3, i ≠ j →
      threeShelf sh0 sh1 sh2 i ∩ threeShelf sh0 sh1 sh2 j = ∅ :=
    fun i j hij => threeShelf_inter_eq_empty hdisj i j hij
  obtain ⟨hmom0, hmom1⟩ := partialBalance_moments μ α (threeShelf sh0 sh1 sh2) c
    hcover' hdisj' hconst hlow hupp
  have hsys : ∀ s, (fun L : Fin 3 → ℝ => L ᵥ* shelfMomentMatrix c w)
      (fun i => ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * N.reactionVector r s) = 0 := by
    intro s
    funext j
    simp only [Pi.zero_apply]
    rcases fin3_cases j with hj | hj | hj
    · subst hj
      simp only [Matrix.vecMul_apply_eq_sum, shelfMomentMatrix_zero, mul_one]
      exact hmom0 s
    · subst hj
      simp only [Matrix.vecMul_apply_eq_sum, shelfMomentMatrix_one]
      rw [Finset.sum_congr rfl fun i _ => mul_comm _ _]
      exact hmom1 s
    · subst hj
      simp only [Matrix.vecMul_apply_eq_sum, shelfMomentMatrix_two]
      rw [Finset.sum_congr rfl fun i _ => mul_comm _ _]
      exact hmom s
  have hzero : ∀ s i, ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * N.reactionVector r s = 0 := by
    intro s i
    have hL : (fun i => ∑ r ∈ threeShelf sh0 sh1 sh2 i, α r * N.reactionVector r s) = 0 :=
      Matrix.eq_zero_of_vecMul_eq_zero hdet (hsys s)
    simpa using congrFun hL i
  refine ⟨fun i s => hzero s i, ?_⟩
  intro i s
  exact shelfLowerBalanced_implies_shelfUpperBalanced N (threeShelf sh0 sh1 sh2 i) α μ
    (fun r hr r' hr' => (hconst i r hr).trans (hconst i r' hr').symm)
    (fun s => hzero s i) s

/-- **The three-shelf converse under three independent moments: the ADA feasibility.** -/
theorem threeShelf_adaFeasible
    (μ : S → ℝ) (α : N.R → ℝ)
    (sh0 sh1 sh2 : Finset N.R) (c : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (hcover : sh0 ∪ sh1 ∪ sh2 = (Finset.univ : Finset N.R))
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅)
    (hconst : ∀ (i : Fin 3) (r : N.R), r ∈ threeShelf sh0 sh1 sh2 i →
        sourcePairing N μ r = c i)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (hmom : ∀ s, ∑ (i : Fin 3), w i * (∑ r ∈ threeShelf sh0 sh1 sh2 i,
        α r * N.reactionVector r s) = 0)
    (hdet : (shelfMomentMatrix c w).det ≠ 0)
    (hα : ∀ r, 0 < α r) (hμ0 : μ ≠ 0) (hsc : N.SignCompatibleWithStoich μ) :
    N.ADAFeasible := by
  obtain ⟨hbal, huppShelf⟩ :=
    threeShelf_shelfBalances μ α sh0 sh1 sh2 c w hcover hdisj hconst hlow hupp hmom hdet
  exact ⟨threeShelfDecomposition sh0 sh1 sh2 hcover hdisj,
    threeShelfConfluences sh0 sh1 sh2 hcover hdisj μ α hα hbal huppShelf, hμ0, hsc⟩

/-- **The three-shelf converse under three independent moments.**  Let the reaction set be
partitioned into three shelves, each pairing-constant at `μ` at the values `c 0`, `c 1`, `c 2`.
Suppose the flux `α` balances the whole network at the lower and at the upper state, and
suppose *additionally* that the partial balances satisfy a third moment relation with weights
`w`.  If the moment matrix `shelfMomentMatrix c w` is nonsingular, then **every partial balance
vanishes**: the flux decomposes into three shelf-wise confluence vectors, the network is ADA
feasible, and it has the capacity for multiple positive steady states.

This is the genuine three-shelf analogue of `twoShelf_decomposition`; the difference is that
the third relation is *extra data*, not the conclusion, so the statement is not circular. -/
theorem threeShelf_decomposition
    (μ : S → ℝ) (α : N.R → ℝ)
    (sh0 sh1 sh2 : Finset N.R) (c : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (hcover : sh0 ∪ sh1 ∪ sh2 = (Finset.univ : Finset N.R))
    (hdisj : sh0 ∩ sh1 = ∅ ∧ sh0 ∩ sh2 = ∅ ∧ sh1 ∩ sh2 = ∅)
    (hconst : ∀ (i : Fin 3) (r : N.R), r ∈ threeShelf sh0 sh1 sh2 i →
        sourcePairing N μ r = c i)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (hmom : ∀ s, ∑ (i : Fin 3), w i * (∑ r ∈ threeShelf sh0 sh1 sh2 i,
        α r * N.reactionVector r s) = 0)
    (hdet : (shelfMomentMatrix c w).det ≠ 0)
    (hα : ∀ r, 0 < α r) (hμ0 : μ ≠ 0) (hsc : N.SignCompatibleWithStoich μ) :
    N.HasMultistationarityCapacity :=
  N.adaFeasible_implies_capacity
    (threeShelf_adaFeasible μ α sh0 sh1 sh2 c w hcover hdisj hconst hlow hupp hmom hdet
      hα hμ0 hsc)

/-! ### The rank obstruction: the moments of a three-shelf partition -/

/-- **The three moments of a three-shelf partition**: the constant moment `1` (the lower
balance), the exponential moment `e^{c}` (the upper balance), and the third moment `w`. -/
noncomputable def threeShelfMoments (c w : Fin 3 → ℝ) : Fin 3 → (Fin 3 → ℝ) :=
  fun j i => shelfMomentMatrix c w i j

/-- The three moments are the *columns* of the moment matrix, i.e. its transpose. -/
theorem threeShelfMoments_eq_transpose (c w : Fin 3 → ℝ) :
    threeShelfMoments c w = (shelfMomentMatrix c w)ᵀ := by
  rfl

/-- The three moments are also the columns of the moment matrix. -/
theorem threeShelfMoments_eq_col (c w : Fin 3 → ℝ) :
    threeShelfMoments c w = (shelfMomentMatrix c w).col := by
  rfl

/-- **The moment system.**  The `i`-th coordinate of the linear combination of the three moments
with the coefficients `k` is `k 0 + k 1 e^{c_i} + k 2 w_i`. -/
theorem threeShelfMoments_sum_apply (c w : Fin 3 → ℝ) (k : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j, k j • threeShelfMoments c w j) i
      = k 0 * 1 + k 1 * Real.exp (c i) + k 2 * w i := by
  rw [Finset.sum_apply, Fin.sum_univ_three]
  simp only [Pi.smul_apply, smul_eq_mul, threeShelfMoments, shelfMomentMatrix_zero,
    shelfMomentMatrix_one, shelfMomentMatrix_two]

/-- **The explicit value of the moment determinant.**  The determinant of the moment matrix is
the alternating sum of the third moment against the two balance moments. -/
theorem shelfMomentMatrix_det (c w : Fin 3 → ℝ) :
    (shelfMomentMatrix c w).det
      = (Real.exp (c 2) - Real.exp (c 1)) * w 0
        + (Real.exp (c 0) - Real.exp (c 2)) * w 1
        + (Real.exp (c 1) - Real.exp (c 0)) * w 2 := by
  rw [shelfMomentMatrix_eq]
  eval_det
  ring

/-- **The third moment is what makes the three-shelf system determined.**  The moment matrix is
nonsingular exactly when the three moments `1`, `e^{c}` and `w` are linearly independent. -/
theorem shelfMomentMatrix_det_ne_zero_iff (c w : Fin 3 → ℝ) :
    (shelfMomentMatrix c w).det ≠ 0 ↔ LinearIndependent ℝ (threeShelfMoments c w) := by
  rw [threeShelfMoments_eq_col, ← Matrix.mulVec_injective_iff,
    Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **A dependent third moment does not determine the system.**  If the third moment is a linear
combination of the two balance moments, `w i = a + b e^{c_i}`, then the moment matrix is
singular. -/
theorem shelfMomentMatrix_det_eq_zero_of_dependent (c w : Fin 3 → ℝ)
    (hw : ∃ a b : ℝ, ∀ i, w i = a + b * Real.exp (c i)) :
    (shelfMomentMatrix c w).det = 0 := by
  obtain ⟨a, b, hab⟩ := hw
  rw [shelfMomentMatrix_det, hab 0, hab 1, hab 2]
  ring

/-- **An independent third moment determines the system.**  If the three pairing values are
pairwise distinct and the third moment is *not* a linear combination of the two balance moments,
then the moment matrix is nonsingular. -/
theorem shelfMomentMatrix_det_ne_zero_of_independent (c w : Fin 3 → ℝ)
    (hc : ∀ i j : Fin 3, i ≠ j → c i ≠ c j)
    (hw : ¬ ∃ a b : ℝ, ∀ i, w i = a + b * Real.exp (c i)) :
    (shelfMomentMatrix c w).det ≠ 0 := by
  -- the constant moment and the exponential moment are linearly independent
  have honeexp : ∀ a b : ℝ, (∀ i, a + b * Real.exp (c i) = 0) → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · have ha : a = 0 := by
        have h := hab 0
        rw [hb] at h
        simpa using h
      exact ⟨ha, hb⟩
    · exfalso
      have hexp : ∀ i, Real.exp (c i) = -a / b := by
        intro i
        have h' : Real.exp (c i) * b = -a := by
          linear_combination hab i
        exact (eq_div_iff hb).2 h'
      have h01 : Real.exp (c 0) = Real.exp (c 1) := by
        rw [hexp 0, hexp 1]
      have h01' : c 0 = c 1 := Real.exp_injective h01
      exact absurd h01' (hc 0 1 (by decide))
  -- the three moments are linearly independent
  have hlin : LinearIndependent ℝ (threeShelfMoments c w) := by
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    intro g h hgh
    have hcoord : ∀ i, (g 0 - h 0) * 1 + (g 1 - h 1) * Real.exp (c i) + (g 2 - h 2) * w i = 0 := by
      intro i
      have h1 := congrFun hgh i
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at h1
      rw [threeShelfMoments_sum_apply, threeShelfMoments_sum_apply] at h1
      linear_combination h1
    by_cases h2 : g 2 - h 2 = 0
    · have hrel : ∀ i, (g 0 - h 0) + (g 1 - h 1) * Real.exp (c i) = 0 := by
        intro i
        have hi := hcoord i
        rw [h2] at hi
        simpa using hi
      obtain ⟨ha, hb'⟩ := honeexp (g 0 - h 0) (g 1 - h 1) hrel
      have hg0 : g 0 = h 0 := by linarith
      have hg1 : g 1 = h 1 := by linarith
      have hg2 : g 2 = h 2 := by linarith
      funext j
      fin_cases j
      · exact hg0
      · exact hg1
      · exact hg2
    · exfalso
      refine hw ⟨-(g 0 - h 0) / (g 2 - h 2), -(g 1 - h 1) / (g 2 - h 2), ?_⟩
      intro i
      have hi := hcoord i
      have hmul : (g 2 - h 2) * w i = -((g 0 - h 0) + (g 1 - h 1) * Real.exp (c i)) := by
        linear_combination hi
      have hne : g 2 - h 2 ≠ 0 := h2
      have hdiv : w i = -((g 0 - h 0) + (g 1 - h 1) * Real.exp (c i)) / (g 2 - h 2) := by
        field_simp
        linear_combination hi
      rw [hdiv]
      have heq : -((g 0 - h 0) + (g 1 - h 1) * Real.exp (c i)) / (g 2 - h 2)
          = -(g 0 - h 0) / (g 2 - h 2) + (-(g 1 - h 1) / (g 2 - h 2)) * Real.exp (c i) := by
        field_simp
        ring
      exact heq
  exact (shelfMomentMatrix_det_ne_zero_iff c w).2 hlin

/-! ### The rank obstruction: the two moment relations leave a nontrivial kernel -/

/-- **The circulation vector of the two moment relations.**  This is the explicit nonzero
solution of the two moment relations `∑_i L i = 0` and `∑_i e^{c_i} L i = 0`. -/
noncomputable def twoMomentKernel (c : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => match i with
    | 0 => Real.exp (c 1) - Real.exp (c 2)
    | 1 => Real.exp (c 2) - Real.exp (c 0)
    | 2 => Real.exp (c 0) - Real.exp (c 1)

/-- The circulation vector satisfies the plain moment relation. -/
theorem twoMomentKernel_sum (c : Fin 3 → ℝ) : ∑ i, twoMomentKernel c i = 0 := by
  rw [Fin.sum_univ_three]
  simp only [twoMomentKernel]
  ring

/-- The circulation vector satisfies the exponential moment relation. -/
theorem twoMomentKernel_exp_sum (c : Fin 3 → ℝ) :
    ∑ i, Real.exp (c i) * twoMomentKernel c i = 0 := by
  rw [Fin.sum_univ_three]
  simp only [twoMomentKernel]
  ring

/-- The circulation vector is nonzero as soon as two of the pairing values differ. -/
theorem twoMomentKernel_ne_zero {c : Fin 3 → ℝ} (hc : ¬ (c 0 = c 1 ∧ c 1 = c 2)) :
    twoMomentKernel c ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [twoMomentKernel] at h0 h1 h2
  have hc01 : c 1 = c 2 := Real.exp_injective (sub_eq_zero.mp h0)
  have hc12 : c 2 = c 0 := Real.exp_injective (sub_eq_zero.mp h1)
  have hc20 : c 0 = c 1 := Real.exp_injective (sub_eq_zero.mp h2)
  exact hc ⟨hc20, hc01⟩

/-- **The rank obstruction, in explicit form.**  The two global balances supply only the moments
`1` and `e^{c}`, so the moment system of a three-shelf partition always has a nonzero solution:
the partial balances are *not* determined by the balances alone. -/
theorem twoMomentRelations_haveNonzeroSolution (c : Fin 3 → ℝ) :
    ∃ L : Fin 3 → ℝ, L ≠ 0 ∧ (∑ i, L i = 0) ∧ (∑ i, Real.exp (c i) * L i = 0) := by
  by_cases hc : c 0 = c 1 ∧ c 1 = c 2
  · -- the two moment relations coincide: any nonzero vector of sum zero works
    refine ⟨fun i => if i = 0 then 1 else if i = 1 then -1 else 0, ?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · rw [Fin.sum_univ_three]
      simp
    · rw [Fin.sum_univ_three]
      simp [hc.1]
  · refine ⟨twoMomentKernel c, twoMomentKernel_ne_zero hc, twoMomentKernel_sum c,
      twoMomentKernel_exp_sum c⟩

/-- **A dependent third moment does not help.**  If the third moment `w` is a linear combination
of the two balance moments, then the *full* three-moment system still admits a nonzero solution:
the three shelf balances are still not forced by the balances.  This is the sharp content of the
rank obstruction. -/
theorem threeShelf_momentSystem_nontrivial_of_dependent (c w : Fin 3 → ℝ)
    (hw : ∃ a b : ℝ, ∀ i, w i = a + b * Real.exp (c i)) :
    ∃ L : Fin 3 → ℝ, L ≠ 0 ∧ (∀ j, (L ᵥ* shelfMomentMatrix c w) j = 0) := by
  obtain ⟨a, b, hab⟩ := hw
  obtain ⟨L, hL, hL0, hL1⟩ := twoMomentRelations_haveNonzeroSolution c
  refine ⟨L, hL, ?_⟩
  intro j
  rw [Matrix.vecMul_apply_eq_sum]
  rcases fin3_cases j with hj | hj | hj
  · subst hj
    simp only [shelfMomentMatrix_zero, mul_one]
    exact hL0
  · subst hj
    simp only [shelfMomentMatrix_one]
    rw [Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact hL1
  · subst hj
    simp only [shelfMomentMatrix_two]
    calc ∑ i, L i * w i = ∑ i, L i * (a + b * Real.exp (c i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hab i]
        _ = ∑ i, (L i * a + (L i * b) * Real.exp (c i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = (∑ i, L i * a) + ∑ i, (L i * b) * Real.exp (c i) := Finset.sum_add_distrib
        _ = a * (∑ i, L i) + b * (∑ i, Real.exp (c i) * L i) := by
          have h1 : (∑ i, L i * a) = a * (∑ i, L i) := by
            rw [← Finset.sum_mul (Finset.univ : Finset (Fin 3)) L a, mul_comm]
          have h2 : (∑ i, (L i * b) * Real.exp (c i)) = b * (∑ i, Real.exp (c i) * L i) := by
            rw [Finset.mul_sum (Finset.univ : Finset (Fin 3)) (fun i => Real.exp (c i) * L i) b]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [h1, h2]
        _ = 0 := by rw [hL0, hL1]; ring

end General

/-! ### A concrete three-shelf instance -/

namespace ThreeShelfExample

open scoped BigOperators

/-- The species of the example: two species `X i`, `Y i` per module `i`. -/
inductive Species
  | X0 | Y0 | X1 | Y1 | X2 | Y2
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.X0, Species.Y0, Species.X1, Species.Y1, Species.X2, Species.Y2}
  complete := by intro s; cases s <;> simp

open Species

/-- The first species of the module `i`. -/
def X : Fin 3 → Species
  | 0 => .X0
  | 1 => .X1
  | 2 => .X2

/-- The second species of the module `i`. -/
def Y : Fin 3 → Species
  | 0 => .Y0
  | 1 => .Y1
  | 2 => .Y2

/-- The reactions of the example: two per module. -/
inductive Rxn
  | m0a | m0b | m1a | m1b | m2a | m2b
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.m0a, Rxn.m0b, Rxn.m1a, Rxn.m1b, Rxn.m2a, Rxn.m2b}
  complete := by intro r; cases r <;> simp

/-- The complex `X i`. -/
def cX (i : Fin 3) : Complex Species := fun t => if t = X i then 1 else 0

/-- The complex `Y i`. -/
def cY (i : Fin 3) : Complex Species := fun t => if t = Y i then 1 else 0

/-- The complex `2 X i + Y i`. -/
def c2XY (i : Fin 3) : Complex Species :=
  fun t => if t = X i then 2 else if t = Y i then 1 else 0

/-- The complex `3 X i`. -/
def c3X (i : Fin 3) : Complex Species := fun t => if t = X i then 3 else 0

/-- **The reactions of the example.**  The module `i` consists of the two reactions
`2 X i + Y i → 3 X i` and `X i → Y i`; their reaction vectors are `+1` on `X i` and `-1` on
`Y i` and its opposite, so each module balances on its own. -/
def reaction : Rxn → Reaction Species
  | .m0a => { source := c2XY 0, target := c3X 0 }
  | .m0b => { source := cX 0, target := cY 0 }
  | .m1a => { source := c2XY 1, target := c3X 1 }
  | .m1b => { source := cX 1, target := cY 1 }
  | .m2a => { source := c2XY 2, target := c3X 2 }
  | .m2b => { source := cX 2, target := cY 2 }

/-- The network of the example. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- The log-ratio: `μ (X i) = c i` and `μ (Y i) = -c i`. -/
def μ : Species → ℝ := fun t =>
  if t = .X0 then 1 else if t = .Y0 then -1 else if t = .X1 then 2 else if t = .Y1 then -2
  else if t = .X2 then 3 else -3

/-- The sign-compatible stoichiometric vector: `σ = μ`. -/
def σ : Species → ℝ := μ

/-- The unit flux. -/
def α : Rxn → ℝ := fun _ => 1

/-- The three pairing values. -/
def c : Fin 3 → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 3

/-- The third moment. -/
def w : Fin 3 → ℝ := fun i => if i = 0 then 1 else 0

/-- The three shelves: the reactions of the three modules. -/
def shelf (i : Fin 3) : Finset Rxn :=
  match i with
  | 0 => {Rxn.m0a, Rxn.m0b}
  | 1 => {Rxn.m1a, Rxn.m1b}
  | 2 => {Rxn.m2a, Rxn.m2b}

/-- The three shelves as the module's indexed family of shelves. -/
lemma threeShelf_eq : ∀ i : Fin 3,
    threeShelf (N := N) (shelf 0) (shelf 1) (shelf 2) i = shelf i := by
  intro i
  fin_cases i <;> simp [threeShelf, shelf]

/-- The univ of the species. -/
lemma univ_species : (Finset.univ : Finset Species) =
    {Species.X0, Species.Y0, Species.X1, Species.Y1, Species.X2, Species.Y2} := by
  ext s; cases s <;> simp

/-- The sum over the species. -/
lemma sum_species (f : Species → ℝ) :
    ∑ s, f s = f .X0 + f .Y0 + f .X1 + f .Y1 + f .X2 + f .Y2 := by
  show Finset.univ.sum f = _
  rw [univ_species]
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

/-- The univ of the reaction index. -/
lemma univ_Rxn : (Finset.univ : Finset Rxn) =
    {Rxn.m0a, Rxn.m0b, Rxn.m1a, Rxn.m1b, Rxn.m2a, Rxn.m2b} := by
  ext r; cases r <;> simp

/-- **The lower balance of the example**: the unit flux balances the whole network. -/
lemma lower_balance : ∀ s : Species, ∑ r, α r * N.reactionVector r s = 0 := by
  intro s
  rw [univ_Rxn]
  cases s <;>
    simp [α, reactionVector_apply, reaction, cX, cY, c2XY, c3X, X, Y,
      Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- **The source pairing of each reaction**: the module `i` pairs at the level `c i`. -/
lemma sourcePairing_eq (r : Rxn) : sourcePairing N μ r =
    match r with
    | .m0a => 1 | .m0b => 1 | .m1a => 2 | .m1b => 2 | .m2a => 3 | .m2b => 3 := by
  cases r <;>
    simp [sourcePairing, reaction, cX, c2XY, X, Y, μ, complexPairing,
      sum_species] <;> ring

/-- **The upper balance of the example**: the unit flux balances the whole network at the upper
state `e^{μ}`. -/
lemma upper_balance : ∀ s : Species,
    ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0 := by
  intro s
  rw [univ_Rxn]
  cases s <;>
    simp [α, sourcePairing_eq, reactionVector_apply, reaction, cX, cY, c2XY, c3X, X, Y,
      Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- **The balance of a shelf**: the module `i` balances on its own. -/
lemma shelf_balance : ∀ (i : Fin 3) (s : Species),
    ∑ r ∈ shelf i, α r * N.reactionVector r s = 0 := by
  intro i s
  fin_cases i <;> cases s <;>
    simp [α, shelf, reactionVector_apply, reaction, cX, cY, c2XY, c3X, X, Y,
      Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- The source pairing of the reactions of the shelf `i` is the level `c i`. -/
lemma sourcePairing_shelf : ∀ (i : Fin 3) (r : Rxn), r ∈ shelf i →
    sourcePairing N μ r = c i := by
  intro i r hr
  fin_cases i
  · simp only [shelf, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [sourcePairing_eq, c]
  · simp only [shelf, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [sourcePairing_eq, c]
  · simp only [shelf, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [sourcePairing_eq, c]

/-- The log-ratio is nonzero. -/
lemma mu_ne_zero : μ ≠ 0 := by
  intro h
  have h1 := congrFun h Species.X0
  simp [μ] at h1

/-- The log-ratio and the stoichiometric vector have the same sign pattern. -/
lemma sameSign : SameSign μ σ := by
  intro s
  cases s <;> simp [μ, σ]

/-- **The sign-compatible vector lies in the stoichiometric subspace**:
`σ = v₁ + 2 v₄ + 3 v₇`. -/
lemma mem_stoichSubspace : σ ∈ N.stoichSubspace := by
  have h1 : N.reactionVector Rxn.m0a ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h2 : N.reactionVector Rxn.m1a ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h3 : N.reactionVector Rxn.m2a ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h12 : (1 : ℝ) • N.reactionVector Rxn.m0a + (2 : ℝ) • N.reactionVector Rxn.m1a
      ∈ N.stoichSubspace :=
    N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem 1 h1) (N.stoichSubspace.smul_mem 2 h2)
  have h123 : (1 : ℝ) • N.reactionVector Rxn.m0a + (2 : ℝ) • N.reactionVector Rxn.m1a
      + (3 : ℝ) • N.reactionVector Rxn.m2a ∈ N.stoichSubspace :=
    N.stoichSubspace.add_mem h12 (N.stoichSubspace.smul_mem 3 h3)
  have heq : σ = (1 : ℝ) • N.reactionVector Rxn.m0a + (2 : ℝ) • N.reactionVector Rxn.m1a
      + (3 : ℝ) • N.reactionVector Rxn.m2a := by
    funext s
    cases s <;>
      simp [σ, μ, reactionVector_apply, reaction, c2XY, c3X, X, Y,
        Pi.smul_apply, smul_eq_mul] <;> ring
  rw [heq]
  exact h123

/-- **The third moment relation**: the partial balances satisfy the third moment with the
weights `w`. -/
lemma third_moment : ∀ s : Species,
    ∑ (i : Fin 3), w i * (∑ r ∈ shelf i, α r * N.reactionVector r s) = 0 := by
  intro s
  rw [Fin.sum_univ_three]
  have h0 := shelf_balance 0 s
  have h1 : w 0 = 1 := by simp [w]
  have h2 : w 1 = 0 := by simp [w]
  have h3 : w 2 = 0 := by simp [w]
  simp only [h1, h2, h3, one_mul, zero_mul, add_zero]
  exact h0

/-- **The moment matrix of the example is nonsingular**: the third moment is independent of the
two balance moments. -/
lemma moment_det_ne_zero : (shelfMomentMatrix c w).det ≠ 0 := by
  refine shelfMomentMatrix_det_ne_zero_of_independent (c := c) (w := w) ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [c] at hij ⊢
  · rintro ⟨a, b, hab⟩
    have h0 := hab 0
    have h1 := hab 1
    have h2 := hab 2
    simp [w] at h0 h1 h2
    have hbne : Real.exp (c 2) ≠ Real.exp (c 1) := by
      intro hcon
      exact absurd (Real.exp_injective hcon) (by simp [c])
    have hmul : b * (Real.exp (c 2) - Real.exp (c 1)) = 0 := by
      have h3 : b * Real.exp (c 2) - b * Real.exp (c 1) = 0 := by linarith [h1, h2]
      calc b * (Real.exp (c 2) - Real.exp (c 1))
          = b * Real.exp (c 2) - b * Real.exp (c 1) := by ring
        _ = 0 := h3
    have hb : b = 0 := (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hbne)
    rw [hb] at h0 h1 h2
    linarith

/-- The three shelves cover the reaction set. -/
lemma shelves_cover : shelf 0 ∪ shelf 1 ∪ shelf 2 = Finset.univ := by
  show {Rxn.m0a, Rxn.m0b} ∪ {Rxn.m1a, Rxn.m1b} ∪ {Rxn.m2a, Rxn.m2b} = _
  rw [univ_Rxn]
  ext r; cases r <;> simp

/-- The three shelves are pairwise disjoint. -/
lemma shelves_disjoint : shelf 0 ∩ shelf 1 = ∅ ∧ shelf 0 ∩ shelf 2 = ∅ ∧ shelf 1 ∩ shelf 2 = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · show {Rxn.m0a, Rxn.m0b} ∩ {Rxn.m1a, Rxn.m1b} = ∅
    ext r; cases r <;> simp
  · show {Rxn.m0a, Rxn.m0b} ∩ {Rxn.m2a, Rxn.m2b} = ∅
    ext r; cases r <;> simp
  · show {Rxn.m1a, Rxn.m1b} ∩ {Rxn.m2a, Rxn.m2b} = ∅
    ext r; cases r <;> simp

/-- **The example has the capacity for multiple positive steady states.**  The three shelves
carry the shelf-wise confluence vectors; the third moment relation is the extra datum which
makes the three-shelf system determined. -/
theorem hasCapacity : N.HasMultistationarityCapacity :=
  threeShelf_decomposition μ α (shelf 0) (shelf 1) (shelf 2) c w
    shelves_cover shelves_disjoint
    (by
      intro i r hr
      have hr' : r ∈ shelf i := by simpa only [threeShelf_eq] using hr
      exact sourcePairing_shelf i r hr')
    lower_balance upper_balance
    (by
      intro s
      simpa only [threeShelf_eq] using third_moment s)
    moment_det_ne_zero
    (fun r => by simp [α]) mu_ne_zero ⟨σ, mem_stoichSubspace, sameSign⟩

end ThreeShelfExample

end Network
end CRNT

/-! ### Axiom audit of the principal results -/

#print axioms CRNT.Network.threeShelf_shelfBalances
#print axioms CRNT.Network.threeShelf_adaFeasible
#print axioms CRNT.Network.threeShelf_decomposition
#print axioms CRNT.Network.shelfMomentMatrix_det_ne_zero_iff
#print axioms CRNT.Network.shelfMomentMatrix_det_eq_zero_of_dependent
#print axioms CRNT.Network.shelfMomentMatrix_det_ne_zero_of_independent
#print axioms CRNT.Network.twoMomentRelations_haveNonzeroSolution
#print axioms CRNT.Network.threeShelf_momentSystem_nontrivial_of_dependent
#print axioms CRNT.Network.ThreeShelfExample.hasCapacity
