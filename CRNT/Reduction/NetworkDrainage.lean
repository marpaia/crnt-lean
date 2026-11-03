import CRNT.Reduction.DrainedIntermediateBlock
import CRNT.Persistence.WeaklyReversibleField

/-!
# Drainage from the network's intermediate structure

For a network `N`, rate constants `κ`, and a set `I` of intermediate species, the coefficients
of the intermediate operator of `CRNT.Elimination` are read off the network:

* `aCoef κ I i j` — total rate constant of reactions `Y_j → Y_i` (`Y_i` the single-species
  complex of `i`);
* `eCoef κ I j` — total rate constant of reactions from `Y_j` to complexes that are not
  intermediate complexes.

`drained_of_reaches`: if every intermediate complex reaches some non-intermediate complex, the
coefficients satisfy `Elimination.Drained` (Feliu–Wiuf 2013, the hypothesis of Theorem 1).  So the
invertibility of the intermediate block (`Elimination.isUnit_det_opMatrix`) and the positivity of
eliminated intermediates follow from a reachability condition on the reaction graph.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The single-species complex of `i`. -/
def interComplex (i : S) : Complex S := fun s => if s = i then 1 else 0

variable (N : Network S)

/-- Total rate constant of the reactions `Y_j → Y_i`. -/
noncomputable def aCoef (κ : N.RateConstants) (I : Finset S) (i j : I) : ℝ :=
  ∑ r, if (N.reaction r).source = interComplex (j : S) ∧
      (N.reaction r).target = interComplex (i : S) then κ.k r else 0

/-- Total rate constant of the reactions from `Y_j` to non-intermediate complexes. -/
noncomputable def eCoef (κ : N.RateConstants) (I : Finset S) (j : I) : ℝ :=
  ∑ r, if (N.reaction r).source = interComplex (j : S) ∧
      ∀ i ∈ I, (N.reaction r).target ≠ interComplex i then κ.k r else 0

theorem aCoef_nonneg (κ : N.RateConstants) (I : Finset S) (i j : I) : 0 ≤ N.aCoef κ I i j :=
  sum_nonneg fun r _ => by split_ifs <;> [exact (κ.positive r).le; exact le_rfl]

theorem eCoef_nonneg (κ : N.RateConstants) (I : Finset S) (j : I) : 0 ≤ N.eCoef κ I j :=
  sum_nonneg fun r _ => by split_ifs <;> [exact (κ.positive r).le; exact le_rfl]

/-- **Drainage from reachability.** If every intermediate complex reaches a complex that is not an
intermediate complex, the intermediate operator of the network is drained. -/
theorem drained_of_reaches (κ : N.RateConstants) (I : Finset S)
    (h : ∀ j ∈ I, ∃ c : Complex S, (∀ i ∈ I, c ≠ interComplex i) ∧ N.Reaches (interComplex j) c) :
    Elimination.Drained (N.aCoef κ I) (N.eCoef κ I) := by
  classical
  intro M ⟨j₀, hj₀⟩
  obtain ⟨c₀, hc₀, hreach⟩ := h j₀ j₀.2
  -- `P c`: `c` is the intermediate complex of a member of `M`
  set P : Complex S → Prop := fun c => ∃ j ∈ M, c = interComplex (j : S) with hP
  obtain ⟨c', d', ⟨q, hqs, hqt⟩, hc', hd'⟩ :=
    Persistence.exists_crossing_of_reflTransGen (fun c => ¬ P c) hreach
      (by simp only [not_not]; exact ⟨j₀, hj₀, rfl⟩)
      (fun ⟨j, _, hj⟩ => hc₀ j j.2 hj)
  simp only [not_not] at hc'
  obtain ⟨j, hjM, rfl⟩ := hc'
  refine ⟨j, hjM, ?_⟩
  by_cases hint : ∃ i ∈ I, d' = interComplex i
  · obtain ⟨i, hiI, rfl⟩ := hint
    right
    refine ⟨⟨i, hiI⟩, fun hiM => hd' ⟨⟨i, hiI⟩, hiM, rfl⟩, ?_⟩
    refine lt_of_lt_of_le (κ.positive q) ?_
    have := single_le_sum (f := fun r => if (N.reaction r).source = interComplex (j : S) ∧
        (N.reaction r).target = interComplex i then κ.k r else 0)
      (fun r _ => by split_ifs <;> [exact (κ.positive r).le; exact le_rfl]) (mem_univ q)
    simpa [aCoef, hqs, hqt] using this
  · left
    push Not at hint
    refine lt_of_lt_of_le (κ.positive q) ?_
    have := single_le_sum (f := fun r => if (N.reaction r).source = interComplex (j : S) ∧
        ∀ i ∈ I, (N.reaction r).target ≠ interComplex i then κ.k r else 0)
      (fun r _ => by split_ifs <;> [exact (κ.positive r).le; exact le_rfl]) (mem_univ q)
    simp only [hqs, hqt, true_and] at this
    rw [if_pos hint] at this
    exact this

/-- Under the reachability condition the intermediate block is invertible. -/
theorem isUnit_det_intermediateBlock (κ : N.RateConstants) (I : Finset S)
    (h : ∀ j ∈ I, ∃ c : Complex S, (∀ i ∈ I, c ≠ interComplex i) ∧ N.Reaches (interComplex j) c) :
    IsUnit (Elimination.opMatrix (N.aCoef κ I) (N.eCoef κ I)).det :=
  Elimination.isUnit_det_opMatrix (N.aCoef_nonneg κ I) (N.eCoef_nonneg κ I)
    (N.drained_of_reaches κ I h)

/-- Inflow into `Y_i` from intermediate-free complexes. -/
noncomputable def bInflow (κ : N.RateConstants) (I : Finset S) (i : S) (x : Concentration S) : ℝ :=
  ∑ r, if (∀ k ∈ I, (N.reaction r).source k = 0) ∧ (N.reaction r).target = interComplex i then
      κ.k r * (N.reaction r).source.massActionMonomial x else 0

/-- Non-interacting intermediates: every complex is an intermediate complex or free of
intermediates. -/
def NonInteracting (I : Finset S) : Prop :=
  ∀ c ∈ N.complexes, (∃ k ∈ I, c = interComplex k) ∨ ∀ k ∈ I, c k = 0

theorem interComplex_apply_self (i : S) : interComplex i i = 1 := by simp [interComplex]

theorem interComplex_injective : Function.Injective (interComplex (S := S)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [interComplex, hij] at this

theorem massActionMonomial_interComplex (i : S) (x : Concentration S) :
    (interComplex i).massActionMonomial x = x i := by
  simp [Complex.massActionMonomial, interComplex]

/-- Coordinate of a complex at an intermediate, under non-interaction. -/
theorem coord_eq_ite_of_dichotomy {I : Finset S} {c : Complex S}
    (hc : (∃ k ∈ I, c = interComplex k) ∨ ∀ k ∈ I, c k = 0) {i : S} (hi : i ∈ I) :
    (c i : ℝ) = if c = interComplex i then 1 else 0 := by
  rcases hc with ⟨k, -, rfl⟩ | hz
  · by_cases hki : k = i
    · subst hki; simp [interComplex]
    · rw [if_neg (fun h => hki (interComplex_injective h))]
      simp [interComplex, Ne.symm hki]
  · rw [hz i hi, if_neg]
    · simp
    · intro h; have := hz i hi; rw [h, interComplex_apply_self] at this; exact one_ne_zero this

/-- **Intermediate field identity** (Feliu–Wiuf 2013, Section 2): for non-interacting
intermediates the rate of change of each intermediate is `b_i(x) - (L u)_i`, with `u` the vector
of intermediate concentrations. -/
theorem massActionVectorField_intermediate (κ : N.RateConstants) {I : Finset S}
    (hI : N.NonInteracting I) (x : Concentration S) (i : I) :
    N.massActionVectorField κ x i =
      N.bInflow κ I i x - Elimination.op (N.aCoef κ I) (N.eCoef κ I) (fun j : I => x j) i := by
  classical
  have hdich := fun r => hI _ (N.source_mem_complexes r)
  have hdicht := fun r => hI _ (N.target_mem_complexes r)
  -- left side, reaction by reaction
  have hL : N.massActionVectorField κ x i = ∑ r, κ.k r * (N.reaction r).source.massActionMonomial x *
      ((if (N.reaction r).target = interComplex (i : S) then 1 else 0) -
        (if (N.reaction r).source = interComplex (i : S) then 1 else 0)) := by
    rw [massActionVectorField_apply]
    refine sum_congr rfl fun r _ => ?_
    rw [reactionVector_apply, coord_eq_ite_of_dichotomy (hdicht r) i.2,
      coord_eq_ite_of_dichotomy (hdich r) i.2]
    simp only [massActionRate]
  -- total outflow coefficient
  have h1 : ∑ k : I, N.aCoef κ I k i + N.eCoef κ I i =
      ∑ r, if (N.reaction r).source = interComplex (i : S) then κ.k r else 0 := by
    simp only [aCoef, eCoef]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    by_cases hs : (N.reaction r).source = interComplex (i : S)
    · simp only [hs, true_and, if_true]
      by_cases ht : ∃ k ∈ I, (N.reaction r).target = interComplex k
      · obtain ⟨k, hk, hkt⟩ := ht
        rw [Fintype.sum_eq_single ⟨k, hk⟩ (fun k' hk' => by
          rw [if_neg]; intro h; apply hk'; apply Subtype.ext
          exact interComplex_injective (h.symm.trans hkt))]
        rw [if_pos hkt, if_neg (by push Not; exact ⟨k, hk, hkt⟩), add_zero]
      · push Not at ht
        rw [sum_eq_zero (fun (k : I) _ => if_neg (ht k k.2)), if_pos ht, zero_add]
    · simp [hs]
  -- conversion inflow
  have h2 : ∑ j : I, N.aCoef κ I i j * x j =
      ∑ r, if (N.reaction r).target = interComplex (i : S) ∧
        ∃ k ∈ I, (N.reaction r).source = interComplex k then
          κ.k r * (N.reaction r).source.massActionMonomial x else 0 := by
    simp only [aCoef, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    by_cases hs : ∃ k ∈ I, (N.reaction r).source = interComplex k
    · obtain ⟨k, hk, hks⟩ := hs
      rw [Fintype.sum_eq_single ⟨k, hk⟩ (fun k' hk' => by
        rw [ite_mul, zero_mul, if_neg]; intro h; apply hk'; apply Subtype.ext
        exact interComplex_injective (h.1.symm.trans hks))]
      by_cases ht : (N.reaction r).target = interComplex (i : S)
      · rw [if_pos ⟨hks, ht⟩, if_pos ⟨ht, k, hk, hks⟩, hks, massActionMonomial_interComplex]
      · rw [if_neg (fun h => ht h.2), if_neg (fun h => ht h.1), zero_mul]
    · push Not at hs
      rw [sum_eq_zero (fun j _ => by rw [if_neg (fun h => hs j j.2 h.1), zero_mul]),
        if_neg (fun ⟨_, k, hk, h⟩ => hs k hk h)]
  -- assemble
  have hnz : ∀ k ∈ I, ¬ ∀ k' ∈ I, interComplex k k' = 0 := fun k hk h => by
    have := h k hk; rw [interComplex_apply_self] at this; exact one_ne_zero this
  rw [hL, Elimination.op, h1, sum_mul, h2, bInflow, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  by_cases ht : (N.reaction r).target = interComplex (i : S) <;>
    by_cases hs : (N.reaction r).source = interComplex (i : S)
  · -- a self-loop `Y_i → Y_i`
    have hex : ∃ k ∈ I, (N.reaction r).source = interComplex k := ⟨i, i.2, hs⟩
    have hnf : ¬ ((∀ k ∈ I, (N.reaction r).source k = 0) ∧
        (N.reaction r).target = interComplex (i : S)) := fun h => hnz i i.2 (hs ▸ h.1)
    rw [if_pos ht, if_pos hs, if_pos hs, if_neg hnf, if_pos ⟨ht, hex⟩, hs,
      massActionMonomial_interComplex]
    ring
  · rw [if_pos ht, if_neg hs, if_neg hs]
    rcases hdich r with ⟨k, hk, hks⟩ | hz
    · have hnf : ¬ ((∀ k ∈ I, (N.reaction r).source k = 0) ∧
          (N.reaction r).target = interComplex (i : S)) := fun h => hnz k hk (hks ▸ h.1)
      rw [if_neg hnf, if_pos ⟨ht, k, hk, hks⟩]; ring
    · have hnex : ¬ ((N.reaction r).target = interComplex (i : S) ∧
          ∃ k ∈ I, (N.reaction r).source = interComplex k) :=
        fun ⟨_, k, hk, h⟩ => hnz k hk (h ▸ hz)
      rw [if_pos ⟨hz, ht⟩, if_neg hnex]; ring
  · have hnf : ¬ ((∀ k ∈ I, (N.reaction r).source k = 0) ∧
        (N.reaction r).target = interComplex (i : S)) := fun h => ht h.2
    have hnex : ¬ ((N.reaction r).target = interComplex (i : S) ∧
        ∃ k ∈ I, (N.reaction r).source = interComplex k) := fun h => ht h.1
    rw [if_neg ht, if_pos hs, if_pos hs, if_neg hnf, if_neg hnex, hs,
      massActionMonomial_interComplex]
    ring
  · have hnf : ¬ ((∀ k ∈ I, (N.reaction r).source k = 0) ∧
        (N.reaction r).target = interComplex (i : S)) := fun h => ht h.2
    have hnex : ¬ ((N.reaction r).target = interComplex (i : S) ∧
        ∃ k ∈ I, (N.reaction r).source = interComplex k) := fun h => ht h.1
    rw [if_neg ht, if_neg hs, if_neg hs, if_neg hnf, if_neg hnex]; ring

/-- **Feliu–Wiuf 2013, Theorem 1 (network form).** For non-interacting intermediates, each of
which reaches a non-intermediate complex: at any state where all intermediates are at steady
state, the intermediate concentrations are the unique solution of `L u = b(x)`; with positive
inflows they are positive. -/
theorem intermediate_steadyState_unique (κ : N.RateConstants) {I : Finset S}
    (hI : N.NonInteracting I)
    (hreach : ∀ j ∈ I, ∃ c : Complex S, (∀ i ∈ I, c ≠ interComplex i) ∧
      N.Reaches (interComplex j) c)
    (x : Concentration S) (hss : ∀ i ∈ I, N.massActionVectorField κ x i = 0) :
    (∀ v : I → ℝ, Elimination.op (N.aCoef κ I) (N.eCoef κ I) v = (fun i : I => N.bInflow κ I i x) →
      v = fun j : I => x j) ∧
    ((∀ i ∈ I, 0 < N.bInflow κ I i x) → ∀ i ∈ I, 0 < x i) := by
  have hdr := N.drained_of_reaches κ I hreach
  have hop : Elimination.op (N.aCoef κ I) (N.eCoef κ I) (fun j : I => x j) =
      fun i : I => N.bInflow κ I i x := by
    funext i
    have := N.massActionVectorField_intermediate κ hI x i
    rw [hss i i.2] at this
    linarith
  refine ⟨fun v hv => ?_, fun hb i hi => ?_⟩
  · obtain ⟨u, -, huniq⟩ := Elimination.existsUnique_solution (N.aCoef_nonneg κ I)
      (N.eCoef_nonneg κ I) hdr (fun i : I => N.bInflow κ I i x)
    exact (huniq v hv).trans (huniq _ hop).symm
  · exact Elimination.pos_of_pos (N.aCoef_nonneg κ I) (N.eCoef_nonneg κ I) hdr hop
      (fun i => hb i i.2) ⟨i, hi⟩

end Network
end CRNT
