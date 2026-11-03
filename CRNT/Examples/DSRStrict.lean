import CRNT.Multistationarity.DSRCriterion

/-!
# The DSR condition is strictly weaker than the true-SR condition

Species `A, B` (indices `0, 1`), irreversible reactions `A → B` and `A → 2B`.

* The true-SR graph has the cycle `A — (A → B) — B — (A → 2B) — A`, which is even (no c-pairs)
  and not an s-cycle (`1 · 2 ≠ 1 · 1`), so the true-SR criterion fails (`not_trueSR`).
* `B` is a reactant of no reaction, so no cycle of the DSR graph exists (every cycle visits `B`,
  which would have to enter its next reaction as a reactant), and the DSR condition holds
  vacuously (`dsr`).
* Hence the fully open network is concordant (`concordant`): every weakly monotonic kinetics on it
  is injective — a conclusion the true-SR theorem does not give for this network.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Examples
namespace DSRStrict

open Network

/-- `A → B`, `A → 2B`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 0], ![0, 1]⟩ else ⟨![1, 0], ![0, 2]⟩⟩

theorem source_B (r : net.R) : (net.reaction r).source 1 = 0 := by
  fin_cases r <;> rfl

theorem sep : net.ReactantProductSeparated := by
  intro r s hs
  fin_cases r <;> fin_cases s <;> simp_all

theorem flows : net.FlowsAreSingletons := by
  intro r hr
  exfalso
  fin_cases r <;> rcases hr with h | h <;>
    first
    | (have := congrFun h 0; simp at this; done)
    | (have := congrFun h 1; simp at this)

theorem not_flow (r : net.R) : ¬ net.IsFlowChannel r := by
  intro hr
  fin_cases r <;> rcases hr with h | h <;>
    first
    | (have := congrFun h 0; simp at this; done)
    | (have := congrFun h 1; simp at this)

/-- Every true-SR cycle visits `B`. -/
theorem visits_B {n : ℕ} (C : net.TrueSRCycle n) : ∃ i, C.species i = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ i, C.species i = 0 := fun i => by
    have := h i
    rcases (show ∀ q : Fin 2, q = 0 ∨ q = 1 by decide) (C.species i) with h' | h'
    · exact h'
    · exact absurd h' this
  have hn := C.nontrivial
  have := C.species_injective (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩)
    (by rw [h0, h0])
  simp at this

/-- **No cycle of the DSR graph.** -/
theorem not_oriented {n : ℕ} (C : net.TrueSRCycle n) : ¬ C.Oriented := by
  intro hC
  obtain ⟨i, hi⟩ := visits_B C
  obtain ⟨r, -, hr⟩ := hC i
  have hocc := (C.leftEdge i).occurs
  rw [C.left_species i, hi, hr, source_B] at hocc
  exact hocc rfl

theorem dsr : net.DSRCriterion :=
  ⟨fun C hC _ => absurd hC (not_oriented C), fun C _ hC _ _ _ => absurd hC (not_oriented C)⟩

/-- The two reactions are different true reactions. -/
theorem not_same : ¬ net.SameTrueReaction 0 1 := by
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · have := congrFun h 1
    simp at this
  · have := congrFun h 0
    simp at this

theorem rv00 : net.reactionVector 0 0 ≠ 0 := by simp [reactionVector_apply]
theorem rv01 : net.reactionVector 0 1 ≠ 0 := by simp [reactionVector_apply]
theorem rv10 : net.reactionVector 1 0 ≠ 0 := by simp [reactionVector_apply]
theorem rv11 : net.reactionVector 1 1 ≠ 0 := by simp [reactionVector_apply]

/-- The even, non-s-cycle `A — (A → B) — B — (A → 2B) — A`. -/
noncomputable def badCycle : net.TrueSRCycle 2 where
  nontrivial := le_rfl
  species := ![0, 1]
  reaction := ![net.trueReaction 0, net.trueReaction 1]
  leftEdge := ![net.bcEdge 0 (not_flow 0) 0 rv00, net.bcEdge 1 (not_flow 1) 1 rv11]
  rightEdge := ![net.bcEdge 0 (not_flow 0) 1 rv01, net.bcEdge 1 (not_flow 1) 0 rv10]
  left_species := by intro i; fin_cases i <;> rfl
  left_reaction := by intro i; fin_cases i <;> rfl
  right_species := by intro i; fin_cases i <;> rfl
  right_reaction := by intro i; fin_cases i <;> rfl
  species_injective := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  reaction_injective := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd (Quotient.exact h) not_same
    · exact absurd (Quotient.exact h.symm) not_same
    · rfl

theorem badCycle_even : badCycle.Even := by
  classical
  have : badCycle.numCPairs = 0 := by
    unfold TrueSRCycle.numCPairs
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    fin_cases i
    · have := congrFun hi 0
      simp [badCycle, bcEdge, bcEndpoint] at this
    · have := congrFun hi 0
      simp [badCycle, bcEdge, bcEndpoint] at this
  unfold TrueSRCycle.Even
  rw [this]
  exact ⟨0, rfl⟩

theorem badCycle_not_sCycle : ¬ badCycle.SCycle := by
  unfold TrueSRCycle.SCycle
  simp [badCycle, Fin.prod_univ_two, TrueSREdge.coeff, bcEdge, bcEndpoint]

/-- **The true-SR criterion fails.** -/
theorem not_trueSR : ¬ net.TrueSRStrongCriterion :=
  fun h => badCycle_not_sCycle (h.1 badCycle badCycle_even)

/-- **The fully open network is concordant**, by the DSR theorem. -/
theorem concordant : net.fullyOpen.Concordant :=
  net.concordant_fullyOpen_of_dsrCriterion sep flows dsr

end DSRStrict
end Examples
end CRNT
