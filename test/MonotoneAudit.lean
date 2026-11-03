import CRNT.Dynamics.CooperativeNetworks
import CRNT.Reduction.LinearElimination
import CRNT.Reduction.DrainedIntermediateBlock

#print axioms CRNT.Monotone.hasDerivAt_posPart_sq
#print axioms CRNT.Monotone.kamke_comparison
#print axioms CRNT.Network.massAction_kamkeOn_of_cooperative
#print axioms CRNT.Network.massAction_order_preserving_of_cooperative

namespace MonotoneAudit
open CRNT

/-- `∅ → A`, `A → B`, `B → ∅` (species `0 = A`, `1 = B`). -/
def chain : Network (Fin 2) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0, 0], ![1, 0]⟩ else if r = 1 then ⟨![1, 0], ![0, 1]⟩
    else ⟨![0, 1], ![0, 0]⟩⟩

/-- Non-vacuity: the production–conversion–degradation chain is cooperative. -/
example : chain.IsCooperativeNetwork := by
  intro r i hneg j hj
  have h : ∀ r : Fin 3, ∀ i j : Fin 2, j ≠ i → chain.reactionVector r i < 0 →
      (chain.reaction r).source j = 0 := by
    intro r i j hj h
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simp_all [chain, Network.reactionVector_apply]
    all_goals norm_num at h
  exact h r i j hj hneg

end MonotoneAudit

#print axioms CRNT.Elimination.nonneg_of_nonneg
#print axioms CRNT.Elimination.existsUnique_solution
#print axioms CRNT.Elimination.pos_of_pos
#print axioms CRNT.Elimination.solution_eq_nonneg_combination
#print axioms CRNT.Elimination.eliminated_eq_monomial_combination

/-- Non-vacuity of drainage: the chain `Y₀ → Y₁ → (exit)` on two intermediates. -/
example : CRNT.Elimination.Drained (ι := Fin 2) (fun i j => if i = 1 ∧ j = 0 then 1 else 0)
    (fun j => if j = 1 then 1 else 0) := by
  intro N hN
  by_cases h1 : (1 : Fin 2) ∈ N
  · exact ⟨1, h1, Or.inl (by simp)⟩
  · obtain ⟨j, hj⟩ := hN
    have : j = 0 := by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h
      · exact h
      · exact absurd (h ▸ hj) h1
    subst this
    exact ⟨0, hj, Or.inr ⟨1, h1, by simp⟩⟩

#print axioms CRNT.Elimination.isUnit_det_opMatrix
#print axioms CRNT.Elimination.drainedBlock_eliminated_nonneg
#print axioms CRNT.Elimination.drainedBlock_eliminated_pos
