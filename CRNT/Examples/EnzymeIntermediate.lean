import CRNT.Examples.Enzyme
import CRNT.Reduction.NetworkDrainage

set_option backward.isDefEq.respectTransparency false

/-!
# Intermediate elimination for `E + S ⇌ ES → E + P`

The complex `ES` is a non-interacting intermediate that reaches the non-intermediate complex
`E + P`, so `intermediate_steadyState_unique` applies: wherever `ES` is at steady state its
concentration is the unique solution of the linear intermediate equation, and it is positive
when the inflow `k₁ [E][S]` is.  Non-vacuity instance for the network form of Feliu–Wiuf.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.Enzyme

open CRNT CRNT.Network Species

theorem interComplex_ES : interComplex ES = cESbound := by
  funext s; cases s <;> simp [interComplex, cESbound]

theorem nonInteracting_ES : N.NonInteracting {ES} := by
  intro c hc
  simp only [complexes, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> cases r <;>
    first
    | exact Or.inl ⟨ES, Finset.mem_singleton_self _, by rw [interComplex_ES]; rfl⟩
    | exact Or.inr fun k hk => by
        rw [Finset.mem_singleton] at hk; subst hk; simp [N, rxn, cES_sub, cEP]

theorem reaches_ES : ∀ j ∈ ({ES} : Finset Species), ∃ c : Complex Species,
    (∀ i ∈ ({ES} : Finset Species), c ≠ interComplex i) ∧ N.Reaches (interComplex j) c := by
  intro j hj
  rw [Finset.mem_singleton] at hj; subst hj
  refine ⟨cEP, fun i hi => ?_, Relation.ReflTransGen.single ⟨Rxn.catalyze, ?_, rfl⟩⟩
  · rw [Finset.mem_singleton] at hi; subst hi
    intro h; have := congrFun h ES; simp [cEP, interComplex] at this
  · rw [interComplex_ES]; rfl

/-- Wherever `ES` is at steady state, its concentration is the unique solution of the intermediate
equation, positive when the inflow is positive. -/
theorem enzyme_intermediate (κ : N.RateConstants) (x : Concentration Species)
    (hss : N.massActionVectorField κ x ES = 0) :
    (∀ v : ({ES} : Finset Species) → ℝ,
      Elimination.op (N.aCoef κ {ES}) (N.eCoef κ {ES}) v = (fun i : ({ES} : Finset Species) => N.bInflow κ {ES} i x) →
        v = fun j : ({ES} : Finset Species) => x j) ∧
    ((∀ i ∈ ({ES} : Finset Species), 0 < N.bInflow κ {ES} i x) →
      ∀ i ∈ ({ES} : Finset Species), 0 < x i) :=
  N.intermediate_steadyState_unique κ nonInteracting_ES reaches_ES x (fun i hi => by
    rw [Finset.mem_singleton] at hi; subst hi; exact hss)

end CRNT.Examples.Enzyme
