import CRNT.Equilibria.ToricCriterion
import CRNT.Computation.StableComputation

#print axioms CRNT.ToricCriterion.mem_ker_iff
#print axioms CRNT.Network.hasToricSteadyStates_of_disjointKernelBasis

namespace ToricCriterionAudit
open CRNT

/-- `A → B`, `B → A`. -/
def revNet : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨![1, 0], ![0, 1]⟩
    else ⟨![0, 1], ![1, 0]⟩⟩

theorem revNet_r0 : revNet.reaction (0 : Fin 2) = ⟨![1, 0], ![0, 1]⟩ := rfl
theorem revNet_r1 : revNet.reaction (1 : Fin 2) = ⟨![0, 1], ![1, 0]⟩ := rfl
theorem revNet_sum (g : revNet.R → ℝ) : ∑ r, g r = g (0 : Fin 2) + g (1 : Fin 2) :=
  Fin.sum_univ_two g

/-- `Σ w = (-k₀ w₀ + k₁ w₁, k₀ w₀ - k₁ w₁)`. -/
def sig (k₀ k₁ : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun w := ![-k₀ * w 0 + k₁ * w 1, k₀ * w 0 - k₁ * w 1]
  map_add' u v := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by funext i; fin_cases i <;> simp <;> ring

theorem factor (κ : revNet.RateConstants) (x : Concentration (Fin 2)) :
    revNet.massActionVectorField κ x =
      sig (κ.k (0 : Fin 2)) (κ.k (1 : Fin 2))
        (fun j => CRNT.Complex.massActionMonomial (![![1, 0], ![0, 1]] j) x) := by
  funext s
  rw [Network.massActionVectorField_apply, revNet_sum]
  fin_cases s <;>
    simp [Network.massActionRate, Network.reactionVector, revNet_r0, revNet_r1,
      Complex.massActionMonomial, Fin.prod_univ_two, sig] <;> ring

/-- Non-vacuity of the toric criterion: `A ⇌ B` has a one-dimensional kernel spanned by the
positive vector `(k₁, k₀)`. -/
example (κ : revNet.RateConstants) : revNet.HasToricSteadyStates κ := by
  have hk0 := κ.positive (0 : Fin 2)
  have hk1 := κ.positive (1 : Fin 2)
  let B : ToricCriterion.DisjointPositiveBasis (Fin 2) 1 :=
    ⟨fun _ => 0, fun _ => ![κ.k (1 : Fin 2), κ.k (0 : Fin 2)],
      fun j => by fin_cases j <;> simp [hk0, hk1],
      fun i j h => absurd (Subsingleton.elim _ _) h⟩
  refine revNet.hasToricSteadyStates_of_disjointKernelBasis κ _ _ (factor κ) B ?_
  have hr : Set.range B.b = {![κ.k (1 : Fin 2), κ.k (0 : Fin 2)]} := Set.range_const
  rw [hr]
  ext w
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hw
    have h0 := congrFun hw 0
    simp [sig] at h0
    refine ⟨w 1 / κ.k (0 : Fin 2), ?_⟩
    funext j
    fin_cases j
    · simp; field_simp; linarith
    · simp; field_simp
  · rintro ⟨c, rfl⟩
    funext i
    fin_cases i <;> simp [sig] <;> ring

end ToricCriterionAudit

#print axioms CRNT.Computation.superadditive_of_outputOblivious
#print axioms CRNT.Computation.not_stablyComputes_max_of_outputOblivious
#print axioms CRNT.Computation.maxCRN_not_outputOblivious
#print axioms CRNT.Computation.initMax_add
