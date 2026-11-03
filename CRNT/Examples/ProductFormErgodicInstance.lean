import CRNT.Stochastic.ProductFormErgodic

/-!
# Instance of `tendsto_transition_productPoisson`

`X ⇌ Y` with unit rates is weakly reversible with the positive complex-balanced equilibrium
`c = (1, 1)`; the one-molecule counts `{X, Y}` form a finite closed irreducible class, so the
transition probabilities converge to the normalized product form on it (`converges`).
-/

namespace CRNT
namespace Examples
namespace IsomerizationErgodic

open Network

/-- The count (or complex) with one molecule of species `i`. -/
def e (i : Fin 2) : Fin 2 → ℕ := fun s => if s = i then 1 else 0

/-- `X ⇌ Y`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨e 0, e 1⟩ else ⟨e 1, e 0⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

def c : Concentration (Fin 2) := fun _ => 1

theorem weaklyReversible : net.WeaklyReversible := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, by simp, by simp⟩
  · exact Relation.ReflTransGen.single ⟨0, by simp, by simp⟩

theorem complexBalanced : net.IsComplexBalanced κ c := by
  intro z _
  simp only [inflow, outflow, Fin.sum_univ_two, massActionRate, Complex.massActionMonomial, κ, c]
  simp only [Fin.isValue, ↓reduceIte, one_pow, Finset.prod_const_one, mul_one, one_ne_zero]
  ring

theorem c_pos : c.Positive := fun _ => one_pos

def K : Finset (Fin 2 → ℕ) := {e 0, e 1}

theorem next_e (i : Fin 2) (r : net.R) (hr : 0 < net.stochasticMassActionRate κ (e i) r) :
    net.jumpNextCount (e i) r ∈ K := by
  have hen : net.Enabled (e i) r := by
    by_contra h
    exact (ne_of_gt hr) (net.stochasticMassActionRate_eq_zero_of_not_enabled κ _ r h)
  simp only [K, Finset.mem_insert, Finset.mem_singleton]
  fin_cases i <;> fin_cases r
  · right; funext s; fin_cases s <;> simp [jumpNextCount, e]
  · exfalso; have := hen 1; simp [e] at this
  · exfalso; have := hen 0; simp [e] at this
  · left; funext s; fin_cases s <;> simp [jumpNextCount, e]

theorem closedOn : (net.jumpSystem κ).ClosedOn K := by
  intro a ha r hr
  simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact next_e 0 r hr
  · exact next_e 1 r hr

theorem step (i j : Fin 2) (r : net.R) (hsrc : (net.reaction r).source = e i)
    (htgt : (net.reaction r).target = e j) : (net.jumpSystem κ).ReachPos (e i) (e j) := by
  have h := net.reachPos_add_of_reaches κ 0 (c := e i) (d := e j)
    (Relation.ReflTransGen.single ⟨r, hsrc, htgt⟩)
  simpa using h

theorem irreducible : ∀ a ∈ K, ∀ b ∈ K, (net.jumpSystem κ).ReachPos a b := by
  have h01 := step 0 1 0 (by simp) (by simp)
  have h10 := step 1 0 1 (by simp) (by simp)
  intro a ha b hb
  simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact h01
  · exact h10
  · exact Relation.ReflTransGen.refl

/-- **Convergence to the product form for `X ⇌ Y` on the one-molecule class.** -/
theorem converges : ∀ a ∈ K, ∀ b ∈ K, Filter.Tendsto (fun t => net.transition κ t a b)
    Filter.atTop (nhds (productPoissonPMF c b / ∑ x ∈ K, productPoissonPMF c x)) :=
  net.tendsto_transition_productPoisson κ weaklyReversible c_pos complexBalanced closedOn
    ⟨e 0, by simp [K]⟩ irreducible

end IsomerizationErgodic
end Examples
end CRNT
