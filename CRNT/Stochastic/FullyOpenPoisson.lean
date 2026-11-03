import CRNT.Stochastic.JahnkeHuisinga
import CRNT.Stochastic.FullyOpenGeometric
import CRNT.Stochastic.MonomolecularLLN

/-!
# The stationary law of monomolecular fully open networks is Poisson

Let every original reaction of `N` have at most one molecule in its source and target and not
increase the number of molecules (for example `X_i → X_j`, `X_i → 0`). For every choice of rates of
the fully open extension and every positive equilibrium `μ*` of its mass-action equation, the
product-Poisson law with mean `μ*` is the unique stationary distribution of the chain
(`fullyOpen_stationary_eq_poisson`), and the law of the chain converges to it in total variation
from every count (`fullyOpen_tendsto_poisson`). Invariance is Jahnke–Huisinga with a constant mean;
uniqueness is `fullyOpen_ergodic`.
-/

open Filter Set
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem fullyOpen_isMonomolecular (N : Network S) (hmono : N.IsMonomolecular) :
    N.fullyOpen.IsMonomolecular := by
  intro r
  rcases r with r | s | s
  · exact hmono r
  · show ∑ t, (Complex.zero : Complex S) t ≤ 1 ∧ ∑ t, singletonComplex s t ≤ 1
    simp [Complex.zero, singletonComplex]
  · show ∑ t, singletonComplex s t ≤ 1 ∧ ∑ t, (Complex.zero : Complex S) t ≤ 1
    simp [Complex.zero, singletonComplex]

/-- The Poisson law at an equilibrium is invariant. -/
theorem tsum_productPoisson_mul_transition_of_equilibrium (N : Network S) (κ : RateConstants N)
    (hmono : N.IsMonomolecular) {μ : Concentration S} (hμ : μ.Positive)
    (heq : N.massActionVectorField κ μ = 0) {t : ℝ} (ht : 0 ≤ t) (m : S → ℕ) :
    ∑' n, productPoissonPMF μ n * N.transition κ t n m = productPoissonPMF μ m := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have h : ∀ n, productPoissonPMF μ n * N.transition κ 0 n m =
        if n = m then productPoissonPMF μ m else 0 := by
      intro n; rw [transition_zero]; split_ifs with h <;> simp [h]
    simp only [h, tsum_ite_eq]
  · exact N.jahnke_huisinga κ hmono hpos (fun _ => μ) (fun _ _ => hμ) continuousOn_const
      (fun _ _ => by rw [heq]; exact hasDerivAt_const _ _) m

/-- **The stationary law of a monomolecular fully open network is Poisson.** -/
theorem fullyOpen_stationary_eq_poisson (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmono : N.IsMonomolecular)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s)
    {μ : Concentration S} (hμ : μ.Positive) (heq : N.fullyOpen.massActionVectorField κ μ = 0) :
    ∀ ν : (S → ℕ) → ℝ, (∀ m, 0 ≤ ν m) → HasSum ν 1 →
      (∀ t, 0 ≤ t → ∀ m, ∑' x, ν x * N.fullyOpen.transition κ t x m = ν m) →
        ν = productPoissonPMF μ := by
  obtain ⟨π, -, hπ1, hπinv, -, huniq⟩ := N.fullyOpen_ergodic κ hmol
  have hP := huniq (productPoissonPMF μ) (fun m => productPoissonPMF_nonneg (fun s => (hμ s).le) m)
    (hasSum_productPoissonPMF fun s => (hμ s).le)
    (fun t ht m => N.fullyOpen.tsum_productPoisson_mul_transition_of_equilibrium κ
      (N.fullyOpen_isMonomolecular hmono) hμ heq ht m)
  intro ν hν0 hν1 hνinv
  rw [huniq ν hν0 hν1 hνinv, hP]

/-- **Convergence to the Poisson law** for monomolecular fully open networks. -/
theorem fullyOpen_tendsto_poisson (N : Network S) (κ : RateConstants N.fullyOpen)
    (hmono : N.IsMonomolecular)
    (hmol : ∀ r : N.R, ∑ s, (N.reaction r).target s ≤ ∑ s, (N.reaction r).source s)
    {μ : Concentration S} (hμ : μ.Positive) (heq : N.fullyOpen.massActionVectorField κ μ = 0)
    (n : S → ℕ) :
    Tendsto (fun t => ∑' m, |N.fullyOpen.transition κ t n m - productPoissonPMF μ m|) atTop
      (𝓝 0) := by
  obtain ⟨π, hπ0, hπ1, hπinv, hconv, -⟩ := N.fullyOpen_ergodic κ hmol
  have h := N.fullyOpen_stationary_eq_poisson κ hmono hmol hμ heq π (fun m => (hπ0 m).le) hπ1
    hπinv
  rw [← h]
  exact hconv n

end Network

namespace Examples
namespace PoissonFlow

open Network

/-- The network with one species and no reactions; its fully open extension is `0 ⇌ X`. -/
def net : Network Unit := ⟨Empty, inferInstance, inferInstance, Empty.elim⟩

def κ : RateConstants net.fullyOpen := ⟨fun _ => 1, fun _ => one_pos⟩

theorem equilibrium : net.fullyOpen.massActionVectorField κ (fun _ => 1) = 0 := by
  funext u
  rw [massActionVectorField_apply]
  have hsplit : ∀ g : net.fullyOpen.R → ℝ, ∑ x, g x = ∑ r : net.R, g (Sum.inl r) +
      (∑ s : Unit, g (Sum.inr (Sum.inl s)) + ∑ s : Unit, g (Sum.inr (Sum.inr s))) := fun g =>
    (Fintype.sum_sum_type (f := g)).trans (by rw [Fintype.sum_sum_type])
  rw [hsplit]
  have e1 : ∑ r : net.R, net.fullyOpen.massActionRate κ (Sum.inl r) (fun _ => 1) *
      net.fullyOpen.reactionVector (Sum.inl r) u = 0 := Finset.sum_eq_zero fun r _ => r.elim
  have e2 : ∀ s : Unit, net.fullyOpen.massActionRate κ (Sum.inr (Sum.inl s)) (fun _ => 1) *
      net.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) u = 1 := by
    intro s
    have hv : net.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) u =
        ((singletonComplex s u : ℕ) : ℝ) - ((Complex.zero : Complex Unit) u : ℝ) := rfl
    have hr : net.fullyOpen.massActionRate κ (Sum.inr (Sum.inl s)) (fun _ => 1) = 1 := by
      show κ.k _ * ∏ t, (fun _ : Unit => (1 : ℝ)) t ^ (Complex.zero : Complex Unit) t = 1
      simp [κ]
    rw [hv, hr]; simp [singletonComplex, Complex.zero]
  have e3 : ∀ s : Unit, net.fullyOpen.massActionRate κ (Sum.inr (Sum.inr s)) (fun _ => 1) *
      net.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) u = -1 := by
    intro s
    have hv : net.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) u =
        ((Complex.zero : Complex Unit) u : ℝ) - ((singletonComplex s u : ℕ) : ℝ) := rfl
    have hr : net.fullyOpen.massActionRate κ (Sum.inr (Sum.inr s)) (fun _ => 1) = 1 := by
      show κ.k _ * ∏ t, (fun _ : Unit => (1 : ℝ)) t ^ singletonComplex s t = 1
      simp [κ]
    rw [hv, hr]; simp [singletonComplex, Complex.zero]
  rw [e1, Finset.sum_congr rfl fun s _ => e2 s, Finset.sum_congr rfl fun s _ => e3 s]
  simp

/-- **`0 ⇌ X` with unit rates converges to Poisson(1)** from every count. -/
theorem tendsto_poisson (n : Unit → ℕ) :
    Tendsto (fun t => ∑' m, |net.fullyOpen.transition κ t n m - productPoissonPMF (fun _ => 1) m|)
      atTop (𝓝 0) :=
  net.fullyOpen_tendsto_poisson κ (fun r => r.elim) (fun r => r.elim) (fun _ => one_pos)
    equilibrium n

end PoissonFlow
end Examples

end CRNT
