import CRNT.Stochastic.ComplexBalancedNonExplosion
import CRNT.Stochastic.ProductFormConvergence
import CRNT.Theorems.DeficiencyZero.HornCharacterization

/-!
# Stochastic consequences of the deficiency zero theorem

For a weakly reversible network of deficiency zero and every choice of positive rate constants
there is a positive complex-balanced equilibrium `c` (S5). Hence, for every `κ`:

* the stochastic mass-action system does not explode (`hasSum_transition_one_of_deficiencyZero`);
* the product-Poisson law `π_c` is invariant for the transition function
  (`exists_productPoisson_invariant_of_deficiencyZero`; Anderson–Craciun–Kurtz 2010, Theorem 4.1,
  in dynamic form);
* if the network is also conservative, from every initial count the transition probabilities
  converge to the normalized product form on the reachable class
  (`exists_tendsto_transition_productPoisson_of_deficiencyZero`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Weakly reversible deficiency-zero networks are non-explosive** for every choice of rates. -/
theorem hasSum_transition_one_of_deficiencyZero (N : Network S) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) (κ : RateConstants N) {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 := by
  obtain ⟨c, hc, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  exact N.hasSum_transition_one_of_complexBalanced κ hc hcb ht n

/-- **Anderson–Craciun–Kurtz, dynamic form.** For a weakly reversible deficiency-zero network and
every choice of rates, some positive product-Poisson law is invariant for the transition function. -/
theorem exists_productPoisson_invariant_of_deficiencyZero (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (κ : RateConstants N) :
    ∃ c : Concentration S, c.Positive ∧ N.IsComplexBalanced κ c ∧
      ∀ t, 0 ≤ t → ∀ m, ∑' n, productPoissonPMF c n * N.transition κ t n m =
        productPoissonPMF c m := by
  obtain ⟨c, hc, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  exact ⟨c, hc, hcb, fun t ht m =>
    N.tsum_productPoisson_mul_transition κ (fun s => (hc s).le) hcb ht m⟩

/-- **Convergence to the product form for conservative weakly reversible deficiency-zero
networks**, for every choice of rates and every initial count. -/
theorem exists_tendsto_transition_productPoisson_of_deficiencyZero (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (hcons : N.IsConservative)
    (κ : RateConstants N) :
    ∃ c : Concentration S, c.Positive ∧ N.IsComplexBalanced κ c ∧
      ∀ n m, (N.jumpSystem κ).ReachPos n m →
        Tendsto (fun t => N.transition κ t n m) atTop
          (𝓝 (productPoissonPMF c m / ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x)) := by
  obtain ⟨c, hc, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  exact ⟨c, hc, hcb, fun n m hm =>
    N.tendsto_transition_productPoisson_of_conservative κ hwr hcons hc hcb hm⟩

/-- **Convergence to the product form for weakly reversible deficiency-zero networks** (no
conservation law), for every choice of rates and every initial count: total variation
convergence to the normalized product form on the reachable class, which is the unique
stationary distribution on that class. -/
theorem exists_tendsto_l1_productPoisson_of_deficiencyZero (N : Network S)
    (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) (κ : RateConstants N) :
    ∃ c : Concentration S, c.Positive ∧ N.IsComplexBalanced κ c ∧ ∀ n,
      Tendsto (fun t => ∑' m, |N.transition κ t n m -
        N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x|) atTop (𝓝 0) := by
  obtain ⟨c, hc, hcb⟩ := N.exists_isComplexBalanced hwr hδ κ
  exact ⟨c, hc, hcb, fun n => N.tendsto_l1_transition_productPoisson κ hwr hc hcb n⟩

end Network
end CRNT
