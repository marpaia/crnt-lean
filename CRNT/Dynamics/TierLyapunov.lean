import CRNT.Dynamics.TierPersistence
import CRNT.Theorems.DeficiencyZero.Stability

/-!
# Tier Lyapunov identity

The deterministic tier proof uses

`U(x) = 1 + Σ_s (x_s (log x_s - 1) + 1)`.

Up to the harmless leading constant, this is `relEntropy 1 x`.  This module proves the exact
mass-action derivative identity used in Proposition 4.6 of Anderson--Cappelletti--Kim--Nguyen:

`dU/dt = Σ_r κ_r x^(source r) log(x^(target r) / x^(source r))`.

Thus the remaining tier analysis can work directly with the same expression as the paper rather
than repeatedly expanding the ODE and the entropy chain rule.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The all-ones concentration used as the reference of the tier Lyapunov function. -/
def tierReference (S : Type) : S → ℝ := fun _ => 1

/-- The tier Lyapunov function.  The added `1` matches the convention in the tier literature and
has no effect on derivatives. -/
noncomputable def tierEntropy (x : Concentration S) : ℝ :=
  1 + relEntropy (tierReference S) x

/-- The monomial notation in `TierPersistence` is definitionally the ordinary mass-action
monomial. -/
@[simp] theorem tierMonomial_eq_massActionMonomial (x : Concentration S) (y : Complex S) :
    tierMonomial x y = y.massActionMonomial x :=
  rfl

/-- Log of a positive complex monomial. -/
theorem log_tierMonomial {x : Concentration S} (hx : x.Positive) (y : Complex S) :
    Real.log (tierMonomial x y) = ∑ s : S, (y s : ℝ) * Real.log (x s) := by
  rw [tierMonomial_eq_massActionMonomial, Complex.massActionMonomial,
    Real.log_prod (fun s _ => (pow_pos (hx s) _).ne')]
  exact Finset.sum_congr rfl fun s _ => Real.log_pow _ _

/-- Pairing `log x` with a reaction vector is the log of the target/source monomial ratio. -/
theorem log_pair_reactionVector (N : Network S) {x : Concentration S} (hx : x.Positive)
    (r : N.R) :
    (∑ s : S, Real.log (x s) * N.reactionVector r s) =
      Real.log (tierMonomial x (N.reaction r).target /
        tierMonomial x (N.reaction r).source) := by
  have htpos : 0 < tierMonomial x (N.reaction r).target := by
    simpa using Complex.massActionMonomial_pos hx (N.reaction r).target
  have hspos : 0 < tierMonomial x (N.reaction r).source := by
    simpa using Complex.massActionMonomial_pos hx (N.reaction r).source
  rw [Real.log_div htpos.ne' hspos.ne', log_tierMonomial hx, log_tierMonomial hx,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [reactionVector_apply]
  ring

/-- The exact tier-dissipation expression occurring in the deterministic permanence proof. -/
noncomputable def tierDissipation (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : ℝ :=
  ∑ r : N.R, κ.k r * tierMonomial x (N.reaction r).source *
    Real.log (tierMonomial x (N.reaction r).target /
      tierMonomial x (N.reaction r).source)

/-- The log-gradient paired with the mass-action vector field is exactly `tierDissipation`. -/
theorem log_pair_massActionVectorField_eq_tierDissipation (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    (∑ s : S, Real.log (x s) * N.massActionVectorField κ x s) =
      N.tierDissipation κ x := by
  rw [tierDissipation]
  simp only [massActionVectorField_apply, massActionRate]
  -- `Finset.sum_comm` needs a literal double sum; the inner sum is still under a product.
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ s : S, Real.log (x s) *
        (κ.k r * (N.reaction r).source.massActionMonomial x * N.reactionVector r s))
        = κ.k r * tierMonomial x (N.reaction r).source *
            (∑ s : S, Real.log (x s) * N.reactionVector r s) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [tierMonomial_eq_massActionMonomial]
              ring
    _ = κ.k r * tierMonomial x (N.reaction r).source *
          Real.log (tierMonomial x (N.reaction r).target /
            tierMonomial x (N.reaction r).source) := by
              rw [N.log_pair_reactionVector hx r]

/-- **Tier Lyapunov derivative identity.** Along any positive differentiable mass-action solution,
`tierEntropy` has derivative exactly `tierDissipation`. -/
theorem tierEntropy_hasDerivAt (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {t : ℝ} (hpos : Concentration.Positive (γ t))
    (hsol : ∀ s, HasDerivAt (fun τ => γ τ s)
      (N.massActionVectorField κ (γ t) s) t) :
    HasDerivAt (fun τ => tierEntropy (γ τ)) (N.tierDissipation κ (γ t)) t := by
  have href : Concentration.Positive (tierReference S : Concentration S) := fun _ => zero_lt_one
  have hchain := relEntropy_hasDerivAt href hpos hsol
  have hder :
      (∑ s : S, (Real.log (γ t s) - Real.log ((tierReference S) s)) *
        N.massActionVectorField κ (γ t) s) = N.tierDissipation κ (γ t) := by
    simp only [tierReference, Real.log_one, sub_zero]
    exact N.log_pair_massActionVectorField_eq_tierDissipation κ hpos
  have hrel : HasDerivAt (fun τ => relEntropy (tierReference S) (γ τ))
      (N.tierDissipation κ (γ t)) t := by
    -- `hchain` states the derivative in fully expanded form (rates times reaction-vector
    -- entries); fold it back into `massActionVectorField` before applying `hder`.
    simpa only [← reactionVector_apply, ← massActionVectorField_apply, hder] using hchain
  simpa [tierEntropy] using hrel.const_add 1

/-- Proposition-4.6-shaped analytic property: every transversal tier sequence eventually has
strictly negative tier dissipation, for every positive constant rate vector. -/
def TierDissipationEventuallyNegative (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, ∀ xs : ℕ → Concentration S,
    N.IsTransversalTierSequence xs →
      ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → N.tierDissipation κ (xs n) < 0

/-- Once eventual tier dissipation is known, the entropy derivative along a mass-action solution is
negative at every sampled state in the corresponding tail.  This is the direct bridge from the
sequence theorem to dynamical Lyapunov arguments. -/
theorem TierDissipationEventuallyNegative.derivative_negative {N : Network S}
    (h : N.TierDissipationEventuallyNegative) (κ : N.RateConstants)
    {xs : ℕ → Concentration S} (htier : N.IsTransversalTierSequence xs) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → N.tierDissipation κ (xs n) < 0 :=
  h κ xs htier

end Network
end CRNT
