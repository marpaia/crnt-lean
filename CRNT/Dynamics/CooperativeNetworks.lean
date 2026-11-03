import CRNT.Dynamics.MonotoneComparison
import CRNT.Multistationarity.InheritanceAddReactions
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Cooperative mass-action networks are monotone

A network is **cooperative** if every reaction that decreases a species `i` has a source
complex containing no species other than `i` (degradation-type and self-conversion reactions
`k i → …`). Then on the nonnegative orthant the mass-action vector field satisfies the Kamke
condition, so its flow preserves the componentwise order (Kamke; Hirsch–Smith; for reaction
networks Angeli–Sontag 2008).

Main results:
* `CRNT.Network.IsCooperativeNetwork`.
* `CRNT.Network.massAction_kamkeOn_of_cooperative`.
* `CRNT.Network.massAction_order_preserving_of_cooperative`: ordered initial conditions stay
  ordered while the solutions remain in a box `[0, M]^S`.
-/

namespace CRNT

namespace Network

open scoped BigOperators NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every reaction that consumes species `i` has a source complex supported on `{i}`. -/
def IsCooperativeNetwork (N : Network S) : Prop :=
  ∀ r i, N.reactionVector r i < 0 → ∀ j, j ≠ i → (N.reaction r).source j = 0

omit [DecidableEq S] in
theorem massActionMonomial_mono {y : Complex S} {a b : Concentration S}
    (ha : a.Nonnegative) (hab : a ≤ b) : y.massActionMonomial a ≤ y.massActionMonomial b :=
  Finset.prod_le_prod₀ (fun s _ => pow_nonneg (ha s) _)
    (fun s _ => pow_le_pow_left₀ (ha s) (hab s) _)

omit [DecidableEq S] in
theorem massActionMonomial_eq_of_support {y : Complex S} {i : S}
    (hy : ∀ j, j ≠ i → y j = 0) {a b : Concentration S} (hab : a i = b i) :
    y.massActionMonomial a = y.massActionMonomial b := by
  unfold Complex.massActionMonomial
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [hy j hj, pow_zero]) (by simp),
    Finset.prod_eq_single i (fun j _ hj => by rw [hy j hj, pow_zero]) (by simp), hab]

/-- **Cooperative networks satisfy the Kamke condition** on the nonnegative orthant. -/
theorem massAction_kamkeOn_of_cooperative (N : Network S) (κ : N.RateConstants)
    (hcoop : N.IsCooperativeNetwork) :
    Monotone.KamkeOn (N.massActionVectorField κ) {x | Concentration.Nonnegative x} := by
  intro a ha b _ hab i hi
  rw [massActionVectorField_apply, massActionVectorField_apply]
  refine Finset.sum_le_sum fun r _ => ?_
  simp only [massActionRate]
  rcases lt_or_ge (N.reactionVector r i) 0 with hneg | hnn
  · rw [massActionMonomial_eq_of_support (hcoop r i hneg) hi]
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (massActionMonomial_mono ha hab) (κ.positive r).le) hnn

/-- **Order preservation for cooperative mass-action networks.** Two solutions on `[0, T]`
that stay in the box `[0, M]^S` and start ordered remain ordered. -/
theorem massAction_order_preserving_of_cooperative (N : Network S) (κ : N.RateConstants)
    (hcoop : N.IsCooperativeNetwork) (M : ℝ) {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (0 : S → ℝ) (fun _ => M))
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (0 : S → ℝ) (fun _ => M))
    (h0 : x 0 ≤ y 0) : ∀ t ∈ Set.Icc 0 T, x t ≤ y t := by
  set K := Set.Icc (0 : S → ℝ) (fun _ => M)
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn (s := K)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  have hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K := fun a ha b hb =>
    ⟨le_sup_of_le_left ha.1, sup_le ha.2 hb.2⟩
  have hk : Monotone.KamkeOn (N.massActionVectorField κ) K := by
    intro a ha b hb hab i hi
    exact N.massAction_kamkeOn_of_cooperative κ hcoop a (fun s => ha.1 s) b
      (fun s => hb.1 s) hab i hi
  exact Monotone.kamke_comparison hL hsup hk hx hy hxK hyK h0

end Network

end CRNT
