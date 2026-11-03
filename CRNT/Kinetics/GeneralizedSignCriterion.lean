import CRNT.Kinetics.SignVectorCriterion
import CRNT.Equilibria.GeneralizedComplexBalanceToric
import CRNT.Graph.PositiveCirculation

/-!
# The Müller–Regensburger sign-vector criterion at network level

For a weakly reversible network with generalized mass-action kinetic orders `G`
(stoichiometric subspace `S`, kinetic-order subspace `S̃`), Müller and Regensburger
(SIAM J. Appl. Math. 72 (2012), Theorem 3.10 / Corollary 3.11) show:

> every stoichiometric class contains at most one positive complex-balanced equilibrium,
> **for every choice of rate constants**, iff `σ(S) ∩ σ(S̃^⊥) = {0}`.

The library already proves sufficiency
(`GeneralizedMassActionData.complexBalanced_unique_in_stoichClass_of_signCompatible`). This module
proves necessity: when the sign condition fails we construct rate constants (from a positive
circulation on the reaction graph) and two distinct positive complex-balanced equilibria in one
stoichiometric class.

Main results:
* `CRNT.Network.GeneralizedMassActionData.exists_rateConstants_complexBalanced_at`: every positive
  point of a weakly reversible network is a complex-balanced equilibrium for suitable rate
  constants.
* `CRNT.Network.GeneralizedMassActionData.exists_two_complexBalanced_of_not_signCompatible`.
* `CRNT.Network.GeneralizedMassActionData.unique_complexBalanced_forall_iff_signCompatible`.
-/

namespace CRNT

namespace Network

namespace GeneralizedMassActionData

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **Rate constants realizing a prescribed complex-balanced equilibrium.** For a weakly
reversible network, every positive `x` is complex balanced for the rate constants
`κ_r = α_r / x^{ỹ(source r)}`, `α` a positive circulation. -/
theorem exists_rateConstants_complexBalanced_at (G : N.GeneralizedMassActionData)
    (hwr : N.WeaklyReversible) (x : Concentration S) :
    ∃ κ : N.RateConstants, G.IsComplexBalanced κ x := by
  obtain ⟨α, hαpos, hαker⟩ := N.exists_positiveGraphCirculation_of_weaklyReversible hwr
  let κ : N.RateConstants := ⟨fun r => α r / G.kineticMonomial (G.kineticComplex (N.sourceIdx r)) x,
    fun r => div_pos (hαpos r) (G.kineticMonomial_pos _ _)⟩
  refine ⟨κ, fun c => ?_⟩
  have hrate : ∀ r, G.generalizedRate κ x r = α r := by
    intro r
    simp only [generalizedRate, κ]
    exact div_mul_cancel₀ _ (G.kineticMonomial_pos _ _).ne'
  have hc := congrFun hαker c
  simp only [incidenceMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_sub,
    Finset.sum_sub_distrib] at hc
  simp only [inflow, outflow, hrate]
  have e1 : ∀ r, (if N.targetIdx r = c then α r else 0) =
      α r * (if N.targetIdx r = c then 1 else 0) := fun r => by split_ifs <;> simp
  have e2 : ∀ r, (if N.sourceIdx r = c then α r else 0) =
      α r * (if N.sourceIdx r = c then 1 else 0) := fun r => by split_ifs <;> simp
  simp_rw [e1, e2]
  linarith

/-- **Necessity of the sign condition.** If `σ(S) ∩ σ(S̃^⊥) ≠ {0}`, there are rate constants
and two distinct positive complex-balanced equilibria in the same stoichiometric class. -/
theorem exists_two_complexBalanced_of_not_signCompatible (G : N.GeneralizedMassActionData)
    (hwr : N.WeaklyReversible)
    (hsign : ¬ SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace)) :
    ∃ (κ : N.RateConstants) (x y : Concentration S), x.Positive ∧ y.Positive ∧ x ≠ y ∧
      SameStoichClass N x y ∧ G.IsComplexBalanced κ x ∧ G.IsComplexBalanced κ y := by
  obtain ⟨x, y, hx, hy, hV, hT, hne⟩ :=
    exists_two_points_of_not_signCompatible _ _ hsign
  obtain ⟨κ, hcby⟩ := G.exists_rateConstants_complexBalanced_at hwr y
  have hcbx : G.IsComplexBalanced κ x :=
    G.complexBalanced_of_toricLeaf κ hwr (xstar := y) hy hcby ⟨hx, by simpa [logRatio, logDiff] using hT⟩
  exact ⟨κ, x, y, hx, hy, hne, hV, hcbx, hcby⟩

/-- **Müller–Regensburger criterion.** For a weakly reversible network with generalized kinetic
orders, every stoichiometric class contains at most one positive complex-balanced equilibrium
for every choice of rate constants iff `σ(S) ∩ σ(S̃^⊥) = {0}`. -/
theorem unique_complexBalanced_forall_iff_signCompatible (G : N.GeneralizedMassActionData)
    (hwr : N.WeaklyReversible) :
    (∀ (κ : N.RateConstants) (x y : Concentration S), x.Positive → y.Positive →
        G.IsComplexBalanced κ x → G.IsComplexBalanced κ y → SameStoichClass N x y → x = y) ↔
      SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace) := by
  constructor
  · intro h
    by_contra hsign
    obtain ⟨κ, x, y, hx, hy, hne, hclass, hcx, hcy⟩ :=
      G.exists_two_complexBalanced_of_not_signCompatible hwr hsign
    exact hne (h κ x y hx hy hcx hcy hclass)
  · intro hsign κ x y hx hy hcx hcy hclass
    exact G.complexBalanced_unique_in_stoichClass_of_signCompatible κ hwr hsign hx hy hcx hcy hclass

end GeneralizedMassActionData

end Network

end CRNT
