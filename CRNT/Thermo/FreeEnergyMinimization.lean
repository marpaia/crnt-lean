import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.Toric

/-!
# The complex-balanced equilibrium minimizes the free energy on its class

For a complex-balanced mass-action system with reference equilibrium `x*`, the Horn–Jackson
pseudo-Helmholtz free energy is `G(x) = ∑ᵢ xᵢ log(xᵢ / x*ᵢ) - xᵢ + x*ᵢ` (`CRNT.relEntropy`). Horn
and Jackson (1972, Lemma 4B; see also Feinberg 2019, ch. 15) show that within each stoichiometric
compatibility class the free energy is uniquely minimized at the complex-balanced equilibrium of
that class. This is the thermodynamic characterization of complex-balanced equilibria, valid
beyond detailed balance, and complements the dissipation statement
`CRNT.Network.relEntropy_antitone_along_solution`.

Main results:
* `CRNT.relEntropy_sub_eq`: `G_{x*}(x) - G_{x*}(x̂) = G_{x̂}(x) + ⟨x - x̂, log x̂ - log x*⟩`.
* `CRNT.Network.relEntropy_ge_at_complexBalanced`: `G_{x*}(x) ≥ G_{x*}(x̂)` on the class of the
  complex-balanced `x̂`, with equality only at `x = x̂`.
-/

namespace CRNT

open scoped BigOperators

/-- **Three-point identity for the free energy.** -/
theorem relEntropy_sub_eq {ι : Type*} [Fintype ι] {xstar xhat x : ι → ℝ}
    (hxs : ∀ i, 0 < xstar i) (hxh : ∀ i, 0 < xhat i) :
    relEntropy xstar x - relEntropy xstar xhat =
      relEntropy xhat x +
        ∑ i, (x i - xhat i) * (Real.log (xhat i) - Real.log (xstar i)) := by
  have hdiv : ∀ (a b : ℝ), 0 < b → a * Real.log (a / b) = a * (Real.log a - Real.log b) := by
    intro a b hb
    rcases eq_or_ne a 0 with ha | ha
    · simp [ha]
    · rw [Real.log_div ha hb.ne']
  unfold relEntropy
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hdiv _ _ (hxs i), hdiv _ _ (hxs i), hdiv _ _ (hxh i)]
  ring

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Free-energy minimization at the complex-balanced equilibrium** (Horn–Jackson 1972). Let
the network be weakly reversible, `x*` and `x̂` positive complex-balanced equilibria for `κ`,
and `x` a nonnegative concentration in the class of `x̂`. Then `G_{x*}(x) ≥ G_{x*}(x̂)`, with
equality only for `x = x̂`. -/
theorem relEntropy_ge_at_complexBalanced (N : Network S) (hwr : N.WeaklyReversible)
    (κ : RateConstants N) {xstar xhat x : Concentration S} (hxs : xstar.Positive)
    (hxh : xhat.Positive) (hcbs : N.IsComplexBalanced κ xstar)
    (hcbh : N.IsComplexBalanced κ xhat) (hx : x.Nonnegative)
    (hclass : x - xhat ∈ N.stoichSubspace) :
    relEntropy xstar xhat ≤ relEntropy xstar x ∧
      (relEntropy xstar x = relEntropy xstar xhat → x = xhat) := by
  have horth := N.logRatio_orthogonal_of_complexBalanced hwr κ hxh hxs hcbh hcbs
  have hzero : ∑ i, (x i - xhat i) * (Real.log (xhat i) - Real.log (xstar i)) = 0 := by
    have := (mem_orthSum.mp horth) _ hclass
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]; ring
  have hid := relEntropy_sub_eq (x := x) hxs hxh
  rw [hzero, add_zero] at hid
  have hnn := relEntropy_nonneg (fun i => hx i) hxh
  refine ⟨by linarith, fun heq => ?_⟩
  have h0 : relEntropy xhat x = 0 := by linarith
  have := (relEntropy_eq_zero_iff (fun i => hx i) hxh).mp h0
  exact this

/-- **The free energy has a unique minimizer on each positive class.** If a weakly reversible
network admits a positive complex-balanced equilibrium `x*`, then every positive compatibility
class contains a point `x̂` minimizing `G_{x*}` over the nonnegative part of the class, uniquely,
and `x̂` is the complex-balanced equilibrium of that class. -/
theorem exists_unique_freeEnergy_minimizer (N : Network S) (hwr : N.WeaklyReversible)
    (κ : RateConstants N) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : N.IsComplexBalanced κ xstar) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ xhat ∈ N.positiveCompatibilityClass x₀, N.IsComplexBalanced κ xhat ∧
      ∀ x : Concentration S, x.Nonnegative → x - x₀ ∈ N.stoichSubspace →
        relEntropy xstar xhat ≤ relEntropy xstar x ∧
          (relEntropy xstar x = relEntropy xstar xhat → x = xhat) := by
  obtain ⟨xhat, hmem, hcbh⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxs hcbs hx₀
  refine ⟨xhat, hmem, hcbh, fun x hx hxc => ?_⟩
  have hclass : x - xhat ∈ N.stoichSubspace := by
    have h1 : xhat - x₀ ∈ N.stoichSubspace := hmem.1
    have : x - xhat = (x - x₀) - (xhat - x₀) := by abel
    rw [this]
    exact N.stoichSubspace.sub_mem hxc h1
  exact N.relEntropy_ge_at_complexBalanced hwr κ hxs hmem.2 hcbs hcbh hx hclass

end Network

end CRNT
