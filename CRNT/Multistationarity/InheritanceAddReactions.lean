import CRNT.Equilibria.SteadyState
import CRNT.Stoich.Subspace
import CRNT.Open.Augmentation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Inheritance of nondegenerate multistationarity under adding reactions

Joshi and Shiu (*Atoms of multistationarity in chemical reaction networks*, J. Math. Chem. 51
(2013), Theorem 3.1 and Corollary 3.2) show that multistationarity of a fully open network is
inherited by every fully open network containing it: adding reactions with small rate constants
perturbs the vector field slightly, and nondegenerate steady states persist by the implicit
function theorem.

This module proves that inheritance step for networks of full stoichiometric rank (the
fully open case: `N.stoichSubspace = ⊤`), where nondegeneracy means that the Jacobian of the
mass-action vector field is invertible on all of `ℝ^S`.

Main results:
* `CRNT.Network.union`, `CRNT.Network.unionRates`, `CRNT.Network.massActionVectorField_union`:
  the network with the reactions of `N` and of `M`, the latter scaled by `ε`.
* `CRNT.Network.contDiff_massActionVectorField`.
* `CRNT.Network.eventually_steadyState_branch`: a nondegenerate steady state persists as a
  continuous branch of steady states of the enlarged network.
* `CRNT.Network.multistationarity_inherited_union`: two distinct nondegenerate positive steady
  states of `(N, κ)` yield, for all small `ε > 0`, two distinct positive steady states of the
  enlarged network in one stoichiometric class.
-/

namespace CRNT

namespace Network

open Filter Topology
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network with the reactions of `N` together with those of `M`. -/
def union (N M : Network S) : Network S :=
  ⟨N.R ⊕ M.R, inferInstance, inferInstance, Sum.elim N.reaction M.reaction⟩

/-- Rate constants on `N.union M`: `κ` on `N`, `ε · κ'` on `M`. -/
def unionRates {N M : Network S} (κ : N.RateConstants) (κM : M.RateConstants) (ε : ℝ)
    (hε : 0 < ε) : (N.union M).RateConstants :=
  ⟨Sum.elim κ.k (fun r => ε * κM.k r), by
    rintro (r | r)
    · exact κ.positive r
    · exact mul_pos hε (κM.positive r)⟩

theorem massActionVectorField_union {N M : Network S} (κ : N.RateConstants)
    (κM : M.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) :
    (N.union M).massActionVectorField (unionRates κ κM ε hε) x =
      N.massActionVectorField κ x + ε • M.massActionVectorField κM x := by
  funext s
  simp only [massActionVectorField_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  show ∑ r : N.R ⊕ M.R, _ = _
  rw [Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [massActionRate, reactionVector, unionRates, union, Sum.elim_inr]
  ring

theorem stoichSubspace_le_union (N M : Network S) :
    N.stoichSubspace ≤ (N.union M).stoichSubspace := by
  unfold stoichSubspace
  refine Submodule.span_mono ?_
  rintro v ⟨r, rfl⟩
  exact ⟨Sum.inl r, rfl⟩

/-- Mass-action vector fields are smooth. -/
theorem contDiff_massActionVectorField (N : Network S) (κ : N.RateConstants) :
    ContDiff ℝ ⊤ (N.massActionVectorField κ) := by
  rw [contDiff_pi]
  intro s
  unfold massActionVectorField massActionRate Complex.massActionMonomial
  fun_prop

/-- The perturbed field `F (ε, x) = f_N(x) + ε f_M(x)`. -/
noncomputable def perturbedField (N M : Network S) (κ : N.RateConstants) (κM : M.RateConstants)
    (p : ℝ × (S → ℝ)) : S → ℝ :=
  N.massActionVectorField κ p.2 + p.1 • M.massActionVectorField κM p.2

theorem contDiff_perturbedField (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) : ContDiff ℝ ⊤ (perturbedField N M κ κM) := by
  unfold perturbedField
  exact ((N.contDiff_massActionVectorField κ).comp contDiff_snd).add
    (contDiff_fst.smul ((M.contDiff_massActionVectorField κM).comp contDiff_snd))

/-- The state derivative of the perturbed field at `ε = 0` is the Jacobian of `f_N`. -/
theorem fderiv_perturbedField_inr (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) (x₀ : S → ℝ) :
    fderiv ℝ (perturbedField N M κ κM) (0, x₀) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) =
      fderiv ℝ (N.massActionVectorField κ) x₀ := by
  have hdiff : DifferentiableAt ℝ (perturbedField N M κ κM) (0, x₀) :=
    ((contDiff_perturbedField N M κ κM).differentiable (by simp)) _
  have hcomp : HasFDerivAt (fun x => perturbedField N M κ κM (0, x))
      (fderiv ℝ (perturbedField N M κ κM) (0, x₀) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) x₀ :=
    hdiff.hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_right (0 : ℝ) x₀)
  have heq : (fun x => perturbedField N M κ κM (0, x)) = N.massActionVectorField κ := by
    funext x; simp [perturbedField]
  rw [heq] at hcomp
  exact hcomp.fderiv.symm

/-- **Persistence of a nondegenerate steady state.** If `x₀` is a steady state of `(N, κ)` with
invertible Jacobian, there is a branch `ψ`, continuous at `0` with `ψ 0 = x₀`, such that `ψ ε`
is a zero of `f_N + ε f_M` for all `ε` near `0`. -/
theorem eventually_steadyState_branch (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) {x₀ : Concentration S} (hss : N.IsMassActionSteadyState κ x₀)
    (hnd : (fderiv ℝ (N.massActionVectorField κ) x₀).IsInvertible) :
    ∃ ψ : ℝ → (S → ℝ), ψ 0 = x₀ ∧ ContinuousAt ψ 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), perturbedField N M κ κM (ε, ψ ε) = 0 := by
  have hcd : ContDiffAt ℝ 1 (perturbedField N M κ κM) (0, x₀) :=
    ((contDiff_perturbedField N M κ κM).of_le (by simp)).contDiffAt
  have hinv : (fderiv ℝ (perturbedField N M κ κM) (0, x₀) ∘L
      ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    rw [fderiv_perturbedField_inr]; exact hnd
  refine ⟨hcd.implicitFunction one_ne_zero hinv, ?_, ?_, ?_⟩
  · exact hcd.implicitFunction_apply_self one_ne_zero hinv
  · exact (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt
  · have h0 : perturbedField N M κ κM (0, x₀) = 0 := by
      funext s
      have := hss s
      simp only [perturbedField, zero_smul, add_zero, Pi.zero_apply]
      exact this
    filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with ε hε
    rw [hε, h0]

/-- **Inheritance of multistationarity (Joshi–Shiu).** Let `N` have full stoichiometric rank and
two distinct positive steady states with invertible Jacobians. For every network `M` and rate
constants `κ'`, there is `ε₀ > 0` such that for all `0 < ε < ε₀` the network `N ∪ M` with rates
`(κ, ε κ')` has two distinct positive steady states in the same stoichiometric class. -/
theorem multistationarity_inherited_union (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) (hS : N.stoichSubspace = ⊤) {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : (fderiv ℝ (N.massActionVectorField κ) x₁).IsInvertible)
    (hnd₂ : (fderiv ℝ (N.massActionVectorField κ) x₂).IsInvertible) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      ∃ y₁ y₂ : Concentration S, y₁.Positive ∧ y₂.Positive ∧ y₁ ≠ y₂ ∧
        y₁ - y₂ ∈ (N.union M).stoichSubspace ∧
        (N.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₁ ∧
        (N.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₂ := by
  obtain ⟨ψ₁, h₁0, h₁c, h₁e⟩ := eventually_steadyState_branch N M κ κM hss₁ hnd₁
  obtain ⟨ψ₂, h₂0, h₂c, h₂e⟩ := eventually_steadyState_branch N M κ κM hss₂ hnd₂
  -- positivity and separation near `ε = 0`
  have hopen : IsOpen {x : S → ℝ | ∀ s, 0 < x s} := by
    have : {x : S → ℝ | ∀ s, 0 < x s} = ⋂ s, {x : S → ℝ | 0 < x s} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  have hpos₁ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₁ ε s :=
    h₁c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₁0]; exact hx₁))
  have hpos₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₂ ε s :=
    h₂c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₂0]; exact hx₂))
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ₁ ε ≠ ψ₂ ε := by
    have hc : ContinuousAt (fun ε => (ψ₁ ε, ψ₂ ε)) 0 := h₁c.prodMk h₂c
    have hdiag : IsOpen {p : (S → ℝ) × (S → ℝ) | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
    exact hc.preimage_mem_nhds (hdiag.mem_nhds (by simpa [h₁0, h₂0] using hne))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (h₁e.and (h₂e.and (hpos₁.and (hpos₂.and hsep))))
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hdist : dist ε 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ
  obtain ⟨e₁, e₂, p₁, p₂, sep⟩ := hball hdist
  have hfield : ∀ y, (N.union M).massActionVectorField (unionRates κ κM ε hε) y =
      perturbedField N M κ κM (ε, y) := fun y => massActionVectorField_union κ κM ε hε y
  refine ⟨ψ₁ ε, ψ₂ ε, p₁, p₂, sep, ?_, ?_, ?_⟩
  · have := stoichSubspace_le_union N M
    rw [hS] at this
    exact this Submodule.mem_top
  · intro s; rw [hfield, e₁]; rfl
  · intro s; rw [hfield, e₂]; rfl

/-- **Fully open form.** Nondegenerate multistationarity of the fully open network `N⁺` is
inherited by `N⁺ ∪ M` for every network `M`, once the added reactions are slow enough. -/
theorem multistationarity_inherited_fullyOpen_union (N M : Network S)
    (κ : N.fullyOpen.RateConstants) (κM : M.RateConstants) {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hss₁ : N.fullyOpen.IsMassActionSteadyState κ x₁)
    (hss₂ : N.fullyOpen.IsMassActionSteadyState κ x₂)
    (hnd₁ : (fderiv ℝ (N.fullyOpen.massActionVectorField κ) x₁).IsInvertible)
    (hnd₂ : (fderiv ℝ (N.fullyOpen.massActionVectorField κ) x₂).IsInvertible) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      ∃ y₁ y₂ : Concentration S, y₁.Positive ∧ y₂.Positive ∧ y₁ ≠ y₂ ∧
        (N.fullyOpen.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₁ ∧
        (N.fullyOpen.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₂ := by
  obtain ⟨ε₀, hε₀, h⟩ := multistationarity_inherited_union N.fullyOpen M κ κM
    (stoichSubspace_fullyOpen_eq_top N) hx₁ hx₂ hne hss₁ hss₂ hnd₁ hnd₂
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨y₁, y₂, p₁, p₂, hne', _, e₁, e₂⟩ := h ε hε hεε
  exact ⟨y₁, y₂, p₁, p₂, hne', e₁, e₂⟩

end Network

end CRNT
