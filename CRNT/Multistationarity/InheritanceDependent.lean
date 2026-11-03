import CRNT.Multistationarity.InheritanceAddReactions
import CRNT.Kinetics.MassActionJacobian
import CRNT.Multistationarity.ReducedSRGraph
import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Inheritance of multistationarity under adding dependent reactions

Joshi–Shiu (2013, Theorem 3.1) in the lower-rank case: let `M`'s reaction vectors lie in the
stoichiometric subspace `S` of `N` (the added reactions are *dependent*).  If `(N, κ)` has two
distinct positive steady states in one stoichiometric class, each nondegenerate relative to the
class (the Jacobian has trivial kernel on `S`), then for all small `ε > 0` the network `N ∪ M`
with rates `(κ, ε κ')` has two distinct positive steady states in one class.

Proof: the implicit function theorem on `ℝ × S`, applied to `G(ε, v) = P (f_N + ε f_M)(x + v)`
with `P` a projection onto `S`.  Both fields take values in `S`, so `G = 0` exactly when the
field vanishes, and the partial derivative in `v` at `(0, 0)` is `P ∘ J ∘ ι`, injective on `S`
by nondegeneracy, hence invertible.  `multistationarity_inherited_union` is the full-rank case.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The perturbed field takes values in `S` when `M`'s reactions are dependent. -/
theorem perturbedField_mem (N M : Network S) (κ : N.RateConstants) (κM : M.RateConstants)
    (hdep : ∀ r : M.R, M.reactionVector r ∈ N.stoichSubspace) (p : ℝ × (S → ℝ)) :
    perturbedField N M κ κM p ∈ N.stoichSubspace := by
  unfold perturbedField
  refine Submodule.add_mem _ (massActionVectorField_mem_stoichSubspace N κ p.2)
    (Submodule.smul_mem _ _ ?_)
  have hle : M.stoichSubspace ≤ N.stoichSubspace := by
    unfold stoichSubspace
    exact Submodule.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact hdep r)
  exact hle (massActionVectorField_mem_stoichSubspace M κM p.2)

/-- **Class-restricted persistence of a nondegenerate steady state.** -/
theorem eventually_steadyState_branch_dependent (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) (hdep : ∀ r : M.R, M.reactionVector r ∈ N.stoichSubspace)
    {x₀ : Concentration S} (hss : N.IsMassActionSteadyState κ x₀)
    (hnd : ∀ v ∈ N.stoichSubspace, N.massActionJacobianCLM κ x₀ v = 0 → v = 0) :
    ∃ ψ : ℝ → (S → ℝ), ψ 0 = x₀ ∧ ContinuousAt ψ 0 ∧ (∀ ε, ψ ε - x₀ ∈ N.stoichSubspace) ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), perturbedField N M κ κM (ε, ψ ε) = 0 := by
  classical
  set V := N.stoichSubspace with hV
  obtain ⟨W, hW⟩ := V.exists_isCompl
  let Pl : (S → ℝ) →ₗ[ℝ] V := V.projectionOnto W hW
  let P : (S → ℝ) →L[ℝ] V := LinearMap.toContinuousLinearMap Pl
  have hPid : ∀ x (hx : x ∈ V), P x = ⟨x, hx⟩ := fun x hx =>
    Submodule.projectionOnto_apply_left hW ⟨x, hx⟩
  let A : ℝ × V →L[ℝ] ℝ × (S → ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ V).prod (V.subtypeL ∘L ContinuousLinearMap.snd ℝ ℝ V)
  let G : ℝ × V → V := fun p => P (perturbedField N M κ κM ((0, x₀) + A p))
  have hG : ∀ p, G p = P (perturbedField N M κ κM (p.1, x₀ + p.2)) := by
    intro p; simp only [G, A]; congr 2; ext <;> simp [add_comm]
  have hcd : ContDiffAt ℝ 1 G (0, 0) := by
    have h1 : ContDiff ℝ ⊤ (fun p : ℝ × V => (0, x₀) + A p) := contDiff_const.add A.contDiff
    exact ((P.contDiff.comp ((contDiff_perturbedField N M κ κM).comp h1)).of_le
      (by simp)).contDiffAt
  -- the partial derivative in `v` at `(0, 0)`
  set T : V →L[ℝ] V := P ∘L N.massActionJacobianCLM κ x₀ ∘L V.subtypeL with hT
  have hpart : fderiv ℝ G (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ V = T := by
    have hdiff : DifferentiableAt ℝ G (0, 0) := hcd.differentiableAt (by simp)
    have hcomp : HasFDerivAt (fun v : V => G (0, v))
        (fderiv ℝ G (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ V) 0 :=
      hdiff.hasFDerivAt.comp (0 : V) (hasFDerivAt_prodMk_right (0 : ℝ) (0 : V))
    have hdirect : HasFDerivAt (fun v : V => G (0, v)) T 0 := by
      have heq : (fun v : V => G (0, v)) =
          fun v : V => P (N.massActionVectorField κ (x₀ + (v : S → ℝ))) := by
        funext v; rw [hG]; simp [perturbedField]
      rw [heq]
      have hJ := N.massActionVectorField_hasFDerivAt κ x₀
      have hin : HasFDerivAt (fun v : V => x₀ + (v : S → ℝ)) V.subtypeL (0 : V) :=
        (V.subtypeL.hasFDerivAt).const_add x₀
      have hJ0 : HasFDerivAt (fun x => N.massActionVectorField κ x) (N.massActionJacobianCLM κ x₀)
          ((fun v : V => x₀ + (v : S → ℝ)) (0 : V)) := by
        show HasFDerivAt _ _ (x₀ + ((0 : V) : S → ℝ))
        rw [Submodule.coe_zero, add_zero]; exact hJ
      have h2 : HasFDerivAt (fun v : V => N.massActionVectorField κ (x₀ + (v : S → ℝ)))
          (N.massActionJacobianCLM κ x₀ ∘L V.subtypeL) (0 : V) :=
        HasFDerivAt.comp (0 : V) (g := fun x => N.massActionVectorField κ x) hJ0 hin
      exact P.hasFDerivAt.comp (0 : V) h2
    exact hcomp.unique hdirect
  have hinj : Function.Injective T := by
    intro u w huw
    have h0 : T (u - w) = 0 := by rw [map_sub, huw, sub_self]
    have hmem := N.massActionJacobianCLM_mem_stoichSubspace κ x₀ ((u - w : V) : S → ℝ)
    have h1 : N.massActionJacobianCLM κ x₀ ((u - w : V) : S → ℝ) = 0 := by
      have := congrArg Subtype.val h0
      simp only [hT, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at this
      rw [hPid _ hmem] at this
      simpa using this
    have := hnd _ (u - w).2 h1
    exact sub_eq_zero.mp (Subtype.ext (by simpa using this))
  have hinv : (fderiv ℝ G (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ V).IsInvertible := by
    rw [hpart]
    let e : V ≃ₗ[ℝ] V := LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℝ] V) hinj
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext v; rfl
  set φ := hcd.implicitFunction one_ne_zero hinv with hφ
  refine ⟨fun ε => x₀ + (φ ε : S → ℝ), ?_, ?_, fun ε => by simp, ?_⟩
  · have h : φ 0 = 0 := hcd.implicitFunction_apply_self one_ne_zero hinv
    show x₀ + ((φ 0 : V) : S → ℝ) = x₀
    rw [h]; simp
  · exact continuousAt_const.add (continuous_subtype_val.continuousAt.comp
      (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt)
  · have h0 : G (0, 0) = 0 := by
      rw [hG]
      have : perturbedField N M κ κM (0, x₀ + ((0 : V) : S → ℝ)) = 0 := by
        funext s; have := hss s; simp only [perturbedField, zero_smul, add_zero,
          Submodule.coe_zero, Pi.zero_apply]; exact this
      rw [this, map_zero]
    filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with ε hε
    rw [← hφ] at hε
    have hGε : G (ε, φ ε) = 0 := by rw [hε, h0]
    rw [hG] at hGε
    have hmem := perturbedField_mem N M κ κM hdep (ε, x₀ + (φ ε : S → ℝ))
    rw [hPid _ hmem] at hGε
    exact congrArg Subtype.val hGε

/-- **Inheritance of multistationarity under adding dependent reactions (Joshi–Shiu 2013,
Theorem 3.1).** Two distinct positive steady states of `(N, κ)` in one class, each nondegenerate
relative to the class, persist for all small `ε > 0` as two distinct positive steady states, in
one class, of `N ∪ M` with rates `(κ, ε κ')`, whenever `M`'s reaction vectors lie in `N`'s
stoichiometric subspace. -/
theorem multistationarity_inherited_dependent (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) (hdep : ∀ r : M.R, M.reactionVector r ∈ N.stoichSubspace)
    {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂) (hcls : x₁ - x₂ ∈ N.stoichSubspace)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : ∀ v ∈ N.stoichSubspace, N.massActionJacobianCLM κ x₁ v = 0 → v = 0)
    (hnd₂ : ∀ v ∈ N.stoichSubspace, N.massActionJacobianCLM κ x₂ v = 0 → v = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      ∃ y₁ y₂ : Concentration S, y₁.Positive ∧ y₂.Positive ∧ y₁ ≠ y₂ ∧
        y₁ - y₂ ∈ N.stoichSubspace ∧
        (N.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₁ ∧
        (N.union M).IsMassActionSteadyState (unionRates κ κM ε hε) y₂ := by
  obtain ⟨ψ₁, h₁0, h₁c, h₁S, h₁e⟩ := eventually_steadyState_branch_dependent N M κ κM hdep hss₁ hnd₁
  obtain ⟨ψ₂, h₂0, h₂c, h₂S, h₂e⟩ := eventually_steadyState_branch_dependent N M κ κM hdep hss₂ hnd₂
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
  · have e : ψ₁ ε - ψ₂ ε = (ψ₁ ε - x₁) - (ψ₂ ε - x₂) + (x₁ - x₂) := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (h₁S ε) (h₂S ε)) hcls
  · intro s; rw [hfield, e₁]; rfl
  · intro s; rw [hfield, e₂]; rfl

end Network
end CRNT
