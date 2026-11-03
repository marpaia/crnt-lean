import CRNT.Algebra.TropicalLifting
import CRNT.Multistationarity.DecoratedSimplicesConservation

/-!
# Lifting tropical equilibrations of reaction networks

Rate constants `κ̄_r ε^{a_r}` (integer orders), totals `ε^{a₀} T̄`. The steady states in the class
`{L x = ε^{a₀} T̄}` are the zeros of the augmented term system with terms
* `ε^{a_r} x^{y_r} (Z(κ̄_r v_r), 0)` for each reaction `r`,
* `x_i (0, L e_i)` for each species `i` (order `0`),
* `ε^{a₀} (0, −T̄)` (the totals).

`lift_network_equilibration`: if the leading system of a tropical equilibration at the valuation
`w` has a nondegenerate positive root `ξ`, the network has, for every small `ε > 0`, a positive
steady state `x(ε) = ε^w ψ(ε)` (`ψ(ε) → ξ`) in the class `{L x = ε^{a₀} T̄}`, nondegenerate
relative to the class, with valuations `log x_s / log ε → w_s` (Noel–Grigoriev–Vakulenko–Radulescu
2012: nondegenerate tropical equilibrations approximate steady states).
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]

/-- Exponents of the augmented terms. -/
def augTermExp (N : Network S) : N.R ⊕ (S ⊕ Unit) → Complex S
  | Sum.inl r => (N.reaction r).source
  | Sum.inr (Sum.inl i) => unitComplex i
  | Sum.inr (Sum.inr _) => 0

/-- Coefficients of the augmented terms. -/
noncomputable def augTermCoeff (N : Network S) (κ : RateConstants N) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (T : E₂ → ℝ) : N.R ⊕ (S ⊕ Unit) → (E₁ ⊕ E₂ → ℝ)
  | Sum.inl r => Sum.elim (Z (κ.k r • N.reactionVector r)) 0
  | Sum.inr (Sum.inl i) => Sum.elim 0 (L (Pi.single i 1))
  | Sum.inr (Sum.inr _) => Sum.elim 0 (-T)

/-- Orders of the augmented terms. -/
def augTermOrder (N : Network S) (a : N.R → ℤ) (a₀ : ℤ) : N.R ⊕ (S ⊕ Unit) → ℤ
  | Sum.inl r => a r
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => a₀

/-- Rates `κ̄_r ε^{a_r}`. -/
noncomputable def orderedRates (N : Network S) (κ : RateConstants N) (a : N.R → ℤ) (t : ℝ) :
    RateConstants N :=
  ⟨fun r => κ.k r * Real.exp ((a r : ℝ) * Real.log t),
    fun r => mul_pos (κ.positive r) (Real.exp_pos _)⟩

/-- The augmented term system is `(Z F_{κ_ε}(x), L x − ε^{a₀} T̄)`. -/
theorem termSys_aug (N : Network S) (κ : RateConstants N) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (T : E₂ → ℝ) (a : N.R → ℤ) (a₀ : ℤ) (t : ℝ) (x : S → ℝ) :
    Tropical.termSys (augTermExp N) (augTermCoeff N κ Z L T) (augTermOrder N a a₀) t x =
      Sum.elim (Z (N.massActionVectorField (orderedRates N κ a t) x))
        (L x - Real.exp ((a₀ : ℝ) * Real.log t) • T) := by
  classical
  simp only [Tropical.termSys, Fintype.sum_sum_type, Fintype.sum_unique]
  have hfield : N.massActionVectorField (orderedRates N κ a t) x =
      ∑ r, (Real.exp ((a r : ℝ) * Real.log t) * (N.reaction r).source.massActionMonomial x) •
        (κ.k r • N.reactionVector r) := by
    funext s
    rw [massActionVectorField_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, massActionRate, orderedRates]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hL : L x = ∑ i, x i • L (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]; congr 2; funext j; simp [Pi.single_apply, eq_comm]
  funext e
  cases e with
  | inl e₁ =>
    simp only [augTermExp, augTermCoeff, augTermOrder, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, Sum.elim_inl, Pi.zero_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      add_zero]
    rw [hfield, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  | inr e₂ =>
    simp only [augTermExp, augTermCoeff, augTermOrder, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, Sum.elim_inr, Pi.zero_apply, smul_zero, Finset.sum_const_zero, zero_add,
      smul_eq_mul, Pi.sub_apply, Pi.neg_apply, Int.cast_zero, zero_mul, Real.exp_zero, one_mul,
      monomial_unitComplex]
    rw [hL, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.massActionMonomial, Pi.zero_apply, pow_zero,
      Finset.prod_const_one, mul_one]
    have h0 : ∀ r : N.R, Real.exp ((a r : ℝ) * Real.log t) *
        (∏ s, x s ^ (N.reaction r).source s) * (0 : ℝ) = 0 := fun r => mul_zero _
    simp only [h0, Finset.sum_const_zero, zero_add]
    ring

/-- **Lifting a nondegenerate tropical equilibration of a reaction network.** -/
theorem lift_network_equilibration (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0)
    (hL : ∀ v, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) (κ : RateConstants N) (T : E₂ → ℝ)
    (a : N.R → ℤ) (a₀ : ℤ)
    (q : Tropical.Equilibration (augTermExp N) (augTermOrder N a a₀)) {ξ : Concentration S}
    (hξ : ξ.Positive) (hlead : q.lead (augTermCoeff N κ Z L T) ξ = 0)
    (hnd : Function.Injective (q.leadJac (augTermCoeff N κ Z L T) ξ)) :
    ∃ ψ : ℝ → (S → ℝ), ψ 0 = ξ ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), (DecoratedCell.scalePoint q.w t (ψ t)).Positive ∧
        N.IsMassActionSteadyState (orderedRates N κ a t) (DecoratedCell.scalePoint q.w t (ψ t)) ∧
        L (DecoratedCell.scalePoint q.w t (ψ t)) = Real.exp ((a₀ : ℝ) * Real.log t) • T ∧
        N.IsNondegenerateSteadyState (orderedRates N κ a t)
          (DecoratedCell.scalePoint q.w t (ψ t))) ∧
      ∀ s, Tendsto (fun t => Real.log (DecoratedCell.scalePoint q.w t (ψ t) s) / Real.log t)
        (𝓝[>] (0 : ℝ)) (𝓝 (q.w s : ℝ)) := by
  classical
  obtain ⟨ψ, hψ0, -, hev, hval⟩ := Tropical.lift_equilibration hcard q hξ hlead hnd
  refine ⟨ψ, hψ0, ?_, hval⟩
  filter_upwards [hev] with t ⟨hpos, hzero, hinj⟩
  set x := DecoratedCell.scalePoint q.w t (ψ t)
  set κ' := orderedRates N κ a t
  set Tt : E₂ → ℝ := Real.exp ((a₀ : ℝ) * Real.log t) • T
  have hid := termSys_aug N κ Z L T a a₀ t
  rw [hid] at hzero
  have hZF : Z (N.massActionVectorField κ' x) = 0 := by
    funext e₁; have := congrFun hzero (Sum.inl e₁); simpa using this
  have hLx : L x = Tt := by
    funext e₂; have := congrFun hzero (Sum.inr e₂); simp at this; simpa [sub_eq_zero, Tt] using this
  have hss : N.IsMassActionSteadyState κ' x := by
    intro s
    have := hZ _ (field_mem_stoichSubspace N κ' x) hZF
    exact congrFun this s
  refine ⟨hpos, hss, hLx, ?_⟩
  intro u hu hJu
  set Zc := LinearMap.toContinuousLinearMap Z
  set Lc := LinearMap.toContinuousLinearMap L
  have hD : HasFDerivAt (Tropical.termSys (augTermExp N) (augTermCoeff N κ Z L T)
      (augTermOrder N a a₀) t)
      (inlCLM E₁ E₂ ∘L Zc ∘L N.massActionJacobianCLM κ' x + inrCLM E₁ E₂ ∘L Lc) x := by
    have heq : Tropical.termSys (augTermExp N) (augTermCoeff N κ Z L T) (augTermOrder N a a₀) t =
        fun y => inlCLM E₁ E₂ (Zc (N.massActionVectorField κ' y)) + inrCLM E₁ E₂ (Lc y - Tt) := by
      funext y
      rw [hid]
      funext e
      cases e
      · simp [inlCLM, inrCLM, Zc, Lc, Tt]; rfl
      · simp [inlCLM, inrCLM, Zc, Lc, Tt]
    rw [heq]
    have h1 : HasFDerivAt (fun y => inlCLM E₁ E₂ (Zc (N.massActionVectorField κ' y)))
        (inlCLM E₁ E₂ ∘L Zc ∘L N.massActionJacobianCLM κ' x) x :=
      (inlCLM E₁ E₂).hasFDerivAt.comp _ (Zc.hasFDerivAt.comp _
        (N.massActionVectorField_hasFDerivAt κ' x))
    have h2 : HasFDerivAt (fun y => inrCLM E₁ E₂ (Lc y - Tt)) (inrCLM E₁ E₂ ∘L Lc) x :=
      (inrCLM E₁ E₂).hasFDerivAt.comp _ (Lc.hasFDerivAt.sub_const Tt)
    exact h1.add h2
  have hDu : fderiv ℝ (Tropical.termSys (augTermExp N) (augTermCoeff N κ Z L T)
      (augTermOrder N a a₀) t) x u = 0 := by
    rw [hD.fderiv]
    have hLu : L u = 0 := (hL u).mpr hu
    simp [hJu, hLu, Zc, Lc]
  exact hinj (by rw [hDu, map_zero])

end Network

end CRNT
