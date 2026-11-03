import CRNT.Algebra.Patchworking

/-!
# Lifting nondegenerate tropical equilibrations (several variables)

Consider a square system of polynomial terms with orders, `∑_{j ∈ J} ε^{h_j} x^{m_j} c_j = 0`
(`c_j ∈ ℝ^E`, `|E| = |S|`, integer orders `h_j`). For a valuation `w ∈ ℤ^S` the term `j` has order
`⟨w, m_j⟩ + h_j`; a **tropical equilibration** at `w` is a set `Δ` of terms attaining the minimal
order `c₀`. Its **leading system** is `∑_{j ∈ Δ} ξ^{m_j} c_j = 0`.

`lift_equilibration`: if the leading system has a positive root `ξ` with injective Jacobian, then
for small `ε > 0` the full system has positive roots `x(ε) = ε^w ψ(ε)` with `ψ(ε) → ξ`, with
injective Jacobian, and valuation `log x_s(ε) / log ε → w_s`. This is the multi-variable converse
of `Tropical.isEquilibrated_of_scaled_zeros` (Noel–Grigoriev–Vakulenko–Radulescu 2012), for
integer orders and valuations (rational ones reduce to this by substituting `ε = τ^D`).
-/

namespace CRNT

namespace Tropical

open Filter Topology Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {E : Type} [Fintype E] {J : Type} [Fintype J]

/-- The system `∑_j ε^{h_j} x^{m_j} c_j` (with `ε^h = exp (h log ε)`). -/
noncomputable def termSys (m : J → Complex S) (c : J → (E → ℝ)) (h : J → ℤ) (t : ℝ)
    (x : S → ℝ) : E → ℝ :=
  ∑ j, (Real.exp ((h j : ℝ) * Real.log t) * (m j).massActionMonomial x) • c j

/-- A tropical equilibration: the terms of minimal order `c₀` at the valuation `w`. -/
structure Equilibration (m : J → Complex S) (h : J → ℤ) where
  Δ : Finset J
  w : S → ℤ
  c₀ : ℤ
  onFace : ∀ j ∈ Δ, pairing w (m j) + h j = c₀
  offFace : ∀ j, j ∉ Δ → c₀ < pairing w (m j) + h j

namespace Equilibration

variable {m : J → Complex S} {h : J → ℤ} (q : Equilibration m h) (c : J → (E → ℝ))

/-- The leading system. -/
noncomputable def lead (y : S → ℝ) : E → ℝ := ∑ j ∈ q.Δ, (m j).massActionMonomial y • c j

/-- Its Jacobian. -/
noncomputable def leadJac (y : S → ℝ) : (S → ℝ) →L[ℝ] (E → ℝ) :=
  ∑ j ∈ q.Δ, (∑ i, massActionMonomialGrad (m j) y i •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) i).smulRight (c j)

theorem lead_hasFDerivAt (y : S → ℝ) : HasFDerivAt (q.lead c) (q.leadJac c y) y := by
  have : q.lead c = fun x => ∑ j ∈ q.Δ, (m j).massActionMonomial x • c j := rfl
  rw [this, leadJac]
  exact HasFDerivAt.fun_sum fun j _ => (massActionMonomial_hasFDerivAt (m j) y).smul_const (c j)

/-- The excess order. -/
noncomputable def expo (j : J) : ℕ := (pairing q.w (m j) + h j - q.c₀).toNat

theorem expo_spec (j : J) : ((q.expo j : ℕ) : ℤ) = pairing q.w (m j) + h j - q.c₀ := by
  unfold expo
  apply Int.toNat_of_nonneg
  by_cases hj : j ∈ q.Δ
  · rw [q.onFace _ hj]; simp
  · have := q.offFace j hj; omega

theorem expo_eq_zero_iff (j : J) : q.expo j = 0 ↔ j ∈ q.Δ := by
  constructor
  · intro h0
    by_contra hj
    have h1 := q.expo_spec j
    rw [h0] at h1
    have := q.offFace j hj
    omega
  · intro hj
    have h1 := q.expo_spec j
    rw [q.onFace _ hj, sub_self] at h1
    exact_mod_cast h1

/-- The system in toric coordinates `G(t, y) = ∑_j t^{e_j} y^{m_j} c_j`. -/
noncomputable def G (p : ℝ × (S → ℝ)) : E → ℝ :=
  ∑ j, (p.1 ^ q.expo j * (m j).massActionMonomial p.2) • c j

theorem G_contDiff : ContDiff ℝ ⊤ (q.G c) := by
  rw [contDiff_pi]
  intro e
  simp only [G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.massActionMonomial]
  fun_prop

theorem G_zero (y : S → ℝ) : q.G c (0, y) = q.lead c y := by
  classical
  simp only [G, lead]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ q.Δ)]
  have hoff : ∑ j ∈ Finset.univ.filter (· ∉ q.Δ),
      ((0 : ℝ) ^ q.expo j * (m j).massActionMonomial y) • c j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : q.expo j ≠ 0 := fun h0 =>
      (Finset.mem_filter.mp hj).2 ((q.expo_eq_zero_iff j).mp h0)
    rw [zero_pow hne, zero_mul, zero_smul]
  rw [hoff, add_zero]
  have hT : Finset.univ.filter (· ∈ q.Δ) = q.Δ := by ext j; simp
  rw [hT]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(q.expo_eq_zero_iff j).mpr hj, pow_zero, one_mul]

theorem termSys_scalePoint {t : ℝ} (ht : 0 < t) (y : Concentration S) :
    termSys m c h t (DecoratedCell.scalePoint q.w t y) =
      Real.exp ((q.c₀ : ℝ) * Real.log t) • q.G c (t, y) := by
  funext e
  simp only [termSys, G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DecoratedCell.monomial_scalePoint]
  have hexp : Real.exp ((h j : ℝ) * Real.log t) *
      Real.exp ((pairing q.w (m j) : ℝ) * Real.log t) =
      Real.exp ((q.c₀ : ℝ) * Real.log t) * t ^ q.expo j := by
    rw [← Real.exp_add, ← Real.exp_log ht, ← Real.exp_nat_mul, Real.exp_log ht, ← Real.exp_add]
    congr 1
    have h' : ((q.expo j : ℕ) : ℝ) = (pairing q.w (m j) : ℝ) + (h j : ℝ) - (q.c₀ : ℝ) := by
      exact_mod_cast q.expo_spec j
    rw [h']; ring
  calc Real.exp ((h j : ℝ) * Real.log t) *
        (Real.exp ((pairing q.w (m j) : ℝ) * Real.log t) * (m j).massActionMonomial y) * c j e
      = (Real.exp ((h j : ℝ) * Real.log t) * Real.exp ((pairing q.w (m j) : ℝ) * Real.log t)) *
          (m j).massActionMonomial y * c j e := by ring
    _ = _ := by rw [hexp]; ring

theorem termSys_differentiable (t : ℝ) : Differentiable ℝ (termSys m c h t) := by
  intro x
  have : termSys m c h t = fun x => ∑ j,
      (Real.exp ((h j : ℝ) * Real.log t) * (m j).massActionMonomial x) • c j := rfl
  rw [this]
  refine DifferentiableAt.fun_sum fun j _ => ?_
  refine DifferentiableAt.smul_const ?_ (c j)
  exact (differentiableAt_const _).mul (massActionMonomial_differentiable (m j) x)

theorem jacobian_scale {t : ℝ} (ht : 0 < t) (y : S → ℝ) :
    fderiv ℝ (termSys m c h t) (DecoratedCell.scalePoint q.w t y) ∘L
        DecoratedCell.scaleCLM q.w t =
      Real.exp ((q.c₀ : ℝ) * Real.log t) •
        (fderiv ℝ (q.G c) (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) := by
  have hsc : (fun y : S → ℝ => DecoratedCell.scalePoint q.w t y) = DecoratedCell.scaleCLM q.w t :=
    by funext y; exact (DecoratedCell.scaleCLM_apply _ _ _).symm
  have h1 : HasFDerivAt (fun y : S → ℝ => termSys m c h t (DecoratedCell.scalePoint q.w t y))
      (fderiv ℝ (termSys m c h t) (DecoratedCell.scalePoint q.w t y) ∘L
        DecoratedCell.scaleCLM q.w t) y := by
    have hJ := (termSys_differentiable (m := m) (h := h) c t
      (DecoratedCell.scalePoint q.w t y)).hasFDerivAt
    have hL : HasFDerivAt (fun y : S → ℝ => DecoratedCell.scalePoint q.w t y)
        (DecoratedCell.scaleCLM q.w t) y := by
      rw [hsc]; exact (DecoratedCell.scaleCLM q.w t).hasFDerivAt
    exact hJ.comp y hL
  have hdiff : DifferentiableAt ℝ (q.G c) (t, y) := ((q.G_contDiff c).differentiable (by simp)) _
  have h2 : HasFDerivAt (fun y : S → ℝ => Real.exp ((q.c₀ : ℝ) * Real.log t) • q.G c (t, y))
      (Real.exp ((q.c₀ : ℝ) * Real.log t) •
        (fderiv ℝ (q.G c) (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) y :=
    (hdiff.hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).const_smul
      (Real.exp ((q.c₀ : ℝ) * Real.log t))
  have heq : (fun y : S → ℝ => termSys m c h t (DecoratedCell.scalePoint q.w t y)) =
      fun y => Real.exp ((q.c₀ : ℝ) * Real.log t) • q.G c (t, y) := by
    funext y; exact q.termSys_scalePoint c ht y
  rw [heq] at h1
  exact h1.unique h2

end Equilibration

/-- **Lifting a nondegenerate tropical equilibration.** If the leading system of an equilibration
at the valuation `w` has a positive root `ξ` with injective Jacobian, then for small `ε > 0` the
full system has a positive root `x(ε) = ε^w ψ(ε)`, `ψ(ε) → ξ`, with injective Jacobian, and
`log x_s(ε) / log ε → w_s`. -/
theorem lift_equilibration {m : J → Complex S} {c : J → (E → ℝ)} {h : J → ℤ}
    (hE : Fintype.card E = Fintype.card S) (q : Equilibration m h) {ξ : Concentration S}
    (hξ : ξ.Positive) (hlead : q.lead c ξ = 0)
    (hnd : Function.Injective (q.leadJac c ξ)) :
    ∃ ψ : ℝ → (S → ℝ), ψ 0 = ξ ∧ ContinuousAt ψ 0 ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), (DecoratedCell.scalePoint q.w t (ψ t)).Positive ∧
        termSys m c h t (DecoratedCell.scalePoint q.w t (ψ t)) = 0 ∧
        Function.Injective (fderiv ℝ (termSys m c h t) (DecoratedCell.scalePoint q.w t (ψ t)))) ∧
      ∀ s, Tendsto (fun t => Real.log (DecoratedCell.scalePoint q.w t (ψ t) s) / Real.log t)
        (𝓝[>] (0 : ℝ)) (𝓝 (q.w s : ℝ)) := by
  classical
  have hG0 : q.G c (0, ξ) = 0 := by rw [Equilibration.G_zero]; exact hlead
  have hcd : ContDiffAt ℝ 1 (q.G c) (0, ξ) := ((q.G_contDiff c).of_le (by simp)).contDiffAt
  have hpart : fderiv ℝ (q.G c) (0, ξ) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) = q.leadJac c ξ := by
    have hdiff : DifferentiableAt ℝ (q.G c) (0, ξ) := ((q.G_contDiff c).differentiable (by simp)) _
    have hcomp : HasFDerivAt (fun x => q.G c (0, x))
        (fderiv ℝ (q.G c) (0, ξ) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) ξ :=
      hdiff.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (0 : ℝ) ξ)
    have heq : (fun x => q.G c (0, x)) = q.lead c := by funext x; exact q.G_zero c x
    rw [heq] at hcomp
    exact hcomp.unique (q.lead_hasFDerivAt c ξ)
  have hinv : (fderiv ℝ (q.G c) (0, ξ) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    rw [hpart]
    have hinj : Function.Injective (q.leadJac c ξ : (S → ℝ) →ₗ[ℝ] (E → ℝ)) := hnd
    have hdim : Module.finrank ℝ (S → ℝ) = Module.finrank ℝ (E → ℝ) := by
      simp [Module.finrank_fintype_fun_eq_card, hE]
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    let e : (S → ℝ) ≃ₗ[ℝ] (E → ℝ) :=
      LinearEquiv.ofBijective (q.leadJac c ξ : (S → ℝ) →ₗ[ℝ] (E → ℝ)) ⟨hinj, hsurj⟩
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    ext v; rfl
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψ0 : ψ 0 = ξ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψc : ContinuousAt ψ 0 := (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt
  have hGz : ∀ᶠ t in 𝓝 (0 : ℝ), q.G c (t, ψ t) = 0 := by
    filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with t ht
    rw [← hψdef] at ht
    rw [ht, hG0]
  have hinvev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (fderiv ℝ (q.G c) (t, ψ t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ)).IsInvertible := by
    have hfc : Continuous (fderiv ℝ (q.G c)) := (q.G_contDiff c).continuous_fderiv (by simp)
    have hpath : ContinuousAt (fun t => ((t, ψ t) : ℝ × (S → ℝ))) 0 :=
      continuousAt_id.prodMk hψc
    set R := (ContinuousLinearMap.compL ℝ (S → ℝ) (ℝ × (S → ℝ)) (E → ℝ)).flip
      (ContinuousLinearMap.inr ℝ ℝ (S → ℝ)) with hR
    have hD : ContinuousAt (fun t => R (fderiv ℝ (q.G c) (t, ψ t))) 0 :=
      R.continuous.continuousAt.comp (hfc.continuousAt.comp hpath)
    have hD0 : R (fderiv ℝ (q.G c) (0, ψ 0)) =
        fderiv ℝ (q.G c) (0, ξ) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ) := by
      rw [hψ0]; rfl
    have hev := hinv.eventually_nhds
    rw [← hD0] at hev
    exact hD.eventually hev
  have hposev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < ψ t s := by
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ψ t s) 0 := (continuous_apply s).continuousAt.comp hψc
    have : 0 < ψ 0 s := by rw [hψ0]; exact hξ s
    exact hcs.eventually (lt_mem_nhds this)
  refine ⟨ψ, hψ0, hψc, ?_, ?_⟩
  · filter_upwards [nhdsWithin_le_nhds hGz, nhdsWithin_le_nhds hinvev,
      nhdsWithin_le_nhds hposev, self_mem_nhdsWithin] with t hG hinv' hp ht
    refine ⟨fun s => mul_pos (Real.exp_pos _) (hp s), ?_, ?_⟩
    · rw [q.termSys_scalePoint c ht, hG, smul_zero]
    · intro u u' huu
      rw [← sub_eq_zero, ← map_sub] at huu
      suffices hz : ∀ v, fderiv ℝ (termSys m c h t) (DecoratedCell.scalePoint q.w t (ψ t)) v = 0 →
          v = 0 from sub_eq_zero.mp (hz _ huu)
      intro v hv
      obtain ⟨e, he⟩ := hinv'
      have hscale := q.jacobian_scale c ht (ψ t)
      set u₀ : S → ℝ := fun s => Real.exp (-(q.w s : ℝ) * Real.log t) * v s with hu₀
      have huv : DecoratedCell.scaleCLM q.w t u₀ = v := by
        funext s
        simp only [DecoratedCell.scaleCLM_apply, DecoratedCell.scalePoint, hu₀, ← mul_assoc,
          ← Real.exp_add]
        rw [show (q.w s : ℝ) * Real.log t + -(q.w s : ℝ) * Real.log t = 0 by ring,
          Real.exp_zero, one_mul]
      have h1 : (Real.exp ((q.c₀ : ℝ) * Real.log t) •
          (fderiv ℝ (q.G c) (t, ψ t) ∘L ContinuousLinearMap.inr ℝ ℝ (S → ℝ))) u₀ = 0 := by
        rw [← hscale, ContinuousLinearMap.comp_apply, huv]; exact hv
      rw [smul_apply, ← he] at h1
      have h2 : (e : (S → ℝ) →L[ℝ] (E → ℝ)) u₀ = 0 :=
        (smul_eq_zero.mp h1).resolve_left (Real.exp_pos _).ne'
      have hv0 : u₀ = 0 := by
        have := congrArg e.symm h2
        simpa using this
      rw [← huv, hv0, map_zero]
  · -- the valuation
    intro s
    have hcs : ContinuousAt (fun t => ψ t s) 0 := (continuous_apply s).continuousAt.comp hψc
    have hlogψ : Tendsto (fun t => Real.log (ψ t s)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (ξ s))) := by
      have hc := (hcs.log (by rw [hψ0]; exact (hξ s).ne')).tendsto
      rw [hψ0] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hinvlog : Tendsto (fun t => (Real.log t)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot
    have hlim := (tendsto_const_nhds (x := (q.w s : ℝ))).add (hlogψ.mul hinvlog)
    rw [mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [nhdsWithin_le_nhds hposev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with t hp ht
    have hlt : Real.log t ≠ 0 := (Real.log_neg ht.1 ht.2).ne
    simp only [DecoratedCell.scalePoint]
    rw [Real.log_mul (Real.exp_pos _).ne' (hp s).ne', Real.log_exp]
    field_simp

end Tropical

end CRNT
