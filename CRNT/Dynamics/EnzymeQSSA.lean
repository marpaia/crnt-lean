import CRNT.Dynamics.EnzymeFastContraction
import CRNT.Dynamics.MichaelisMentenCoupledContraction

/-!
# Quasi-steady-state error bound for the Michaelis–Menten mass-action system

For `E + S ⇌ C → E + P` with rate constants `k₁, k₋₁, k₂ > 0` and total enzyme `e₀`, the substrate
and complex obey

`ṡ = -k₁ (e₀ - c) s + k₋₁ c`,   `ċ = k₁ (e₀ - c) s - (k₋₁ + k₂) c`.

`qssa_error_le`: if `s ≥ 0` and `|ṡ| ≤ D` for `t ≥ 0`, then for all `t ≥ 0`

`|c(t) - c*(s(t))| ≤ |c(0) - c*(s(0))| + (e₀ / K_M) · D / (k₋₁ + k₂)`,

where `c*(s) = e₀ s / (s + K_M)` is the Briggs–Haldane quasi-steady state and
`K_M = (k₋₁ + k₂)/k₁`.  This is the coupled (moving-substrate) form of the transverse estimate
`Enzyme.fast_dist_qss_le`: the fast field is contracting with rate `k₋₁ + k₂` at every `s ≥ 0`,
it vanishes on `c*`, and the reference `c*(s(t))` moves with speed at most `(e₀/K_M)·|ṡ|`.

`coupled_dissipative_ceiling_forward` is `ODE.coupled_dissipative_ceiling_nonauto` with all
hypotheses required only for `t ≥ 0`.

Nothing here is an axiom or a `sorry`.
-/

open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Forward-time version of `coupled_dissipative_ceiling_nonauto`. -/
theorem coupled_dissipative_ceiling_forward {full : ℝ → E → E} {x m m' : ℝ → E} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (full t (x t)) t) (hm : ∀ t, 0 ≤ t → HasDerivAt m (m' t) t)
    (hcon : ∀ t, 0 ≤ t → ⟪full t (x t) - full t (m t), x t - m t⟫ ≤ -lam * ‖x t - m t‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t → ‖full t (m t) - m' t‖ ≤ δ) :
    ∀ t, 0 ≤ t → ‖x t - m t‖ ≤ ‖x 0 - m 0‖ + δ / lam := by
  -- Error curve `e t = x t - m t` with derivative `full t (x t) - m' t`.
  set e : ℝ → E := fun t => x t - m t with he
  have hed : ∀ t, 0 ≤ t → HasDerivAt e (full t (x t) - m' t) t := fun t ht => (hx t ht).sub (hm t ht)
  -- Lyapunov square `V t = ⟪e t, e t⟫ = ‖e t‖²` with derivative `2⟪full t (x t) - m' t, e t⟫`.
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVd : ∀ t, 0 ≤ t → HasDerivAt V (2 * ⟪full t (x t) - m' t, e t⟫) t := by
    intro t ht
    have h := (hed t ht).inner ℝ (hed t ht)
    have hsym : ⟪e t, full t (x t) - m' t⟫ + ⟪full t (x t) - m' t, e t⟫
        = 2 * ⟪full t (x t) - m' t, e t⟫ := by
      rw [real_inner_comm (e t) (full t (x t) - m' t)]; ring
    simpa [hV, hsym] using h
  -- The dissipative differential inequality on `V`: `V' t ≤ -2λ·V t + 2δ·‖e t‖`.
  have hVbound : ∀ t, 0 ≤ t → 2 * ⟪full t (x t) - m' t, e t⟫ ≤ -2 * lam * V t + 2 * δ * ‖e t‖ := by
    intro t ht
    have hsplit : full t (x t) - m' t = (full t (x t) - full t (m t)) + (full t (m t) - m' t) := by
      abel
    have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
    have hc : ⟪full t (x t) - full t (m t), e t⟫ ≤ -lam * ‖e t‖ ^ 2 := hcon t ht
    have hd : ⟪full t (m t) - m' t, e t⟫ ≤ δ * ‖e t‖ := by
      calc ⟪full t (m t) - m' t, e t⟫
          ≤ ‖full t (m t) - m' t‖ * ‖e t‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖e t‖ := mul_le_mul_of_nonneg_right (hdef t ht) (norm_nonneg _)
    have hinner : ⟪full t (x t) - m' t, e t⟫
        = ⟪full t (x t) - full t (m t), e t⟫ + ⟪full t (m t) - m' t, e t⟫ := by
      rw [hsplit, inner_add_left]
    rw [hVe]
    nlinarith [hc, hd, hinner]
  -- Fence `V` below the ceiling `(gap 0 + δ/λ)²` via strictly-larger comparison constants.
  set gap0 : ℝ := ‖x 0 - m 0‖ with hgap0
  have hgap0_nonneg : 0 ≤ gap0 := norm_nonneg _
  have hVη : ∀ {η : ℝ}, 0 < η → ∀ t, 0 ≤ t → V t ≤ (gap0 + (δ + η) / lam) ^ 2 := by
    intro η hη t ht
    set C : ℝ := gap0 + (δ + η) / lam with hC
    have hCpos : 0 < C := by
      have : 0 < (δ + η) / lam := by positivity
      linarith
    have hVcont : ContinuousOn V (Icc 0 t) :=
      fun s hs => (hVd s hs.1).continuousAt.continuousWithinAt
    have ha : V 0 ≤ C ^ 2 := by
      have hV0 : V 0 = gap0 ^ 2 := by
        simp only [hV, he, hgap0]; rw [real_inner_self_eq_norm_sq]
      rw [hV0]
      have hle : gap0 ≤ C := by
        rw [hC]
        have hdη : 0 ≤ (δ + η) / lam := by positivity
        linarith
      exact pow_le_pow_left₀ hgap0_nonneg hle 2
    have hbound : ∀ s ∈ Ico 0 t, V s = C ^ 2 →
        2 * ⟪full s (x s) - m' s, e s⟫ < (0 : ℝ) := by
      intro s hs hVs
      have hs0 : 0 ≤ s := hs.1
      have hVe : V s = ‖e s‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
      have hnormC : ‖e s‖ = C := by
        have h1 : ‖e s‖ ^ 2 = C ^ 2 := by rw [← hVe, hVs]
        nlinarith [norm_nonneg (e s), hCpos.le, sq_nonneg (‖e s‖ - C), h1]
      have hb := hVbound s hs0
      rw [hVs] at hb
      have hcalc : -2 * lam * C ^ 2 + 2 * δ * ‖e s‖ < 0 := by
        rw [hnormC]
        have hexpand : -2 * lam * C ^ 2 + 2 * δ * C = 2 * C * (δ - lam * C) := by ring
        have hlamC : lam * C = lam * gap0 + (δ + η) := by
          rw [hC, mul_add]
          field_simp
        have hfac : δ - lam * C = -(lam * gap0) - η := by rw [hlamC]; ring
        rw [hexpand, hfac]
        have hneg : -(lam * gap0) - η < 0 := by
          have : 0 ≤ lam * gap0 := mul_nonneg hlam.le hgap0_nonneg
          linarith
        have : 2 * C > 0 := by linarith
        exact mul_neg_of_pos_of_neg this hneg
      linarith [hb, hcalc]
    have hkey := image_le_of_deriv_right_lt_deriv_boundary
      (f := V) (f' := fun s => 2 * ⟪full s (x s) - m' s, e s⟫) (a := 0) (b := t)
      hVcont (fun s hs => (hVd s hs.1).hasDerivWithinAt)
      (B := fun _ => C ^ 2) (B' := fun _ => 0) ha (fun _ => hasDerivAt_const _ (C ^ 2))
      (fun s hs hVs => hbound s hs hVs)
    exact hkey (right_mem_Icc.2 ht)
  intro t ht
  have hVlim : V t ≤ (gap0 + δ / lam) ^ 2 := by
    have hcont : ContinuousWithinAt (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (Ioi 0) 0 := by
      fun_prop
    have htend : Tendsto (fun η : ℝ => (gap0 + (δ + η) / lam) ^ 2) (𝓝[>] 0)
        (𝓝 ((gap0 + δ / lam) ^ 2)) := by
      have h := hcont.tendsto
      simpa [add_zero] using h
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hVη hη t ht
  set C0 : ℝ := gap0 + δ / lam with hC0
  have hC0_nonneg : 0 ≤ C0 := by
    rw [hC0]
    have hdl : 0 ≤ δ / lam := by positivity
    linarith
  have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
  rw [hVe] at hVlim
  have : ‖e t‖ ≤ C0 := by nlinarith [norm_nonneg (e t), hC0_nonneg, sq_nonneg (‖e t‖ - C0)]
  simpa [he, hC0] using this

/-- **Dissipative tracking with decaying initial error.** Under the hypotheses of
`coupled_dissipative_ceiling_forward`, `‖x t - m t‖ ≤ e^{-λt} ‖x 0 - m 0‖ + δ/λ` for `t ≥ 0`. -/
theorem coupled_dissipative_decay_forward {full : ℝ → E → E} {x m m' : ℝ → E} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (full t (x t)) t) (hm : ∀ t, 0 ≤ t → HasDerivAt m (m' t) t)
    (hcon : ∀ t, 0 ≤ t → ⟪full t (x t) - full t (m t), x t - m t⟫ ≤ -lam * ‖x t - m t‖ ^ 2)
    (hdef : ∀ t, 0 ≤ t → ‖full t (m t) - m' t‖ ≤ δ) :
    ∀ t, 0 ≤ t → ‖x t - m t‖ ≤ Real.exp (-lam * t) * ‖x 0 - m 0‖ + δ / lam := by
  set e : ℝ → E := fun t => x t - m t with he
  have hed : ∀ t, 0 ≤ t → HasDerivAt e (full t (x t) - m' t) t := fun t ht => (hx t ht).sub (hm t ht)
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVe : ∀ t, V t = ‖e t‖ ^ 2 := fun t => by simp only [hV]; rw [real_inner_self_eq_norm_sq]
  have hVd : ∀ t, 0 ≤ t → HasDerivAt V (2 * ⟪full t (x t) - m' t, e t⟫) t := by
    intro t ht
    have h := (hed t ht).inner ℝ (hed t ht)
    have hsym : ⟪e t, full t (x t) - m' t⟫ + ⟪full t (x t) - m' t, e t⟫
        = 2 * ⟪full t (x t) - m' t, e t⟫ := by
      rw [real_inner_comm (e t) (full t (x t) - m' t)]; ring
    simpa [hV, hsym] using h
  have hVbound : ∀ t, 0 ≤ t →
      2 * ⟪full t (x t) - m' t, e t⟫ ≤ -2 * lam * V t + 2 * δ * ‖e t‖ := by
    intro t ht
    have hsplit : full t (x t) - m' t = (full t (x t) - full t (m t)) + (full t (m t) - m' t) := by
      abel
    have hc : ⟪full t (x t) - full t (m t), e t⟫ ≤ -lam * ‖e t‖ ^ 2 := hcon t ht
    have hd : ⟪full t (m t) - m' t, e t⟫ ≤ δ * ‖e t‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hdef t ht) (norm_nonneg _))
    rw [hsplit, inner_add_left, hVe t]
    nlinarith [hc, hd]
  set g0 : ℝ := ‖e 0‖ with hg0
  have hg0nn : 0 ≤ g0 := norm_nonneg _
  -- comparison with `C(t)² = (e^{-λt} g0 + (δ+η)/λ)²`
  have hVη : ∀ {η : ℝ}, 0 < η → ∀ t, 0 ≤ t →
      V t ≤ (Real.exp (-lam * t) * g0 + (δ + η) / lam) ^ 2 := by
    intro η hη t ht
    set C : ℝ → ℝ := fun s => Real.exp (-lam * s) * g0 + (δ + η) / lam with hC
    have hCpos : ∀ s, 0 < C s := fun s => by
      have : 0 < (δ + η) / lam := by positivity
      have : 0 ≤ Real.exp (-lam * s) * g0 := mul_nonneg (Real.exp_pos _).le hg0nn
      simp only [hC]; linarith
    have hCd : ∀ s, HasDerivAt C (-lam * Real.exp (-lam * s) * g0) s := by
      intro s
      have h := ((hasDerivAt_id s).const_mul (-lam)).exp.mul_const g0
      have h2 := h.add_const ((δ + η) / lam)
      convert h2 using 1
      · funext s'; simp only [hC, id]
      · simp only [id]; ring
    have hBd : ∀ s, HasDerivAt (fun s => C s ^ 2)
        (2 * C s * (-lam * Real.exp (-lam * s) * g0)) s := by
      intro s
      have := (hCd s).pow 2
      convert this using 1; ring
    have hkey := image_le_of_deriv_right_lt_deriv_boundary' (f := V)
      (f' := fun s => 2 * ⟪full s (x s) - m' s, e s⟫) (a := 0) (b := t)
      (fun s hs => (hVd s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => (hVd s hs.1).hasDerivWithinAt)
      (B := fun s => C s ^ 2) (B' := fun s => 2 * C s * (-lam * Real.exp (-lam * s) * g0))
      (by
        rw [hVe 0]
        have hle : g0 ≤ C 0 := by
          simp only [hC, mul_zero, Real.exp_zero, one_mul]
          have : 0 ≤ (δ + η) / lam := by positivity
          linarith
        exact pow_le_pow_left₀ hg0nn hle 2)
      (fun s _ => (hBd s).continuousAt.continuousWithinAt)
      (fun s _ => (hBd s).hasDerivWithinAt)
      (fun s hs hVs => by
        have hb := hVbound s hs.1
        have hnorm : ‖e s‖ = C s := by
          have h1 : ‖e s‖ ^ 2 = C s ^ 2 := by rw [← hVe s, hVs]
          nlinarith [norm_nonneg (e s), (hCpos s).le, sq_nonneg (‖e s‖ - C s), h1]
        rw [hVs, hnorm] at hb
        have hlamC : lam * C s = lam * (Real.exp (-lam * s) * g0) + (δ + η) := by
          simp only [hC]; field_simp
        have hlt : 2 * C s * (δ - lam * C s) < 2 * C s * (-lam * Real.exp (-lam * s) * g0) := by
          apply mul_lt_mul_of_pos_left _ (by linarith [hCpos s])
          rw [hlamC]; linarith
        have : -2 * lam * C s ^ 2 + 2 * δ * C s = 2 * C s * (δ - lam * C s) := by ring
        linarith)
    exact hkey (right_mem_Icc.2 ht)
  intro t ht
  have hVlim : V t ≤ (Real.exp (-lam * t) * g0 + δ / lam) ^ 2 := by
    have htend : Tendsto (fun η : ℝ => (Real.exp (-lam * t) * g0 + (δ + η) / lam) ^ 2) (𝓝[>] 0)
        (𝓝 ((Real.exp (-lam * t) * g0 + δ / lam) ^ 2)) := by
      have hc : Continuous (fun η : ℝ => (Real.exp (-lam * t) * g0 + (δ + η) / lam) ^ 2) := by
        fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hVη hη t ht
  rw [hVe t] at hVlim
  have hC0 : 0 ≤ Real.exp (-lam * t) * g0 + δ / lam :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hg0nn) (by positivity)
  have : ‖e t‖ ≤ Real.exp (-lam * t) * g0 + δ / lam := by
    nlinarith [norm_nonneg (e t), sq_nonneg (‖e t‖ - (Real.exp (-lam * t) * g0 + δ / lam))]
  simpa [he, hg0] using this

end ODE


namespace CRNT
namespace Enzyme

/-- **QSSA error bound for the Michaelis–Menten system with moving substrate.** -/
theorem qssa_error_le {k₁ km₁ k₂ e₀ D : ℝ} (hk₁ : 0 < k₁) (hkm : 0 < km₁ + k₂) (he₀ : 0 ≤ e₀)
    (hD : 0 ≤ D) {s c : ℝ → ℝ}
    (hs : ∀ t, 0 ≤ t → HasDerivAt s (-k₁ * (e₀ - c t) * s t + km₁ * c t) t)
    (hc : ∀ t, 0 ≤ t → HasDerivAt c (fastField k₁ km₁ k₂ e₀ (s t) (c t)) t)
    (hsnn : ∀ t, 0 ≤ t → 0 ≤ s t)
    (hdrift : ∀ t, 0 ≤ t → |-k₁ * (e₀ - c t) * s t + km₁ * c t| ≤ D) :
    ∀ t, 0 ≤ t → |c t - qss k₁ km₁ k₂ e₀ (s t)| ≤
      |c 0 - qss k₁ km₁ k₂ e₀ (s 0)| + (e₀ / ((km₁ + k₂) / k₁)) * D / (km₁ + k₂) := by
  set K := (km₁ + k₂) / k₁ with hK
  have hKpos : 0 < K := div_pos hkm hk₁
  set sd : ℝ → ℝ := fun t => -k₁ * (e₀ - c t) * s t + km₁ * c t with hsd
  set m' : ℝ → ℝ := fun t => e₀ * K / (s t + K) ^ 2 * sd t with hm'
  have hden : ∀ t, 0 ≤ t → 0 < s t + K := fun t ht => by linarith [hsnn t ht]
  have hm : ∀ t, 0 ≤ t → HasDerivAt (fun τ => qss k₁ km₁ k₂ e₀ (s τ)) (m' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => e₀ * s τ) (e₀ * sd t) t := (hs t ht).const_mul e₀
    have h2 : HasDerivAt (fun τ => s τ + K) (sd t) t := (hs t ht).add_const K
    have h3 := h1.div h2 (hden t ht).ne'
    convert h3 using 1
    · funext τ; simp [qss, hK]
    · simp only [hm']; field_simp; ring
  have hcon : ∀ t, 0 ≤ t →
      ⟪fastField k₁ km₁ k₂ e₀ (s t) (c t) - fastField k₁ km₁ k₂ e₀ (s t) (qss k₁ km₁ k₂ e₀ (s t)),
        c t - qss k₁ km₁ k₂ e₀ (s t)⟫ ≤ -(km₁ + k₂) * ‖c t - qss k₁ km₁ k₂ e₀ (s t)‖ ^ 2 :=
    fun t ht => fastField_isContracting hk₁.le (hsnn t ht) _ (mem_univ _) _ (mem_univ _)
  have hdef : ∀ t, 0 ≤ t →
      ‖fastField k₁ km₁ k₂ e₀ (s t) (qss k₁ km₁ k₂ e₀ (s t)) - m' t‖ ≤ e₀ / K * D := by
    intro t ht
    rw [fastField_qss hk₁ hkm (hsnn t ht), zero_sub, norm_neg, Real.norm_eq_abs]
    simp only [hm']
    rw [abs_mul]
    have hcoef : |e₀ * K / (s t + K) ^ 2| ≤ e₀ / K := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ (pow_pos (hden t ht) 2) hKpos]
      have : K ^ 2 ≤ (s t + K) ^ 2 := by nlinarith [hsnn t ht]
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg he₀ hKpos.le)]
    exact mul_le_mul hcoef (hdrift t ht) (abs_nonneg _) (by positivity)
  have h := ODE.coupled_dissipative_ceiling_forward (full := fun t y => fastField k₁ km₁ k₂ e₀ (s t) y)
    (x := c) (m := fun τ => qss k₁ km₁ k₂ e₀ (s τ)) (m' := m') hkm (by positivity) hc hm hcon hdef
  intro t ht
  have := h t ht
  simpa [Real.norm_eq_abs] using this

/-- **Tikhonov-type QSSA bound**: the initial mismatch decays at rate `k₋₁ + k₂`. -/
theorem qssa_error_decay {k₁ km₁ k₂ e₀ D : ℝ} (hk₁ : 0 < k₁) (hkm : 0 < km₁ + k₂) (he₀ : 0 ≤ e₀)
    (hD : 0 ≤ D) {s c : ℝ → ℝ}
    (hs : ∀ t, 0 ≤ t → HasDerivAt s (-k₁ * (e₀ - c t) * s t + km₁ * c t) t)
    (hc : ∀ t, 0 ≤ t → HasDerivAt c (fastField k₁ km₁ k₂ e₀ (s t) (c t)) t)
    (hsnn : ∀ t, 0 ≤ t → 0 ≤ s t)
    (hdrift : ∀ t, 0 ≤ t → |-k₁ * (e₀ - c t) * s t + km₁ * c t| ≤ D) :
    ∀ t, 0 ≤ t → |c t - qss k₁ km₁ k₂ e₀ (s t)| ≤
      Real.exp (-(km₁ + k₂) * t) * |c 0 - qss k₁ km₁ k₂ e₀ (s 0)|
        + (e₀ / ((km₁ + k₂) / k₁)) * D / (km₁ + k₂) := by
  set K := (km₁ + k₂) / k₁ with hK
  have hKpos : 0 < K := div_pos hkm hk₁
  set sd : ℝ → ℝ := fun t => -k₁ * (e₀ - c t) * s t + km₁ * c t with hsd
  set m' : ℝ → ℝ := fun t => e₀ * K / (s t + K) ^ 2 * sd t with hm'
  have hden : ∀ t, 0 ≤ t → 0 < s t + K := fun t ht => by linarith [hsnn t ht]
  have hm : ∀ t, 0 ≤ t → HasDerivAt (fun τ => qss k₁ km₁ k₂ e₀ (s τ)) (m' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => e₀ * s τ) (e₀ * sd t) t := (hs t ht).const_mul e₀
    have h2 : HasDerivAt (fun τ => s τ + K) (sd t) t := (hs t ht).add_const K
    have h3 := h1.div h2 (hden t ht).ne'
    convert h3 using 1
    · funext τ; simp [qss, hK]
    · simp only [hm']; field_simp; ring
  have hcon : ∀ t, 0 ≤ t →
      ⟪fastField k₁ km₁ k₂ e₀ (s t) (c t) - fastField k₁ km₁ k₂ e₀ (s t) (qss k₁ km₁ k₂ e₀ (s t)),
        c t - qss k₁ km₁ k₂ e₀ (s t)⟫ ≤ -(km₁ + k₂) * ‖c t - qss k₁ km₁ k₂ e₀ (s t)‖ ^ 2 :=
    fun t ht => fastField_isContracting hk₁.le (hsnn t ht) _ (mem_univ _) _ (mem_univ _)
  have hdef : ∀ t, 0 ≤ t →
      ‖fastField k₁ km₁ k₂ e₀ (s t) (qss k₁ km₁ k₂ e₀ (s t)) - m' t‖ ≤ e₀ / K * D := by
    intro t ht
    rw [fastField_qss hk₁ hkm (hsnn t ht), zero_sub, norm_neg, Real.norm_eq_abs]
    simp only [hm']
    rw [abs_mul]
    have hcoef : |e₀ * K / (s t + K) ^ 2| ≤ e₀ / K := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ (pow_pos (hden t ht) 2) hKpos]
      have : K ^ 2 ≤ (s t + K) ^ 2 := by nlinarith [hsnn t ht]
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg he₀ hKpos.le)]
    exact mul_le_mul hcoef (hdrift t ht) (abs_nonneg _) (by positivity)
  have h := ODE.coupled_dissipative_decay_forward (full := fun t y => fastField k₁ km₁ k₂ e₀ (s t) y)
    (x := c) (m := fun τ => qss k₁ km₁ k₂ e₀ (s τ)) (m' := m') hkm (by positivity) hc hm hcon hdef
  intro t ht
  have := h t ht
  simpa [Real.norm_eq_abs] using this

end Enzyme
end CRNT
