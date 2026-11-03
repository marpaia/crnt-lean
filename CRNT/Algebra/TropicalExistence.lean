import CRNT.Algebra.TropicalEquilibration
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Tropical equilibrations give scaled roots: one variable

The converse direction of `CRNT.Algebra.TropicalEquilibration` in one variable. For
`f_ε(x) = ∑_j c_j ε^{a_j} x^{m_j}` and an order `u`, let `e_min` be a lower bound of the orders
`a_j + m_j u` of the nonzero terms and let `P(ξ) = ∑_{a_j + m_j u = e_min} c_j ξ^{m_j}` be the leading
part. If `P` changes sign on an interval `[ξ₁, ξ₂] ⊂ (0, ∞)`, then for every small `ε > 0` the
polynomial `f_ε` has a positive root `ε^u ξ` with `ξ ∈ (ξ₁, ξ₂)`, and these roots have valuation
`log x / log ε → u`. A sign change of `P` is the transversality condition of tropical
equilibration: by `Tropical.isEquilibrated_of_scaled_zeros` the minimum must be attained by terms of
both signs, and with two terms of distinct exponents `P` changes sign.

* `scaledPoly`, `leadingPart`.
* `tendsto_scaled_leadingPart`: `ε^{−e_min} f_ε(ε^u ξ) → P(ξ)`.
* `eventually_exists_scaled_root`: roots for all small `ε`.
* `exists_scaled_root_family`: a family of roots with valuation `u`.
* `Network.oneSpecies_exists_scaled_steadyStates`: for a one-species network with rate constants
  `κ̄_r ε^{a_r}`, a sign change of the leading part gives positive steady states `x(ε)` with
  valuation `u`.

The multi-variable converse (Hensel/implicit-function lifting of nondegenerate equilibrations)
is not formalized.
-/

namespace CRNT

namespace Tropical

open Filter Topology Set

variable {J : Type*} [Fintype J]

/-- `f_ε(x) = ∑_j c_j ε^{a_j} x^{m_j}`. -/
noncomputable def scaledPoly (c a m : J → ℝ) (ε x : ℝ) : ℝ := ∑ j, c j * ε ^ a j * x ^ m j

/-- The leading part at the order `u` and level `e_min`. -/
noncomputable def leadingPart (c a m : J → ℝ) (u emin ξ : ℝ) : ℝ := by
  classical
  exact ∑ j, if a j + m j * u = emin then c j * ξ ^ m j else 0

theorem scaledPoly_scale (c a m : J → ℝ) (u emin : ℝ) {ε ξ : ℝ} (hε : 0 < ε) (hξ : 0 < ξ) :
    ε ^ (-emin) * scaledPoly c a m ε (ε ^ u * ξ) =
      ∑ j, c j * ε ^ (a j + m j * u - emin) * ξ ^ m j := by
  rw [scaledPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) hξ.le, ← Real.rpow_mul hε.le,
    show a j + m j * u - emin = -emin + a j + u * m j by ring,
    Real.rpow_add hε, Real.rpow_add hε]
  ring

/-- **The rescaled polynomial converges to the leading part.** -/
theorem tendsto_scaled_leadingPart (c a m : J → ℝ) (u emin : ℝ)
    (hmin : ∀ j, c j ≠ 0 → emin ≤ a j + m j * u) {ξ : ℝ} (hξ : 0 < ξ) :
    Tendsto (fun ε => ε ^ (-emin) * scaledPoly c a m ε (ε ^ u * ξ)) (𝓝[>] 0)
      (𝓝 (leadingPart c a m u emin ξ)) := by
  classical
  have hterm : ∀ j, Tendsto (fun ε : ℝ => c j * ε ^ (a j + m j * u - emin) * ξ ^ m j) (𝓝[>] 0)
      (𝓝 (if a j + m j * u = emin then c j * ξ ^ m j else 0)) := by
    intro j
    by_cases hc : c j = 0
    · simp [hc]
    by_cases he : a j + m j * u = emin
    · simp only [he, sub_self, ↓reduceIte]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [Real.rpow_zero, mul_one]
    · simp only [he, ↓reduceIte]
      have hpos : 0 < a j + m j * u - emin := sub_pos.mpr (lt_of_le_of_ne (hmin j hc) (Ne.symm he))
      have hcont : ContinuousAt (fun ε : ℝ => ε ^ (a j + m j * u - emin)) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr hpos.le)
      have h0 : Tendsto (fun ε : ℝ => ε ^ (a j + m j * u - emin)) (𝓝[>] 0) (𝓝 0) := by
        have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        rwa [Real.zero_rpow hpos.ne'] at this
      have := (h0.const_mul (c j)).mul_const (ξ ^ m j)
      simpa using this
  have hsum := tendsto_finsetSum (Finset.univ : Finset J) fun j _ => hterm j
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (scaledPoly_scale c a m u emin hε hξ).symm

theorem scaledPoly_continuousOn (c a m : J → ℝ) {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ξ₁ ξ₂ : ℝ}
    (h₁ : 0 < ξ₁) : ContinuousOn (fun ξ => scaledPoly c a m ε (ε ^ u * ξ)) (Icc ξ₁ ξ₂) := by
  unfold scaledPoly
  refine continuousOn_finsetSum _ fun j _ => fun ξ hξ => ?_
  have hξ0 : 0 < ξ := lt_of_lt_of_le h₁ hξ.1
  have hx : 0 < ε ^ u * ξ := mul_pos (Real.rpow_pos_of_pos hε _) hξ0
  refine ContinuousAt.continuousWithinAt ?_
  exact continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inl hx.ne')).comp
    (continuousAt_const.mul continuousAt_id))

/-- **Roots for every small `ε`.** If the leading part has opposite signs at `ξ₁ < ξ₂` in
`(0, ∞)`, then for every small `ε > 0` there is `ξ ∈ (ξ₁, ξ₂)` with `f_ε(ε^u ξ) = 0`. -/
theorem eventually_exists_scaled_root (c a m : J → ℝ) (u emin : ℝ)
    (hmin : ∀ j, c j ≠ 0 → emin ≤ a j + m j * u) {ξ₁ ξ₂ : ℝ} (h₁ : 0 < ξ₁) (h₁₂ : ξ₁ < ξ₂)
    (hsign : leadingPart c a m u emin ξ₁ * leadingPart c a m u emin ξ₂ < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ξ ∈ Ioo ξ₁ ξ₂, scaledPoly c a m ε (ε ^ u * ξ) = 0 := by
  have t₁ := tendsto_scaled_leadingPart c a m u emin hmin h₁
  have t₂ := tendsto_scaled_leadingPart c a m u emin hmin (h₁.trans h₁₂)
  rcases mul_neg_iff.mp hsign with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · filter_upwards [t₁.eventually (lt_mem_nhds hp), t₂.eventually (gt_mem_nhds hn),
      self_mem_nhdsWithin] with ε e₁ e₂ (hε : 0 < ε)
    have hs : 0 < ε ^ (-emin) := Real.rpow_pos_of_pos hε _
    have v₁ : 0 < scaledPoly c a m ε (ε ^ u * ξ₁) := (pos_iff_pos_of_mul_pos e₁).mp hs
    have v₂ : scaledPoly c a m ε (ε ^ u * ξ₂) < 0 := by
      by_contra h; push Not at h; nlinarith [mul_nonneg hs.le h]
    obtain ⟨ξ, hξ, hz⟩ := intermediate_value_Ioo' h₁₂.le
      (scaledPoly_continuousOn c a m hε u h₁) ⟨v₂, v₁⟩
    exact ⟨ξ, hξ, hz⟩
  · filter_upwards [t₁.eventually (gt_mem_nhds hn), t₂.eventually (lt_mem_nhds hp),
      self_mem_nhdsWithin] with ε e₁ e₂ (hε : 0 < ε)
    have hs : 0 < ε ^ (-emin) := Real.rpow_pos_of_pos hε _
    have v₂ : 0 < scaledPoly c a m ε (ε ^ u * ξ₂) := (pos_iff_pos_of_mul_pos e₂).mp hs
    have v₁ : scaledPoly c a m ε (ε ^ u * ξ₁) < 0 := by
      by_contra h; push Not at h; nlinarith [mul_nonneg hs.le h]
    obtain ⟨ξ, hξ, hz⟩ := intermediate_value_Ioo h₁₂.le
      (scaledPoly_continuousOn c a m hε u h₁) ⟨v₁, v₂⟩
    exact ⟨ξ, hξ, hz⟩

/-- **A family of roots with valuation `u`.** Under the hypotheses of
`eventually_exists_scaled_root` there is `x(ε)`, a positive root of `f_ε` for every small `ε`,
with `log x(ε) / log ε → u` as `ε → 0⁺`. -/
theorem exists_scaled_root_family (c a m : J → ℝ) (u emin : ℝ)
    (hmin : ∀ j, c j ≠ 0 → emin ≤ a j + m j * u) {ξ₁ ξ₂ : ℝ} (h₁ : 0 < ξ₁) (h₁₂ : ξ₁ < ξ₂)
    (hsign : leadingPart c a m u emin ξ₁ * leadingPart c a m u emin ξ₂ < 0) :
    ∃ x : ℝ → ℝ, (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < x ε ∧ scaledPoly c a m ε (x ε) = 0) ∧
      Tendsto (fun ε => Real.log (x ε) / Real.log ε) (𝓝[>] 0) (𝓝 u) := by
  classical
  have hev := eventually_exists_scaled_root c a m u emin hmin h₁ h₁₂ hsign
  let ξf : ℝ → ℝ := fun ε =>
    if h : ∃ ξ ∈ Ioo ξ₁ ξ₂, scaledPoly c a m ε (ε ^ u * ξ) = 0 then h.choose else ξ₁
  have hξf : ∀ ε, ξ₁ ≤ ξf ε ∧ ξf ε ≤ ξ₂ := by
    intro ε
    simp only [ξf]
    split_ifs with h
    · exact ⟨h.choose_spec.1.1.le, h.choose_spec.1.2.le⟩
    · exact ⟨le_rfl, h₁₂.le⟩
  refine ⟨fun ε => ε ^ u * ξf ε, ?_, ?_⟩
  · filter_upwards [hev, self_mem_nhdsWithin] with ε h (hε : 0 < ε)
    refine ⟨mul_pos (Real.rpow_pos_of_pos hε _) (lt_of_lt_of_le h₁ (hξf ε).1), ?_⟩
    simp only [ξf, h, ↓reduceDIte]
    exact h.choose_spec.2
  · -- `log x / log ε = u + log ξ / log ε`
    have hlog : Tendsto Real.log (𝓝[>] (0 : ℝ)) atBot := Real.tendsto_log_nhdsGT_zero
    set B : ℝ := |Real.log ξ₁| + |Real.log ξ₂| with hB
    have hbound : ∀ ε, |Real.log (ξf ε)| ≤ B := by
      intro ε
      have hpos : 0 < ξf ε := lt_of_lt_of_le h₁ (hξf ε).1
      rw [abs_le]
      constructor
      · have := Real.log_le_log h₁ (hξf ε).1
        have := neg_abs_le (Real.log ξ₁)
        have := abs_nonneg (Real.log ξ₂)
        linarith
      · have := Real.log_le_log hpos (hξf ε).2
        have := le_abs_self (Real.log ξ₂)
        have := abs_nonneg (Real.log ξ₁)
        linarith
    have hsmall : Tendsto (fun ε => Real.log (ξf ε) / Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have hinv : Tendsto (fun ε => (Real.log ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_inv_atBot_zero.comp hlog
      have hB' : Tendsto (fun ε => B * |(Real.log ε)⁻¹|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using (hinv.abs.const_mul B)
      refine squeeze_zero_norm (fun ε => ?_) hB'
      rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound ε) (abs_nonneg _)
    have := hsmall.const_add u
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hlog.eventually_lt_atBot 0] with ε (hε : 0 < ε) hl
    have hpos : 0 < ξf ε := lt_of_lt_of_le h₁ (hξf ε).1
    rw [Real.log_mul (Real.rpow_pos_of_pos hε _).ne' hpos.ne', Real.log_rpow hε, add_div,
      mul_div_cancel_right₀ _ hl.ne]

end Tropical

namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Scaled steady states of a one-species network.** Let `S` have the single species `s₀`, rate
constants `κ̄_r ε^{a_r}`, and let the leading part of the steady-state polynomial at the order `u`
change sign on `[ξ₁, ξ₂] ⊂ (0, ∞)`. Then there are positive steady states `x(ε)` for every small
`ε` with `log x(ε) / log ε → u`. -/
theorem oneSpecies_exists_scaled_steadyStates (N : Network S) (s₀ : S) (hS : ∀ s, s = s₀)
    (κ : RateConstants N) (a : N.R → ℝ) (u emin : ℝ)
    (hmin : ∀ r, κ.k r * N.reactionVector r s₀ ≠ 0 →
      emin ≤ a r + ((N.reaction r).source s₀ : ℝ) * u) {ξ₁ ξ₂ : ℝ} (h₁ : 0 < ξ₁) (h₁₂ : ξ₁ < ξ₂)
    (hsign : Tropical.leadingPart (fun r => κ.k r * N.reactionVector r s₀) a
        (fun r => ((N.reaction r).source s₀ : ℝ)) u emin ξ₁ *
      Tropical.leadingPart (fun r => κ.k r * N.reactionVector r s₀) a
        (fun r => ((N.reaction r).source s₀ : ℝ)) u emin ξ₂ < 0) :
    ∃ x : ℝ → ℝ, (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ hε : 0 < ε, 0 < x ε ∧
      N.IsMassActionSteadyState (N.scaledRateConstants κ a ε hε) (fun _ => x ε)) ∧
      Tendsto (fun ε => Real.log (x ε) / Real.log ε) (𝓝[>] 0) (𝓝 u) := by
  obtain ⟨x, hx, hval⟩ := Tropical.exists_scaled_root_family _ _ _ u emin hmin h₁ h₁₂ hsign
  refine ⟨x, ?_, hval⟩
  filter_upwards [hx, self_mem_nhdsWithin] with ε ⟨hxpos, hroot⟩ (hε : 0 < ε)
  refine ⟨hε, hxpos, fun s => ?_⟩
  show N.massActionVectorField _ _ s = 0
  rw [hS s, massActionVectorField_apply]
  rw [Tropical.scaledPoly] at hroot
  rw [← hroot]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hmono : (N.reaction r).source.massActionMonomial (fun _ => x ε) =
      x ε ^ ((N.reaction r).source s₀ : ℝ) := by
    rw [Complex.massActionMonomial, Real.rpow_natCast]
    rw [Finset.prod_eq_single s₀ (fun s _ hs => absurd (hS s) hs) (by simp)]
  simp only [massActionRate, scaledRateConstants, hmono]
  ring

end Network

end CRNT
