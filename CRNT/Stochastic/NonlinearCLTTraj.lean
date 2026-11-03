import CRNT.Stochastic.NonlinearCLT

/-!
# The nonlinear CLT along a trajectory

The generator–duality argument of `NonlinearCLT`, with the centring `x*` replaced by a solution
`x(u)` of the mass-action equation: for a conservative network, a solution `x` on `[0, T]`, and a
`C¹` solution `θ(·)` of the adjoint linearized equation along `x`,
`θ'(u) · v = −θ(u) · Df(x(u)) v`, with `√V (n_V/V − x(0)) → z₀`,

`E exp(i θ(T) · √V (X^V(T)/V − x(T))) → exp(i θ(0) · z₀ − ½ ∫₀ᵀ ∑_r λ_r(x(u)) (θ(u) · Δ_r)² du)`

(`nonlinear_clt_traj`).  Compared with the equilibrium case the time derivative of the centred
fluctuation contributes `−√V θ · f(x(u))`, which cancels the leading part of the drift; the
Taylor and Lipschitz constants are taken uniform over base points in a box
(`exists_taylor_bound_unif`, `exists_rate_lipschitz_unif`).
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Second-order Taylor bound, uniform over base points of a box.** -/
theorem exists_taylor_bound_unif (N : Network S) (κ : RateConstants N) {Rb : ℝ} :
    ∃ L₂ : ℝ, 0 ≤ L₂ ∧ ∀ xs ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ‖N.massActionVectorField κ z - N.massActionVectorField κ xs -
        fderiv ℝ (N.massActionVectorField κ) xs (z - xs)‖ ≤ L₂ * ‖z - xs‖ ^ 2 := by
  set f := N.massActionVectorField κ with hf
  have hfC : ContDiff ℝ ⊤ f := N.contDiff_massActionVectorField κ
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hfC.fderiv_right (by norm_num)
  obtain ⟨L, hL⟩ := (hDf.contDiffOn (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  refine ⟨L, L.2, fun xs hxs z hz => ?_⟩
  set J := fderiv ℝ f xs with hJ
  set g : Concentration S → Concentration S := fun w => f w - J w with hg
  have hseg : segment ℝ xs z ⊆ Icc (0 : Concentration S) fun _ => Rb :=
    (convex_Icc _ _).segment_subset hxs hz
  have hder : ∀ w ∈ segment ℝ xs z, HasFDerivWithinAt g (fderiv ℝ f w - J) (segment ℝ xs z) w :=
    fun w _ => ((hfC.differentiable (by simp) w).hasFDerivAt.sub J.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ w ∈ segment ℝ xs z, ‖fderiv ℝ f w - J‖ ≤ L * ‖z - xs‖ := by
    intro w hw
    have h1 := hL.norm_sub_le (hseg hw) hxs
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    have : a • xs + b • z - xs = b • (z - xs) := by
      rw [show a = 1 - b by linarith]; simp [sub_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have := (convex_segment xs z).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound
    (left_mem_segment ℝ xs z) (right_mem_segment ℝ xs z)
  have hgd : g z - g xs = f z - f xs - J (z - xs) := by
    simp only [hg, map_sub]; abel
  rw [hgd] at this
  calc ‖f z - f xs - J (z - xs)‖ ≤ L * ‖z - xs‖ * ‖z - xs‖ := this
    _ = (L : ℝ) * ‖z - xs‖ ^ 2 := by ring

/-- **Lipschitz bound of the rates, uniform over base points of a box.** -/
theorem exists_rate_lipschitz_unif (N : Network S) (κ : RateConstants N) {Rb : ℝ} :
    ∃ Lρ : ℝ, 0 ≤ Lρ ∧ ∀ r, ∀ xs ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      |N.massActionRate κ r z - N.massActionRate κ r xs| ≤ Lρ * ‖z - xs‖ := by
  have hC : ∀ r, ContDiff ℝ 1 fun z => N.massActionRate κ r z := by
    intro r
    unfold massActionRate Complex.massActionMonomial
    fun_prop
  choose L hL using fun r => ((hC r).contDiffOn (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  refine ⟨∑ r, (L r : ℝ), Finset.sum_nonneg fun r _ => (L r).2, fun r xs hxs z hz => ?_⟩
  have h1 := (hL r).dist_le_mul z hz xs hxs
  rw [Real.dist_eq, dist_eq_norm] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := fun r => (L r : ℝ)) (fun r _ => (L r).2) (Finset.mem_univ r)

set_option maxHeartbeats 1600000 in
/-- **The generator error.** On counts with `c ≤ R₁ V`, for `θ` with `∑ |θ_s| ≤ Θ` and `θ'`
satisfying the adjoint relation `θ' · v = −θ · Df(x*) v`,
`|∑_r λ_r(c)(e^{i θ·Δ_r/√V} − 1) + i θ' · ζ(c) + θᵀGθ/2| ≤ C (1 + ‖ζ(c)‖²)/√V`. -/
theorem generator_error_le_traj (N : Network S) (κ : RateConstants N) {R₁ Θ : ℝ} (hR₁ : 0 ≤ R₁)
    (hΘ : 0 ≤ Θ) :
    ∃ C V₀ : ℝ, 0 ≤ C ∧ 1 ≤ V₀ ∧ ∀ xs ∈ Icc (0 : Concentration S) (fun _ => R₁),
      ∀ (θ θ' : S → ℝ), ∑ s, |θ s| ≤ Θ →
      (∀ v : S → ℝ, ∑ s, θ' s * v s =
        -∑ s, θ s * fderiv ℝ (N.massActionVectorField κ) xs v s) →
      ∀ V : ℝ, ∀ hV1 : 1 ≤ V, V₀ ≤ V → ∀ c : S → ℕ, (∀ s, (c s : ℝ) ≤ R₁ * V) →
        ‖∑ r, (N.stochasticMassActionRate (N.volumeScale κ V (by linarith)) c r : ℂ) *
            (Complex.exp (I * ((∑ s, θ s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θ' s * zeta V xs c s -
            Real.sqrt V * ∑ s, θ s * N.massActionVectorField κ xs s : ℝ) : ℂ) +
          ((N.quadG κ xs θ / 2 : ℝ) : ℂ)‖ ≤
        C * (1 + ‖zeta V xs c‖ ^ 2) / Real.sqrt V := by
  classical
  obtain ⟨L₂, hL₂0, hL₂⟩ := N.exists_taylor_bound_unif κ (Rb := R₁)
  obtain ⟨Lρ, hLρ0, hLρ⟩ := N.exists_rate_lipschitz_unif κ (Rb := R₁)
  set Dsum := ∑ r, ‖N.reactionVector r‖ with hDsum
  have hD0 : 0 ≤ Dsum := Finset.sum_nonneg fun r _ => norm_nonneg _
  set W := Θ * Dsum with hW
  have hW0 : 0 ≤ W := mul_nonneg hΘ hD0
  set B : N.R → ℝ := fun r => κ.k r * ((R₁ + N.srcMol r + 1) ^ N.srcMol r) ^ Fintype.card S
    with hB
  set E : N.R → ℝ := fun r => κ.k r * (((R₁ + N.srcMol r + 1) ^ N.srcMol r) ^
    (Fintype.card S + 1) * (Fintype.card S * (N.srcMol r : ℝ) ^ 2)) with hE
  have hB0 : ∀ r, 0 ≤ B r := fun r => mul_nonneg (κ.positive r).le (by positivity)
  have hE0 : ∀ r, 0 ≤ E r := fun r => mul_nonneg (κ.positive r).le (by positivity)
  set Bs := ∑ r, B r with hBs
  set Es := ∑ r, E r with hEs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun r _ => hB0 r
  have hEs0 : 0 ≤ Es := Finset.sum_nonneg fun r _ => hE0 r
  set nR := (Fintype.card N.R : ℝ) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set C := Bs * W ^ 3 + Θ * L₂ + Es * W + nR * Lρ * W ^ 2 + Es * W ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, max 1 (W ^ 2), hC0, le_max_left _ _, fun xs hxsB θ θ' hθ hadj V hV1 hV c hc => ?_⟩
  have hV0 : 0 < V := by linarith
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have hsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV0.le
  have hsV1 : 1 ≤ Real.sqrt V := Real.one_le_sqrt.mpr hV1
  have hWV : W ≤ Real.sqrt V := by
    rw [← Real.sqrt_sq hW0]
    exact Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hV)
  set z : Concentration S := fun s => (c s : ℝ) / V with hz
  have hzB : z ∈ Icc (0 : Concentration S) fun _ => R₁ := by
    refine ⟨fun s => div_nonneg (Nat.cast_nonneg _) hV0.le, fun s => ?_⟩
    show (c s : ℝ) / V ≤ R₁
    rw [div_le_iff₀ hV0]; exact hc s
  set ζ := zeta V xs c with hζ
  have hζz : ζ = Real.sqrt V • (z - xs) := by
    funext s; simp [hζ, zeta, hz]
  have hnormζ : ‖ζ‖ = Real.sqrt V * ‖z - xs‖ := by
    rw [hζz, norm_smul, Real.norm_eq_abs, abs_of_pos hsV]
  have hzx : ‖z - xs‖ = ‖ζ‖ / Real.sqrt V := by rw [hnormζ]; field_simp
  set J := fderiv ℝ (N.massActionVectorField κ) xs with hJ
  set td : N.R → ℝ := fun r => ∑ s, θ s * N.reactionVector r s with htd
  have htd_le : ∀ r, |td r| ≤ W := by
    intro r
    refine (abs_dot_le θ _).trans ?_
    have : ‖N.reactionVector r‖ ≤ Dsum := Finset.single_le_sum
      (f := fun r => ‖N.reactionVector r‖) (fun r _ => norm_nonneg _) (Finset.mem_univ r)
    exact mul_le_mul hθ this (norm_nonneg _) hΘ
  set lam : N.R → ℝ := fun r => N.stochasticMassActionRate (N.volumeScale κ V hV0) c r with hlam
  set dr : N.R → ℝ := fun r => N.densRate κ V r c with hdr
  have hlamV : ∀ r, lam r = V * dr r := fun r => stochasticRate_volumeScale N κ hV0 c r
  have hdr0 : ∀ r, 0 ≤ dr r := fun r => N.densRate_nonneg κ hV0 r c
  have hdrB : ∀ r, dr r ≤ B r := fun r => N.densRate_le κ r hV1 hR₁ c hc
  have herr : ∀ r, |dr r - N.massActionRate κ r z| ≤ E r / V := fun r =>
    N.abs_densRate_sub κ r hV1 hR₁ c hc
  set w : N.R → ℝ := fun r => td r / Real.sqrt V with hw
  have hw1 : ∀ r, |w r| ≤ W / Real.sqrt V := fun r => by
    rw [hw, abs_div, abs_of_pos hsV]; exact div_le_div_of_nonneg_right (htd_le r) hsV.le
  have hwle1 : ∀ r, |w r| ≤ 1 := fun r =>
    (hw1 r).trans (by rw [div_le_one hsV]; exact hWV)
  -- decomposition
  set T1 : ℂ := ∑ r, (lam r : ℂ) * (Complex.exp (I * (w r : ℝ)) - 1 - I * (w r : ℝ) +
    ((w r : ℝ) : ℂ) ^ 2 / 2) with hT1
  set T2 : ℝ := ∑ r, lam r * w r + (∑ s, θ' s * ζ s -
    Real.sqrt V * ∑ s, θ s * N.massActionVectorField κ xs s) with hT2
  set T3 : ℝ := ∑ r, lam r * w r ^ 2 - N.quadG κ xs θ with hT3
  have hdecomp : ∑ r, (lam r : ℂ) * (Complex.exp (I * (w r : ℝ)) - 1) +
      I * ((∑ s, θ' s * ζ s - Real.sqrt V * ∑ s, θ s * N.massActionVectorField κ xs s : ℝ) : ℂ) +
      ((N.quadG κ xs θ / 2 : ℝ) : ℂ) = T1 + I * (T2 : ℂ) - ((T3 / 2 : ℝ) : ℂ) := by
    simp only [hT1, hT2, hT3]
    push_cast
    have e1 : ∑ r, (lam r : ℂ) * (Complex.exp (I * (w r : ℂ)) - 1 - I * (w r : ℂ) +
        (w r : ℂ) ^ 2 / 2) = ∑ r, (lam r : ℂ) * (Complex.exp (I * (w r : ℂ)) - 1) -
          I * ∑ r, (lam r : ℂ) * (w r : ℂ) + (∑ r, (lam r : ℂ) * (w r : ℂ) ^ 2) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e1]
    ring
  -- bound T1
  have hT1b : ‖T1‖ ≤ Bs * W ^ 3 / Real.sqrt V := by
    calc ‖T1‖ ≤ ∑ r, ‖(lam r : ℂ) * (Complex.exp (I * (w r : ℝ)) - 1 - I * (w r : ℝ) +
          ((w r : ℝ) : ℂ) ^ 2 / 2)‖ := norm_sum_le _ _
      _ ≤ ∑ r, V * B r * (W / Real.sqrt V) ^ 3 := Finset.sum_le_sum fun r _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
            (N.stochasticMassActionRate_nonneg _ c r)]
          have h1 := norm_cexp_I_mul_sub_le (hwle1 r)
          have h2 : |w r| ^ 3 ≤ (W / Real.sqrt V) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hw1 r) 3
          have h3 : lam r ≤ V * B r := by rw [hlamV]; exact mul_le_mul_of_nonneg_left (hdrB r) hV0.le
          have h4 : 0 ≤ lam r := N.stochasticMassActionRate_nonneg _ c r
          calc lam r * ‖Complex.exp (I * (w r : ℂ)) - 1 - I * (w r : ℂ) + (w r : ℂ) ^ 2 / 2‖
              ≤ lam r * |w r| ^ 3 := mul_le_mul_of_nonneg_left h1 h4
            _ ≤ V * B r * (W / Real.sqrt V) ^ 3 :=
                mul_le_mul h3 h2 (by positivity) (by have := hB0 r; positivity)
      _ = Bs * W ^ 3 / Real.sqrt V := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, div_pow]
          have : Real.sqrt V ^ 3 = V * Real.sqrt V := by rw [pow_succ, hsq]
          rw [this, ← hBs]; field_simp
  -- bound T2
  have hfz : ∑ r, N.massActionRate κ r z * td r = ∑ s, θ s * N.massActionVectorField κ z s := by
    simp only [htd, massActionVectorField_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hlinJ : ∑ s, θ' s * ζ s = -(Real.sqrt V * ∑ s, θ s * J (z - xs) s) := by
    rw [hadj ζ, hζz, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  have hT2eq : T2 = Real.sqrt V * ∑ s, θ s * (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs)) s +
      Real.sqrt V * ∑ r, (dr r - N.massActionRate κ r z) * td r := by
    have h1 : ∑ r, lam r * w r = Real.sqrt V * ∑ r, dr r * td r := by
      simp only [hlamV, hw, Finset.mul_sum]
      have hdiv : V / Real.sqrt V = Real.sqrt V := Real.div_sqrt
      exact Finset.sum_congr rfl fun r _ => by
        rw [show V * dr r * (td r / Real.sqrt V) = V / Real.sqrt V * (dr r * td r) by ring, hdiv]
    rw [hT2, h1, hlinJ]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [← hfz]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hT2b : |T2| ≤ (Θ * L₂ * ‖ζ‖ ^ 2 + Es * W) / Real.sqrt V := by
    rw [hT2eq]
    have hA : |Real.sqrt V * ∑ s, θ s * (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs)) s| ≤
        Θ * L₂ * ‖ζ‖ ^ 2 / Real.sqrt V := by
      rw [abs_mul, abs_of_pos hsV]
      have h1 := abs_dot_le θ (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs))
      have h2 := hL₂ xs hxsB z hzB
      have h3 : (∑ s, |θ s|) * ‖N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs)‖ ≤
          Θ * (L₂ * ‖z - xs‖ ^ 2) := mul_le_mul hθ h2 (norm_nonneg _) hΘ
      have h4 : Real.sqrt V * (Θ * (L₂ * ‖z - xs‖ ^ 2)) = Θ * L₂ * ‖ζ‖ ^ 2 / Real.sqrt V := by
        rw [hzx]; field_simp
      calc Real.sqrt V * |∑ s, θ s * (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs)) s|
          ≤ Real.sqrt V * (Θ * (L₂ * ‖z - xs‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (h1.trans h3) hsV.le
        _ = _ := h4
    have hB' : |Real.sqrt V * ∑ r, (dr r - N.massActionRate κ r z) * td r| ≤ Es * W / Real.sqrt V := by
      rw [abs_mul, abs_of_pos hsV]
      have : |∑ r, (dr r - N.massActionRate κ r z) * td r| ≤ ∑ r, E r / V * W := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (herr r) (htd_le r) (abs_nonneg _) (div_nonneg (hE0 r) hV0.le)
      calc Real.sqrt V * |∑ r, (dr r - N.massActionRate κ r z) * td r|
          ≤ Real.sqrt V * ∑ r, E r / V * W := mul_le_mul_of_nonneg_left this hsV.le
        _ = Es * W / Real.sqrt V := by
            rw [← Finset.sum_mul, ← Finset.sum_div, ← hEs]
            have hsd : Real.sqrt V / V = 1 / Real.sqrt V := Real.sqrt_div_self'
            rw [show Real.sqrt V * (Es / V * W) = Es * W * (Real.sqrt V / V) by ring, hsd]
            ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ Θ * L₂ * ‖ζ‖ ^ 2 / Real.sqrt V + Es * W / Real.sqrt V := add_le_add hA hB'
      _ = _ := by ring
  -- bound T3
  have hT3eq : T3 = ∑ r, (dr r - N.massActionRate κ r xs) * td r ^ 2 := by
    rw [hT3, quadG, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hlamV, hw, div_pow, hsq]
    field_simp
    ring
  have hT3b : |T3| ≤ (nR * Lρ * W ^ 2 * ‖ζ‖ + Es * W ^ 2) / Real.sqrt V := by
    rw [hT3eq]
    have hterm : ∀ r, |(dr r - N.massActionRate κ r xs) * td r ^ 2| ≤
        (Lρ * W ^ 2 * ‖ζ‖ + E r * W ^ 2) / Real.sqrt V := by
      intro r
      rw [abs_mul, abs_of_nonneg (sq_nonneg (td r))]
      have h1 : |dr r - N.massActionRate κ r xs| ≤ E r / V + Lρ * ‖z - xs‖ := by
        have := hLρ r xs hxsB z hzB
        calc |dr r - N.massActionRate κ r xs| = |(dr r - N.massActionRate κ r z) +
              (N.massActionRate κ r z - N.massActionRate κ r xs)| := by ring_nf
          _ ≤ _ := (abs_add_le _ _).trans (add_le_add (herr r) this)
      have h2 : td r ^ 2 ≤ W ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (htd_le r) 2
      have h3 : E r / V ≤ E r / Real.sqrt V := div_le_div_of_nonneg_left (hE0 r) hsV
        (by nlinarith [hsq, hsV1])
      have h4 : Lρ * ‖z - xs‖ = Lρ * ‖ζ‖ / Real.sqrt V := by rw [hzx]; ring
      calc |dr r - N.massActionRate κ r xs| * td r ^ 2 ≤ (E r / V + Lρ * ‖z - xs‖) * W ^ 2 :=
            mul_le_mul h1 h2 (sq_nonneg _)
              (add_nonneg (div_nonneg (hE0 r) hV0.le) (mul_nonneg hLρ0 (norm_nonneg _)))
        _ ≤ (E r / Real.sqrt V + Lρ * ‖ζ‖ / Real.sqrt V) * W ^ 2 := by
            rw [h4]; gcongr
        _ = (Lρ * W ^ 2 * ‖ζ‖ + E r * W ^ 2) / Real.sqrt V := by ring
    calc |∑ r, (dr r - N.massActionRate κ r xs) * td r ^ 2|
        ≤ ∑ r, (Lρ * W ^ 2 * ‖ζ‖ + E r * W ^ 2) / Real.sqrt V :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => hterm r)
      _ = (nR * Lρ * W ^ 2 * ‖ζ‖ + Es * W ^ 2) / Real.sqrt V := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.sum_mul, ← hEs, ← hnR]
          ring
  -- assemble
  rw [hdecomp]
  have hζ1 : ‖ζ‖ ≤ 1 + ‖ζ‖ ^ 2 := by nlinarith [sq_nonneg (‖ζ‖ - 1)]
  have hnorm : ‖T1 + I * (T2 : ℂ) - ((T3 / 2 : ℝ) : ℂ)‖ ≤ ‖T1‖ + |T2| + |T3| / 2 := by
    calc ‖T1 + I * (T2 : ℂ) - ((T3 / 2 : ℝ) : ℂ)‖ ≤ ‖T1 + I * (T2 : ℂ)‖ + ‖((T3 / 2 : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖T1‖ + ‖I * (T2 : ℂ)‖ + ‖((T3 / 2 : ℝ) : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ = ‖T1‖ + |T2| + |T3| / 2 := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two]
  refine hnorm.trans ?_
  have hsum : ‖T1‖ + |T2| + |T3| / 2 ≤
      (Bs * W ^ 3 + (Θ * L₂ * ‖ζ‖ ^ 2 + Es * W) + (nR * Lρ * W ^ 2 * ‖ζ‖ + Es * W ^ 2)) /
        Real.sqrt V := by
    have : |T3| / 2 ≤ |T3| := by linarith [abs_nonneg T3]
    calc ‖T1‖ + |T2| + |T3| / 2 ≤ ‖T1‖ + |T2| + |T3| := by linarith
      _ ≤ Bs * W ^ 3 / Real.sqrt V + (Θ * L₂ * ‖ζ‖ ^ 2 + Es * W) / Real.sqrt V +
          (nR * Lρ * W ^ 2 * ‖ζ‖ + Es * W ^ 2) / Real.sqrt V := by
          gcongr
      _ = _ := by ring
  refine hsum.trans ?_
  apply div_le_div_of_nonneg_right _ hsV.le
  have h1 : nR * Lρ * W ^ 2 * ‖ζ‖ ≤ nR * Lρ * W ^ 2 * (1 + ‖ζ‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hζ1 (by positivity)
  have h2 : 0 ≤ ‖ζ‖ ^ 2 := sq_nonneg _
  simp only [hC]
  nlinarith [mul_nonneg hBs0 (pow_nonneg hW0 3), mul_nonneg hEs0 hW0, mul_nonneg hEs0 (sq_nonneg W),
    mul_nonneg (mul_nonneg hΘ hL₂0) h2, mul_nonneg (mul_nonneg hBs0 (pow_nonneg hW0 3)) h2,
    mul_nonneg (mul_nonneg hEs0 hW0) h2, mul_nonneg (mul_nonneg hEs0 (sq_nonneg W)) h2,
    mul_nonneg hΘ hL₂0]


theorem continuous_quadG₂ (N : Network S) (κ : RateConstants N) :
    Continuous fun p : Concentration S × (S → ℝ) => N.quadG κ p.1 p.2 := by
  unfold quadG massActionRate Complex.massActionMonomial
  fun_prop

set_option maxHeartbeats 3200000 in
/-- **The CLT error estimate along a trajectory, at fixed volume.** -/
theorem clt_error_traj (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (θf θf' : ℝ → S → ℝ) (hθc : ContinuousOn θf (Icc 0 T))
    (hθd : ∀ u ∈ Ioo 0 T, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s) :
    ∃ K V₀ : ℝ, 0 ≤ K ∧ 1 ≤ V₀ ∧ ∀ (V : ℝ) (hV1 : 1 ≤ V), V₀ ≤ V → ∀ n : S → ℕ,
      ∑ s, w s * (n s : ℝ) ≤ M * V →
      ‖∑' m, (N.transition (N.volumeScale κ V (by linarith)) T n m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
          (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ))‖ ≤
        K * (1 + ∑ s, zeta V (x 0) n s ^ 2) / Real.sqrt V := by
  classical
  set R₁ := ∑ s, M / w s with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun s _ => div_nonneg hM (hwpos s).le
  set Rb := max R₁ Rx with hRb
  have hRb0 : 0 ≤ Rb := le_trans hR₁0 (le_max_left _ _)
  have hxB' : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rb := fun t ht =>
    ⟨(hxB t ht).1, fun s => ((hxB t ht).2 s).trans (le_max_right _ _)⟩
  have hx0 : ∀ t ∈ Icc 0 T, ∀ s, 0 ≤ x t s := fun t ht s => (hxB t ht).1 s
  -- the conservative law of large numbers along `x`
  obtain ⟨C₁, C₂, hC₁, hC₂, hlln⟩ := N.conservative_lln κ hwinv hwpos (T := T) (Rx := Rb) hM
    x hxc hx hxB'
  -- a bound on θ over [0, T]
  obtain ⟨Θ₀, hΘ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun u => ∑ s, |θf u s|)
    (continuousOn_finsetSum _ fun s _ => ((continuous_apply s).comp_continuousOn hθc).abs)
  set Θ := max Θ₀ 0 with hΘ
  have hΘ0 : 0 ≤ Θ := le_max_right _ _
  have hθΘ : ∀ u ∈ Icc 0 T, ∑ s, |θf u s| ≤ Θ := fun u hu =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hΘ₀ u hu).trans (le_max_left _ _))
  obtain ⟨C, V₀, hC0, hV₀, hgen⟩ := N.generator_error_le_traj κ hRb0 hΘ0
  set K := T * C * (1 + C₂ * T) * Real.exp (C₁ * T) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, V₀, hK0, hV₀, fun V hV1 hV n hn => ?_⟩
  have hV0 : 0 < V := by linarith
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  set κV := N.volumeScale κ V hV0 with hκV
  set J := N.jumpSystem κV with hJ
  have hcons : N.IsConservative := ⟨w, hwinv, hwpos⟩
  set Rset := N.reachClass κV hcons n with hRset
  have hsupp : ∀ τ, ∀ b, b ∉ Rset → J.Pmin τ n b = 0 := fun τ b hb =>
    J.Pmin_eq_zero_of_not_reachPos τ fun h => hb ((N.mem_reachClass κV hcons).mpr h)
  have hclosed : ∀ c ∈ Rset, ∀ i, 0 < J.rate i c → J.next i c ∈ Rset := by
    intro c hc i hi
    rw [N.mem_reachClass κV hcons] at hc ⊢
    exact hc.tail ⟨i, hi, rfl⟩
  have hnR : n ∈ Rset := (N.mem_reachClass κV hcons).mpr Relation.ReflTransGen.refl
  have hcR : ∀ c ∈ Rset, ∀ s, (c s : ℝ) ≤ Rb * V := by
    intro c hc s
    have hw := N.weight_of_reachPos κV hwinv ((N.mem_reachClass κV hcons).mp hc)
    have h1 : w s * (c s : ℝ) ≤ M * V := by
      rw [← hw] at hn
      refine le_trans ?_ hn
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ M / w s * V := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (hwpos s)]; linarith
    have h3 : M / w s ≤ R₁ := Finset.single_le_sum (f := fun s => M / w s)
      (fun s _ => div_nonneg hM (hwpos s).le) (Finset.mem_univ s)
    exact h2.trans (mul_le_mul_of_nonneg_right (h3.trans (le_max_left _ _)) hV0.le)
  -- the Gaussian factor
  set Φ : ℝ → ℝ := fun u => N.quadG κ (x u) (θf u) with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) := by
    have h2 : ContinuousOn (fun u => (x u, θf u)) (Icc 0 T) := hxc.prodMk hθc
    exact ((N.continuous_quadG₂ κ).comp_continuousOn h2).congr fun u _ => rfl
  have hΦ0 : ∀ u ∈ Icc 0 T, 0 ≤ Φ u := fun u hu => N.quadG_nonneg κ (hx0 u hu) _
  set Ifn : ℝ → ℝ := fun u => ∫ v in u..T, Φ v with hIfn
  have hIder : ∀ u ∈ Ioo 0 T, HasDerivAt Ifn (-Φ u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_left ((hΦc.mono (Icc_subset_Icc hu.1.le le_rfl)).intervalIntegrable_of_Icc hu.2.le)
      ((hΦc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu)
      ((hΦc.mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hu.1 hu.2))
  have hIc : ContinuousOn Ifn (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (a := 0) (b := T)
      (f := Φ) (by rw [uIcc_of_le hT.le]; exact hΦc.integrableOn_Icc)
    rwa [uIcc_of_le hT.le] at this
  have hI0 : ∀ u ∈ Icc 0 T, 0 ≤ Ifn u := fun u hu =>
    intervalIntegral.integral_nonneg hu.2 fun v hv => hΦ0 v ⟨hu.1.trans hv.1, hv.2⟩
  -- the observable
  set th : ℝ → (S → ℕ) → ℝ := fun u b => ∑ s, θf u s * zeta V (x u) b s with hth
  set F : ℝ → (S → ℕ) → ℂ := fun u b =>
    Complex.exp (I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ)) with hF
  set F' : ℝ → (S → ℕ) → ℂ := fun u b =>
    F u b * (I * ((∑ s, θf' u s * zeta V (x u) b s -
      Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
      ((Φ u / 2 : ℝ) : ℂ)) with hF'
  have hFnorm : ∀ u ∈ Icc 0 T, ∀ b, ‖F u b‖ ≤ 1 := by
    intro u hu b
    simp only [hF, Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    have := hI0 u hu
    linarith
  have hFder : ∀ u ∈ Ioo 0 T, ∀ b, HasDerivAt (fun u => F u b) (F' u b) u := by
    intro u hu b
    have hxs := hasDerivAt_pi.mp (hx u hu)
    have hzd : ∀ s, HasDerivAt (fun u => zeta V (x u) b s)
        (-(Real.sqrt V * N.massActionVectorField κ (x u) s)) u := by
      intro s
      have := ((hxs s).const_sub ((b s : ℝ) / V)).const_mul (Real.sqrt V)
      simpa [zeta, mul_neg] using this
    have hth' : HasDerivAt (fun u => th u b) (∑ s, θf' u s * zeta V (x u) b s -
        Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s) u := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun s u => θf u s * zeta V (x u) b s)
        (A' := fun s => θf' u s * zeta V (x u) b s +
          θf u s * -(Real.sqrt V * N.massActionVectorField κ (x u) s)) fun s _ =>
          ((hasDerivAt_pi.mp (hθd u hu)) s).mul (hzd s)
      convert this using 1
      rw [Finset.sum_add_distrib, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring
    have hin : HasDerivAt (fun u => I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ))
        (I * ((∑ s, θf' u s * zeta V (x u) b s -
          Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)) u := by
      have h1 := (hth'.ofReal_comp).const_mul I
      have h2 := ((hIder u hu).div_const 2).ofReal_comp
      convert h1.sub h2 using 1
      push_cast; ring
    have := hin.cexp
    simpa [hF', hF] using this
  -- pointwise error
  have hpt : ∀ u ∈ Icc 0 T, ∀ c ∈ Rset,
      ‖J.cdrift (F u) c + F' u c‖ ≤ C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V := by
    intro u hu c hc
    have hcd := N.cdrift_expObs κ hV0 (x u) (θf u) ((Ifn u / 2 : ℝ) : ℂ) c
    have heqF : J.cdrift (F u) c + F' u c = F u c *
        (∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V (x u) c s -
            Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)) := by
      have : J.cdrift (F u) c = F u c * ∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) := hcd
      rw [this]
      simp only [hF']
      ring
    rw [heqF, norm_mul]
    have hg := hgen (x u) (hxB' u hu) (θf u) (θf' u) (hθΘ u hu) (hadj u hu) V hV1 hV c (hcR c hc)
    have hz2 : ‖zeta V (x u) c‖ ^ 2 ≤ ∑ s, zeta V (x u) c s ^ 2 := norm_sq_le_sum_sq _
    calc ‖F u c‖ * ‖∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V (x u) c s -
            Real.sqrt V * ∑ s, θf u s * N.massActionVectorField κ (x u) s : ℝ) : ℂ) +
          ((Φ u / 2 : ℝ) : ℂ)‖
        ≤ 1 * (C * (1 + ‖zeta V (x u) c‖ ^ 2) / Real.sqrt V) :=
          mul_le_mul (hFnorm u hu c) hg (norm_nonneg _) zero_le_one
      _ ≤ C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V := by
          rw [one_mul]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hsV.le
  -- the expectation and its derivative
  set E : ℝ → ℂ := fun u => ∑ b ∈ Rset, (J.Pmin u n b : ℂ) * F u b with hE
  have hEder : ∀ u ∈ Ioo 0 T, HasDerivAt E (∑ c ∈ Rset, (J.Pmin u n c : ℂ) *
      (J.cdrift (F u) c + F' u c)) u := fun u hu =>
    J.hasDerivAt_csum_finite n Rset hsupp hclosed F F' hu.1 fun b _ => hFder u hu b
  -- the mean squared fluctuation
  set G₀ := ∑ s, zeta V (x 0) n s ^ 2 with hG₀
  have hG₀0 : 0 ≤ G₀ := Finset.sum_nonneg fun s _ => sq_nonneg _
  set B := C / Real.sqrt V * ((1 + C₂ * T) * Real.exp (C₁ * T) * (1 + G₀)) with hBdef
  have hEbound : ∀ u ∈ Ioo 0 T, ‖∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c)‖ ≤ B := by
    intro u hu
    have hu0 := hu.1.le
    have hP0 : ∀ c, 0 ≤ J.Pmin u n c := fun c => J.Pmin_nonneg u hu0 n c
    have hD := hlln V hV1 n hn u (Ioo_subset_Icc_self hu)
    have hDR : ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - x u s) ^ 2 ≤
        gronwallBound (∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) C₁ (C₂ / V) u := by
      have : ∑' m, N.transition κV u n m * ∑ s, ((m s : ℝ) / V - x u s) ^ 2 =
          ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - x u s) ^ 2 :=
        tsum_eq_sum fun c hc => by
          show J.Pmin u n c * _ = 0
          rw [hsupp u c hc, zero_mul]
      rw [← this]; exact hD
    have hzV : ∀ (y : Concentration S) (c : S → ℕ),
        ∑ s, zeta V y c s ^ 2 = V * ∑ s, ((c s : ℝ) / V - y s) ^ 2 := by
      intro y c
      simp only [zeta, mul_pow, Real.sq_sqrt hV0.le, Finset.mul_sum]
    have hg0 : 0 ≤ ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
    have hgr := gronwallBound_le_mul_exp hg0 hC₁ (div_nonneg hC₂ hV0.le) hu0 (K := C₁)
      (ε := C₂ / V) (δ := ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2)
    have hVD : ∑ c ∈ Rset, J.Pmin u n c * ∑ s, zeta V (x u) c s ^ 2 ≤
        (G₀ + C₂ * T) * Real.exp (C₁ * T) := by
      simp only [hzV (x u)]
      have e1 : ∑ c ∈ Rset, J.Pmin u n c * (V * ∑ s, ((c s : ℝ) / V - x u s) ^ 2) =
          V * ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - x u s) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1]
      have hexp : Real.exp (C₁ * u) ≤ Real.exp (C₁ * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2.le hC₁)
      have hG : G₀ = V * ∑ s, ((n s : ℝ) / V - x 0 s) ^ 2 := hzV (x 0) n
      calc V * ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - x u s) ^ 2
          ≤ V * (((∑ s, ((n s : ℝ) / V - x 0 s) ^ 2) + C₂ / V * u) * Real.exp (C₁ * u)) :=
            mul_le_mul_of_nonneg_left (hDR.trans hgr) hV0.le
        _ = (G₀ + C₂ * u) * Real.exp (C₁ * u) := by rw [hG]; field_simp
        _ ≤ (G₀ + C₂ * T) * Real.exp (C₁ * T) := by
            apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
            nlinarith [hu.2.le]
    have hsumP : ∑ c ∈ Rset, J.Pmin u n c ≤ 1 := J.sum_Pmin_le_one u hu0 n Rset
    calc ‖∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c)‖
        ≤ ∑ c ∈ Rset, J.Pmin u n c * (C * (1 + ∑ s, zeta V (x u) c s ^ 2) / Real.sqrt V) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 c)]
          exact mul_le_mul_of_nonneg_left (hpt u (Ioo_subset_Icc_self hu) c hc) (hP0 c)
      _ = C / Real.sqrt V * (∑ c ∈ Rset, J.Pmin u n c +
            ∑ c ∈ Rset, J.Pmin u n c * ∑ s, zeta V (x u) c s ^ 2) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ C / Real.sqrt V * (1 + (G₀ + C₂ * T) * Real.exp (C₁ * T)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have he1 : 1 ≤ Real.exp (C₁ * T) := Real.one_le_exp (mul_nonneg hC₁ hT.le)
          nlinarith [mul_nonneg hG₀0 (mul_nonneg hC₂ hT.le)]
  -- continuity of `E`
  have hEc : ContinuousOn E (Icc 0 T) := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn
        ((J.continuousOn_Pmin n b).mono fun u hu => hu.1))
    · simp only [hF, hth, zeta]
      refine Continuous.comp_continuousOn Complex.continuous_exp ?_
      refine ContinuousOn.sub (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_))
        (Complex.continuous_ofReal.comp_continuousOn (hIc.div_const 2))
      refine continuousOn_finsetSum _ fun s _ => ?_
      exact ((continuous_apply s).comp_continuousOn hθc).mul (continuousOn_const.mul
        (continuousOn_const.sub ((continuous_apply s).comp_continuousOn hxc)))
  -- mean value inequality, away from `0`, then `ε → 0`
  have hmv : ∀ ε ∈ Ioo 0 T, ‖E T - E ε‖ ≤ B * (T - ε) := by
    intro ε hε
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := E)
      (f' := fun u => ∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c))
      (a := ε) (b := T) (C := B) (hEc.mono (Icc_subset_Icc hε.1.le le_rfl))
      (fun u hu => (hEder u ⟨lt_of_lt_of_le hε.1 hu.1, hu.2⟩).hasDerivWithinAt)
      (fun u hu => hEbound u ⟨lt_of_lt_of_le hε.1 hu.1, hu.2⟩) T ⟨hε.2.le, le_rfl⟩
    exact this
  have hlimE : Tendsto (fun ε => ‖E T - E ε‖) (𝓝[>] 0) (𝓝 ‖E T - E 0‖) := by
    have h1 : Tendsto E (𝓝[>] 0) (𝓝 (E 0)) :=
      ((hEc 0 ⟨le_rfl, hT.le⟩).tendsto).mono_left (nhdsWithin_le_of_mem
        (mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self))
    exact (tendsto_const_nhds.sub h1).norm
  have hlimB : Tendsto (fun ε => B * (T - ε)) (𝓝[>] 0) (𝓝 (B * (T - 0))) :=
    ((tendsto_const_nhds.sub tendsto_id).const_mul B).mono_left nhdsWithin_le_nhds
  have hET0 : ‖E T - E 0‖ ≤ B * T := by
    have := le_of_tendsto_of_tendsto hlimE hlimB (by
      filter_upwards [Ioo_mem_nhdsGT hT] with ε hε using hmv ε hε)
    simpa using this
  -- identify `E T` and `E 0`
  have hET : E T = ∑' m, (N.transition κV T n m : ℂ) *
      Complex.exp (I * ((∑ s, θf T s * zeta V (x T) m s : ℝ) : ℂ)) := by
    simp only [hE, hF, hIfn, intervalIntegral.integral_same, zero_div, Complex.ofReal_zero,
      sub_zero]
    refine (tsum_eq_sum fun m hm => ?_).symm
    show (J.Pmin T n m : ℂ) * _ = 0
    rw [hsupp T m hm]; simp
  have hE0 : E 0 = Complex.exp (I * ((∑ s, θf 0 s * zeta V (x 0) n s : ℝ) : ℂ) -
      (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ)) := by
    simp only [hE, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
      (fun h => absurd hnR h)]
    simp [hF, hIfn, hth, hΦ]
  rw [← hET, ← hE0]
  calc ‖E T - E 0‖ ≤ B * T := hET0
    _ = K * (1 + G₀) / Real.sqrt V := by
        simp only [hBdef, hK]
        field_simp


/-- **Central limit theorem for nonlinear conservative networks along a trajectory.** For a
conservative network, a solution `x` of the mass-action equation on `[0, T]` with values in
`[0, R_x]^S`, a `C¹` solution `θ(·)` of the adjoint linearized equation
`θ'(u) · v = −θ(u) · Df(x(u)) v`, and initial counts with `⟨w, n_V⟩ ≤ M V` and
`√V (n_V/V − x(0)) → z₀`:

`E exp(i θ(T) · √V (X^V(T)/V − x(T))) → exp(i θ(0) · z₀ − ½ ∫₀ᵀ ∑_r λ_r(x(u)) (θ(u) · Δ_r)² du)`. -/
theorem nonlinear_clt_traj (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {M T Rx : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hRx : 0 ≤ Rx) (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (θf θf' : ℝ → S → ℝ) (hθc : ContinuousOn θf (Icc 0 T))
    (hθd : ∀ u ∈ Ioo 0 T, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) (x u) v s)
    (n : ℕ → S → ℕ) (hn : ∀ k : ℕ, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) (x 0) (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (n k) m : ℂ) * Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)))
      atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) -
        (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ)))) := by
  obtain ⟨K, V₀, hK0, hV₀, hbd⟩ := N.clt_error_traj κ hwinv hwpos hM hT hRx x hxc hx hxB θf θf'
    hθc hθd hadj
  set Ib : ℂ := (((∫ u in (0 : ℝ)..T, N.quadG κ (x u) (θf u)) / 2 : ℝ) : ℂ) with hIb
  set b : ℕ → ℂ := fun k => Complex.exp (I * ((∑ s, θf 0 s * zeta ((k : ℝ) + 1) (x 0) (n k) s : ℝ) : ℂ) - Ib)
    with hb
  have hblim : Tendsto b atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib))) := by
    have hcont : Continuous fun z : S → ℝ =>
        Complex.exp (I * ((∑ s, θf 0 s * z s : ℝ) : ℂ) - Ib) := by fun_prop
    exact (hcont.tendsto z₀).comp hz
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hden
  have hG : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2)) atTop
      (𝓝 (K * (1 + ∑ s, z₀ s ^ 2))) := by
    have hc : Continuous fun z : S → ℝ => K * (1 + ∑ s, z s ^ 2) := by fun_prop
    exact (hc.tendsto z₀).comp hz
  have herr : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2) /
      Real.sqrt ((k : ℝ) + 1)) atTop (𝓝 0) := hG.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb' := (tendsto_iff_norm_sub_tendsto_zero.mp hblim)
  have htot := herr.add hb'
  rw [add_zero] at htot
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ htot
  have hV : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  filter_upwards [hden.eventually_ge_atTop V₀] with k hk
  have h1 := hbd ((k : ℝ) + 1) (hV k) hk (n k) (hn k)
  calc ‖∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖
      ≤ ‖∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) (x T) m s : ℝ) : ℂ)) - b k‖ +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * (1 + ∑ s, zeta ((k : ℝ) + 1) (x 0) (n k) s ^ 2) / Real.sqrt ((k : ℝ) + 1) +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := by
        gcongr


end Network
end CRNT
