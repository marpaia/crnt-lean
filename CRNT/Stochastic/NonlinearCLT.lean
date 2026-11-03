import CRNT.Stochastic.ConservativeLLN

/-!
# A central limit theorem for nonlinear conservative networks at an equilibrium

For a conservative network with a positive equilibrium `x*` of the mass-action equation, the
fluctuation `ζ^V(t) = √V (X^V(t)/V − x*)` of the volume-scaled chain satisfies, for every
direction `θ` and every solution `θ(·)` of the adjoint linearized equation
`θ'(u) = −Df(x*)ᵀ θ(u)` with `θ(t) = θ`,

`E exp(i θ · ζ^V(t)) → exp(i θ(0) · z₀ − ½ ∫₀ᵗ ∑_r λ_r(x*) (θ(u) · Δ_r)² du)`

whenever `ζ^V(0) → z₀` (`nonlinear_clt`): the characteristic function of `θ · ζ^V(t)` converges to
that of the Gaussian with mean `θ(0) · z₀ = θ · e^{t Df(x*)} z₀` and variance
`∫₀ᵗ θ(u)ᵀ G θ(u) du`, `G = ∑_r λ_r(x*) Δ_r Δ_rᵀ` (the linear noise approximation).

Proof without martingales (the generator and duality argument of Ethier–Kurtz, Ch. 1):
`F(u, c) = exp(i θ(u) · ζ(c) − ½ ∫_u^t θᵀ G θ)` satisfies `|(∂_u + Q^V) F| ≤ C (1 + |ζ|²)/√V`
on the (finite) class — the first-order term cancels against the adjoint equation, the
second-order term against `∂_u` of the Gaussian factor, and the remainders are third-order in
`1/√V`, second-order Taylor errors of the field, Lipschitz errors of the rates and the
falling-factorial correction — and `E |ζ|²` stays bounded by the conservative law of large
numbers.
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology NNReal

namespace CRNT

/-- `|e^{iw} − 1 − iw + w²/2| ≤ |w|³` for `|w| ≤ 1`. -/
theorem norm_cexp_I_mul_sub_le {w : ℝ} (hw : |w| ≤ 1) :
    ‖Complex.exp (I * w) - 1 - I * w + (w : ℂ) ^ 2 / 2‖ ≤ |w| ^ 3 := by
  have hx : ‖(I * (w : ℂ))‖ = |w| := by simp
  have h := Complex.exp_bound (x := I * (w : ℂ)) (by rw [hx]; exact hw) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (I * (w : ℂ)) ^ m / (m.factorial : ℂ) =
      1 + I * w - (w : ℂ) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, mul_pow, Complex.I_sq]
    ring
  rw [hsum, hx] at h
  have heq : Complex.exp (I * w) - 1 - I * w + (w : ℂ) ^ 2 / 2 =
      Complex.exp (I * w) - (1 + I * w - (w : ℂ) ^ 2 / 2) := by ring
  rw [heq]
  refine h.trans ?_
  have : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by norm_num
  have h3 : 0 ≤ |w| ^ 3 := by positivity
  calc |w| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹)
      ≤ |w| ^ 3 * 1 := mul_le_mul_of_nonneg_left this h3
    _ = |w| ^ 3 := mul_one _

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The generator applied to a complex observable. -/
noncomputable def cdrift (f : α → ℂ) (c : α) : ℂ :=
  ∑ i, (J.rate i c : ℂ) * (f (J.next i c) - f c)

theorem cdrift_re (f : α → ℂ) (c : α) : (J.cdrift f c).re = J.drift (fun b => (f b).re) c := by
  unfold cdrift drift
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Complex.mul_re]

theorem cdrift_im (f : α → ℂ) (c : α) : (J.cdrift f c).im = J.drift (fun b => (f b).im) c := by
  unfold cdrift drift
  rw [Complex.im_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Complex.mul_im]

/-- **Forward equation on a finite closed class, complex observables.** -/
theorem hasDerivAt_csum_finite (a : α) (R : Finset α)
    (hsupp : ∀ τ, ∀ b, b ∉ R → J.Pmin τ a b = 0)
    (hclosed : ∀ c ∈ R, ∀ i, 0 < J.rate i c → J.next i c ∈ R)
    (g g' : ℝ → α → ℂ) {t : ℝ} (ht : 0 < t)
    (hg : ∀ b ∈ R, HasDerivAt (fun τ => g τ b) (g' t b) t) :
    HasDerivAt (fun τ => ∑ b ∈ R, (J.Pmin τ a b : ℂ) * g τ b)
      (∑ c ∈ R, (J.Pmin t a c : ℂ) * (J.cdrift (g t) c + g' t c)) t := by
  have hre := J.hasDerivAt_sum_finite a R hsupp hclosed (fun τ b => (g τ b).re)
    (fun τ b => (g' τ b).re) ht fun b hb => by
      have := (hg b hb)
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t this)
  have him := J.hasDerivAt_sum_finite a R hsupp hclosed (fun τ b => (g τ b).im)
    (fun τ b => (g' τ b).im) ht fun b hb => by
      have := (hg b hb)
      exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t this)
  have hc := hre.ofReal_comp.add (him.ofReal_comp.const_mul I)
  have hfun : (fun τ => ∑ b ∈ R, (J.Pmin τ a b : ℂ) * g τ b) =
      fun τ => ((∑ b ∈ R, J.Pmin τ a b * (g τ b).re : ℝ) : ℂ) +
        I * ((∑ b ∈ R, J.Pmin τ a b * (g τ b).im : ℝ) : ℂ) := by
    funext τ
    apply Complex.ext <;> simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im]
  rw [hfun]
  convert hc using 1
  apply Complex.ext
  · simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, cdrift_re, cdrift_im]
  · simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, cdrift_re, cdrift_im]

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `|∑ θ_s v_s| ≤ (∑ |θ_s|) ‖v‖`. -/
theorem abs_dot_le (θ v : S → ℝ) : |∑ s, θ s * v s| ≤ (∑ s, |θ s|) * ‖v‖ := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v s) (abs_nonneg _)

/-- `‖v‖² ≤ ∑ v_s²`. -/
theorem norm_sq_le_sum_sq (v : S → ℝ) : ‖v‖ ^ 2 ≤ ∑ s, v s ^ 2 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [Subsingleton.elim v 0]
  obtain ⟨s₀, hs₀⟩ : ∃ s, ‖v‖ = |v s| := by
    have := Finite.exists_max fun s => |v s|
    obtain ⟨s, hs⟩ := this
    refine ⟨s, le_antisymm ?_ (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v s)⟩
    exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun s' => by
      rw [Real.norm_eq_abs]; exact hs s'
  rw [hs₀, sq_abs]
  exact Finset.single_le_sum (f := fun s => v s ^ 2) (fun s _ => sq_nonneg _) (Finset.mem_univ s₀)

/-- **Second-order Taylor bound of the mass-action field on a box.** -/
theorem exists_taylor_bound (N : Network S) (κ : RateConstants N) {Rb : ℝ}
    {xs : Concentration S} (hxs : xs ∈ Icc (0 : Concentration S) fun _ => Rb) :
    ∃ L₂ : ℝ, 0 ≤ L₂ ∧ ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      ‖N.massActionVectorField κ z - N.massActionVectorField κ xs -
        fderiv ℝ (N.massActionVectorField κ) xs (z - xs)‖ ≤ L₂ * ‖z - xs‖ ^ 2 := by
  set f := N.massActionVectorField κ with hf
  have hfC : ContDiff ℝ ⊤ f := N.contDiff_massActionVectorField κ
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hfC.fderiv_right (by norm_num)
  obtain ⟨L, hL⟩ := (hDf.contDiffOn (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  refine ⟨L, L.2, fun z hz => ?_⟩
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

/-- **Lipschitz bound of the rates on a box.** -/
theorem exists_rate_lipschitz (N : Network S) (κ : RateConstants N) {Rb : ℝ}
    {xs : Concentration S} (hxs : xs ∈ Icc (0 : Concentration S) fun _ => Rb) :
    ∃ Lρ : ℝ, 0 ≤ Lρ ∧ ∀ r, ∀ z ∈ Icc (0 : Concentration S) (fun _ => Rb),
      |N.massActionRate κ r z - N.massActionRate κ r xs| ≤ Lρ * ‖z - xs‖ := by
  have hC : ∀ r, ContDiff ℝ 1 fun z => N.massActionRate κ r z := by
    intro r
    unfold massActionRate Complex.massActionMonomial
    fun_prop
  choose L hL using fun r => ((hC r).contDiffOn (s := Icc (0 : Concentration S) fun _ => Rb)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  refine ⟨∑ r, (L r : ℝ), Finset.sum_nonneg fun r _ => (L r).2, fun r z hz => ?_⟩
  have h1 := (hL r).dist_le_mul z hz xs hxs
  rw [Real.dist_eq, dist_eq_norm] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := fun r => (L r : ℝ)) (fun r _ => (L r).2) (Finset.mem_univ r)

/-- The fluctuation `ζ(c) = √V (c/V − x*)`. -/
noncomputable def zeta (V : ℝ) (xs : Concentration S) (c : S → ℕ) : S → ℝ :=
  fun s => Real.sqrt V * ((c s : ℝ) / V - xs s)

/-- The diffusion quadratic form `θᵀ G θ = ∑_r λ_r(x*) (θ · Δ_r)²`. -/
noncomputable def quadG (N : Network S) (κ : RateConstants N) (xs : Concentration S)
    (θ : S → ℝ) : ℝ :=
  ∑ r, N.massActionRate κ r xs * (∑ s, θ s * N.reactionVector r s) ^ 2

theorem quadG_nonneg (N : Network S) (κ : RateConstants N) {xs : Concentration S}
    (hxs : ∀ s, 0 ≤ xs s) (θ : S → ℝ) : 0 ≤ N.quadG κ xs θ :=
  Finset.sum_nonneg fun r _ => mul_nonneg (N.massActionRate_nonneg κ r hxs) (sq_nonneg _)

set_option maxHeartbeats 1600000 in
/-- **The generator error.** On counts with `c ≤ R₁ V`, for `θ` with `∑ |θ_s| ≤ Θ` and `θ'`
satisfying the adjoint relation `θ' · v = −θ · Df(x*) v`,
`|∑_r λ_r(c)(e^{i θ·Δ_r/√V} − 1) + i θ' · ζ(c) + θᵀGθ/2| ≤ C (1 + ‖ζ(c)‖²)/√V`. -/
theorem generator_error_le (N : Network S) (κ : RateConstants N) {xs : Concentration S}
    (heq : N.massActionVectorField κ xs = 0) {R₁ Θ : ℝ} (hR₁ : 0 ≤ R₁) (hΘ : 0 ≤ Θ)
    (hxsB : xs ∈ Icc (0 : Concentration S) fun _ => R₁) :
    ∃ C V₀ : ℝ, 0 ≤ C ∧ 1 ≤ V₀ ∧ ∀ (θ θ' : S → ℝ), ∑ s, |θ s| ≤ Θ →
      (∀ v : S → ℝ, ∑ s, θ' s * v s =
        -∑ s, θ s * fderiv ℝ (N.massActionVectorField κ) xs v s) →
      ∀ V : ℝ, ∀ hV1 : 1 ≤ V, V₀ ≤ V → ∀ c : S → ℕ, (∀ s, (c s : ℝ) ≤ R₁ * V) →
        ‖∑ r, (N.stochasticMassActionRate (N.volumeScale κ V (by linarith)) c r : ℂ) *
            (Complex.exp (I * ((∑ s, θ s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θ' s * zeta V xs c s : ℝ) : ℂ) + ((N.quadG κ xs θ / 2 : ℝ) : ℂ)‖ ≤
        C * (1 + ‖zeta V xs c‖ ^ 2) / Real.sqrt V := by
  classical
  obtain ⟨L₂, hL₂0, hL₂⟩ := N.exists_taylor_bound κ hxsB
  obtain ⟨Lρ, hLρ0, hLρ⟩ := N.exists_rate_lipschitz κ hxsB
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
  refine ⟨C, max 1 (W ^ 2), hC0, le_max_left _ _, fun θ θ' hθ hadj V hV1 hV c hc => ?_⟩
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
  set T2 : ℝ := ∑ r, lam r * w r + ∑ s, θ' s * ζ s with hT2
  set T3 : ℝ := ∑ r, lam r * w r ^ 2 - N.quadG κ xs θ with hT3
  have hdecomp : ∑ r, (lam r : ℂ) * (Complex.exp (I * (w r : ℝ)) - 1) +
      I * ((∑ s, θ' s * ζ s : ℝ) : ℂ) + ((N.quadG κ xs θ / 2 : ℝ) : ℂ) =
      T1 + I * (T2 : ℂ) - ((T3 / 2 : ℝ) : ℂ) := by
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
    rw [hT2, h1, hlinJ, heq]
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, mul_sub, Finset.sum_sub_distrib]
    rw [← hfz]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hT2b : |T2| ≤ (Θ * L₂ * ‖ζ‖ ^ 2 + Es * W) / Real.sqrt V := by
    rw [hT2eq]
    have hA : |Real.sqrt V * ∑ s, θ s * (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs)) s| ≤
        Θ * L₂ * ‖ζ‖ ^ 2 / Real.sqrt V := by
      rw [abs_mul, abs_of_pos hsV]
      have h1 := abs_dot_le θ (N.massActionVectorField κ z - N.massActionVectorField κ xs - J (z - xs))
      have h2 := hL₂ z hzB
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
        have := hLρ r z hzB
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

/-- `gronwallBound δ K ε x ≤ (δ + ε x) e^{K x}`. -/
theorem gronwallBound_le_mul_exp {δ K ε x : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hx : 0 ≤ x) : gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with h0 | hpos
  · subst h0; rw [gronwallBound_K0]; simp
  · rw [gronwallBound_of_K_ne_0 hpos.ne']
    have he := Real.exp_pos (K * x)
    have h1 : (Real.exp (K * x) - 1) / K ≤ x * Real.exp (K * x) := by
      rw [div_le_iff₀ hpos]
      have h2 := Real.add_one_le_exp (-(K * x))
      have h3 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [mul_le_mul_of_nonneg_right h2 he.le]
    have h4 := mul_le_mul_of_nonneg_left h1 hε
    have : ε / K * (Real.exp (K * x) - 1) = ε * ((Real.exp (K * x) - 1) / K) := by ring
    show δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1) ≤ (δ + ε * x) * Real.exp (K * x)
    rw [this]
    nlinarith

/-- One jump moves the fluctuation by `Δ_r / √V`. -/
theorem zeta_next (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) {c : S → ℕ} {r : N.R}
    (hr : 0 < N.stochasticMassActionRate (N.volumeScale κ V hV) c r) (s : S) :
    zeta V xs (N.jumpNextCount c r) s = zeta V xs c s + N.reactionVector r s / Real.sqrt V := by
  have hen : N.Enabled c r := by
    by_contra h
    rw [N.stochasticMassActionRate_eq_zero_of_not_enabled _ c r h] at hr
    exact lt_irrefl _ hr
  have hcast : (N.jumpNextCount c r s : ℝ) = (c s : ℝ) + N.reactionVector r s := by
    simp only [jumpNextCount, reactionVector_apply]
    rw [Nat.cast_add, Nat.cast_sub (hen s)]
    ring
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsd : Real.sqrt V / V = 1 / Real.sqrt V := Real.sqrt_div_self'
  simp only [zeta, hcast]
  rw [show Real.sqrt V * (((c s : ℝ) + N.reactionVector r s) / V - xs s) =
    Real.sqrt V * ((c s : ℝ) / V - xs s) + N.reactionVector r s * (Real.sqrt V / V) by ring, hsd]
  ring

/-- The generator of `c ↦ exp(i θ · ζ(c) − a)`. -/
theorem cdrift_expObs (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (xs : Concentration S) (θ : S → ℝ) (a : ℂ) (c : S → ℕ) :
    (N.jumpSystem (N.volumeScale κ V hV)).cdrift
        (fun b => Complex.exp (I * ((∑ s, θ s * zeta V xs b s : ℝ) : ℂ) - a)) c =
      Complex.exp (I * ((∑ s, θ s * zeta V xs c s : ℝ) : ℂ) - a) *
        ∑ r, (N.stochasticMassActionRate (N.volumeScale κ V hV) c r : ℂ) *
          (Complex.exp (I * ((∑ s, θ s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) := by
  unfold JumpSystem.cdrift
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  show (N.stochasticMassActionRate (N.volumeScale κ V hV) c r : ℂ) *
      (Complex.exp (I * ((∑ s, θ s * zeta V xs (N.jumpNextCount c r) s : ℝ) : ℂ) - a) -
        Complex.exp (I * ((∑ s, θ s * zeta V xs c s : ℝ) : ℂ) - a)) = _
  rcases (N.stochasticMassActionRate_nonneg (N.volumeScale κ V hV) c r).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hsum : ∑ s, θ s * zeta V xs (N.jumpNextCount c r) s =
        ∑ s, θ s * zeta V xs c s + (∑ s, θ s * N.reactionVector r s) / Real.sqrt V := by
      simp only [N.zeta_next κ hV xs hpos, mul_add, Finset.sum_add_distrib, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsum]
    push_cast
    set A : ℂ := ∑ x, (θ x : ℂ) * (zeta V xs c x : ℂ) with hA
    set B : ℂ := (∑ x, (θ x : ℂ) * (N.reactionVector r x : ℂ)) / (Real.sqrt V : ℂ) with hB
    rw [show I * (A + B) - a = (I * A - a) + I * B by ring, Complex.exp_add]
    ring

theorem continuous_quadG (N : Network S) (κ : RateConstants N) (xs : Concentration S) :
    Continuous fun θ : S → ℝ => N.quadG κ xs θ := by
  unfold quadG
  fun_prop

set_option maxHeartbeats 3200000 in
/-- **The CLT error estimate at fixed volume.** -/
theorem clt_error (N : Network S) (κ : RateConstants N) {w : S → ℝ} (hwinv : N.IsPInvariant w)
    (hwpos : ∀ s, 0 < w s) {xs : Concentration S} (heq : N.massActionVectorField κ xs = 0)
    (hxs0 : ∀ s, 0 ≤ xs s) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (θf θf' : ℝ → S → ℝ) (hθd : ∀ u, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) xs v s) :
    ∃ K V₀ : ℝ, 0 ≤ K ∧ 1 ≤ V₀ ∧ ∀ (V : ℝ) (hV1 : 1 ≤ V), V₀ ≤ V → ∀ n : S → ℕ,
      ∑ s, w s * (n s : ℝ) ≤ M * V →
      ‖∑' m, (N.transition (N.volumeScale κ V (by linarith)) T n m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta V xs m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * zeta V xs n s : ℝ) : ℂ) -
          (((∫ u in (0 : ℝ)..T, N.quadG κ xs (θf u)) / 2 : ℝ) : ℂ))‖ ≤
        K * (1 + ∑ s, zeta V xs n s ^ 2) / Real.sqrt V := by
  classical
  set R₁ := ∑ s, M / w s with hR₁
  have hR₁0 : 0 ≤ R₁ := Finset.sum_nonneg fun s _ => div_nonneg hM (hwpos s).le
  set Rb := max R₁ (∑ s, xs s) with hRb
  have hRb0 : 0 ≤ Rb := le_trans hR₁0 (le_max_left _ _)
  have hxsB : xs ∈ Icc (0 : Concentration S) fun _ => Rb := ⟨fun s => hxs0 s, fun s =>
    le_trans (Finset.single_le_sum (f := fun s => xs s) (fun s _ => hxs0 s) (Finset.mem_univ s))
      (le_max_right _ _)⟩
  -- the conservative law of large numbers at the equilibrium
  obtain ⟨C₁, C₂, hC₁, hC₂, hlln⟩ := N.conservative_lln κ hwinv hwpos (T := T) (Rx := Rb) hM
    (fun _ => xs) continuousOn_const (fun t _ => by rw [heq]; exact hasDerivAt_const _ _)
    (fun t _ => hxsB)
  -- a bound on θ over [0, T]
  have hθc : Continuous θf := continuous_iff_continuousAt.mpr fun u => (hθd u).continuousAt
  obtain ⟨Θ₀, hΘ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun u => ∑ s, |θf u s|) (by fun_prop)
  set Θ := max Θ₀ 0 with hΘ
  have hΘ0 : 0 ≤ Θ := le_max_right _ _
  have hθΘ : ∀ u ∈ Icc 0 T, ∑ s, |θf u s| ≤ Θ := fun u hu =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hΘ₀ u hu).trans (le_max_left _ _))
  obtain ⟨C, V₀, hC0, hV₀, hgen⟩ := N.generator_error_le κ heq hRb0 hΘ0 hxsB
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
  set Φ : ℝ → ℝ := fun u => N.quadG κ xs (θf u) with hΦ
  have hΦc : Continuous Φ := (N.continuous_quadG κ xs).comp hθc
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => N.quadG_nonneg κ hxs0 _
  set Ifn : ℝ → ℝ := fun u => ∫ v in u..T, Φ v with hIfn
  have hIder : ∀ u, HasDerivAt Ifn (-Φ u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_left (hΦc.intervalIntegrable _ _)
      hΦc.aestronglyMeasurable.stronglyMeasurableAtFilter hΦc.continuousAt
  have hIc : Continuous Ifn := continuous_iff_continuousAt.mpr fun u => (hIder u).continuousAt
  have hI0 : ∀ u, u ≤ T → 0 ≤ Ifn u := fun u hu =>
    intervalIntegral.integral_nonneg hu fun v _ => hΦ0 v
  -- the observable
  set th : ℝ → (S → ℕ) → ℝ := fun u b => ∑ s, θf u s * zeta V xs b s with hth
  set F : ℝ → (S → ℕ) → ℂ := fun u b =>
    Complex.exp (I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ)) with hF
  set F' : ℝ → (S → ℕ) → ℂ := fun u b =>
    F u b * (I * ((∑ s, θf' u s * zeta V xs b s : ℝ) : ℂ) + ((Φ u / 2 : ℝ) : ℂ)) with hF'
  have hFnorm : ∀ u, u ≤ T → ∀ b, ‖F u b‖ ≤ 1 := by
    intro u hu b
    simp only [hF, Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    have := hI0 u hu
    linarith
  have hFder : ∀ u, ∀ b, HasDerivAt (fun u => F u b) (F' u b) u := by
    intro u b
    have hth' : HasDerivAt (fun u => th u b) (∑ s, θf' u s * zeta V xs b s) u := by
      have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun s u => θf u s * zeta V xs b s)
        (A' := fun s => θf' u s * zeta V xs b s) fun s _ =>
          ((hasDerivAt_pi.mp (hθd u)) s).mul_const _
      simpa [hth] using this
    have hin : HasDerivAt (fun u => I * ((th u b : ℝ) : ℂ) - ((Ifn u / 2 : ℝ) : ℂ))
        (I * ((∑ s, θf' u s * zeta V xs b s : ℝ) : ℂ) + ((Φ u / 2 : ℝ) : ℂ)) u := by
      have h1 := (hth'.ofReal_comp).const_mul I
      have h2 := ((hIder u).div_const 2).ofReal_comp
      convert h1.sub h2 using 1
      push_cast; ring
    have := hin.cexp
    simpa [hF', hF] using this
  -- pointwise error
  have hpt : ∀ u ∈ Icc 0 T, ∀ c ∈ Rset,
      ‖J.cdrift (F u) c + F' u c‖ ≤ C * (1 + ∑ s, zeta V xs c s ^ 2) / Real.sqrt V := by
    intro u hu c hc
    have hcd := N.cdrift_expObs κ hV0 xs (θf u) ((Ifn u / 2 : ℝ) : ℂ) c
    have heqF : J.cdrift (F u) c + F' u c = F u c *
        (∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V xs c s : ℝ) : ℂ) + ((Φ u / 2 : ℝ) : ℂ)) := by
      have : J.cdrift (F u) c = F u c * ∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) := hcd
      rw [this]
      simp only [hF']
      ring
    rw [heqF, norm_mul]
    have hg := hgen (θf u) (θf' u) (hθΘ u hu) (hadj u hu) V hV1 hV c (hcR c hc)
    have hz2 : ‖zeta V xs c‖ ^ 2 ≤ ∑ s, zeta V xs c s ^ 2 := norm_sq_le_sum_sq _
    calc ‖F u c‖ * ‖∑ r, (N.stochasticMassActionRate κV c r : ℂ) *
          (Complex.exp (I * ((∑ s, θf u s * N.reactionVector r s) / Real.sqrt V : ℝ)) - 1) +
          I * ((∑ s, θf' u s * zeta V xs c s : ℝ) : ℂ) + ((Φ u / 2 : ℝ) : ℂ)‖
        ≤ 1 * (C * (1 + ‖zeta V xs c‖ ^ 2) / Real.sqrt V) :=
          mul_le_mul (hFnorm u hu.2 c) hg (norm_nonneg _) zero_le_one
      _ ≤ C * (1 + ∑ s, zeta V xs c s ^ 2) / Real.sqrt V := by
          rw [one_mul]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hsV.le
  -- the expectation and its derivative
  set E : ℝ → ℂ := fun u => ∑ b ∈ Rset, (J.Pmin u n b : ℂ) * F u b with hE
  have hEder : ∀ u, 0 < u → HasDerivAt E (∑ c ∈ Rset, (J.Pmin u n c : ℂ) *
      (J.cdrift (F u) c + F' u c)) u := fun u hu =>
    J.hasDerivAt_csum_finite n Rset hsupp hclosed F F' hu fun b _ => hFder u b
  -- the mean squared fluctuation
  set G₀ := ∑ s, zeta V xs n s ^ 2 with hG₀
  have hG₀0 : 0 ≤ G₀ := Finset.sum_nonneg fun s _ => sq_nonneg _
  set B := C / Real.sqrt V * ((1 + C₂ * T) * Real.exp (C₁ * T) * (1 + G₀)) with hBdef
  have hEbound : ∀ u ∈ Ioo 0 T, ‖∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c)‖ ≤ B := by
    intro u hu
    have hu0 := hu.1.le
    have hP0 : ∀ c, 0 ≤ J.Pmin u n c := fun c => J.Pmin_nonneg u hu0 n c
    have hD := hlln V hV1 n hn u (Ioo_subset_Icc_self hu)
    have hDR : ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - xs s) ^ 2 ≤
        gronwallBound (∑ s, ((n s : ℝ) / V - xs s) ^ 2) C₁ (C₂ / V) u := by
      have : ∑' m, N.transition κV u n m * ∑ s, ((m s : ℝ) / V - xs s) ^ 2 =
          ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - xs s) ^ 2 :=
        tsum_eq_sum fun c hc => by
          show J.Pmin u n c * _ = 0
          rw [hsupp u c hc, zero_mul]
      rw [← this]; exact hD
    have hzV : ∀ c : S → ℕ, ∑ s, zeta V xs c s ^ 2 = V * ∑ s, ((c s : ℝ) / V - xs s) ^ 2 := by
      intro c
      simp only [zeta, mul_pow, Real.sq_sqrt hV0.le, Finset.mul_sum]
    have hg0 : 0 ≤ ∑ s, ((n s : ℝ) / V - xs s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
    have hgr := gronwallBound_le_mul_exp hg0 hC₁ (div_nonneg hC₂ hV0.le) hu0 (K := C₁)
      (ε := C₂ / V) (δ := ∑ s, ((n s : ℝ) / V - xs s) ^ 2)
    have hVD : ∑ c ∈ Rset, J.Pmin u n c * ∑ s, zeta V xs c s ^ 2 ≤
        (G₀ + C₂ * T) * Real.exp (C₁ * T) := by
      simp only [hzV]
      have e1 : ∑ c ∈ Rset, J.Pmin u n c * (V * ∑ s, ((c s : ℝ) / V - xs s) ^ 2) =
          V * ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - xs s) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1]
      have hexp : Real.exp (C₁ * u) ≤ Real.exp (C₁ * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2.le hC₁)
      have hG : G₀ = V * ∑ s, ((n s : ℝ) / V - xs s) ^ 2 := hzV n
      calc V * ∑ c ∈ Rset, J.Pmin u n c * ∑ s, ((c s : ℝ) / V - xs s) ^ 2
          ≤ V * (((∑ s, ((n s : ℝ) / V - xs s) ^ 2) + C₂ / V * u) * Real.exp (C₁ * u)) :=
            mul_le_mul_of_nonneg_left (hDR.trans hgr) hV0.le
        _ = (G₀ + C₂ * u) * Real.exp (C₁ * u) := by rw [hG]; field_simp
        _ ≤ (G₀ + C₂ * T) * Real.exp (C₁ * T) := by
            apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
            nlinarith [hu.2.le]
    have hsumP : ∑ c ∈ Rset, J.Pmin u n c ≤ 1 := J.sum_Pmin_le_one u hu0 n Rset
    calc ‖∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c)‖
        ≤ ∑ c ∈ Rset, J.Pmin u n c * (C * (1 + ∑ s, zeta V xs c s ^ 2) / Real.sqrt V) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 c)]
          exact mul_le_mul_of_nonneg_left (hpt u (Ioo_subset_Icc_self hu) c hc) (hP0 c)
      _ = C / Real.sqrt V * (∑ c ∈ Rset, J.Pmin u n c +
            ∑ c ∈ Rset, J.Pmin u n c * ∑ s, zeta V xs c s ^ 2) := by
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
    · have : Continuous fun u => F u b := continuous_iff_continuousAt.mpr fun u =>
        (hFder u b).continuousAt
      exact this.continuousOn
  -- mean value inequality, away from `0`, then `ε → 0`
  have hmv : ∀ ε ∈ Ioo 0 T, ‖E T - E ε‖ ≤ B * (T - ε) := by
    intro ε hε
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := E)
      (f' := fun u => ∑ c ∈ Rset, (J.Pmin u n c : ℂ) * (J.cdrift (F u) c + F' u c))
      (a := ε) (b := T) (C := B)
      (fun u hu => (hEder u (lt_of_lt_of_le hε.1 hu.1)).hasDerivWithinAt)
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
      Complex.exp (I * ((∑ s, θf T s * zeta V xs m s : ℝ) : ℂ)) := by
    simp only [hE, hF, hIfn, intervalIntegral.integral_same, zero_div, Complex.ofReal_zero,
      sub_zero]
    refine (tsum_eq_sum fun m hm => ?_).symm
    show (J.Pmin T n m : ℂ) * _ = 0
    rw [hsupp T m hm]; simp
  have hE0 : E 0 = Complex.exp (I * ((∑ s, θf 0 s * zeta V xs n s : ℝ) : ℂ) -
      (((∫ u in (0 : ℝ)..T, N.quadG κ xs (θf u)) / 2 : ℝ) : ℂ)) := by
    simp only [hE, JumpSystem.Pmin_zero]
    rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
      (fun h => absurd hnR h)]
    simp [hF, hIfn, hth, hΦ]
  rw [← hET, ← hE0]
  calc ‖E T - E 0‖ ≤ B * T := hET0
    _ = K * (1 + G₀) / Real.sqrt V := by
        simp only [hBdef, hK]
        field_simp

/-- **Central limit theorem for nonlinear conservative networks at an equilibrium.** For a
conservative network with an equilibrium `x* ≥ 0` of the mass-action equation, a `C¹` solution
`θ(·)` of the adjoint linearized equation `θ'(u) · v = −θ(u) · Df(x*) v` on `[0, T]`, and initial
counts with `⟨w, n_V⟩ ≤ M V` and `√V (n_V/V − x*) → z₀`, the characteristic function of
`θ(T) · √V (X^V(T)/V − x*)` converges:

`E exp(i θ(T) · ζ^V(T)) → exp(i θ(0) · z₀ − ½ ∫₀ᵀ ∑_r λ_r(x*) (θ(u) · Δ_r)² du)`. -/
theorem nonlinear_clt (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hwinv : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {xs : Concentration S}
    (heq : N.massActionVectorField κ xs = 0) (hxs0 : ∀ s, 0 ≤ xs s) {M T : ℝ} (hM : 0 ≤ M)
    (hT : 0 < T) (θf θf' : ℝ → S → ℝ) (hθd : ∀ u, HasDerivAt θf (θf' u) u)
    (hadj : ∀ u ∈ Icc 0 T, ∀ v : S → ℝ, ∑ s, θf' u s * v s =
      -∑ s, θf u s * fderiv ℝ (N.massActionVectorField κ) xs v s)
    (n : ℕ → S → ℕ) (hn : ∀ k : ℕ, ∑ s, w s * (n k s : ℝ) ≤ M * ((k : ℝ) + 1))
    {z₀ : S → ℝ} (hz : Tendsto (fun k : ℕ => zeta ((k : ℝ) + 1) xs (n k)) atTop (𝓝 z₀)) :
    Tendsto (fun k : ℕ => ∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity))
        T (n k) m : ℂ) * Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ)))
      atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) -
        (((∫ u in (0 : ℝ)..T, N.quadG κ xs (θf u)) / 2 : ℝ) : ℂ)))) := by
  obtain ⟨K, V₀, hK0, hV₀, hbd⟩ := N.clt_error κ hwinv hwpos heq hxs0 hM hT θf θf' hθd hadj
  set Ib : ℂ := (((∫ u in (0 : ℝ)..T, N.quadG κ xs (θf u)) / 2 : ℝ) : ℂ) with hIb
  set b : ℕ → ℂ := fun k => Complex.exp (I * ((∑ s, θf 0 s * zeta ((k : ℝ) + 1) xs (n k) s : ℝ) : ℂ) - Ib)
    with hb
  have hblim : Tendsto b atTop (𝓝 (Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib))) := by
    have hcont : Continuous fun z : S → ℝ =>
        Complex.exp (I * ((∑ s, θf 0 s * z s : ℝ) : ℂ) - Ib) := by fun_prop
    exact (hcont.tendsto z₀).comp hz
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hden
  have hG : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) xs (n k) s ^ 2)) atTop
      (𝓝 (K * (1 + ∑ s, z₀ s ^ 2))) := by
    have hc : Continuous fun z : S → ℝ => K * (1 + ∑ s, z s ^ 2) := by fun_prop
    exact (hc.tendsto z₀).comp hz
  have herr : Tendsto (fun k : ℕ => K * (1 + ∑ s, zeta ((k : ℝ) + 1) xs (n k) s ^ 2) /
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
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ)) -
        Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖
      ≤ ‖∑' m, (N.transition (N.volumeScale κ ((k : ℝ) + 1) (by positivity)) T (n k) m : ℂ) *
          Complex.exp (I * ((∑ s, θf T s * zeta ((k : ℝ) + 1) xs m s : ℝ) : ℂ)) - b k‖ +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * (1 + ∑ s, zeta ((k : ℝ) + 1) xs (n k) s ^ 2) / Real.sqrt ((k : ℝ) + 1) +
        ‖b k - Complex.exp (I * ((∑ s, θf 0 s * z₀ s : ℝ) : ℂ) - Ib)‖ := by
        gcongr

end Network
end CRNT
