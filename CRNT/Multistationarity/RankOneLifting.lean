import CRNT.Multistationarity.RevIrrReaction

/-!
# Lifting one-species multistationarity to rank-one networks

Let `N` be a network whose reaction vectors are all multiples of one vector `v`
(`reactionVector r = c_r v`), and let `i` be a species with `v_i ≠ 0`. Keeping only species `i`
gives the one-species embedded network with steady-state polynomial
`p(u) = ∑_r k_r c_r u^{y_{r,i}}`. If for some positive rates `k` this polynomial changes sign twice
(`p(u₀) p(u₁) < 0`, `p(u₁) p(u₂) < 0`), then `N` itself is multistationary.

Proof (frozen species): put species `i` at `1` and every other species at a large value `M`, move
along the class line `x(t) = x(M) + t v`, and take rate constants `κ_r = k_r / M^{∑_{s≠i} y_{r,s}}`.
As `M → ∞` the steady-state function `∑_r κ_r x(t)^{y_r} c_r` tends to `p(1 + t v_i)` at each fixed
`t`; the signs at the three sample points are inherited for large `M`, and the intermediate value
theorem gives two steady states in one class.

* `rankOne_multistationary_of_embedded_signChanges`.
* `rankOne_multistationary_of_alternating_triple`: three reactions with increasing source
  coefficients at `i` and alternating multipliers (a 2-alternating embedded one-species
  subnetwork) make a rank-one network multistationary; the triple gets the coefficients of an
  alternating three-term sum with a strict interior extremum, and the other reactions a small rate.
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
theorem tendsto_frozen_ratio_pow (c : ℝ) (n : ℕ) :
    Tendsto (fun M : ℝ => ((M + c) / M) ^ n) atTop (𝓝 1) := by
  have h0 : Tendsto (fun M : ℝ => c / M) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun M : ℝ => 1 + c / M) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  have h2 := h1.pow n
  rw [one_pow] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  congr 1; field_simp

/-- **Lifting sign changes of the one-species embedded network.** -/
theorem rankOne_multistationary_of_embedded_signChanges (N : Network S) {v : S → ℝ}
    (c : N.R → ℝ) (hc : ∀ r s, N.reactionVector r s = c r * v s) (i : S) (hvi : v i ≠ 0)
    (k : N.R → ℝ) (hk : ∀ r, 0 < k r) {u₀ u₁ u₂ : ℝ} (h0 : 0 < u₀) (h01 : u₀ < u₁)
    (h12 : u₁ < u₂)
    (hsign : (∑ r, k r * c r * u₀ ^ (N.reaction r).source i) *
        (∑ r, k r * c r * u₁ ^ (N.reaction r).source i) < 0 ∧
      (∑ r, k r * c r * u₁ ^ (N.reaction r).source i) *
        (∑ r, k r * c r * u₂ ^ (N.reaction r).source i) < 0) :
    N.HasMultistationarityCapacity := by
  classical
  set p : ℝ → ℝ := fun u => ∑ r, k r * c r * u ^ (N.reaction r).source i with hp
  -- the sample parameters `1 + t v_i = u_j`
  set t₀ := (u₀ - 1) / v i
  set t₁ := (u₁ - 1) / v i
  set t₂ := (u₂ - 1) / v i
  have hu : ∀ u, 1 + (u - 1) / v i * v i = u := fun u => by field_simp; ring
  -- the rescaled steady-state function
  let κM : ℝ → N.R → ℝ := fun M r => k r / ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s
  let Φ : ℝ → ℝ → ℝ := fun M t =>
    ∑ r, κM M r * (N.reaction r).source.massActionMonomial (frozenPoint i v M t) * c r
  have hlim : ∀ t, Tendsto (fun M => Φ M t) atTop (𝓝 (p (1 + t * v i))) := by
    intro t
    have hterm : ∀ r, Tendsto (fun M => κM M r *
        (N.reaction r).source.massActionMonomial (frozenPoint i v M t) * c r) atTop
        (𝓝 (k r * c r * (1 + t * v i) ^ (N.reaction r).source i)) := by
      intro r
      have hprod : Tendsto (fun M : ℝ => ∏ s ∈ Finset.univ.erase i,
          ((M + t * v s) / M) ^ (N.reaction r).source s) atTop (𝓝 1) := by
        have := tendsto_finsetProd (Finset.univ.erase i) fun s _ =>
          tendsto_frozen_ratio_pow (t * v s) ((N.reaction r).source s)
        simpa using this
      have key : ∀ M : ℝ, 0 < M → κM M r *
          (N.reaction r).source.massActionMonomial (frozenPoint i v M t) * c r =
          k r * (1 + t * v i) ^ (N.reaction r).source i *
            (∏ s ∈ Finset.univ.erase i, ((M + t * v s) / M) ^ (N.reaction r).source s) * c r := by
        intro M hM
        have hprodfp : (N.reaction r).source.massActionMonomial (frozenPoint i v M t) =
            (1 + t * v i) ^ (N.reaction r).source i *
              ∏ s ∈ Finset.univ.erase i, (M + t * v s) ^ (N.reaction r).source s := by
          rw [Complex.massActionMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
          congr 1
          · simp [frozenPoint]
          · exact Finset.prod_congr rfl fun s hs => by
              simp [frozenPoint, Finset.ne_of_mem_erase hs]
        have hdiv : ∏ s ∈ Finset.univ.erase i, ((M + t * v s) / M) ^ (N.reaction r).source s =
            (∏ s ∈ Finset.univ.erase i, (M + t * v s) ^ (N.reaction r).source s) /
              ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s := by
          rw [← Finset.prod_div_distrib]
          exact Finset.prod_congr rfl fun s _ => div_pow _ _ _
        have hP : ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ hM.ne'
        simp only [κM]
        rw [hprodfp, hdiv]
        field_simp
      have h := (hprod.const_mul (k r * (1 + t * v i) ^ (N.reaction r).source i)).mul_const (c r)
      have hval : k r * (1 + t * v i) ^ (N.reaction r).source i * 1 * c r =
          k r * c r * (1 + t * v i) ^ (N.reaction r).source i := by ring
      rw [hval] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
      rw [key M hM]
    have := tendsto_finsetSum (Finset.univ : Finset N.R) fun r _ => hterm r
    simpa [hp] using this
  -- signs at the three sample points for large `M`
  set T : ℝ := |t₀| + |t₁| + |t₂| with hT
  set V : ℝ := ∑ s, |v s| + 1 with hV
  have hV0 : 0 < V := by positivity
  have hpt : ∀ j : ℝ, p (1 + (j - 1) / v i * v i) = p j := fun j => by rw [hu]
  obtain ⟨M, hM0, hM1, hM2, hMb⟩ : ∃ M : ℝ, Φ M t₀ * Φ M t₁ < 0 ∧ Φ M t₁ * Φ M t₂ < 0 ∧
      True ∧ T * V + 1 < M := by
    have e0 := hlim t₀
    have e1 := hlim t₁
    have e2 := hlim t₂
    have ht0 : 1 + t₀ * v i = u₀ := hu u₀
    have ht1 : 1 + t₁ * v i = u₁ := hu u₁
    have ht2 : 1 + t₂ * v i = u₂ := hu u₂
    rw [ht0] at e0
    rw [ht1] at e1
    rw [ht2] at e2
    have h01' := ((e0.mul e1).eventually (gt_mem_nhds hsign.1))
    have h12' := ((e1.mul e2).eventually (gt_mem_nhds hsign.2))
    exact ((h01'.and h12').and (eventually_gt_atTop (T * V + 1))).exists.imp
      fun M h => ⟨h.1.1, h.1.2, trivial, h.2⟩
  have hMpos : 0 < M := by
    have : 0 ≤ T * V := mul_nonneg (by positivity) hV0.le
    linarith
  -- continuity: the steady-state function is polynomial in `t`
  have hcont : Continuous (Φ M) := by
    simp only [Φ, Complex.massActionMonomial, frozenPoint]
    fun_prop
  -- the middle sample point lies strictly between the outer ones
  have hmid : (t₀ - t₁) * (t₂ - t₁) < 0 := by
    have : (t₀ - t₁) * (t₂ - t₁) = (u₀ - u₁) * (u₂ - u₁) / (v i) ^ 2 := by
      simp only [t₀, t₁, t₂]; field_simp; ring
    rw [this]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
      (by positivity)
  -- zeros between the sample points
  have hzero : ∀ a b, Φ M a * Φ M b < 0 → ∃ τ ∈ Set.uIcc a b, Φ M τ = 0 := by
    intro a b hab
    have hmem : (0 : ℝ) ∈ Set.uIcc (Φ M a) (Φ M b) := by
      rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Set.mem_uIcc.mpr (Or.inr ⟨hb.le, ha.le⟩)
      · exact Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩)
    obtain ⟨τ, hτ, hΦτ⟩ := intermediate_value_uIcc hcont.continuousOn hmem
    exact ⟨τ, hτ, hΦτ⟩
  obtain ⟨τ, hτ, hΦτ⟩ := hzero t₀ t₁ hM0
  obtain ⟨τ', hτ', hΦτ'⟩ := hzero t₁ t₂ hM1
  have hΦt₁ : Φ M t₁ ≠ 0 := fun h => by rw [h, mul_zero] at hM0; exact lt_irrefl 0 hM0
  have hne : τ ≠ τ' := by
    intro heq
    subst heq
    apply hΦt₁
    have : τ = t₁ := by
      rw [Set.mem_uIcc] at hτ hτ'
      rcases mul_neg_iff.mp hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hτ with ⟨_, h⟩ | ⟨h, _⟩ <;> rcases hτ' with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith
      · rcases hτ with ⟨_, h⟩ | ⟨h, _⟩ <;> rcases hτ' with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith
    rw [← this]; exact hΦτ
  -- positivity of the two points
  have hbound : ∀ t ∈ Set.uIcc t₀ t₂, |t| ≤ T ∧ 0 < 1 + t * v i := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    constructor
    · rw [hT]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;>
        cases abs_cases t₀ <;> cases abs_cases t₂ <;> cases abs_cases t₁ <;> linarith
    · have e0 := hu u₀
      have e2 := hu u₂
      rcases lt_or_gt_of_ne hvi with hv | hv
      · rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · nlinarith [mul_le_mul_of_nonpos_right h2 hv.le]
        · nlinarith [mul_le_mul_of_nonpos_right h2 hv.le]
      · rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · nlinarith [mul_le_mul_of_nonneg_right h1 hv.le]
        · nlinarith [mul_le_mul_of_nonneg_right h1 hv.le]
  have hsub : ∀ t, t ∈ Set.uIcc t₀ t₁ ∨ t ∈ Set.uIcc t₁ t₂ → t ∈ Set.uIcc t₀ t₂ := by
    intro t ht
    simp only [Set.mem_uIcc] at ht ⊢
    rcases mul_neg_iff.mp hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases ht with ((⟨a1, a2⟩ | ⟨a1, a2⟩) | (⟨a1, a2⟩ | ⟨a1, a2⟩)) <;>
      first | (left; constructor <;> linarith) | (right; constructor <;> linarith)
  have hpos : ∀ t ∈ Set.uIcc t₀ t₂, (frozenPoint i v M t).Positive := by
    intro t ht s
    obtain ⟨hTt, hi⟩ := hbound t ht
    by_cases hs : s = i
    · subst hs; simpa [frozenPoint] using hi
    · simp only [frozenPoint, hs, ↓reduceIte]
      have hvs : |v s| ≤ V := by
        have := Finset.single_le_sum (f := fun s => |v s|) (fun s _ => abs_nonneg _)
          (Finset.mem_univ s)
        simp only [hV]; linarith
      have : |t * v s| ≤ T * V := by
        rw [abs_mul]; exact mul_le_mul hTt hvs (abs_nonneg _) (by positivity)
      have := neg_abs_le (t * v s)
      linarith
  -- rate constants and steady states
  have hκpos : ∀ r, 0 < κM M r := fun r =>
    div_pos (hk r) (Finset.prod_pos fun s _ => pow_pos hMpos _)
  let κ : RateConstants N := ⟨κM M, hκpos⟩
  have hsteady : ∀ t, Φ M t = 0 → N.IsMassActionSteadyState κ (frozenPoint i v M t) := by
    intro t ht s
    show N.massActionVectorField κ (frozenPoint i v M t) s = 0
    rw [massActionVectorField_apply]
    have : ∑ r, N.massActionRate κ r (frozenPoint i v M t) * N.reactionVector r s =
        Φ M t * v s := by
      simp only [Φ, Finset.sum_mul, hc, massActionRate]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this, ht, zero_mul]
  -- `v` lies in the stoichiometric subspace
  obtain ⟨r₀, hr₀⟩ : ∃ r, c r ≠ 0 := by
    by_contra hall
    push Not at hall
    have : ∀ u : ℝ, (∑ r, k r * c r * u ^ (N.reaction r).source i) = 0 := fun u => by
      simp [hall]
    rw [this u₀, this u₁, zero_mul] at hsign
    exact lt_irrefl 0 hsign.1
  have hvS : v ∈ N.stoichSubspace := by
    have : v = (c r₀)⁻¹ • N.reactionVector r₀ := by
      funext s; rw [Pi.smul_apply, smul_eq_mul, hc]; field_simp
    rw [this]; exact Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r₀)
  have hp₁ := hpos τ (hsub τ (Or.inl hτ))
  have hp₂ := hpos τ' (hsub τ' (Or.inr hτ'))
  refine ⟨κ, frozenPoint i v M τ, frozenPoint i v M τ, frozenPoint i v M τ',
    ⟨StoichCompatible.refl _ _, hp₁⟩, ⟨?_, hp₂⟩, hsteady τ hΦτ, hsteady τ' hΦτ', ?_⟩
  · show frozenPoint i v M τ' - frozenPoint i v M τ ∈ N.stoichSubspace
    have : frozenPoint i v M τ' - frozenPoint i v M τ = (τ' - τ) • v := by
      funext s; simp only [frozenPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact Submodule.smul_mem _ _ hvS
  · intro heq
    have := congrFun heq i
    simp only [frozenPoint, ↓reduceIte, add_right_inj] at this
    exact hne (mul_right_cancel₀ hvi this)

/-- Sign preservation under a small perturbation. -/
theorem mul_neg_of_perturb {q₀ q₁ e₀ e₁ : ℝ} (h : q₀ * q₁ < 0) (h₀ : |e₀| < |q₀|)
    (h₁ : |e₁| < |q₁|) : (q₀ + e₀) * (q₁ + e₁) < 0 := by
  rcases mul_neg_iff.mp h with ⟨a, b⟩ | ⟨a, b⟩
  · rw [abs_of_pos a] at h₀; rw [abs_of_neg b] at h₁
    have := (abs_lt.mp h₀).1; have := (abs_lt.mp h₁).2
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · rw [abs_of_neg a] at h₀; rw [abs_of_pos b] at h₁
    have := (abs_lt.mp h₀).2; have := (abs_lt.mp h₁).1
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- **Alternating triples lift.** In a rank-one network (`reactionVector r = c_r v`), if three
reactions have increasing source coefficients `e₁ < e₂ < e₃` at a species `i` with `v_i ≠ 0`, and
their multipliers alternate in sign (`c₁ c₂ < 0`, `c₂ c₃ < 0`) — a 2-alternating one-species
embedded subnetwork in the sense of Joshi–Shiu — then the network is multistationary. -/
theorem rankOne_multistationary_of_alternating_triple (N : Network S) {v : S → ℝ}
    (c : N.R → ℝ) (hc : ∀ r s, N.reactionVector r s = c r * v s) (i : S) (hvi : v i ≠ 0)
    {r₁ r₂ r₃ : N.R} (he₁₂ : (N.reaction r₁).source i < (N.reaction r₂).source i)
    (he₂₃ : (N.reaction r₂).source i < (N.reaction r₃).source i)
    (hc₁₂ : c r₁ * c r₂ < 0) (hc₂₃ : c r₂ * c r₃ < 0) :
    N.HasMultistationarityCapacity := by
  classical
  -- normalize the sign: `c r₁ > 0`
  wlog hpos : 0 < c r₁ generalizing c v
  · have hc₁ : c r₁ ≠ 0 := fun h => by rw [h, zero_mul] at hc₁₂; exact lt_irrefl 0 hc₁₂
    refine this (fun r => -c r) (v := fun s => -v s) (fun r s => by rw [hc]; ring)
      (neg_ne_zero.mpr hvi) (by nlinarith) (by nlinarith) ?_
    have : c r₁ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hc₁
    linarith
  have h12 : r₁ ≠ r₂ := fun h => by rw [h] at he₁₂; exact lt_irrefl _ he₁₂
  have h23 : r₂ ≠ r₃ := fun h => by rw [h] at he₂₃; exact lt_irrefl _ he₂₃
  have h13 : r₁ ≠ r₃ := fun h => by rw [h] at he₁₂; exact lt_irrefl _ (he₁₂.trans he₂₃)
  have hneg2 : c r₂ < 0 := by
    by_contra h; push Not at h; nlinarith [mul_nonneg hpos.le h]
  have hpos3 : 0 < c r₃ := by
    by_contra h; push Not at h; nlinarith [mul_nonneg_of_nonpos_of_nonpos hneg2.le h]
  set e₁ := (N.reaction r₁).source i
  set e₂ := (N.reaction r₂).source i
  set e₃ := (N.reaction r₃).source i
  -- the three-term profile `|B| e^{τA} + |A| e^{τB}` with `A = e₁ − e₂ < 0 < B = e₃ − e₂`
  set A : ℝ := (e₁ : ℝ) - e₂ with hA
  set B : ℝ := (e₃ : ℝ) - e₂ with hB
  have hA0 : A < 0 := by
    rw [hA]; have : (e₁ : ℝ) < e₂ := by exact_mod_cast he₁₂
    linarith
  have hB0 : 0 < B := by
    rw [hB]; have : (e₂ : ℝ) < e₃ := by exact_mod_cast he₂₃
    linarith
  have hAB : A * B < 0 := mul_neg_of_neg_of_pos hA0 hB0
  set F : ℝ → ℝ := fun τ => |B| * Real.exp (τ * A) + |A| * Real.exp (τ * B) with hF
  have hfp : |A| + |B| < F 1 := frozen_min_gap hAB 1 (Or.inl rfl)
  have hfm : |A| + |B| < F (-1) := frozen_min_gap hAB (-1) (Or.inr rfl)
  set L := ((|A| + |B|) + min (F 1) (F (-1))) / 2 with hL
  have hmin := lt_min hfp hfm
  have hL0 : |A| + |B| < L := by rw [hL]; linarith
  have hL1 : L < F 1 := by rw [hL]; have := min_le_left (F 1) (F (-1)); linarith
  have hL2 : L < F (-1) := by rw [hL]; have := min_le_right (F 1) (F (-1)); linarith
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL0
  -- the triple polynomial
  set q : ℝ → ℝ := fun u => |B| * u ^ e₁ - L * u ^ e₂ + |A| * u ^ e₃ with hq
  have hqexp : ∀ τ : ℝ, q (Real.exp τ) = Real.exp (τ * e₂) * (F τ - L) := by
    intro τ
    simp only [hq, hF, ← Real.exp_nat_mul, hA, hB]
    have e1 : Real.exp (τ * ((e₁ : ℝ) - e₂)) * Real.exp (τ * e₂) = Real.exp (e₁ * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (τ * ((e₃ : ℝ) - e₂)) * Real.exp (τ * e₂) = Real.exp (e₃ * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← e1, ← e3, show (e₂ : ℝ) * τ = τ * e₂ by ring]
    ring
  have hq0 : 0 < q (Real.exp (-1)) := by
    rw [hqexp]; exact mul_pos (Real.exp_pos _) (by linarith)
  have hq1 : q (Real.exp 0) < 0 := by
    rw [hqexp]
    have : F 0 = |B| + |A| := by simp [hF]
    rw [this]; exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)
  have hq2 : 0 < q (Real.exp 1) := by
    rw [hqexp]; exact mul_pos (Real.exp_pos _) (by linarith)
  -- the remaining reactions with a small rate `ε`
  set T : Finset N.R := {r₁, r₂, r₃} with hT
  set R : ℝ → ℝ := fun u => ∑ r ∈ Finset.univ.filter (· ∉ T), c r * u ^ (N.reaction r).source i
    with hR
  set u₀ := Real.exp (-1)
  set u₁ := Real.exp 0
  set u₂ := Real.exp 1
  set m : ℝ := min |q u₀| (min |q u₁| |q u₂|) with hm
  have hm0 : 0 < m := lt_min (abs_pos.mpr hq0.ne') (lt_min (abs_pos.mpr hq1.ne) (abs_pos.mpr hq2.ne'))
  set Bd : ℝ := |R u₀| + |R u₁| + |R u₂| + 1 with hBd
  have hBd0 : 0 < Bd := by positivity
  set ε : ℝ := m / (2 * Bd) with hε
  have hε0 : 0 < ε := by positivity
  have hsmall : ∀ u, |R u| < Bd → |ε * R u| < m := by
    intro u hu
    rw [abs_mul, abs_of_pos hε0, hε]
    calc m / (2 * Bd) * |R u| ≤ m / (2 * Bd) * Bd :=
          mul_le_mul_of_nonneg_left hu.le (by positivity)
      _ = m / 2 := by field_simp
      _ < m := by linarith
  have hB₀ : |R u₀| < Bd := by
    rw [hBd]; have := abs_nonneg (R u₁); have := abs_nonneg (R u₂); linarith
  have hB₁ : |R u₁| < Bd := by
    rw [hBd]; have := abs_nonneg (R u₀); have := abs_nonneg (R u₂); linarith
  have hB₂ : |R u₂| < Bd := by
    rw [hBd]; have := abs_nonneg (R u₀); have := abs_nonneg (R u₁); linarith
  -- the rates
  set k : N.R → ℝ := fun r => if r = r₁ then |B| / c r₁ else if r = r₂ then L / (-c r₂)
    else if r = r₃ then |A| / c r₃ else ε with hk
  have hkpos : ∀ r, 0 < k r := by
    intro r; simp only [hk]
    split_ifs
    · exact div_pos (abs_pos.mpr hB0.ne') hpos
    · exact div_pos hLpos (by linarith)
    · exact div_pos (abs_pos.mpr hA0.ne) hpos3
    · exact hε0
  have hk1 : k r₁ = |B| / c r₁ := by simp [hk]
  have hk2 : k r₂ = L / (-c r₂) := by simp [hk, Ne.symm h12]
  have hk3 : k r₃ = |A| / c r₃ := by simp [hk, Ne.symm h13, Ne.symm h23]
  have hkε : ∀ r, r ∉ T → k r = ε := by
    intro r hr
    simp only [hT, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    simp [hk, hr.1, hr.2.1, hr.2.2]
  have hdecomp : ∀ u, ∑ r, k r * c r * u ^ (N.reaction r).source i = q u + ε * R u := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T)]
    have hT' : Finset.univ.filter (· ∈ T) = T := by ext r; simp
    rw [hT']
    have hrest : ∑ r ∈ Finset.univ.filter (· ∉ T), k r * c r * u ^ (N.reaction r).source i =
        ε * R u := by
      rw [hR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hkε r (Finset.mem_filter.mp hr).2]; ring
    rw [hrest, hT, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton, hk1, hk2, hk3]
    simp only [hq]
    have h1ne := hpos.ne'
    have h2ne := hneg2.ne
    have h3ne := hpos3.ne'
    field_simp
    ring
  refine rankOne_multistationary_of_embedded_signChanges N c hc i hvi k hkpos
    (u₀ := u₀) (u₁ := u₁) (u₂ := u₂) (Real.exp_pos _)
    (Real.exp_lt_exp.mpr (by norm_num)) (Real.exp_lt_exp.mpr (by norm_num)) ⟨?_, ?_⟩
  · rw [hdecomp, hdecomp]
    exact mul_neg_of_perturb (mul_neg_of_pos_of_neg hq0 hq1)
      (lt_of_lt_of_le (hsmall _ hB₀) (min_le_left _ _))
      (lt_of_lt_of_le (hsmall _ hB₁) ((min_le_right _ _).trans (min_le_left _ _)))
  · rw [hdecomp, hdecomp]
    exact mul_neg_of_perturb (mul_neg_of_neg_of_pos hq1 hq2)
      (lt_of_lt_of_le (hsmall _ hB₁) ((min_le_right _ _).trans (min_le_left _ _)))
      (lt_of_lt_of_le (hsmall _ hB₂) ((min_le_right _ _).trans (min_le_right _ _)))

/-- The network `y ⇌ y'`, `z ⇌ z'`: reactions `0 : y → y'`, `1 : y' → y`, `2 : z → z'`,
`3 : z' → z`. -/
def revRev (y y' z z' : Complex S) : Network S :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨y, y'⟩ else if r = 1 then ⟨y', y⟩ else if r = 2 then ⟨z, z'⟩ else ⟨z', z⟩⟩

/-- **Joshi–Shiu 2017, Theorem 5.12, sufficiency.** If `z' − z = μ (y' − y)` with `μ ≠ 0` and for
some species `i` the coordinate intervals of the two reversible pairs are disjoint and
nondegenerate (`max {y_i, y'_i} < min {z_i, z'_i}` or `max {z_i, z'_i} < min {y_i, y'_i}`, with
`y_i ≠ y'_i`), then `y ⇌ y'`, `z ⇌ z'` is multistationary. -/
theorem revRev_multistationary_of_separated {y y' z z' : Complex S} {μ : ℝ} (hμ : μ ≠ 0)
    (hw : ∀ s, rv z z' s = μ * rv y y' s) (i : S) (hyi : y i ≠ y' i)
    (hsep : max (y i) (y' i) < min (z i) (z' i) ∨ max (z i) (z' i) < min (y i) (y' i)) :
    (revRev y y' z z').HasMultistationarityCapacity := by
  classical
  let c : (revRev y y' z z').R → ℝ := fun (r : Fin 4) =>
    if r = 0 then 1 else if r = 1 then -1 else if r = 2 then μ else -μ
  have hc : ∀ r s, (revRev y y' z z').reactionVector r s = c r * rv y y' s := by
    intro r s
    have h := hw s
    fin_cases r
    · show ((y' s : ℝ) - y s) = 1 * rv y y' s; simp [rv]
    · show ((y s : ℝ) - y' s) = -1 * rv y y' s; simp [rv]
    · show ((z' s : ℝ) - z s) = μ * rv y y' s; exact h
    · show ((z s : ℝ) - z' s) = -μ * rv y y' s
      have : ((z s : ℝ) - z' s) = -rv z z' s := by simp [rv]
      rw [this, h]; ring
  have hvi : rv y y' i ≠ 0 := by
    simp only [rv]; intro h; apply hyi; exact_mod_cast (sub_eq_zero.mp h).symm
  have hwi := hw i
  simp only [rv] at hwi
  have hc0 : c (0 : Fin 4) = 1 := rfl
  have hc1 : c (1 : Fin 4) = -1 := rfl
  have hc2 : c (2 : Fin 4) = μ := rfl
  have hc3 : c (3 : Fin 4) = -μ := rfl
  have hs0 : ((revRev y y' z z').reaction (0 : Fin 4)).source i = y i := rfl
  have hs1 : ((revRev y y' z z').reaction (1 : Fin 4)).source i = y' i := rfl
  have hs2 : ((revRev y y' z z').reaction (2 : Fin 4)).source i = z i := rfl
  have hs3 : ((revRev y y' z z').reaction (3 : Fin 4)).source i = z' i := rfl
  have tri := fun (r₁ r₂ r₃ : Fin 4) => rankOne_multistationary_of_alternating_triple
    (revRev y y' z z') c hc i hvi (r₁ := r₁) (r₂ := r₂) (r₃ := r₃)
  have hzz : z i ≠ z' i := by
    intro h
    have h0 : ((z' i : ℝ) - z i) = 0 := by rw [h]; ring
    rw [hwi] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hμ h1
    · exact hvi (by simp only [rv]; exact h1)
  rcases lt_or_gt_of_ne hyi with hy | hy
  · -- `y_i < y'_i`
    have hy' : (y i : ℝ) < y' i := by exact_mod_cast hy
    rcases hsep with hs | hs
    · rcases lt_or_gt_of_ne hzz with hz' | hz'
      · have hzr : (z i : ℝ) < z' i := by exact_mod_cast hz'
        have : 0 < μ := by nlinarith
        exact tri 0 1 2 (by rw [hs0, hs1]; exact hy) (by rw [hs1, hs2]; omega)
          (by rw [hc0, hc1]; norm_num) (by rw [hc1, hc2]; linarith)
      · have hzr : (z' i : ℝ) < z i := by exact_mod_cast hz'
        have : μ < 0 := by nlinarith
        exact tri 0 1 3 (by rw [hs0, hs1]; exact hy) (by rw [hs1, hs3]; omega)
          (by rw [hc0, hc1]; norm_num) (by rw [hc1, hc3]; linarith)
    · rcases lt_or_gt_of_ne hzz with hz' | hz'
      · have hzr : (z i : ℝ) < z' i := by exact_mod_cast hz'
        have : 0 < μ := by nlinarith
        exact tri 2 3 0 (by rw [hs2, hs3]; exact hz') (by rw [hs3, hs0]; omega)
          (by rw [hc2, hc3]; nlinarith) (by rw [hc3, hc0]; linarith)
      · have hzr : (z' i : ℝ) < z i := by exact_mod_cast hz'
        have : μ < 0 := by nlinarith
        exact tri 3 2 0 (by rw [hs3, hs2]; exact hz') (by rw [hs2, hs0]; omega)
          (by rw [hc3, hc2]; nlinarith) (by rw [hc2, hc0]; linarith)
  · -- `y'_i < y_i`
    have hy' : (y' i : ℝ) < y i := by exact_mod_cast hy
    rcases hsep with hs | hs
    · rcases lt_or_gt_of_ne hzz with hz' | hz'
      · have hzr : (z i : ℝ) < z' i := by exact_mod_cast hz'
        have : μ < 0 := by nlinarith
        exact tri 1 0 2 (by rw [hs1, hs0]; exact hy) (by rw [hs0, hs2]; omega)
          (by rw [hc1, hc0]; norm_num) (by rw [hc0, hc2]; linarith)
      · have hzr : (z' i : ℝ) < z i := by exact_mod_cast hz'
        have : 0 < μ := by nlinarith
        exact tri 1 0 3 (by rw [hs1, hs0]; exact hy) (by rw [hs0, hs3]; omega)
          (by rw [hc1, hc0]; norm_num) (by rw [hc0, hc3]; linarith)
    · rcases lt_or_gt_of_ne hzz with hz' | hz'
      · have hzr : (z i : ℝ) < z' i := by exact_mod_cast hz'
        have : μ < 0 := by nlinarith
        exact tri 2 3 1 (by rw [hs2, hs3]; exact hz') (by rw [hs3, hs1]; omega)
          (by rw [hc2, hc3]; nlinarith) (by rw [hc3, hc1]; linarith)
      · have hzr : (z' i : ℝ) < z i := by exact_mod_cast hz'
        have : 0 < μ := by nlinarith
        exact tri 3 2 1 (by rw [hs3, hs2]; exact hz') (by rw [hs2, hs1]; omega)
          (by rw [hc3, hc2]; nlinarith) (by rw [hc2, hc1]; linarith)

end Network

end CRNT
