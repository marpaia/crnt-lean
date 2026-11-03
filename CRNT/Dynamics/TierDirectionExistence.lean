import CRNT.Dynamics.TierDirectionFeasibility
import CRNT.Dynamics.GordanAlternative
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Every tier sequence has a realizing direction

`exists_direction_of_sequence` (a transposition theorem along a sequence): if finitely many linear
forms `⟨d_k, ·⟩` tend to `-∞` along a sequence `L n` while finitely many forms `⟨e_j, ·⟩` stay
eventually bounded, some fixed direction `w` has `⟨e_j, w⟩ = 0` for all `j` and `⟨d_k, w⟩ ≤ -1`
for all `k`.

Proof: otherwise the open negative orthant of `ℝ^K` misses the image of `⋂ ker ⟨e_j, ·⟩` under
`w ↦ (⟨d_k, w⟩)_k`; Hahn–Banach separation gives `c ≥ 0`, `c ≠ 0`, whose combination
`∑ c_k ⟨d_k, ·⟩` vanishes on that kernel, hence (`mem_span_of_iInf_ker_le_ker`) equals some
`∑ μ_j ⟨e_j, ·⟩`.  Evaluated along `L n` the left side tends to `-∞` and the right side is bounded.

`tierDirectionSystemFeasible_of_positiveSequence` applies this to `log xs n`: strict tier
comparisons give forms tending to `-∞`, same-tier comparisons give convergent forms.  This proves
`EveryTransversalTierDirectionSystemFeasible`, the finite-dimensional input of the
strongly-endotactic tier characterization (`TierDirectionSystemFeasibilityClaim`).

Nothing here is an axiom or a `sorry`.
-/

open Finset Filter Topology

namespace CRNT

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Direction from a sequence.** -/
theorem exists_direction_of_sequence {K J : Type} [Fintype K] [Fintype J]
    (d : K → S → ℝ) (e : J → S → ℝ) (L : ℕ → S → ℝ)
    (hd : ∀ k, Tendsto (fun n => ∑ s, d k s * L n s) atTop atBot)
    (he : ∀ j, ∃ C, ∀ᶠ n in atTop, |∑ s, e j s * L n s| ≤ C) :
    ∃ w : S → ℝ, (∀ j, ∑ s, e j s * w s = 0) ∧ ∀ k, ∑ s, d k s * w s ≤ -1 := by
  classical
  -- linear forms
  let ψ : J → (S → ℝ) →ₗ[ℝ] ℝ := fun j =>
    { toFun := fun w => ∑ s, e j s * w s
      map_add' := fun a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c a => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
                                 exact sum_congr rfl fun s _ => by ring }
  let A : (S → ℝ) →ₗ[ℝ] (K → ℝ) :=
    { toFun := fun w k => ∑ s, d k s * w s
      map_add' := fun a b => by funext k; simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c a => by
        funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun s _ => by ring }
  set V : Submodule ℝ (S → ℝ) := ⨅ j, LinearMap.ker (ψ j) with hV
  -- step 1: a direction with strict signs
  have hstrict : ∃ w ∈ V, ∀ k, A w k < 0 := by
    by_contra hno
    push Not at hno
    set O : Set (K → ℝ) := {z | ∀ k, z k < 0} with hO
    set T : Set (K → ℝ) := (V.map A : Set (K → ℝ)) with hT
    have hOc : Convex ℝ O := by
      intro x hx y hy a b ha hb hab k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases ha.eq_or_lt with rfl | ha'
      · simp at hab; subst hab; simpa using hy k
      · nlinarith [hx k, hy k]
    have hOo : IsOpen O := by
      have : O = ⋂ k, {z : K → ℝ | z k < 0} := by ext z; simp [hO]
      rw [this]; exact isOpen_iInter_of_finite fun k => isOpen_lt (continuous_apply k) continuous_const
    have hTc : Convex ℝ T := (V.map A).convex
    have hdisj : Disjoint O T := by
      rw [Set.disjoint_left]
      rintro z hz ⟨w, hwV, rfl⟩
      obtain ⟨k, hk⟩ := hno w hwV
      exact absurd (hz k) (not_lt.mpr hk)
    obtain ⟨f, u, hfO, hfT⟩ := geometric_hahn_banach_open hOc hOo hTc hdisj
    set c : K → ℝ := fun k => f (Pi.single k 1) with hc
    have hf : ∀ z, f z = ∑ k, z k * c k := strongDual_apply_eq_sum f
    have hu : u ≤ 0 := by have := hfT 0 (V.map A).zero_mem; rwa [map_zero] at this
    -- `f` vanishes on `T`
    have hfT0 : ∀ t ∈ T, f t = 0 := by
      intro t ht
      by_contra hne
      have hmem : (-(1 - u) / f t) • t ∈ T := (V.map A).smul_mem _ ht
      have := hfT _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    -- coefficients are nonnegative, not all zero
    have hneg1 : (fun _ : K => (-1 : ℝ)) ∈ O := fun _ => by norm_num
    have hcnn : ∀ k, 0 ≤ c k := by
      intro k
      by_contra hck
      push Not at hck
      set M : ℝ := (∑ k', c k' - u + 1) / (-c k) with hM
      have hMpos : 0 ≤ M := by
        apply div_nonneg _ (by linarith)
        have := hfO _ hneg1
        rw [hf] at this
        simp only [neg_one_mul, sum_neg_distrib] at this
        linarith
      have hz : (fun k' => (-1 : ℝ) - M * (if k' = k then 1 else 0)) ∈ O := by
        intro k'
        show (-1 : ℝ) - M * (if k' = k then 1 else 0) < 0
        split_ifs <;> nlinarith
      have h := hfO _ hz
      rw [hf] at h
      have e1 : ∑ k', ((-1 : ℝ) - M * (if k' = k then 1 else 0)) * c k' =
          -∑ k', c k' - M * c k := by
        simp only [sub_mul, sum_sub_distrib, neg_one_mul, sum_neg_distrib, mul_assoc, ite_mul,
          one_mul, zero_mul, ← mul_sum, sum_ite_eq', mem_univ, if_true]
      rw [e1] at h
      have : M * c k = -(∑ k', c k' - u + 1) := by
        rw [hM, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
      linarith
    have hcpos : 0 < ∑ k, c k := by
      have := hfO _ hneg1
      rw [hf] at this
      simp only [neg_one_mul, sum_neg_distrib] at this
      linarith
    -- the combination of the `d`-forms lies in the span of the `e`-forms
    let φ : (S → ℝ) →ₗ[ℝ] ℝ := (Finset.univ.sum fun k => c k • (LinearMap.proj k ∘ₗ A))
    have hφ : ∀ w, φ w = ∑ k, c k * ∑ s, d k s * w s := by
      intro w; simp [φ, A, LinearMap.sum_apply]
    have hker : ⨅ j, LinearMap.ker (ψ j) ≤ LinearMap.ker φ := by
      intro w hw
      rw [LinearMap.mem_ker, hφ]
      have h0 := hfT0 (A w) ⟨w, hw, rfl⟩
      rw [hf] at h0
      simpa [A, mul_comm] using h0
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hker)
    have hμL : ∀ n, ∑ k, c k * ∑ s, d k s * L n s = ∑ j, μ j * ∑ s, e j s * L n s := by
      intro n
      have := congrArg (fun F : (S → ℝ) →ₗ[ℝ] ℝ => F (L n)) hμ
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
      rw [← hφ]; rw [← this]; rfl
    -- bounds
    choose C hC using he
    have hbound : ∀ᶠ n in atTop, -(∑ j, |μ j| * C j) ≤ ∑ j, μ j * ∑ s, e j s * L n s := by
      filter_upwards [eventually_all.mpr hC] with n hn
      rw [← sum_neg_distrib]
      refine sum_le_sum fun j _ => ?_
      have := hn j
      have h1 := abs_le.mp this
      have hCj : 0 ≤ C j := (abs_nonneg _).trans this
      rcases le_or_gt 0 (μ j) with hμj | hμj
      · rw [abs_of_nonneg hμj]; nlinarith
      · rw [abs_of_neg hμj]; nlinarith
    obtain ⟨k₀, hk₀⟩ : ∃ k, 0 < c k := by
      by_contra hall; push Not at hall
      exact absurd (sum_nonpos fun k _ => hall k) (not_le.mpr hcpos)
    have hlim : Tendsto (fun n => ∑ k, c k * ∑ s, d k s * L n s) atTop atBot := by
      have hmain : Tendsto (fun n => c k₀ * ∑ s, d k₀ s * L n s) atTop atBot :=
        (hd k₀).const_mul_atBot hk₀
      refine tendsto_atBot_mono' atTop ?_ hmain
      have hev : ∀ᶠ n in atTop, ∀ k, ∑ s, d k s * L n s ≤ 0 :=
        eventually_all.mpr fun k => (hd k).eventually (eventually_le_atBot 0)
      filter_upwards [hev] with n hn
      rw [← add_sum_erase _ _ (mem_univ k₀)]
      have : ∑ k ∈ univ.erase k₀, c k * ∑ s, d k s * L n s ≤ 0 :=
        sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hcnn k) (hn k)
      linarith
    obtain ⟨n, hn1, hn2⟩ := ((hlim.eventually (eventually_lt_atBot (-(∑ j, |μ j| * C j)))).and
      hbound).exists
    rw [hμL] at hn1
    linarith
  -- step 2: normalize
  obtain ⟨w, hwV, hwneg⟩ := hstrict
  have hwe : ∀ j, ∑ s, e j s * w s = 0 := by
    intro j
    have := (Submodule.mem_iInf _).mp hwV j
    simpa [ψ] using this
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨w, hwe, fun k => (hK.false k).elim⟩
  set m := univ.sup' univ_nonempty (fun k => A w k) with hm
  obtain ⟨k₁, -, hk₁⟩ := univ.exists_mem_eq_sup' univ_nonempty (fun k => A w k)
  have hmneg : m < 0 := by rw [hm, hk₁]; exact hwneg k₁
  refine ⟨(-1 / m) • w, fun j => ?_, fun k => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ s, e j s * (-1 / m * w s) = -1 / m * ∑ s, e j s * w s by
      rw [mul_sum]; exact sum_congr rfl fun s _ => by ring, hwe j, mul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ s, d k s * (-1 / m * w s) = -1 / m * A w k by
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, mul_sum]; exact sum_congr rfl fun s _ => by ring]
    have hle : A w k ≤ m := univ.le_sup' (fun k => A w k) (mem_univ k)
    have hpos : 0 < -1 / m := div_pos_of_neg_of_neg (by norm_num) hmneg
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rw [div_mul_cancel₀ _ hmneg.ne] at this
    linarith

namespace Network

open RationalFarkas

/-- The log of a monomial ratio at a positive state. -/
theorem log_tierMonomial_div {x : Concentration S} (hx : x.Positive) (y y' : Complex S) :
    Real.log (tierMonomial x y / tierMonomial x y') =
      ∑ s, ((y s : ℝ) - y' s) * Real.log (x s) := by
  have hpos : ∀ c : Complex S, 0 < tierMonomial x c := fun c =>
    prod_pos fun s _ => pow_pos (hx s) _
  rw [Real.log_div (hpos y).ne' (hpos y').ne', tierMonomial, tierMonomial,
    Real.log_prod (fun s _ => (pow_pos (hx s) _).ne'),
    Real.log_prod (fun s _ => (pow_pos (hx s) _).ne'), ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [Real.log_pow, Real.log_pow]; ring

/-- **Every positive sequence makes its tier-direction system feasible.** -/
theorem tierDirectionSystemFeasible_of_positiveSequence (N : Network S)
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs) : N.TierDirectionSystemFeasible xs := by
  classical
  set P := N.complexes ×ˢ N.complexes
  let K := {p // p ∈ P.filter fun p => TierStrictBelow xs p.1 p.2}
  let J := {p // p ∈ P.filter fun p => TierSame xs p.1 p.2}
  letI : Fintype K := Finset.fintypeCoeSort _
  letI : Fintype J := Finset.fintypeCoeSort _
  let dK : K → S → ℝ := fun p s => ((p.1.1 s : ℝ) - p.1.2 s)
  let eJ : J → S → ℝ := fun p s => ((p.1.1 s : ℝ) - p.1.2 s)
  let L : ℕ → S → ℝ := fun n s => Real.log (xs n s)
  have hratio_pos : ∀ n (y y' : Complex S), 0 < tierMonomial (xs n) y / tierMonomial (xs n) y' :=
    fun n y y' => div_pos (prod_pos fun s _ => pow_pos (hpos n s) _)
      (prod_pos fun s _ => pow_pos (hpos n s) _)
  have hlog : ∀ n (y y' : Complex S), ∑ s, ((y s : ℝ) - y' s) * L n s =
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') :=
    fun n y y' => (log_tierMonomial_div (hpos n) y y').symm
  obtain ⟨w, hwe, hwd⟩ := exists_direction_of_sequence dK eJ L
    (fun p => by
      have hb : TierStrictBelow xs p.1.1 p.1.2 := (mem_filter.mp p.2).2
      have h0 : Tendsto (fun n => tierMonomial (xs n) p.1.1 / tierMonomial (xs n) p.1.2) atTop
          (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hb, Eventually.of_forall fun n =>
            hratio_pos n _ _⟩
      have := Real.tendsto_log_nhdsGT_zero.comp h0
      simpa [dK, hlog, Function.comp_def] using this)
    (fun p => by
      obtain ⟨c, hc, hlim⟩ := (mem_filter.mp p.2).2
      have hl := ((Real.continuousAt_log hc.ne').tendsto).comp hlim
      refine ⟨|Real.log c| + 1, ?_⟩
      filter_upwards [hl.eventually (Metric.ball_mem_nhds _ one_pos)] with n hn
      have hn' : |Real.log (tierMonomial (xs n) p.1.1 / tierMonomial (xs n) p.1.2) -
          Real.log c| < 1 := by simpa [Real.dist_eq] using hn
      simp only [eJ, hlog]
      have := abs_sub_abs_le_abs_sub (Real.log (tierMonomial (xs n) p.1.1 /
        tierMonomial (xs n) p.1.2)) (Real.log c)
      linarith)
  set eq := Fintype.equivFin S
  refine ⟨fun i => w (eq.symm i), fun I hI => ?_⟩
  simp only [tierDirectionSystem, List.mem_flatMap, Finset.mem_toList, Prod.exists] at hI
  obtain ⟨y, y', hyy', hI⟩ := hI
  have hval : ∀ c : Complex S, complexWValue (fun s => (fun i => w (eq.symm i)) (eq s)) c =
      ∑ s, w s * (c s : ℝ) := fun c => by
    simp [complexWValue, dotProduct, exponentVector]
  have hdiff : complexWValue (fun s => (fun i => w (eq.symm i)) (eq s)) y -
      complexWValue (fun s => (fun i => w (eq.symm i)) (eq s)) y' =
        ∑ s, ((y s : ℝ) - y' s) * w s := by
    rw [hval, hval, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
  have hdiff' : complexWValue (fun s => (fun i => w (eq.symm i)) (eq s)) y' -
      complexWValue (fun s => (fun i => w (eq.symm i)) (eq s)) y =
        -∑ s, ((y s : ℝ) - y' s) * w s := by rw [← hdiff]; ring
  unfold tierComparisonRows at hI
  by_cases hsame : TierSame xs y y'
  · rw [dif_pos hsame] at hI
    have h0 := hwe ⟨(y, y'), mem_filter.mpr ⟨hyy', hsame⟩⟩
    simp only [eJ] at h0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · rw [Ineq.holdsℝ, lhsℝ_tierDiffRow, hdiff, h0]; simp
    · rw [Ineq.holdsℝ, lhsℝ_tierDiffRow, hdiff', h0]; simp
  · rw [dif_neg hsame] at hI
    by_cases hbelow : TierStrictBelow xs y y'
    · rw [dif_pos hbelow] at hI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
      subst hI
      have h1 := hwd ⟨(y, y'), mem_filter.mpr ⟨hyy', hbelow⟩⟩
      simp only [dK] at h1
      rw [Ineq.holdsℝ, lhsℝ_tierDiffRow, hdiff]
      simp only [encodeRow]; push_cast; linarith
    · rw [dif_neg hbelow] at hI
      simp at hI

/-- **The tier-direction feasibility claim holds.** -/
theorem everyTransversalTierDirectionSystemFeasible (N : Network S) :
    N.EveryTransversalTierDirectionSystemFeasible :=
  fun _ htrans => N.tierDirectionSystemFeasible_of_positiveSequence htrans.1.1

end Network

end CRNT
