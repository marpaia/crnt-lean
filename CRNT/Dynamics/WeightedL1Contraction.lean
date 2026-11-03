import CRNT.Dynamics.EuclideanContraction
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Contraction in a weighted `ℓ¹` norm (column logarithmic norm)

For positive weights `w`, the weighted `ℓ¹` logarithmic norm of a matrix `J` is
`μ_{1,w}(J) = max_j (J_jj + ∑_{i ≠ j} (w_i / w_j) |J_ij|)`.  If on a convex set `C` the Jacobian of
a vector field satisfies `w_j J_jj(x) + ∑_{i ≠ j} w_i |J_ij(x)| ≤ −c w_j` for every column `j`, then
any two solutions staying in `C` approach each other exponentially in the weighted `ℓ¹` distance
`∑ w_i |x_i − y_i|` (`l1_contraction_of_jacobian`; mass action: `massAction_l1_contraction`).  Row version: if
`J_ii + ∑_{j ≠ i} (v_i/v_j) |J_ij| ≤ −c` for every row, the weighted `ℓ^∞` distance
`max_i v_i |x_i − y_i|` contracts at rate `c` (`linf_contraction_of_jacobian`,
`massAction_linf_contraction`); the right Dini derivative of the maximum is controlled by the
active coordinates (`oneSided_linf_of_jacobian`), the inactive ones staying below by continuity.

Proof: for signs `σ` with `|σ_i| ≤ 1` and `σ_j u_j = |u_j|`, the column condition gives
`∑ w_i σ_i (J u)_i ≤ −c ∑ w_j |u_j|` (`sum_weighted_sign_le`); integrating along the segment
(antitone-function argument) gives the one-sided bound `∑ w_i σ_i (f a − f b)_i ≤ −c ∑ w_i |a_i −
b_i|` (`oneSided_l1_of_jacobian`).  The weighted distance along two solutions has, at every time,
a right derivative of the form `∑ w_i σ_i (f(x) − f(y))_i` (`hasDerivWithinAt_abs_Ici`), so
Grönwall's inequality for right Dini derivatives applies.

The weighted `ℓ¹` criterion is not implied by the Euclidean one: for `0 → X → Y → 0` with rates
`1, 8, 1` the Jacobian is `[[−8, 0], [8, −1]]`; the Euclidean criterion fails (`⟨u, J u⟩ > 0` for
`u = (1, 4)`), while the weighted `ℓ¹` criterion holds with weights `(1, 1/2)` and rate `1`
(`CRNT.Examples.L1Contraction`).

Nothing here is an axiom or a `sorry`.
-/

open Set Filter Topology Finset

namespace CRNT
namespace Network

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The weighted `ℓ¹` distance. -/
noncomputable def wl1Dist (w x y : S → ℝ) : ℝ := ∑ s, w s * |x s - y s|

/-- The column condition bounds the weighted signed sum of `J u`. -/
theorem sum_weighted_sign_le (J : (S → ℝ) →L[ℝ] (S → ℝ)) {w : S → ℝ} (hw : ∀ s, 0 < w s) {c : ℝ}
    (hcol : ∀ j, w j * J (Pi.single j 1) j + ∑ i ∈ univ.erase j, w i * |J (Pi.single j 1) i| ≤
      -c * w j)
    (u σ : S → ℝ) (hσ : ∀ i, |σ i| ≤ 1) (hσu : ∀ j, σ j * u j = |u j|) :
    ∑ i, w i * σ i * J u i ≤ -c * ∑ j, w j * |u j| := by
  have hJu : ∀ i, J u i = ∑ j, u j * J (Pi.single j 1) i := by
    intro i
    have hu : u = ∑ j, u j • (Pi.single j 1 : S → ℝ) := by
      funext s; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hu]
    simp [map_sum, map_smul, Finset.sum_apply]
  have hexp : ∑ i, w i * σ i * J u i = ∑ j, ∑ i, w i * σ i * (u j * J (Pi.single j 1) i) := by
    simp only [hJu, mul_sum]
    rw [sum_comm]
  rw [hexp, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [← add_sum_erase _ _ (mem_univ j)]
  have hdiag : w j * σ j * (u j * J (Pi.single j 1) j) = |u j| * (w j * J (Pi.single j 1) j) := by
    rw [← hσu j]; ring
  have hoff : ∀ i ∈ univ.erase j, w i * σ i * (u j * J (Pi.single j 1) i) ≤
      |u j| * (w i * |J (Pi.single j 1) i|) := by
    intro i _
    have h1 : w i * σ i * (u j * J (Pi.single j 1) i) ≤
        |w i * σ i * (u j * J (Pi.single j 1) i)| := le_abs_self _
    have h2 : |w i * σ i * (u j * J (Pi.single j 1) i)| =
        w i * |σ i| * (|u j| * |J (Pi.single j 1) i|) := by
      simp only [abs_mul, abs_of_pos (hw i)]
    have h3 : w i * |σ i| * (|u j| * |J (Pi.single j 1) i|) ≤
        w i * 1 * (|u j| * |J (Pi.single j 1) i|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hσ i) (hw i).le)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    nlinarith
  have hsum := sum_le_sum hoff
  rw [← mul_sum] at hsum
  have hcolj := mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg (u j))
  rw [hdiag]
  nlinarith

/-- **One-sided bound in the weighted `ℓ¹` norm from the Jacobian.** -/
theorem oneSided_l1_of_jacobian {f : (S → ℝ) → (S → ℝ)} {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x)
    {w : S → ℝ} (hw : ∀ s, 0 < w s) {c : ℝ}
    (hcol : ∀ x ∈ C, ∀ j, w j * J x (Pi.single j 1) j +
      ∑ i ∈ univ.erase j, w i * |J x (Pi.single j 1) i| ≤ -c * w j)
    {a b : S → ℝ} (ha : a ∈ C) (hb : b ∈ C) (σ : S → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (hσu : ∀ j, σ j * (a j - b j) = |a j - b j|) :
    ∑ i, w i * σ i * (f a i - f b i) ≤ -c * wl1Dist w a b := by
  set u : S → ℝ := a - b
  set z : ℝ → (S → ℝ) := fun τ => b + τ • u
  have hz : ∀ τ ∈ Icc (0 : ℝ) 1, z τ ∈ C := by
    intro τ hτ
    have : z τ = (1 - τ) • b + τ • a := by
      funext s; simp [z, u]; ring
    rw [this]
    exact hC hb ha (by linarith [hτ.2]) hτ.1 (by ring)
  set g : ℝ → ℝ := fun τ => ∑ s, w s * σ s * f (z τ) s
  have hzd : ∀ τ, HasDerivAt z u τ := by
    intro τ
    have := ((hasDerivAt_id τ).smul_const u).const_add b
    simpa [z] using this
  have hgd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (∑ s, w s * σ s * J (z τ) u s) τ := by
    intro τ hτ
    have hcomp : HasDerivAt (fun τ => f (z τ)) (J (z τ) u) τ :=
      (hf (z τ) (hz τ hτ)).comp_hasDerivAt τ (hzd τ)
    have := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
      ((hasDerivAt_pi.mp hcomp) s).const_mul (w s * σ s)
    simpa [g] using this
  have hσu' : ∀ j, σ j * u j = |u j| := fun j => by simpa [u] using hσu j
  set D : ℝ := ∑ s, w s * |u s| with hD
  set W : ℝ → ℝ := fun τ => g τ + c * D * τ
  have hWanti : AntitoneOn W (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ hτ => ?_) (fun τ hτ => ?_) (fun τ hτ => ?_)
      (f' := fun τ => ∑ s, w s * σ s * J (z τ) u s + c * D * 1)
    · exact ((hgd τ hτ).add ((hasDerivAt_id τ).const_mul _)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at hτ
      exact ((hgd τ (Ioo_subset_Icc_self hτ)).add
        ((hasDerivAt_id τ).const_mul _)).hasDerivWithinAt
    · rw [interior_Icc] at hτ
      have := sum_weighted_sign_le (J (z τ)) hw (hcol (z τ) (hz τ (Ioo_subset_Icc_self hτ)))
        u σ hσ hσu'
      simp only [hD]
      linarith
  have h01 := hWanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [W, g, mul_zero, add_zero, mul_one] at h01
  have hz0 : z 0 = b := by simp [z]
  have hz1 : z 1 = a := by funext s; simp [z, u]
  rw [hz0, hz1] at h01
  have hsum : ∑ i, w i * σ i * (f a i - f b i) =
      ∑ s, w s * σ s * f a s - ∑ s, w s * σ s * f b s := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum]
  have hsd : wl1Dist w a b = D := by simp [wl1Dist, hD, u]
  rw [hsd]
  linarith

/-- The absolute value of a differentiable function has a right derivative `σ · h'` with
`|σ| ≤ 1` and `σ · h = |h|`. -/
theorem hasDerivWithinAt_abs_Ici {h : ℝ → ℝ} {d t : ℝ} (hd : HasDerivAt h d t) :
    ∃ σ : ℝ, |σ| ≤ 1 ∧ σ * h t = |h t| ∧
      HasDerivWithinAt (fun s => |h s|) (σ * d) (Ici t) t := by
  rcases lt_trichotomy (h t) 0 with hneg | hzero | hpos
  · refine ⟨-1, by norm_num, by rw [abs_of_neg hneg]; ring, ?_⟩
    have heq : (fun s => |h s|) =ᶠ[𝓝 t] fun s => -h s := by
      filter_upwards [hd.continuousAt.eventually (gt_mem_nhds hneg)] with s hs
      exact abs_of_neg hs
    have := (hd.neg.congr_of_eventuallyEq heq).hasDerivWithinAt (s := Ici t)
    simpa using this
  · refine ⟨if 0 ≤ d then 1 else -1, by split_ifs <;> norm_num, by rw [hzero]; simp, ?_⟩
    have hσd : (if 0 ≤ d then (1:ℝ) else -1) * d = |d| := by
      split_ifs with h0
      · rw [one_mul, abs_of_nonneg h0]
      · push Not at h0; rw [abs_of_neg h0]; ring
    rw [hσd, hasDerivWithinAt_iff_tendsto_slope]
    have hs := (hasDerivWithinAt_iff_tendsto_slope.mp (hd.hasDerivWithinAt (s := Ici t)))
    have habs := (continuous_abs.tendsto d).comp hs
    refine habs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hsm
    have hst : t < s := lt_of_le_of_ne hsm.1 (Ne.symm hsm.2)
    simp only [Function.comp_apply, slope_def_field, hzero, abs_zero, sub_zero]
    rw [abs_div, abs_of_pos (sub_pos.mpr hst)]
  · refine ⟨1, by norm_num, by rw [abs_of_pos hpos]; ring, ?_⟩
    have heq : (fun s => |h s|) =ᶠ[𝓝 t] h := by
      filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hpos)] with s hs
      exact abs_of_pos hs
    have := (hd.congr_of_eventuallyEq heq).hasDerivWithinAt (s := Ici t)
    simpa using this

/-- **Exponential contraction in the weighted `ℓ¹` distance.** -/
theorem l1_contraction_of_jacobian {f : (S → ℝ) → (S → ℝ)}
    {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x)
    {w : S → ℝ} (hw : ∀ s, 0 < w s) {c : ℝ}
    (hcol : ∀ x ∈ C, ∀ j, w j * J x (Pi.single j 1) j +
      ∑ i ∈ univ.erase j, w i * |J x (Pi.single j 1) i| ≤ -c * w j)
    {x y : ℝ → (S → ℝ)} (hx : ∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → wl1Dist w (x t) (y t) ≤ Real.exp (-c * t) * wl1Dist w (x 0) (y 0) := by
  classical
  have hcomp : ∀ s t, 0 ≤ t → HasDerivAt (fun τ => x τ s - y τ s) (f (x t) s - f (y t) s) t :=
    fun s t ht => ((hasDerivAt_pi.mp (hx t ht)) s).sub ((hasDerivAt_pi.mp (hy t ht)) s)
  have hch : ∀ s t, 0 ≤ t → ∃ σ : ℝ, |σ| ≤ 1 ∧ σ * (x t s - y t s) = |x t s - y t s| ∧
      HasDerivWithinAt (fun τ => |x τ s - y τ s|) (σ * (f (x t) s - f (y t) s)) (Ici t) t :=
    fun s t ht => hasDerivWithinAt_abs_Ici (hcomp s t ht)
  choose σ hσ1 hσu hσd using hch
  set F : ℝ → ℝ := fun t => wl1Dist w (x t) (y t) with hF
  set F' : ℝ → ℝ := fun t => if ht : 0 ≤ t then
    ∑ s, w s * (σ s t ht * (f (x t) s - f (y t) s)) else 0 with hF'
  have hFd : ∀ t (ht : 0 ≤ t), HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    have := HasDerivWithinAt.fun_sum (u := Finset.univ) fun s _ => (hσd s t ht).const_mul (w s)
    simp only [hF', dif_pos ht]
    simpa [hF, wl1Dist] using this
  have hbound : ∀ t (ht : 0 ≤ t), F' t ≤ -c * F t := by
    intro t ht
    simp only [hF', dif_pos ht]
    have := oneSided_l1_of_jacobian hC hf hw hcol (hxC t ht) (hyC t ht) (fun s => σ s t ht)
      (fun s => hσ1 s t ht) (fun s => hσu s t ht)
    have e : ∑ s, w s * (σ s t ht * (f (x t) s - f (y t) s)) =
        ∑ i, w i * σ i t ht * (f (x t) i - f (y t) i) :=
      Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    exact this
  intro t ht
  have hcont : ContinuousOn F (Icc 0 (t + 1)) := by
    intro τ hτ
    have : ContinuousAt F τ := by
      have hc : ∀ s, ContinuousAt (fun τ => |x τ s - y τ s|) τ := fun s =>
        continuous_abs.continuousAt.comp (hcomp s τ hτ.1).continuousAt
      have : ContinuousAt (fun τ => ∑ s, w s * |x τ s - y τ s|) τ := by
        unfold ContinuousAt
        exact tendsto_finsetSum _ fun s _ => (continuousAt_const.mul (hc s))
      simpa [hF, wl1Dist] using this
    exact this.continuousWithinAt
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := F') (δ := F 0)
    (K := -c) (ε := 0) (a := 0) (b := t + 1) hcont
    (by
      intro τ hτ r hr
      have hs := hasDerivWithinAt_iff_tendsto_slope.mp (hFd τ hτ.1)
      have hev : ∀ᶠ z in 𝓝[Ici τ \ {τ}] τ, slope F τ z < r := hs.eventually (gt_mem_nhds hr)
      have hset : Ici τ \ {τ} = Ioi τ := by
        ext z; simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
        constructor
        · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
        · intro h; exact ⟨h.le, ne_of_gt h⟩
      rw [hset] at hev
      refine (hev.mono fun z hz => ?_).frequently
      simpa [slope_def_field, div_eq_inv_mul] using hz)
    le_rfl
    (by
      intro τ hτ
      have := hbound τ hτ.1
      linarith)
    t ⟨ht, by linarith⟩
  rw [gronwallBound_ε0, sub_zero] at hG
  simp only [hF] at hG
  linarith [mul_comm (wl1Dist w (x 0) (y 0)) (Real.exp (-c * t))]

/-- The weighted `ℓ^∞` distance `max_i v_i |x_i − y_i|`. -/
noncomputable def wlinfDist [Nonempty S] (v x y : S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => v i * |x i - y i|

/-- **One-sided bound for a maximal row.** If row `i` of the Jacobian satisfies
`J_ii + ∑_{j ≠ i} (v_i/v_j) |J_ij| ≤ −c` on `C`, and `v_i |u_i|` is maximal among the
`v_j |u_j|` (`u = a − b`), then `v_i σ (f a − f b)_i ≤ −c v_i |u_i|` for `σ u_i = |u_i|`,
`|σ| ≤ 1`. -/
theorem oneSided_linf_of_jacobian {f : (S → ℝ) → (S → ℝ)}
    {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x)
    {v : S → ℝ} (hv : ∀ s, 0 < v s) {c : ℝ}
    (hrow : ∀ x ∈ C, ∀ i, J x (Pi.single i 1) i +
      ∑ j ∈ univ.erase i, v i / v j * |J x (Pi.single j 1) i| ≤ -c)
    {a b : S → ℝ} (ha : a ∈ C) (hb : b ∈ C) (i : S)
    (hmax : ∀ j, v j * |a j - b j| ≤ v i * |a i - b i|) (σ : ℝ) (hσ : |σ| ≤ 1)
    (hσu : σ * (a i - b i) = |a i - b i|) :
    v i * σ * (f a i - f b i) ≤ -c * (v i * |a i - b i|) := by
  set u : S → ℝ := a - b
  set z : ℝ → (S → ℝ) := fun τ => b + τ • u
  have hz : ∀ τ ∈ Icc (0 : ℝ) 1, z τ ∈ C := by
    intro τ hτ
    have : z τ = (1 - τ) • b + τ • a := by
      funext s; simp [z, u]; ring
    rw [this]
    exact hC hb ha (by linarith [hτ.2]) hτ.1 (by ring)
  set g : ℝ → ℝ := fun τ => v i * σ * f (z τ) i
  have hzd : ∀ τ, HasDerivAt z u τ := by
    intro τ
    have := ((hasDerivAt_id τ).smul_const u).const_add b
    simpa [z] using this
  have hgd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (v i * σ * J (z τ) u i) τ := by
    intro τ hτ
    have hcomp : HasDerivAt (fun τ => f (z τ)) (J (z τ) u) τ :=
      (hf (z τ) (hz τ hτ)).comp_hasDerivAt τ (hzd τ)
    exact ((hasDerivAt_pi.mp hcomp) i).const_mul (v i * σ)
  have hJu : ∀ (A : (S → ℝ) →L[ℝ] (S → ℝ)) k, A u k = ∑ j, u j * A (Pi.single j 1) k := by
    intro A k
    have hu : u = ∑ j, u j • (Pi.single j 1 : S → ℝ) := by
      funext s; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hu]
    simp [map_sum, map_smul, Finset.sum_apply]
  have hσu' : σ * u i = |u i| := by simpa [u] using hσu
  have hmax' : ∀ j, v j * |u j| ≤ v i * |u i| := fun j => by simpa [u] using hmax j
  -- the pointwise bound
  have hpt : ∀ τ ∈ Icc (0 : ℝ) 1, v i * σ * J (z τ) u i ≤ -c * (v i * |u i|) := by
    intro τ hτ
    set A := J (z τ)
    rw [hJu A i, mul_sum, ← add_sum_erase _ _ (mem_univ i)]
    have hdiag : v i * σ * (u i * A (Pi.single i 1) i) = v i * |u i| * A (Pi.single i 1) i := by
      rw [← hσu']; ring
    have hoff : ∀ j ∈ univ.erase i, v i * σ * (u j * A (Pi.single j 1) i) ≤
        v i * |u i| * (v i / v j * |A (Pi.single j 1) i|) := by
      intro j _
      have h1 : v i * σ * (u j * A (Pi.single j 1) i) ≤
          |v i * σ * (u j * A (Pi.single j 1) i)| := le_abs_self _
      have h2 : |v i * σ * (u j * A (Pi.single j 1) i)| =
          v i * |σ| * (|u j| * |A (Pi.single j 1) i|) := by
        simp only [abs_mul, abs_of_pos (hv i)]
      have h3 : v i * |σ| * (|u j| * |A (Pi.single j 1) i|) ≤
          v i * 1 * (|u j| * |A (Pi.single j 1) i|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ (hv i).le)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have h4 : |u j| ≤ v i * |u i| / v j := by
        rw [le_div_iff₀ (hv j)]; linarith [hmax' j]
      have h5 : v i * 1 * (|u j| * |A (Pi.single j 1) i|) ≤
          v i * (v i * |u i| / v j * |A (Pi.single j 1) i|) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h4 (abs_nonneg _)) (hv i).le
      have e : v i * (v i * |u i| / v j * |A (Pi.single j 1) i|) =
          v i * |u i| * (v i / v j * |A (Pi.single j 1) i|) := by
        field_simp
      linarith
    have hsum : ∑ j ∈ univ.erase i, v i * σ * (u j * A (Pi.single j 1) i) ≤
        v i * |u i| * ∑ j ∈ univ.erase i, v i / v j * |A (Pi.single j 1) i| := by
      rw [mul_sum]; exact sum_le_sum hoff
    have hrowi : v i * |u i| * (A (Pi.single i 1) i +
        ∑ j ∈ univ.erase i, v i / v j * |A (Pi.single j 1) i|) ≤ v i * |u i| * -c :=
      mul_le_mul_of_nonneg_left (hrow (z τ) (hz τ hτ) i)
        (mul_nonneg (hv i).le (abs_nonneg (u i)))
    rw [mul_add] at hrowi
    rw [hdiag]
    linarith
  set D : ℝ := v i * |u i| with hD
  set W : ℝ → ℝ := fun τ => g τ + c * D * τ
  have hWanti : AntitoneOn W (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ hτ => ?_) (fun τ hτ => ?_) (fun τ hτ => ?_)
      (f' := fun τ => v i * σ * J (z τ) u i + c * D * 1)
    · exact ((hgd τ hτ).add ((hasDerivAt_id τ).const_mul _)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at hτ
      exact ((hgd τ (Ioo_subset_Icc_self hτ)).add
        ((hasDerivAt_id τ).const_mul _)).hasDerivWithinAt
    · rw [interior_Icc] at hτ
      have := hpt τ (Ioo_subset_Icc_self hτ)
      simp only [hD]
      linarith
  have h01 := hWanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [W, g, mul_zero, add_zero, mul_one] at h01
  have hz0 : z 0 = b := by simp [z]
  have hz1 : z 1 = a := by funext s; simp [z, u]
  rw [hz0, hz1] at h01
  have : v i * σ * (f a i - f b i) = v i * σ * f a i - v i * σ * f b i := by ring
  rw [this]
  have hDe : D = v i * |a i - b i| := by simp [hD, u]
  rw [← hDe]
  linarith

/-- **Exponential contraction in the weighted `ℓ^∞` distance** under the row condition
`J_ii + ∑_{j ≠ i} (v_i/v_j) |J_ij| ≤ −c`. -/
theorem linf_contraction_of_jacobian [Nonempty S] {f : (S → ℝ) → (S → ℝ)}
    {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x)
    {v : S → ℝ} (hv : ∀ s, 0 < v s) {c : ℝ}
    (hrow : ∀ x ∈ C, ∀ i, J x (Pi.single i 1) i +
      ∑ j ∈ univ.erase i, v i / v j * |J x (Pi.single j 1) i| ≤ -c)
    {x y : ℝ → (S → ℝ)} (hx : ∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → wlinfDist v (x t) (y t) ≤ Real.exp (-c * t) * wlinfDist v (x 0) (y 0) := by
  classical
  have hcomp : ∀ s t, 0 ≤ t → HasDerivAt (fun τ => x τ s - y τ s) (f (x t) s - f (y t) s) t :=
    fun s t ht => ((hasDerivAt_pi.mp (hx t ht)) s).sub ((hasDerivAt_pi.mp (hy t ht)) s)
  have hch : ∀ s t, 0 ≤ t → ∃ σ : ℝ, |σ| ≤ 1 ∧ σ * (x t s - y t s) = |x t s - y t s| ∧
      HasDerivWithinAt (fun τ => |x τ s - y τ s|) (σ * (f (x t) s - f (y t) s)) (Ici t) t :=
    fun s t ht => hasDerivWithinAt_abs_Ici (hcomp s t ht)
  choose σ hσ1 hσu hσd using hch
  set g : S → ℝ → ℝ := fun i τ => v i * |x τ i - y τ i| with hg
  set F : ℝ → ℝ := fun t => wlinfDist v (x t) (y t) with hF
  have hFg : ∀ t, F t = Finset.univ.sup' Finset.univ_nonempty fun i => g i t := fun t => rfl
  have hgc : ∀ i τ, 0 ≤ τ → ContinuousAt (g i) τ := fun i τ hτ =>
    continuousAt_const.mul (continuous_abs.continuousAt.comp (hcomp i τ hτ).continuousAt)
  intro t ht
  have hcont : ContinuousOn F (Icc 0 (t + 1)) := by
    intro τ hτ
    have : ContinuousAt F τ := by
      have := ContinuousAt.finset_sup'_apply (s := Finset.univ) (f := g) Finset.univ_nonempty
        fun i _ => hgc i τ hτ.1
      exact this
    exact this.continuousWithinAt
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := F) (f' := fun τ => -c * F τ)
    (δ := F 0) (K := -c) (ε := 0) (a := 0) (b := t + 1) hcont
    (by
      intro τ hτ r hr
      have hτ0 := hτ.1
      -- every coordinate is eventually below the line `F τ + r (s − τ)`
      have hev : ∀ i, ∀ᶠ s in 𝓝[>] τ, g i s < F τ + r * (s - τ) := by
        intro i
        by_cases hact : g i τ = F τ
        · -- an active coordinate: its right derivative is at most `-c F τ < r`
          have hmax : ∀ j, v j * |x τ j - y τ j| ≤ v i * |x τ i - y τ i| := by
            intro j
            have := Finset.le_sup' (fun k => g k τ) (Finset.mem_univ j)
            simp only [hg] at this hact
            rw [hact]
            exact this
          have hd := oneSided_linf_of_jacobian hC hf hv hrow (hxC τ hτ0) (hyC τ hτ0) i hmax
            (σ i τ hτ0) (hσ1 i τ hτ0) (hσu i τ hτ0)
          have hgd : HasDerivWithinAt (g i) (v i * (σ i τ hτ0 * (f (x τ) i - f (y τ) i)))
              (Ici τ) τ := (hσd i τ hτ0).const_mul (v i)
          have hdlt : v i * (σ i τ hτ0 * (f (x τ) i - f (y τ) i)) < r := by
            have e : v i * (σ i τ hτ0 * (f (x τ) i - f (y τ) i)) =
                v i * σ i τ hτ0 * (f (x τ) i - f (y τ) i) := by ring
            rw [e]
            have : -c * (v i * |x τ i - y τ i|) = -c * F τ := by
              rw [← hact]
            linarith
          have hs := hasDerivWithinAt_iff_tendsto_slope.mp hgd
          have hset : Ici τ \ {τ} = Ioi τ := by
            ext z; simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
            constructor
            · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
            · intro h; exact ⟨h.le, ne_of_gt h⟩
          rw [hset] at hs
          filter_upwards [hs.eventually (gt_mem_nhds hdlt), self_mem_nhdsWithin] with s hs1 hs2
          have hst : 0 < s - τ := sub_pos.mpr hs2
          rw [slope_def_field] at hs1
          rw [div_lt_iff₀ hst] at hs1
          linarith
        · -- an inactive coordinate stays below by continuity
          have hlt : g i τ < F τ := lt_of_le_of_ne
            (Finset.le_sup' (fun k => g k τ) (Finset.mem_univ i)) hact
          have hc : Tendsto (fun s => F τ + r * (s - τ) - g i s) (𝓝 τ)
              (𝓝 (F τ + r * (τ - τ) - g i τ)) :=
            ((continuousAt_const.add (continuousAt_const.mul
              (continuousAt_id.sub continuousAt_const))).sub (hgc i τ hτ0)).tendsto
          have hpos : 0 < F τ + r * (τ - τ) - g i τ := by simp; linarith
          filter_upwards [nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds hpos))] with s hs
          linarith
      have hall := (eventually_all.mpr hev)
      refine (hall.and self_mem_nhdsWithin).mono (fun s hs => ?_) |>.frequently
      obtain ⟨hs1, hs2⟩ := hs
      have hst : 0 < s - τ := sub_pos.mpr hs2
      have hFs : F s < F τ + r * (s - τ) := by
        rw [hFg s]
        exact (Finset.sup'_lt_iff _).mpr fun i _ => hs1 i
      rw [inv_mul_lt_iff₀ hst]
      linarith)
    le_rfl
    (by intro τ _; linarith)
    t ⟨ht, by linarith⟩
  rw [gronwallBound_ε0, sub_zero] at hG
  simp only [hF] at hG
  linarith [mul_comm (wlinfDist v (x 0) (y 0)) (Real.exp (-c * t))]

/-- **Mass-action systems: exponential contraction in a weighted `ℓ¹` distance** under the
column condition on the mass-action Jacobian. -/
theorem massAction_l1_contraction (N : Network S) (κ : N.RateConstants)
    {C : Set (Concentration S)} (hC : Convex ℝ C) {w : S → ℝ} (hw : ∀ s, 0 < w s) {c : ℝ}
    (hcol : ∀ x ∈ C, ∀ j, w j * N.massActionJacobianCLM κ x (Pi.single j 1) j +
      ∑ i ∈ univ.erase j, w i * |N.massActionJacobianCLM κ x (Pi.single j 1) i| ≤ -c * w j)
    {x y : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (N.massActionVectorField κ (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → wl1Dist w (x t) (y t) ≤ Real.exp (-c * t) * wl1Dist w (x 0) (y 0) :=
  l1_contraction_of_jacobian hC (fun x _ => N.massActionVectorField_hasFDerivAt κ x) hw hcol
    hx hy hxC hyC

/-- **Mass-action systems: exponential contraction in a weighted `ℓ^∞` distance** under the
row condition on the mass-action Jacobian. -/
theorem massAction_linf_contraction [Nonempty S] (N : Network S) (κ : N.RateConstants)
    {C : Set (Concentration S)} (hC : Convex ℝ C) {v : S → ℝ} (hv : ∀ s, 0 < v s) {c : ℝ}
    (hrow : ∀ x ∈ C, ∀ i, N.massActionJacobianCLM κ x (Pi.single i 1) i +
      ∑ j ∈ univ.erase i, v i / v j * |N.massActionJacobianCLM κ x (Pi.single j 1) i| ≤ -c)
    {x y : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (N.massActionVectorField κ (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → wlinfDist v (x t) (y t) ≤ Real.exp (-c * t) * wlinfDist v (x 0) (y 0) :=
  linf_contraction_of_jacobian hC (fun x _ => N.massActionVectorField_hasFDerivAt κ x) hv hrow
    hx hy hxC hyC

end Network
end CRNT
