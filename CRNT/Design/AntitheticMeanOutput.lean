import CRNT.Design.AntitheticErgodic
import CRNT.Stochastic.MinimalSemigroupMoments

/-!
# Convergence of the mean output of the antithetic closed loop

For the antithetic integral controller closed around a production–degradation plant, the mean
output converges to the setpoint from every initial count, for every choice of positive rates:
`E_n[X(t)] → μ/θ` (`closedLoop_mean_output_tendsto`).

The ergodicity Lyapunov function `V` of `AntitheticErgodic` has only a linear drift in the region
`q = z₁ − z₂ < 0`. The function

`W = V` (`z₂ ≤ z₁`),  `W = b x² + d z₁²` (`z₁ < z₂`)

satisfies `W ≤ V` everywhere (`wLyap_le_lyap`), so on `z₂ ≤ z₁` its drift is at most that of `V`,
which there is at most `−c V + K` because `f ≥ c V` on that region (`lyap_le_fLyap`); on
`z₁ < z₂` the drift of `W` is explicit (`drift_wLyap_neg`) and the annihilation supplies a cubic
`−η d z₁³` that dominates. Hence `QW ≤ −c W + K` everywhere (`drift_wLyap_le`). The sublevel sets
of `W` are infinite (`z₂` is unconstrained when `z₁ < z₂`), but the exponential drift alone gives
`E_n[W(X(t))] ≤ W(n) + K/c` uniformly in time (`sum_Pmin_mul_le_contract`), hence a uniform bound
on `E_n[X(t)²]`; with the total-variation convergence of `closedLoop_ergodic` this gives the
convergence of the mean.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Antithetic

open Network

variable (κ : closedLoop.RateConstants)

/-- The modified Lyapunov function. -/
noncomputable def wLyap (n : Fin 3 → ℕ) : ℝ :=
  if n 1 ≤ n 0 then lyap κ n else cb κ * (n 2 : ℝ) ^ 2 + cd κ * (n 0 : ℝ) ^ 2

theorem wLyap_le_lyap (n : Fin 3 → ℕ) : wLyap κ n ≤ lyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  unfold wLyap
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have hq : (n 0 : ℝ) - n 1 < 0 := by
      have : (n 0 : ℝ) < n 1 := by exact_mod_cast h
      linarith
    have hz : (n 0 : ℝ) ^ 2 ≤ (n 0 : ℝ) * n 1 := by
      have : (n 0 : ℝ) ≤ n 1 := by exact_mod_cast h.le
      nlinarith [Nat.cast_nonneg (α := ℝ) (n 0)]
    have hphi : 0 ≤ phi κ (n 0) (n 1) := by
      unfold phi; split_ifs
      · exact mul_nonneg (cA_pos κ).le (sq_nonneg _)
      · exact mul_nonneg (by unfold cB; positivity) (sq_nonneg _)
    have hcross : 0 ≤ -(cc κ * (n 2 : ℝ) * ((n 0 : ℝ) - n 1)) := by
      have : 0 ≤ cc κ * (n 2 : ℝ) := by unfold cc; positivity
      nlinarith
    have hd : 0 < cd κ := by unfold cd; positivity
    unfold lyap
    nlinarith [mul_le_mul_of_nonneg_left hz hd.le]

theorem wLyap_nonneg (n : Fin 3 → ℕ) : 0 ≤ wLyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  unfold wLyap
  split_ifs
  · exact lyap_nonneg κ n
  · have : 0 < cb κ := by unfold cb; positivity
    have : 0 < cd κ := by unfold cd; positivity
    positivity

/-- `W` controls the square of the output. -/
theorem sq_le_wLyap (n : Fin 3 → ℕ) :
    min (32 / 3 * θ κ ^ 2) (cb κ) * (n 2 : ℝ) ^ 2 ≤ wLyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  unfold wLyap
  split_ifs
  · have h := lyap_ge κ n
    have h1 : min (32 / 3 * θ κ ^ 2) (cb κ) * (n 2 : ℝ) ^ 2 ≤ 32 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have h2 : 0 ≤ cB κ / 4 * ((n 0 : ℝ) - n 1) ^ 2 := by positivity
    have h3 : 0 ≤ cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  · have h1 : min (32 / 3 * θ κ ^ 2) (cb κ) * (n 2 : ℝ) ^ 2 ≤ cb κ * (n 2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    have : 0 ≤ cd κ * (n 0 : ℝ) ^ 2 := by positivity
    linarith

/-- The constant comparing `V` with `f` on `z₂ ≤ z₁`. -/
noncomputable def cM : ℝ := cA κ + cb κ + cc κ + cd κ

/-- On `z₂ ≤ z₁`, `V ≤ (cM/ε) f`. -/
theorem lyap_le_fLyap {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) :
    lyap κ n ≤ cM κ / cε κ * fLyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hε := cε_pos κ
  have hA := cA_pos κ
  have hb : 0 < cb κ := by unfold cb; positivity
  have hcc : 0 < cc κ := by unfold cc; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  have hq : 0 ≤ (n 0 : ℝ) - n 1 := by
    have : (n 1 : ℝ) ≤ n 0 := by exact_mod_cast h
    linarith
  have hphi : phi κ (n 0) (n 1) = cA κ * ((n 0 : ℝ) - n 1) ^ 2 := by
    unfold phi; rw [if_pos h]
  set q := (n 0 : ℝ) - n 1 with hqdef
  set x := (n 2 : ℝ) with hx
  set P := (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) with hP
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := annih_nonneg (n 0) (n 1)
  have hz := prod_le_annih (n 0) (n 1)
  have hmax : max q 0 = q := max_eq_left hq
  have habs : |q| = q := abs_of_nonneg hq
  have hF : fLyap κ n = cε κ * (x ^ 2 + q + q ^ 2 + x * q + P) := by
    unfold fLyap; rw [hmax, habs]
  have hL : lyap κ n ≤ cA κ * q ^ 2 + cb κ * x ^ 2 + cc κ * (x * q) + cd κ * P := by
    unfold lyap; rw [hphi]
    have : 0 ≤ cc κ * x * q := by positivity
    have : cd κ * ((n 0 : ℝ) * n 1) ≤ cd κ * P := mul_le_mul_of_nonneg_left hz hd.le
    nlinarith
  rw [hF]
  have hS : cA κ * q ^ 2 + cb κ * x ^ 2 + cc κ * (x * q) + cd κ * P ≤
      cM κ * (x ^ 2 + q + q ^ 2 + x * q + P) := by
    unfold cM
    have h1 : 0 ≤ q ^ 2 := sq_nonneg _
    have h2 : 0 ≤ x ^ 2 := sq_nonneg _
    have h3 : 0 ≤ x * q := mul_nonneg hx0 hq
    nlinarith [mul_nonneg hA.le hq, mul_nonneg hb.le hq, mul_nonneg hcc.le hq, mul_nonneg hd.le hq,
      mul_nonneg hA.le h2, mul_nonneg hA.le h3, mul_nonneg hA.le hP0, mul_nonneg hb.le h1,
      mul_nonneg hb.le h3, mul_nonneg hb.le hP0, mul_nonneg hcc.le h1, mul_nonneg hcc.le h2,
      mul_nonneg hcc.le hP0, mul_nonneg hd.le h1, mul_nonneg hd.le h2, mul_nonneg hd.le h3]
  calc lyap κ n ≤ cA κ * q ^ 2 + cb κ * x ^ 2 + cc κ * (x * q) + cd κ * P := hL
    _ ≤ cM κ * (x ^ 2 + q + q ^ 2 + x * q + P) := hS
    _ = cM κ / cε κ * (cε κ * (x ^ 2 + q + q ^ 2 + x * q + P)) := by field_simp

theorem wLyap_of_lt {n : Fin 3 → ℕ} (h : n 0 < n 1) :
    wLyap κ n = cb κ * (n 2 : ℝ) ^ 2 + cd κ * (n 0 : ℝ) ^ 2 := by
  unfold wLyap; rw [if_neg (by omega)]

theorem wLyap_of_le {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) : wLyap κ n = lyap κ n := by
  unfold wLyap; rw [if_pos h]

/-- **The drift of `W` on `z₁ < z₂`.** -/
theorem drift_wLyap_neg {n : Fin 3 → ℕ} (hlt : n 0 < n 1) :
    (closedLoop.jumpSystem κ).drift (wLyap κ) n =
      μ κ * (cd κ * (2 * (n 0 : ℝ) + 1)) + η κ * (n 0 : ℝ) * (n 1 : ℝ) * (cd κ * (1 - 2 * (n 0 : ℝ))) +
      kk κ * (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1)) + γ κ * (n 2 : ℝ) * (cb κ * (1 - 2 * (n 2 : ℝ))) := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ n
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ n r *
      (wLyap κ (closedLoop.jumpNextCount n r) - wLyap κ n) = _
  change ∑ r : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have hW := wLyap_of_lt κ hlt
  have t0 : closedLoop.stochasticMassActionRate κ n (0 : Fin 5) *
      (wLyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - wLyap κ n) =
      μ κ * (cd κ * (2 * (n 0 : ℝ) + 1)) := by
    obtain ⟨a, b, c⟩ := next0 n
    rw [r0, hW]
    by_cases h : n 1 ≤ n 0 + 1
    · have heq : n 1 = n 0 + 1 := by omega
      rw [wLyap_of_le κ (by rw [a, b]; exact h)]
      unfold lyap phi
      rw [a, b, c, if_pos h]
      rw [heq]; push_cast; ring
    · rw [wLyap_of_lt κ (by rw [a, b]; omega), a, c]
      push_cast; ring
  have t1 : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
      (wLyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - wLyap κ n) =
      η κ * (n 0 : ℝ) * (n 1 : ℝ) * (cd κ * (1 - 2 * (n 0 : ℝ))) := by
    rw [r1]
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · simp [h0]
    obtain ⟨a, b, c⟩ := next1 n
    rw [hW, wLyap_of_lt κ (by rw [a, b]; omega), a, c, Nat.cast_sub h0]
    push_cast; ring
  have t2 : closedLoop.stochasticMassActionRate κ n (2 : Fin 5) *
      (wLyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - wLyap κ n) =
      kk κ * (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1)) := by
    rw [r2]
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · simp [h0]
    obtain ⟨a, b, c⟩ := next2 n
    have ha : n 0 - 1 + 1 = n 0 := by omega
    rw [hW, wLyap_of_lt κ (by rw [a, b, ha]; exact hlt), a, c, ha]
    push_cast; ring
  have t3 : closedLoop.stochasticMassActionRate κ n (3 : Fin 5) *
      (wLyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - wLyap κ n) =
      γ κ * (n 2 : ℝ) * (cb κ * (1 - 2 * (n 2 : ℝ))) := by
    rw [r3]
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · simp [h2]
    obtain ⟨a, b, c⟩ := next3 n
    rw [hW, wLyap_of_lt κ (by rw [a, b]; exact hlt), a, c, Nat.cast_sub h2]
    push_cast; ring
  have t4 : closedLoop.stochasticMassActionRate κ n (4 : Fin 5) *
      (wLyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - wLyap κ n) = 0 := by
    rw [r4]
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · simp [h2]
    obtain ⟨a, b, c⟩ := next4 n
    have hc : n 2 - 1 + 1 = n 2 := by omega
    rw [hW, wLyap_of_lt κ (by rw [a, b]; omega), a, c, hc]
    ring
  rw [t0, t1, t2, t3, t4]
  ring

/-- **Exponential drift of `W` on `z₁ < z₂`.** -/
theorem drift_wLyap_neg_le {n : Fin 3 → ℕ} (hlt : n 0 < n 1) :
    (closedLoop.jumpSystem κ).drift (wLyap κ) n ≤
      -(min (γ κ) 1) * wLyap κ n +
        (μ κ * cd κ + γ κ * cb κ / 2 + (2 * μ κ * cd κ + kk κ * cb κ) / 4 +
          4 * (2 * kk κ ^ 2 * cb κ / γ κ + cd κ + (2 * μ κ * cd κ + kk κ * cb κ)) ^ 3 /
            (27 * (η κ * cd κ) ^ 2)) := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hb : 0 < cb κ := by unfold cb; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  rw [drift_wLyap_neg κ hlt, wLyap_of_lt κ hlt]
  set Z := (n 0 : ℝ) with hZ
  set X := (n 2 : ℝ) with hX
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  -- the annihilation term
  have hann : η κ * Z * (n 1 : ℝ) * (cd κ * (1 - 2 * Z)) ≤ -(η κ * cd κ) * Z ^ 3 := by
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · have : Z = 0 := by rw [hZ, h0]; simp
      rw [this]; simp
    have hZ1 : 1 ≤ Z := by rw [hZ]; exact_mod_cast h0
    have hz2 : Z + 1 ≤ (n 1 : ℝ) := by rw [hZ]; exact_mod_cast hlt
    have h1 : 1 - 2 * Z ≤ -Z := by linarith
    have h2 : Z * (n 1 : ℝ) * (1 - 2 * Z) ≤ -(Z ^ 3) := by
      have h3 : Z * (n 1 : ℝ) * (1 - 2 * Z) ≤ Z * (n 1 : ℝ) * (-Z) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : Z * (n 1 : ℝ) * (-Z) ≤ -(Z ^ 3) := by
        have hzn : Z ≤ (n 1 : ℝ) := by linarith
        have : Z ^ 3 ≤ Z * (n 1 : ℝ) * Z := by
          calc Z ^ 3 = Z * Z * Z := by ring
            _ ≤ Z * (n 1 : ℝ) * Z :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hZ0) hZ0
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ η κ * cd κ by positivity)
    nlinarith
  -- the output terms
  have hyoung : 2 * kk κ * Z * X ≤ γ κ / 2 * X ^ 2 + 2 * kk κ ^ 2 / γ κ * Z ^ 2 := by
    have := young_le (show 0 < γ κ / 2 by positivity) X (2 * kk κ * Z)
    have e : (2 * kk κ * Z) ^ 2 / (4 * (γ κ / 2)) = 2 * kk κ ^ 2 / γ κ * Z ^ 2 := by
      field_simp; ring
    rw [e] at this; linarith
  have hlinX : γ κ * X ≤ γ κ / 2 * X ^ 2 + γ κ / 2 := by
    nlinarith [sq_nonneg (X - 1), hγ]
  set G := 2 * kk κ ^ 2 * cb κ / γ κ with hG
  set L := 2 * μ κ * cd κ + kk κ * cb κ with hL
  have hG0 : 0 ≤ G := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hlin := lin_le_sq L Z hL0
  have hcub := cubic_le (a := η κ * cd κ) (G := G + cd κ + L) (m := Z) (by positivity)
    (by positivity) hZ0
  have hmin1 : min (γ κ) 1 ≤ γ κ := min_le_left _ _
  have hmin2 : min (γ κ) 1 ≤ 1 := min_le_right _ _
  have hmin0 : 0 < min (γ κ) 1 := lt_min hγ one_pos
  have e1 : -(min (γ κ) 1) * (cb κ * X ^ 2 + cd κ * Z ^ 2) ≥ -(γ κ * cb κ * X ^ 2) - cd κ * Z ^ 2 := by
    have a1 : min (γ κ) 1 * (cb κ * X ^ 2) ≤ γ κ * (cb κ * X ^ 2) :=
      mul_le_mul_of_nonneg_right hmin1 (by positivity)
    have a2 : min (γ κ) 1 * (cd κ * Z ^ 2) ≤ 1 * (cd κ * Z ^ 2) :=
      mul_le_mul_of_nonneg_right hmin2 (by positivity)
    nlinarith
  have hkx : kk κ * Z * (cb κ * (2 * X + 1)) = cb κ * (2 * kk κ * Z * X) + kk κ * cb κ * Z := by ring
  have hgx : γ κ * X * (cb κ * (1 - 2 * X)) = cb κ * (γ κ * X) - 2 * γ κ * cb κ * X ^ 2 := by ring
  have hb1 := mul_le_mul_of_nonneg_left hyoung hb.le
  have hb2 := mul_le_mul_of_nonneg_left hlinX hb.le
  have hGe : cb κ * (2 * kk κ ^ 2 / γ κ * Z ^ 2) = G * Z ^ 2 := by rw [hG]; field_simp
  nlinarith [hann, e1, hlin, hcub, hb1, hb2, hGe, hkx, hgx]

/-- **Exponential drift of `W`**, everywhere. -/
theorem drift_wLyap_le : ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
    ∀ n, (closedLoop.jumpSystem κ).drift (wLyap κ) n ≤ -c * wLyap κ n + K := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hb : 0 < cb κ := by unfold cb; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  have hA := cA_pos κ
  have hcc : 0 < cc κ := by unfold cc; positivity
  have hε := cε_pos κ
  have hM : 0 < cM κ := by unfold cM; positivity
  set K₁ := μ κ * cd κ + γ κ * cb κ / 2 + (2 * μ κ * cd κ + kk κ * cb κ) / 4 +
    4 * (2 * kk κ ^ 2 * cb κ / γ κ + cd κ + (2 * μ κ * cd κ + kk κ * cb κ)) ^ 3 /
      (27 * (η κ * cd κ) ^ 2) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK := cK_nonneg κ
  set c := min (min (γ κ) 1) (cε κ / cM κ) with hc
  have hc0 : 0 < c := lt_min (lt_min hγ one_pos) (by positivity)
  refine ⟨c, K₁ + cK κ, hc0, by positivity, fun n => ?_⟩
  have hW0 := wLyap_nonneg κ n
  by_cases hle : n 1 ≤ n 0
  · -- the drift of `W` is at most that of `V`
    have hWn := wLyap_of_le κ hle
    have hdr : (closedLoop.jumpSystem κ).drift (wLyap κ) n ≤
        (closedLoop.jumpSystem κ).drift (lyap κ) n := by
      unfold JumpSystem.drift
      refine Finset.sum_le_sum fun r _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ ((closedLoop.jumpSystem κ).rate_nonneg r n)
      rw [hWn]
      linarith [wLyap_le_lyap κ ((closedLoop.jumpSystem κ).next r n)]
    have h1 := drift_lyap_le κ n
    have h2 := lyap_le_fLyap κ hle
    have h3 : cε κ / cM κ * lyap κ n ≤ fLyap κ n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM]
      have := mul_le_mul_of_nonneg_left h2 hε.le
      have e : cε κ * (cM κ / cε κ * fLyap κ n) = fLyap κ n * cM κ := by field_simp
      linarith
    have h4 : c * wLyap κ n ≤ cε κ / cM κ * lyap κ n := by
      rw [hWn]; exact mul_le_mul_of_nonneg_right (min_le_right _ _) (lyap_nonneg κ n)
    linarith
  · push Not at hle
    have h1 := drift_wLyap_neg_le κ hle
    have h2 : c * wLyap κ n ≤ min (γ κ) 1 * wLyap κ n :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hW0
    have : -(min (γ κ) 1) * wLyap κ n + K₁ ≤ -c * wLyap κ n + (K₁ + cK κ) := by nlinarith
    exact h1.trans this

/-- **Uniform second moment of the output.** -/
theorem output_sq_moment_le : ∃ B : (Fin 3 → ℕ) → ℝ, ∀ n t, 0 ≤ t →
    ∀ F : Finset (Fin 3 → ℕ), ∑ m ∈ F, closedLoop.transition κ t n m * (m 2 : ℝ) ^ 2 ≤ B n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨c, K, hc, hK, hdrift⟩ := drift_wLyap_le κ
  have hb : 0 < cb κ := by unfold cb; positivity
  set cw := min (32 / 3 * θ κ ^ 2) (cb κ) with hcw
  have hcw0 : 0 < cw := lt_min (by positivity) hb
  refine ⟨fun n => (wLyap κ n + K / c) / cw, fun n t ht F => ?_⟩
  have h := (closedLoop.jumpSystem κ).sum_Pmin_mul_le_contract (wLyap κ) (wLyap_nonneg κ) hc hK
    hdrift ht n F
  have he : Real.exp (-(c * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 : 0 < Real.exp (-(c * t)) := Real.exp_pos _
  have hKc : 0 ≤ K / c := div_nonneg hK hc.le
  have hW := wLyap_nonneg κ n
  have hB : ∑ b ∈ F, (closedLoop.jumpSystem κ).Pmin t n b * wLyap κ b ≤ wLyap κ n + K / c := by
    have : Real.exp (-(c * t)) * wLyap κ n + K / c * (1 - Real.exp (-(c * t))) ≤
        wLyap κ n + K / c := by nlinarith
    linarith
  rw [le_div_iff₀ hcw0, Finset.sum_mul]
  calc ∑ m ∈ F, closedLoop.transition κ t n m * (m 2 : ℝ) ^ 2 * cw
      ≤ ∑ m ∈ F, (closedLoop.jumpSystem κ).Pmin t n m * wLyap κ m :=
        Finset.sum_le_sum fun m _ => by
          have h1 := sq_le_wLyap κ m
          have h0 : 0 ≤ closedLoop.transition κ t n m := closedLoop.transition_nonneg κ ht n m
          have : closedLoop.transition κ t n m * (m 2 : ℝ) ^ 2 * cw =
              closedLoop.transition κ t n m * (cw * (m 2 : ℝ) ^ 2) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h1 h0
    _ ≤ wLyap κ n + K / c := hB

/-- **Convergence of the mean output to the setpoint** (Briat–Gupta–Khammash): for every
initial count, `E_n[X(t)] → μ/θ`. -/
theorem closedLoop_mean_output_tendsto (n : Fin 3 → ℕ) :
    Tendsto (fun t => ∑' m, closedLoop.transition κ t n m * (m 2 : ℝ)) atTop
      (𝓝 (κ.k rRef / κ.k rSense)) := by
  classical
  obtain ⟨π, hπ0, hπ1, -, hTV, -, -, hmean⟩ := closedLoop_ergodic κ
  obtain ⟨B₀, hB₀⟩ := output_sq_moment_le κ
  set B := max (B₀ n) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ t, 0 ≤ t → ∀ F : Finset (Fin 3 → ℕ),
      ∑ m ∈ F, closedLoop.transition κ t n m * (m 2 : ℝ) ^ 2 ≤ B := fun t ht F =>
    (hB₀ n t ht F).trans (le_max_left _ _)
  set P : ℝ → (Fin 3 → ℕ) → ℝ := fun t m => closedLoop.transition κ t n m with hP
  have hP0 : ∀ t, 0 ≤ t → ∀ m, 0 ≤ P t m := fun t ht m => closedLoop.transition_nonneg κ ht n m
  have hPs : ∀ t, 0 ≤ t → Summable (P t) := fun t ht =>
    summable_of_sum_le (hP0 t ht) fun F => closedLoop.sum_transition_le_one κ ht n F
  have hπs : Summable π := hπ1.summable
  have hx2 : ∀ m : Fin 3 → ℕ, 0 ≤ (m 2 : ℝ) ^ 2 := fun m => sq_nonneg _
  have hPx2 : ∀ t, 0 ≤ t → Summable fun m => P t m * (m 2 : ℝ) ^ 2 := fun t ht =>
    summable_of_sum_le (fun m => mul_nonneg (hP0 t ht m) (hx2 m)) (hB t ht)
  have hPx2le : ∀ t, 0 ≤ t → ∑' m, P t m * (m 2 : ℝ) ^ 2 ≤ B := fun t ht =>
    (hPx2 t ht).tsum_le_of_sum_le (hB t ht)
  have habs : ∀ t, 0 ≤ t → Summable fun m => |P t m - π m| := fun t ht =>
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => by
      rw [abs_le]; constructor <;> linarith [hP0 t ht m, hπ0 m]) ((hPs t ht).add hπs)
  -- pointwise convergence, hence the stationary second moment
  have hpt : ∀ m, Tendsto (fun t => P t m) atTop (𝓝 (π m)) := by
    intro m
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ (hTV n)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Real.norm_eq_abs]
    exact (habs t ht).le_tsum m fun b _ => abs_nonneg _
  have hπF : ∀ F : Finset (Fin 3 → ℕ), ∑ m ∈ F, π m * (m 2 : ℝ) ^ 2 ≤ B := by
    intro F
    have hlim : Tendsto (fun t => ∑ m ∈ F, P t m * (m 2 : ℝ) ^ 2) atTop
        (𝓝 (∑ m ∈ F, π m * (m 2 : ℝ) ^ 2)) :=
      tendsto_finsetSum _ fun m _ => (hpt m).mul_const _
    exact le_of_tendsto hlim (by filter_upwards [eventually_ge_atTop 0] with t ht using hB t ht F)
  have hπx2 : Summable fun m => π m * (m 2 : ℝ) ^ 2 :=
    summable_of_sum_le (fun m => mul_nonneg (hπ0 m).le (hx2 m)) hπF
  have hπx2le : ∑' m, π m * (m 2 : ℝ) ^ 2 ≤ B := hπx2.tsum_le_of_sum_le hπF
  have hxle : ∀ m : Fin 3 → ℕ, (m 2 : ℝ) ≤ 1 + (m 2 : ℝ) ^ 2 := fun m => by
    nlinarith [sq_nonneg ((m 2 : ℝ) - 1)]
  have hPx : ∀ t, 0 ≤ t → Summable fun m => P t m * (m 2 : ℝ) := fun t ht =>
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hP0 t ht m) (Nat.cast_nonneg _))
      (fun m => by
        have := mul_le_mul_of_nonneg_left (hxle m) (hP0 t ht m)
        linarith) ((hPs t ht).add (hPx2 t ht))
  have hπx : Summable fun m => π m * (m 2 : ℝ) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hπ0 m).le (Nat.cast_nonneg _))
      (fun m => by
        have := mul_le_mul_of_nonneg_left (hxle m) (hπ0 m).le
        linarith) (hπs.add hπx2)
  -- the key estimate
  have hkey : ∀ t, 0 ≤ t → ∀ L : ℝ, 0 < L →
      |∑' m, P t m * (m 2 : ℝ) - ∑' m, π m * (m 2 : ℝ)| ≤
        L * ∑' m, |P t m - π m| + 2 * B / L := by
    intro t ht L hL
    rw [← (hPx t ht).tsum_sub hπx]
    have hs1 : Summable fun m => |P t m - π m| * (m 2 : ℝ) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
        (fun m => by
          have h1 : |P t m - π m| ≤ P t m + π m := by
            rw [abs_le]; constructor <;> linarith [hP0 t ht m, hπ0 m]
          have := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) (m 2))
          linarith) ((hPx t ht).add hπx)
    have hs2 : Summable fun m => L * |P t m - π m| + (P t m + π m) * (m 2 : ℝ) ^ 2 / L :=
      ((habs t ht).mul_left L).add (((hPx2 t ht).add hπx2).div_const L |>.congr fun m => by ring)
    calc |∑' m, (P t m * (m 2 : ℝ) - π m * (m 2 : ℝ))|
        ≤ ∑' m, |P t m * (m 2 : ℝ) - π m * (m 2 : ℝ)| := by
          have := norm_tsum_le_tsum_norm (f := fun m => P t m * (m 2 : ℝ) - π m * (m 2 : ℝ))
            (hs1.congr fun m => by rw [Real.norm_eq_abs, ← sub_mul, abs_mul,
              abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (m 2))])
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' m, (L * |P t m - π m| + (P t m + π m) * (m 2 : ℝ) ^ 2 / L) := by
          refine (hs1.congr fun m => ?_).tsum_le_tsum (fun m => ?_) hs2
          · rw [← sub_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (m 2))]
          · rw [← sub_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (m 2))]
            have hx : (m 2 : ℝ) ≤ L + (m 2 : ℝ) ^ 2 / L := by
              rcases le_total (m 2 : ℝ) L with h | h
              · have : 0 ≤ (m 2 : ℝ) ^ 2 / L := by positivity
                linarith
              · have : (m 2 : ℝ) ≤ (m 2 : ℝ) ^ 2 / L := by
                  rw [le_div_iff₀ hL]; nlinarith
                linarith
            have h1 : |P t m - π m| ≤ P t m + π m := by
              rw [abs_le]; constructor <;> linarith [hP0 t ht m, hπ0 m]
            have h2 := mul_le_mul_of_nonneg_left hx (abs_nonneg (P t m - π m))
            have h3 : |P t m - π m| * ((m 2 : ℝ) ^ 2 / L) ≤ (P t m + π m) * (m 2 : ℝ) ^ 2 / L := by
              rw [mul_div_assoc']
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (hx2 m)) hL.le
            nlinarith
      _ = L * ∑' m, |P t m - π m| + (∑' m, P t m * (m 2 : ℝ) ^ 2 + ∑' m, π m * (m 2 : ℝ) ^ 2) / L := by
          rw [((habs t ht).mul_left L).tsum_add (((hPx2 t ht).add hπx2).div_const L |>.congr
            fun m => by ring), tsum_mul_left]
          congr 1
          rw [← (hPx2 t ht).tsum_add hπx2, ← tsum_div_const]
          exact tsum_congr fun m => by ring
      _ ≤ L * ∑' m, |P t m - π m| + 2 * B / L := by
          have : (∑' m, P t m * (m 2 : ℝ) ^ 2 + ∑' m, π m * (m 2 : ℝ) ^ 2) / L ≤ 2 * B / L :=
            div_le_div_of_nonneg_right (by linarith [hPx2le t ht]) hL.le
          linarith
  -- conclusion
  rw [← hmean, Metric.tendsto_atTop]
  intro ε hε
  set L := 4 * B / ε + 1 with hL
  have hL0 : 0 < L := by positivity
  have hBL : 2 * B / L < ε / 2 := by
    rw [div_lt_iff₀ hL0]
    have : ε / 2 * L = 2 * B + ε / 2 := by rw [hL]; field_simp; ring
    rw [this]; linarith
  have hev : ∀ᶠ t in atTop, ∑' m, |P t m - π m| < ε / (2 * L) := by
    have := (hTV n).eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * L) by positivity))
    exact this
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 0))
  refine ⟨T₀, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ t ht
  rw [Real.dist_eq]
  have h3 := hkey t h2 L hL0
  have h4 : L * ∑' m, |P t m - π m| < ε / 2 := by
    have := mul_lt_mul_of_pos_left h1 hL0
    have e : L * (ε / (2 * L)) = ε / 2 := by field_simp
    linarith
  linarith

/-- Instance: with unit rates the mean output converges to `1` from every initial count. -/
theorem unitRates_mean_output_tendsto (n : Fin 3 → ℕ) :
    Tendsto (fun t => ∑' m, closedLoop.transition unitRates t n m * (m 2 : ℝ)) atTop (𝓝 1) := by
  have h := closedLoop_mean_output_tendsto unitRates n
  simpa [unitRates] using h

end Antithetic
end CRNT
