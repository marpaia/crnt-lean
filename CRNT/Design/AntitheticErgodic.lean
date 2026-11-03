import CRNT.Design.Antithetic
import CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov
import CRNT.Stochastic.ProductFormErgodic
import CRNT.Stochastic.InvariantMoments

/-!
# Ergodicity of the antithetic closed loop

For the antithetic integral controller closed around a production–degradation plant
(`CRNT.Antithetic.closedLoop`), with reference rate `μ`, annihilation `η`, actuation `k`,
degradation `γ` and sensing `θ`, the function of the charge `q = z₁ − z₂`, the output `x` and the
controller species

`V = φ(q) + b x² − c x q + d z₁ z₂`,  `φ(q) = A q²` (`q ≥ 0`), `B q²` (`q < 0`),

with `A = 32kθ + 9γ²`, `B = 4γ²`, `b = 32θ²`, `c = 16γθ`, `d = 2γ²`, is a Foster–Lyapunov function:
`QV ≤ −f + K` with `f` norm-like (`drift_lyap_le`), for every choice of positive rates.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Antithetic

open Network

variable (κ : closedLoop.RateConstants)

/-- The rates. -/
noncomputable def μ : ℝ := κ.k (0 : Fin 5)
noncomputable def η : ℝ := κ.k (1 : Fin 5)
noncomputable def kk : ℝ := κ.k (2 : Fin 5)
noncomputable def γ : ℝ := κ.k (3 : Fin 5)
noncomputable def θ : ℝ := κ.k (4 : Fin 5)

/-- The coefficients of the Lyapunov function. -/
noncomputable def cA : ℝ := 32 * kk κ * θ κ + 9 * γ κ ^ 2
noncomputable def cB : ℝ := 4 * γ κ ^ 2
noncomputable def cb : ℝ := 32 * θ κ ^ 2
noncomputable def cc : ℝ := 16 * γ κ * θ κ
noncomputable def cd : ℝ := 2 * γ κ ^ 2

/-- `φ(q)` at a count: `A q²` if `z₂ ≤ z₁`, `B q²` otherwise. -/
noncomputable def phi (z1 z2 : ℕ) : ℝ :=
  if z2 ≤ z1 then cA κ * ((z1 : ℝ) - z2) ^ 2 else cB κ * ((z1 : ℝ) - z2) ^ 2

/-- **The Lyapunov function.** -/
noncomputable def lyap (n : Fin 3 → ℕ) : ℝ :=
  phi κ (n 0) (n 1) + cb κ * (n 2 : ℝ) ^ 2 - cc κ * (n 2 : ℝ) * ((n 0 : ℝ) - n 1) +
    cd κ * (n 0 : ℝ) * (n 1 : ℝ)

theorem rate_eq (n : Fin 3 → ℕ) :
    closedLoop.stochasticMassActionRate κ n (0 : Fin 5) = μ κ ∧
    closedLoop.stochasticMassActionRate κ n (1 : Fin 5) = η κ * (n 0 : ℝ) * (n 1 : ℝ) ∧
    closedLoop.stochasticMassActionRate κ n (2 : Fin 5) = kk κ * (n 0 : ℝ) ∧
    closedLoop.stochasticMassActionRate κ n (3 : Fin 5) = γ κ * (n 2 : ℝ) ∧
    closedLoop.stochasticMassActionRate κ n (4 : Fin 5) = θ κ * (n 2 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stochasticMassActionRate, closedLoop, rxn, μ, η, kk, γ, θ, Fin.prod_univ_three] <;> ring

theorem next0 (n : Fin 3 → ℕ) : closedLoop.jumpNextCount n (0 : Fin 5) 0 = n 0 + 1 ∧
    closedLoop.jumpNextCount n (0 : Fin 5) 1 = n 1 ∧
    closedLoop.jumpNextCount n (0 : Fin 5) 2 = n 2 := by
  simp [jumpNextCount, closedLoop, rxn]

theorem next1 (n : Fin 3 → ℕ) : closedLoop.jumpNextCount n (1 : Fin 5) 0 = n 0 - 1 ∧
    closedLoop.jumpNextCount n (1 : Fin 5) 1 = n 1 - 1 ∧
    closedLoop.jumpNextCount n (1 : Fin 5) 2 = n 2 := by
  simp [jumpNextCount, closedLoop, rxn]

theorem next2 (n : Fin 3 → ℕ) : closedLoop.jumpNextCount n (2 : Fin 5) 0 = n 0 - 1 + 1 ∧
    closedLoop.jumpNextCount n (2 : Fin 5) 1 = n 1 ∧
    closedLoop.jumpNextCount n (2 : Fin 5) 2 = n 2 + 1 := by
  simp [jumpNextCount, closedLoop, rxn]

theorem next3 (n : Fin 3 → ℕ) : closedLoop.jumpNextCount n (3 : Fin 5) 0 = n 0 ∧
    closedLoop.jumpNextCount n (3 : Fin 5) 1 = n 1 ∧
    closedLoop.jumpNextCount n (3 : Fin 5) 2 = n 2 - 1 := by
  simp [jumpNextCount, closedLoop, rxn]

theorem next4 (n : Fin 3 → ℕ) : closedLoop.jumpNextCount n (4 : Fin 5) 0 = n 0 ∧
    closedLoop.jumpNextCount n (4 : Fin 5) 1 = n 1 + 1 ∧
    closedLoop.jumpNextCount n (4 : Fin 5) 2 = n 2 - 1 + 1 := by
  simp [jumpNextCount, closedLoop, rxn]

/-- **The drift of the Lyapunov function.** -/
theorem drift_lyap (n : Fin 3 → ℕ) :
    (closedLoop.jumpSystem κ).drift (lyap κ) n =
      μ κ * ((phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1)) - cc κ * (n 2 : ℝ) + cd κ * (n 1 : ℝ)) +
      η κ * (n 0 : ℝ) * (n 1 : ℝ) * (cd κ * (1 - (n 0 : ℝ) - (n 1 : ℝ))) +
      kk κ * (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1)) +
      γ κ * (n 2 : ℝ) * (cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1)) +
      θ κ * (n 2 : ℝ) * ((phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1)) + cc κ * (n 2 : ℝ) +
        cd κ * (n 0 : ℝ)) := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ n
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ n r *
      (lyap κ (closedLoop.jumpNextCount n r) - lyap κ n) = _
  change ∑ r : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have t0 : closedLoop.stochasticMassActionRate κ n (0 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (0 : Fin 5)) - lyap κ n) =
      μ κ * ((phi κ (n 0 + 1) (n 1) - phi κ (n 0) (n 1)) - cc κ * (n 2 : ℝ) + cd κ * (n 1 : ℝ)) := by
    obtain ⟨a, b, c⟩ := next0 n
    rw [r0]; unfold lyap; rw [a, b, c]; push_cast; ring
  have t1 : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n) =
      η κ * (n 0 : ℝ) * (n 1 : ℝ) * (cd κ * (1 - (n 0 : ℝ) - (n 1 : ℝ))) := by
    rw [r1]
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · simp [h0]
    rcases Nat.eq_zero_or_pos (n 1) with h1 | h1
    · simp [h1]
    obtain ⟨a, b, c⟩ := next1 n
    unfold lyap; rw [a, b, c]
    have hphi : phi κ (n 0 - 1) (n 1 - 1) = phi κ (n 0) (n 1) := by
      unfold phi
      have hiff : n 1 - 1 ≤ n 0 - 1 ↔ n 1 ≤ n 0 := by omega
      rw [Nat.cast_sub h0, Nat.cast_sub h1]
      simp only [hiff]
      split_ifs <;> ring
    rw [hphi, Nat.cast_sub h0, Nat.cast_sub h1]; push_cast; ring
  have t2 : closedLoop.stochasticMassActionRate κ n (2 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (2 : Fin 5)) - lyap κ n) =
      kk κ * (n 0 : ℝ) * (cb κ * (2 * (n 2 : ℝ) + 1) - cc κ * ((n 0 : ℝ) - n 1)) := by
    rw [r2]
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · simp [h0]
    obtain ⟨a, b, c⟩ := next2 n
    have ha : n 0 - 1 + 1 = n 0 := by omega
    unfold lyap; rw [a, b, c, ha]; push_cast; ring
  have t3 : closedLoop.stochasticMassActionRate κ n (3 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (3 : Fin 5)) - lyap κ n) =
      γ κ * (n 2 : ℝ) * (cb κ * (1 - 2 * (n 2 : ℝ)) + cc κ * ((n 0 : ℝ) - n 1)) := by
    rw [r3]
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · simp [h2]
    obtain ⟨a, b, c⟩ := next3 n
    unfold lyap; rw [a, b, c, Nat.cast_sub h2]; push_cast; ring
  have t4 : closedLoop.stochasticMassActionRate κ n (4 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (4 : Fin 5)) - lyap κ n) =
      θ κ * (n 2 : ℝ) * ((phi κ (n 0) (n 1 + 1) - phi κ (n 0) (n 1)) + cc κ * (n 2 : ℝ) +
        cd κ * (n 0 : ℝ)) := by
    rw [r4]
    rcases Nat.eq_zero_or_pos (n 2) with h2 | h2
    · simp [h2]
    obtain ⟨a, b, c⟩ := next4 n
    have hc : n 2 - 1 + 1 = n 2 := by omega
    unfold lyap; rw [a, b, c, hc]; push_cast; ring
  rw [t0, t1, t2, t3, t4]

/-! ## Elementary inequalities -/

theorem young_le {a : ℝ} (ha : 0 < a) (u v : ℝ) : u * v ≤ a * u ^ 2 + v ^ 2 / (4 * a) := by
  rw [← sub_nonneg]
  have h : a * u ^ 2 + v ^ 2 / (4 * a) - u * v = (2 * a * u - v) ^ 2 / (4 * a) := by
    field_simp; ring
  rw [h]; positivity

theorem cubic_le {a G m : ℝ} (ha : 0 < a) (hG : 0 ≤ G) (hm : 0 ≤ m) :
    G * m ^ 2 ≤ a * m ^ 3 + 4 * G ^ 3 / (27 * a ^ 2) := by
  rw [← sub_nonneg]
  have h : a * m ^ 3 + 4 * G ^ 3 / (27 * a ^ 2) - G * m ^ 2 =
      a * (m - 2 * G / (3 * a)) ^ 2 * (m + G / (3 * a)) := by
    field_simp; ring
  rw [h]
  have : 0 ≤ m + G / (3 * a) := by positivity
  positivity

theorem lin_le_sq (lm m : ℝ) (hlm : 0 ≤ lm) : lm * m ≤ lm * m ^ 2 + lm / 4 := by
  nlinarith [mul_nonneg hlm (sq_nonneg (m - 1 / 2))]

/-- **Case `q ≥ 1`** of the drift bound, with abstract coefficients. -/
theorem caseI_gen {α β δ E Lm lm Lq Lx c0 c1 ε K m q X P : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hLm : 0 ≤ Lm) (hLmlm : Lm ≤ lm) (hLq : 0 ≤ Lq) (hLx : 0 ≤ Lx)
    (hc1 : 0 ≤ c1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 8 * α) (hε2 : ε ≤ β / 8) (hε3 : ε ≤ δ / 4)
    (hK : c0 + lm / 4 + 4 * (E ^ 2 / (48 * α) + lm) ^ 3 / (27 * (δ / 4) ^ 2) + Lq ^ 2 / β +
      Lx ^ 2 / (48 * α) ≤ K)
    (hm : 0 ≤ m) (hq : 1 ≤ q) (hX : 0 ≤ X) (hP : m ^ 3 ≤ P) :
    -β * q ^ 2 - 48 * α * X ^ 2 - β * m * q + E * m * X - δ * P + Lq * q + c0 + Lm * m + Lx * X -
      c1 * X + ε * (X ^ 2 + q + q ^ 2 + X * q + P) ≤ K := by
  have hlm : 0 ≤ lm := hLm.trans hLmlm
  set G := E ^ 2 / (48 * α) + lm with hG
  have hG0 : 0 ≤ G := by positivity
  have F1 : E * m * X ≤ 12 * α * X ^ 2 + E ^ 2 / (48 * α) * m ^ 2 := by
    have := young_le (show 0 < 12 * α by positivity) X (E * m)
    have e : (E * m) ^ 2 / (4 * (12 * α)) = E ^ 2 / (48 * α) * m ^ 2 := by
      field_simp; ring
    nlinarith [this, e]
  have F2 : lm * m ≤ lm * m ^ 2 + lm / 4 := lin_le_sq lm m hlm
  have F2' : Lm * m ≤ lm * m := mul_le_mul_of_nonneg_right hLmlm hm
  have F3 := cubic_le (show 0 < δ / 4 by positivity) hG0 hm
  have F4 : Lq * q ≤ β / 4 * q ^ 2 + Lq ^ 2 / β := by
    have := young_le (show 0 < β / 4 by positivity) q Lq
    have e : Lq ^ 2 / (4 * (β / 4)) = Lq ^ 2 / β := by field_simp
    nlinarith [this, e]
  have F5 : Lx * X ≤ 12 * α * X ^ 2 + Lx ^ 2 / (48 * α) := by
    have := young_le (show 0 < 12 * α by positivity) X Lx
    have e : Lx ^ 2 / (4 * (12 * α)) = Lx ^ 2 / (48 * α) := by field_simp; ring
    nlinarith [this, e]
  have hXq : X * q ≤ (X ^ 2 + q ^ 2) / 2 := by nlinarith [sq_nonneg (X - q)]
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have E1 : ε * X ^ 2 ≤ 8 * α * X ^ 2 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg _)
  have E2 : ε * q ^ 2 ≤ β / 8 * q ^ 2 := mul_le_mul_of_nonneg_right hε2 (sq_nonneg _)
  have E3 : ε * P ≤ δ / 4 * P := mul_le_mul_of_nonneg_right hε3 hP0
  have E4 : ε * (X * q) ≤ ε * ((X ^ 2 + q ^ 2) / 2) := mul_le_mul_of_nonneg_left hXq hε0
  have E5 : ε * q ≤ ε * q ^ 2 := mul_le_mul_of_nonneg_left hqq hε0
  have hm3 : δ / 4 * m ^ 3 ≤ δ / 4 * P := mul_le_mul_of_nonneg_left hP (by positivity)
  have S1 : 0 ≤ α * X ^ 2 := by positivity
  have S2 : 0 ≤ β * q ^ 2 := by positivity
  have S3 : 0 ≤ β * m * q := by have : 0 ≤ q := by linarith
                                positivity
  have S4 : 0 ≤ δ * P := by positivity
  have S5 : 0 ≤ c1 * X := by positivity
  have S6 : 0 ≤ ε * X ^ 2 := by positivity
  linarith [F1, F2, F2', F3, F4, F5, E1, E2, E3, E4, E5, hm3, S1, S2, S3, S4, S5, S6]

/-- **Case `q = 0`.** -/
theorem caseII_gen {α δ E Lm lm Lx c0 c0' c1 ε K m X P : ℝ} (hα : 0 < α)
    (hδ : 0 < δ) (hLm : 0 ≤ Lm) (hLmlm : Lm ≤ lm) (hLx : 0 ≤ Lx)
    (hc1 : 0 ≤ c1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 8 * α) (hε3 : ε ≤ δ / 4) (hc0 : c0' ≤ c0)
    (hK : c0 + lm / 4 + 4 * (E ^ 2 / (48 * α) + lm) ^ 3 / (27 * (δ / 4) ^ 2) + Lx ^ 2 / (48 * α) ≤ K)
    (hm : 0 ≤ m) (hX : 0 ≤ X) (hP : m ^ 3 ≤ P) :
    -48 * α * X ^ 2 + E * m * X - δ * P + c0' + Lm * m + Lx * X - c1 * X +
      ε * (X ^ 2 + P) ≤ K := by
  have hlm : 0 ≤ lm := hLm.trans hLmlm
  set G := E ^ 2 / (48 * α) + lm with hG
  have hG0 : 0 ≤ G := by positivity
  have F1 : E * m * X ≤ 12 * α * X ^ 2 + E ^ 2 / (48 * α) * m ^ 2 := by
    have := young_le (show 0 < 12 * α by positivity) X (E * m)
    have e : (E * m) ^ 2 / (4 * (12 * α)) = E ^ 2 / (48 * α) * m ^ 2 := by
      field_simp; ring
    nlinarith [this, e]
  have F2 : lm * m ≤ lm * m ^ 2 + lm / 4 := lin_le_sq lm m hlm
  have F2' : Lm * m ≤ lm * m := mul_le_mul_of_nonneg_right hLmlm hm
  have F3 := cubic_le (show 0 < δ / 4 by positivity) hG0 hm
  have F5 : Lx * X ≤ 12 * α * X ^ 2 + Lx ^ 2 / (48 * α) := by
    have := young_le (show 0 < 12 * α by positivity) X Lx
    have e : Lx ^ 2 / (4 * (12 * α)) = Lx ^ 2 / (48 * α) := by field_simp; ring
    nlinarith [this, e]
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have E1 : ε * X ^ 2 ≤ 8 * α * X ^ 2 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg _)
  have E3 : ε * P ≤ δ / 4 * P := mul_le_mul_of_nonneg_right hε3 hP0
  have hm3 : δ / 4 * m ^ 3 ≤ δ / 4 * P := mul_le_mul_of_nonneg_left hP (by positivity)
  have S1 : 0 ≤ α * X ^ 2 := by positivity
  have S4 : 0 ≤ δ * P := by positivity
  have S5 : 0 ≤ c1 * X := by positivity
  linarith [F1, F2, F2', F3, F5, E1, E3, hm3, S1, S4, S5]

/-- **Case `q ≤ −1`**, with `p = −q`. -/
theorem caseIII_gen {α β δ ρ σ E Lm lm Lx c0 c0' c1 ε K m p X P : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hLm : 0 ≤ Lm) (hLmlm : Lm + β ^ 2 / δ ≤ lm)
    (hLx : 0 ≤ Lx) (hc1 : 0 ≤ c1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 8 * α) (hε3 : ε ≤ δ / 4)
    (hε4 : ε ≤ ρ) (hε5 : ε ≤ σ) (hc0 : c0' ≤ c0)
    (hK : c0 + lm / 4 + 4 * (E ^ 2 / (48 * α) + lm) ^ 3 / (27 * (δ / 4) ^ 2) + Lx ^ 2 / (48 * α) ≤ K)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hX : 0 ≤ X) (hP : m ^ 3 ≤ P) (hP' : m * p ^ 2 ≤ P) :
    -48 * α * X ^ 2 - ρ * p * X - σ * p - δ * P + E * m * X + β * m * p + c0' + Lm * m +
      Lx * X - c1 * X + ε * (X ^ 2 + p + X * p + P) ≤ K := by
  have hlm : 0 ≤ lm := le_trans (by positivity) hLmlm
  set G := E ^ 2 / (48 * α) + lm with hG
  have hG0 : 0 ≤ G := by positivity
  have F1 : E * m * X ≤ 12 * α * X ^ 2 + E ^ 2 / (48 * α) * m ^ 2 := by
    have := young_le (show 0 < 12 * α by positivity) X (E * m)
    have e : (E * m) ^ 2 / (4 * (12 * α)) = E ^ 2 / (48 * α) * m ^ 2 := by
      field_simp; ring
    nlinarith [this, e]
  have F0 : β * m * p ≤ δ / 4 * (m * p ^ 2) + β ^ 2 / δ * m := by
    have h := young_le (show 0 < δ / 4 by positivity) p β
    have e : β ^ 2 / (4 * (δ / 4)) = β ^ 2 / δ := by field_simp
    have h' : p * β ≤ δ / 4 * p ^ 2 + β ^ 2 / δ := by linarith [h, e]
    have := mul_le_mul_of_nonneg_left h' hm
    nlinarith [this]
  have F2 : lm * m ≤ lm * m ^ 2 + lm / 4 := lin_le_sq lm m hlm
  have F2' : (Lm + β ^ 2 / δ) * m ≤ lm * m := mul_le_mul_of_nonneg_right hLmlm hm
  have F3 := cubic_le (show 0 < δ / 4 by positivity) hG0 hm
  have F5 : Lx * X ≤ 12 * α * X ^ 2 + Lx ^ 2 / (48 * α) := by
    have := young_le (show 0 < 12 * α by positivity) X Lx
    have e : Lx ^ 2 / (4 * (12 * α)) = Lx ^ 2 / (48 * α) := by field_simp; ring
    nlinarith [this, e]
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hp0 : 0 ≤ p := by linarith
  have E1 : ε * X ^ 2 ≤ 8 * α * X ^ 2 := mul_le_mul_of_nonneg_right hε1 (sq_nonneg _)
  have E3 : ε * P ≤ δ / 4 * P := mul_le_mul_of_nonneg_right hε3 hP0
  have E4 : ε * (X * p) ≤ ρ * (X * p) := mul_le_mul_of_nonneg_right hε4 (by positivity)
  have E5 : ε * p ≤ σ * p := mul_le_mul_of_nonneg_right hε5 hp0
  have hm3 : δ / 4 * m ^ 3 ≤ δ / 4 * P := mul_le_mul_of_nonneg_left hP (by positivity)
  have hmp : δ / 4 * (m * p ^ 2) ≤ δ / 4 * P := mul_le_mul_of_nonneg_left hP' (by positivity)
  have S1 : 0 ≤ α * X ^ 2 := by positivity
  have S4 : 0 ≤ δ * P := by positivity
  have S5 : 0 ≤ c1 * X := by positivity
  linarith [F0, F1, F2, F2', F3, F5, E1, E3, E4, E5, hm3, hmp, S1, S4, S5]

/-! ## The drift bound -/

theorem cA_pos : 0 < cA κ := by
  unfold cA kk θ γ
  have := κ.positive (2 : Fin 5); have := κ.positive (4 : Fin 5); have := κ.positive (3 : Fin 5)
  positivity
theorem cB_le_cA : cB κ ≤ cA κ := by
  unfold cA cB kk θ γ
  have := κ.positive (2 : Fin 5); have := κ.positive (4 : Fin 5)
  nlinarith [sq_nonneg (κ.k (3 : Fin 5)), mul_pos (κ.positive (2 : Fin 5)) (κ.positive (4 : Fin 5))]

theorem phi_succ_left (z1 z2 : ℕ) :
    phi κ (z1 + 1) z2 - phi κ z1 z2 =
      (if z2 ≤ z1 then cA κ else cB κ) * (2 * ((z1 : ℝ) - z2) + 1) := by
  unfold phi
  by_cases h : z2 ≤ z1
  · rw [if_pos (by omega), if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]
    by_cases h' : z2 ≤ z1 + 1
    · rw [if_pos h']
      have e : (z2 : ℝ) = z1 + 1 := by exact_mod_cast (by omega : z2 = z1 + 1)
      rw [e]; push_cast; ring
    · rw [if_neg h']; push_cast; ring

theorem phi_succ_right (z1 z2 : ℕ) :
    phi κ z1 (z2 + 1) - phi κ z1 z2 =
      (if z2 + 1 ≤ z1 then cA κ else cB κ) * (1 - 2 * ((z1 : ℝ) - z2)) := by
  unfold phi
  by_cases h : z2 + 1 ≤ z1
  · rw [if_pos h, if_pos h, if_pos (by omega)]; push_cast; ring
  · rw [if_neg h, if_neg h]
    by_cases h' : z2 ≤ z1
    · rw [if_pos h']
      have e : (z2 : ℝ) = z1 := by exact_mod_cast (by omega : z2 = z1)
      push_cast; rw [e]; ring
    · rw [if_neg h']; push_cast; ring

/-- The composite coefficients. -/
noncomputable def cα : ℝ := γ κ * θ κ ^ 2
noncomputable def cβ : ℝ := cc κ * kk κ
noncomputable def cδ : ℝ := cd κ * η κ
noncomputable def cρ : ℝ := 8 * γ κ ^ 2 * θ κ
noncomputable def cσ : ℝ := 6 * μ κ * γ κ ^ 2
noncomputable def cE : ℝ := 2 * kk κ * cb κ + θ κ * cd κ
noncomputable def clm : ℝ := μ κ * cd κ + kk κ * cb κ + cβ κ ^ 2 / cδ κ
noncomputable def cLx : ℝ := γ κ * cb κ + θ κ * cA κ
noncomputable def cLq : ℝ := 2 * μ κ * cA κ + kk κ * cb κ

/-- The constant of the drift bound. -/
noncomputable def cK : ℝ :=
  (μ κ * cA κ + μ κ * cB κ) + clm κ / 4 +
    4 * (cE κ ^ 2 / (48 * cα κ) + clm κ) ^ 3 / (27 * (cδ κ / 4) ^ 2) + cLq κ ^ 2 / cβ κ +
      cLx κ ^ 2 / (48 * cα κ)

/-- The weight of the norm-like function. -/
noncomputable def cε : ℝ := min (min (min (min (8 * cα κ) (cβ κ / 8)) (cδ κ / 4)) (cρ κ)) (cσ κ)

/-- **The norm-like function** `ε (x² + |q| + (q⁺)² + x |q| + z₁ z₂ (z₁ + z₂ − 1))`. -/
noncomputable def fLyap (n : Fin 3 → ℕ) : ℝ :=
  cε κ * ((n 2 : ℝ) ^ 2 + |(n 0 : ℝ) - n 1| + (max ((n 0 : ℝ) - n 1) 0) ^ 2 +
    (n 2 : ℝ) * |(n 0 : ℝ) - n 1| + (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1))

theorem params_pos : 0 < μ κ ∧ 0 < η κ ∧ 0 < kk κ ∧ 0 < γ κ ∧ 0 < θ κ :=
  ⟨κ.positive _, κ.positive _, κ.positive _, κ.positive _, κ.positive _⟩


theorem cK_ge_I :
    μ κ * cA κ + clm κ / 4 + 4 * (cE κ ^ 2 / (48 * cα κ) + clm κ) ^ 3 / (27 * (cδ κ / 4) ^ 2) +
      cLq κ ^ 2 / cβ κ + (γ κ * cb κ + θ κ * cA κ) ^ 2 / (48 * cα κ) ≤ cK κ := by
  obtain ⟨hμ, -, -, -, -⟩ := params_pos κ
  have : 0 ≤ μ κ * cB κ := mul_nonneg hμ.le (by unfold cB; positivity)
  unfold cK cLx; linarith

theorem cK_ge_II :
    (μ κ * cA κ + μ κ * cB κ) + clm κ / 4 +
      4 * (cE κ ^ 2 / (48 * cα κ) + clm κ) ^ 3 / (27 * (cδ κ / 4) ^ 2) +
      (γ κ * cb κ + θ κ * cB κ) ^ 2 / (48 * cα κ) ≤ cK κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hα : 0 < cα κ := by unfold cα; positivity
  have hβ : 0 < cβ κ := by unfold cβ cc; positivity
  have h1 : (γ κ * cb κ + θ κ * cB κ) ^ 2 / (48 * cα κ) ≤ cLx κ ^ 2 / (48 * cα κ) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    unfold cLx
    have hb : 0 < cb κ := by unfold cb; positivity
    have hB : 0 < cB κ := by unfold cB; positivity
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left (cB_le_cA κ) hθ.le]) 2
  have : 0 ≤ cLq κ ^ 2 / cβ κ := by positivity
  unfold cK; linarith

set_option maxHeartbeats 1000000 in
/-- **Foster–Lyapunov drift bound for the antithetic closed loop.** -/
theorem drift_lyap_le (n : Fin 3 → ℕ) :
    (closedLoop.jumpSystem κ).drift (lyap κ) n ≤ -fLyap κ n + cK κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hα : 0 < cα κ := by unfold cα; positivity
  have hβ : 0 < cβ κ := by unfold cβ cc; positivity
  have hδ : 0 < cδ κ := by unfold cδ cd; positivity
  have hρ : 0 < cρ κ := by unfold cρ; positivity
  have hσ : 0 < cσ κ := by unfold cσ; positivity
  have hA := cA_pos κ
  have hBA := cB_le_cA κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hb : 0 < cb κ := by unfold cb; positivity
  have hcc : 0 < cc κ := by unfold cc; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  have hE : 0 ≤ cE κ := by unfold cE; positivity
  have hLx : 0 ≤ cLx κ := by unfold cLx; positivity
  have hLq : 0 ≤ cLq κ := by unfold cLq; positivity
  have hε0 : 0 ≤ cε κ := by
    unfold cε; refine le_min (le_min (le_min (le_min ?_ ?_) ?_) ?_) ?_ <;> positivity
  have hε1 : cε κ ≤ 8 * cα κ := by
    unfold cε; exact (min_le_left _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _)))
  have hε2 : cε κ ≤ cβ κ / 8 := by
    unfold cε; exact (min_le_left _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _)))
  have hε3 : cε κ ≤ cδ κ / 4 := by
    unfold cε; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε4 : cε κ ≤ cρ κ := by unfold cε; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε5 : cε κ ≤ cσ κ := by unfold cε; exact min_le_right _ _
  have hlm : μ κ * cd κ + kk κ * cb κ ≤ clm κ := by
    unfold clm; have : 0 ≤ cβ κ ^ 2 / cδ κ := by positivity
    linarith
  have hlm' : μ κ * cd κ + kk κ * cb κ + cβ κ ^ 2 / cδ κ ≤ clm κ := le_of_eq rfl
  rw [drift_lyap, phi_succ_left, phi_succ_right]
  set Z1 : ℝ := (n 0 : ℝ) with hZ1
  set Z2 : ℝ := (n 1 : ℝ) with hZ2
  set X : ℝ := (n 2 : ℝ) with hX
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hZ10 : 0 ≤ Z1 := Nat.cast_nonneg _
  have hZ20 : 0 ≤ Z2 := Nat.cast_nonneg _
  unfold fLyap
  rw [← hZ1, ← hZ2, ← hX]
  rcases lt_trichotomy (n 1) (n 0) with h | h | h
  · -- case `q ≥ 1`
    have hq : 1 ≤ Z1 - Z2 := by
      have : (n 1 : ℝ) + 1 ≤ n 0 := by exact_mod_cast h
      rw [hZ1, hZ2]; linarith
    rw [if_pos h.le, if_pos (show n 1 + 1 ≤ n 0 from h), abs_of_pos (by linarith),
      max_eq_left (by linarith)]
    have hP : Z2 ^ 3 ≤ Z1 * Z2 * (Z1 + Z2 - 1) := by
      have h1 : Z2 ≤ Z1 := by linarith
      have h2 : Z2 ≤ Z1 + Z2 - 1 := by linarith
      calc Z2 ^ 3 = Z2 * Z2 * Z2 := by ring
        _ ≤ Z1 * Z2 * (Z1 + Z2 - 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hZ20) h2 hZ20 (by positivity)
    have key := caseI_gen (α := cα κ) (β := cβ κ) (δ := cδ κ) (E := cE κ)
      (Lm := μ κ * cd κ + kk κ * cb κ) (lm := clm κ) (Lq := cLq κ)
      (Lx := γ κ * cb κ + θ κ * cA κ) (c0 := μ κ * cA κ) (c1 := μ κ * cc κ) (ε := cε κ)
      (K := cK κ) (m := Z2) (q := Z1 - Z2) (X := X) (P := Z1 * Z2 * (Z1 + Z2 - 1))
      hα hβ hδ hE (by positivity) hlm hLq (by positivity) (by positivity) hε0 hε1 hε2 hε3
      (cK_ge_I κ) hZ20 hq hX0 hP
    have e : μ κ * (cA κ * (2 * (Z1 - Z2) + 1) - cc κ * X + cd κ * Z2) +
        η κ * Z1 * Z2 * (cd κ * (1 - Z1 - Z2)) +
        kk κ * Z1 * (cb κ * (2 * X + 1) - cc κ * (Z1 - Z2)) +
        γ κ * X * (cb κ * (1 - 2 * X) + cc κ * (Z1 - Z2)) +
        θ κ * X * (cA κ * (1 - 2 * (Z1 - Z2)) + cc κ * X + cd κ * Z1) =
      -cβ κ * (Z1 - Z2) ^ 2 - 48 * cα κ * X ^ 2 - cβ κ * Z2 * (Z1 - Z2) + cE κ * Z2 * X -
        cδ κ * (Z1 * Z2 * (Z1 + Z2 - 1)) + cLq κ * (Z1 - Z2) + μ κ * cA κ +
        (μ κ * cd κ + kk κ * cb κ) * Z2 + (γ κ * cb κ + θ κ * cA κ) * X - μ κ * cc κ * X := by
      unfold cβ cα cE cδ cLq cA cb cc cd; ring
    linarith [key, e]
  · -- case `q = 0`
    have hq : Z1 = Z2 := by rw [hZ1, hZ2, h]
    rw [if_pos h.le, if_neg (by omega), hq, sub_self, abs_zero, max_eq_right le_rfl]
    have hP : Z2 ^ 3 ≤ Z2 * Z2 * (Z2 + Z2 - 1) := by
      rcases Nat.eq_zero_or_pos (n 1) with h0 | h0
      · have : Z2 = 0 := by rw [hZ2, h0]; simp
        rw [this]; norm_num
      · have : (1 : ℝ) ≤ Z2 := by rw [hZ2]; exact_mod_cast h0
        nlinarith [mul_nonneg hZ20 hZ20]
    have key := caseII_gen (α := cα κ) (δ := cδ κ) (E := cE κ)
      (Lm := μ κ * cd κ + kk κ * cb κ) (lm := clm κ) (Lx := γ κ * cb κ + θ κ * cB κ)
      (c0 := μ κ * cA κ + μ κ * cB κ) (c0' := μ κ * cA κ) (c1 := μ κ * cc κ) (ε := cε κ)
      (K := cK κ) (m := Z2) (X := X) (P := Z2 * Z2 * (Z2 + Z2 - 1))
      hα hδ (by positivity) hlm (by positivity) (by positivity) hε0 hε1 hε3
      (by have : 0 ≤ μ κ * cB κ := by positivity
          linarith)
      (cK_ge_II κ) hZ20 hX0 hP
    have e : μ κ * (cA κ * (2 * (Z2 - Z2) + 1) - cc κ * X + cd κ * Z2) +
        η κ * Z2 * Z2 * (cd κ * (1 - Z2 - Z2)) +
        kk κ * Z2 * (cb κ * (2 * X + 1) - cc κ * (Z2 - Z2)) +
        γ κ * X * (cb κ * (1 - 2 * X) + cc κ * (Z2 - Z2)) +
        θ κ * X * (cB κ * (1 - 2 * (Z2 - Z2)) + cc κ * X + cd κ * Z2) =
      -48 * cα κ * X ^ 2 + cE κ * Z2 * X - cδ κ * (Z2 * Z2 * (Z2 + Z2 - 1)) + μ κ * cA κ +
        (μ κ * cd κ + kk κ * cb κ) * Z2 + (γ κ * cb κ + θ κ * cB κ) * X - μ κ * cc κ * X := by
      unfold cα cE cδ cB cA cb cc cd; ring
    have e2 : cε κ * (X ^ 2 + 0 + 0 ^ 2 + X * 0 + Z2 * Z2 * (Z2 + Z2 - 1)) =
        cε κ * (X ^ 2 + Z2 * Z2 * (Z2 + Z2 - 1)) := by ring
    linarith [key, e, e2]
  · -- case `q ≤ −1`
    have hp : 1 ≤ Z2 - Z1 := by
      have : (n 0 : ℝ) + 1 ≤ n 1 := by exact_mod_cast h
      rw [hZ1, hZ2]; linarith
    rw [if_neg (by omega), if_neg (by omega), abs_of_neg (by linarith),
      max_eq_right (by linarith)]
    have hP : Z1 ^ 3 ≤ Z1 * Z2 * (Z1 + Z2 - 1) := by
      have h1 : Z1 ≤ Z2 := by linarith
      have h2 : Z1 ≤ Z1 + Z2 - 1 := by linarith
      calc Z1 ^ 3 = Z1 * Z1 * Z1 := by ring
        _ ≤ Z1 * Z2 * (Z1 + Z2 - 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hZ10) h2 hZ10 (by nlinarith)
    have hP' : Z1 * (Z2 - Z1) ^ 2 ≤ Z1 * Z2 * (Z1 + Z2 - 1) := by
      rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
      · have : Z1 = 0 := by rw [hZ1, h0]; simp
        rw [this]; norm_num
      · have h1 : (1 : ℝ) ≤ Z1 := by rw [hZ1]; exact_mod_cast h0
        have h3 : 0 ≤ 3 * Z1 - 1 := by linarith
        have h4 : (Z1 + 1) * (3 * Z1 - 1) ≤ Z2 * (3 * Z1 - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) h3
        have h5 : (Z2 - Z1) ^ 2 ≤ Z2 * (Z1 + Z2 - 1) := by nlinarith
        have := mul_le_mul_of_nonneg_left h5 hZ10
        linarith
    have key := caseIII_gen (α := cα κ) (β := cβ κ) (δ := cδ κ) (ρ := cρ κ) (σ := cσ κ)
      (E := cE κ) (Lm := μ κ * cd κ + kk κ * cb κ) (lm := clm κ)
      (Lx := γ κ * cb κ + θ κ * cB κ) (c0 := μ κ * cA κ + μ κ * cB κ) (c0' := μ κ * cB κ)
      (c1 := μ κ * cc κ) (ε := cε κ) (K := cK κ) (m := Z1) (p := Z2 - Z1) (X := X)
      (P := Z1 * Z2 * (Z1 + Z2 - 1))
      hα hβ hδ hρ.le hσ.le (by positivity) hlm' (by positivity) (by positivity) hε0 hε1 hε3 hε4 hε5
      (by have : 0 ≤ μ κ * cA κ := by positivity
          linarith)
      (cK_ge_II κ) hZ10 hp hX0 hP hP'
    have e : μ κ * (cB κ * (2 * (Z1 - Z2) + 1) - cc κ * X + cd κ * Z2) +
        η κ * Z1 * Z2 * (cd κ * (1 - Z1 - Z2)) +
        kk κ * Z1 * (cb κ * (2 * X + 1) - cc κ * (Z1 - Z2)) +
        γ κ * X * (cb κ * (1 - 2 * X) + cc κ * (Z1 - Z2)) +
        θ κ * X * (cB κ * (1 - 2 * (Z1 - Z2)) + cc κ * X + cd κ * Z1) =
      -48 * cα κ * X ^ 2 - cρ κ * (Z2 - Z1) * X - cσ κ * (Z2 - Z1) -
        cδ κ * (Z1 * Z2 * (Z1 + Z2 - 1)) + cE κ * Z1 * X + cβ κ * Z1 * (Z2 - Z1) + μ κ * cB κ +
        (μ κ * cd κ + kk κ * cb κ) * Z1 + (γ κ * cb κ + θ κ * cB κ) * X - μ κ * cc κ * X := by
      unfold cα cρ cσ cE cδ cβ cB cb cc cd; ring
    have e2 : cε κ * (X ^ 2 + -(Z1 - Z2) + 0 ^ 2 + X * -(Z1 - Z2) + Z1 * Z2 * (Z1 + Z2 - 1)) =
        cε κ * (X ^ 2 + (Z2 - Z1) + X * (Z2 - Z1) + Z1 * Z2 * (Z1 + Z2 - 1)) := by ring
    linarith [key, e, e2]

/-! ## Norm-like bounds -/

theorem cε_pos : 0 < cε κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  unfold cε cα cβ cδ cρ cσ cc cd
  refine lt_min (lt_min (lt_min (lt_min ?_ ?_) ?_) ?_) ?_ <;> positivity

theorem annih_nonneg (z1 z2 : ℕ) : 0 ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  rcases Nat.eq_zero_or_pos z1 with h | h
  · simp [h]
  rcases Nat.eq_zero_or_pos z2 with h' | h'
  · simp [h']
  have : (1 : ℝ) ≤ z1 := by exact_mod_cast h
  have : (1 : ℝ) ≤ z2 := by exact_mod_cast h'
  have : 0 ≤ (z1 : ℝ) + z2 - 1 := by linarith
  positivity

theorem min_cube_le (z1 z2 : ℕ) :
    ((min z1 z2 : ℕ) : ℝ) ^ 3 ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  rcases Nat.eq_zero_or_pos (min z1 z2) with h | h
  · rw [h]; simp only [Nat.cast_zero]; norm_num; exact annih_nonneg z1 z2
  have h1 : ((min z1 z2 : ℕ) : ℝ) ≤ z1 := by exact_mod_cast min_le_left _ _
  have h2 : ((min z1 z2 : ℕ) : ℝ) ≤ z2 := by exact_mod_cast min_le_right _ _
  have h0 : (1 : ℝ) ≤ ((min z1 z2 : ℕ) : ℝ) := by exact_mod_cast h
  have h3 : ((min z1 z2 : ℕ) : ℝ) ≤ (z1 : ℝ) + z2 - 1 := by linarith
  calc ((min z1 z2 : ℕ) : ℝ) ^ 3 = ((min z1 z2 : ℕ) : ℝ) * ((min z1 z2 : ℕ) : ℝ) *
        ((min z1 z2 : ℕ) : ℝ) := by ring
    _ ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) :=
      mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
        (by positivity)

theorem fLyap_nonneg (n : Fin 3 → ℕ) : 0 ≤ fLyap κ n := by
  unfold fLyap
  have := annih_nonneg (n 0) (n 1)
  have := (cε_pos κ).le
  positivity

theorem fLyap_ge (n : Fin 3 → ℕ) :
    cε κ * ((n 2 : ℝ) ^ 2 + |(n 0 : ℝ) - n 1| + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 3) ≤ fLyap κ n := by
  unfold fLyap
  have h1 := min_cube_le (n 0) (n 1)
  have h2 : 0 ≤ (max ((n 0 : ℝ) - n 1) 0) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (cε_pos κ).le
  linarith

/-- A count is bounded by the minimum plus the gap. -/
theorem coord_le_min_add (z1 z2 : ℕ) :
    (z1 : ℝ) ≤ ((min z1 z2 : ℕ) : ℝ) + |(z1 : ℝ) - z2| ∧
      (z2 : ℝ) ≤ ((min z1 z2 : ℕ) : ℝ) + |(z1 : ℝ) - z2| := by
  rcases le_total z1 z2 with h | h
  · rw [min_eq_left h]
    have : (z1 : ℝ) ≤ z2 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]; constructor <;> linarith
  · rw [min_eq_right h]
    have : (z2 : ℝ) ≤ z1 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; constructor <;> linarith

theorem finite_of_bounds (B : ℝ) (T : Set (Fin 3 → ℕ))
    (hT : ∀ n ∈ T, (n 0 : ℝ) ≤ B ∧ (n 1 : ℝ) ≤ B ∧ (n 2 : ℝ) ≤ B) : T.Finite := by
  refine (Fintype.piFinset fun _ : Fin 3 => Finset.range (⌈B⌉₊ + 1)).finite_toSet.subset ?_
  intro n hn
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  obtain ⟨h0, h1, h2⟩ := hT n hn
  rw [Finset.mem_range, Nat.lt_succ_iff]
  fin_cases i
  · exact_mod_cast h0.trans (Nat.le_ceil B)
  · exact_mod_cast h1.trans (Nat.le_ceil B)
  · exact_mod_cast h2.trans (Nat.le_ceil B)

theorem cast_le_cube (m : ℕ) : (m : ℝ) ≤ (m : ℝ) ^ 3 := by
  exact_mod_cast Nat.le_self_pow (by norm_num) m

theorem cast_le_sq (m : ℕ) : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
  exact_mod_cast Nat.le_self_pow (by norm_num) m

/-- `f` has finite sublevel sets. -/
theorem fLyap_finite (R : ℝ) : {n | fLyap κ n ≤ R}.Finite := by
  have hε := cε_pos κ
  refine finite_of_bounds (2 * (|R| / cε κ) + 2) _ fun n hn => ?_
  have h := (fLyap_ge κ n).trans hn
  have hR : (n 2 : ℝ) ^ 2 + |(n 0 : ℝ) - n 1| + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 3 ≤ |R| / cε κ := by
    rw [le_div_iff₀ hε]; nlinarith [le_abs_self R]
  have hx := cast_le_sq (n 2)
  have hm := cast_le_cube (min (n 0) (n 1))
  have hq := abs_nonneg ((n 0 : ℝ) - n 1)
  have hm0 : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) ^ 3 := by positivity
  have hx0 : (0 : ℝ) ≤ (n 2 : ℝ) ^ 2 := sq_nonneg _
  obtain ⟨c1, c2⟩ := coord_le_min_add (n 0) (n 1)
  have hRe : 0 ≤ |R| / cε κ := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

theorem lyap_ge (n : Fin 3 → ℕ) :
    cB κ / 4 * ((n 0 : ℝ) - n 1) ^ 2 + 32 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 +
      cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤ lyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hphi : cB κ * ((n 0 : ℝ) - n 1) ^ 2 ≤ phi κ (n 0) (n 1) := by
    unfold phi; split_ifs
    · exact mul_le_mul_of_nonneg_right (cB_le_cA κ) (sq_nonneg _)
    · exact le_rfl
  have hY := young_le (show 0 < 3 * cB κ / 4 by positivity) ((n 0 : ℝ) - n 1) (cc κ * (n 2 : ℝ))
  have e : (cc κ * (n 2 : ℝ)) ^ 2 / (4 * (3 * cB κ / 4)) = 64 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 := by
    unfold cc cB; field_simp; ring
  have hmin : ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤ (n 0 : ℝ) * (n 1 : ℝ) := by
    have h1 : ((min (n 0) (n 1) : ℕ) : ℝ) ≤ n 0 := by exact_mod_cast min_le_left _ _
    have h2 : ((min (n 0) (n 1) : ℕ) : ℝ) ≤ n 1 := by exact_mod_cast min_le_right _ _
    rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hd : 0 ≤ cd κ := by unfold cd; positivity
  have := mul_le_mul_of_nonneg_left hmin hd
  unfold lyap cb
  nlinarith [hY, e, hphi, this]

theorem lyap_nonneg (n : Fin 3 → ℕ) : 0 ≤ lyap κ n := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have := lyap_ge κ n
  have hB : 0 < cB κ := by unfold cB; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  have : 0 ≤ cB κ / 4 * ((n 0 : ℝ) - n 1) ^ 2 + 32 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 +
      cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem lyap_finite (R : ℝ) : {n | lyap κ n ≤ R}.Finite := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  set C := min (min (cB κ / 4) (32 / 3 * θ κ ^ 2)) (cd κ) with hC
  have hC0 : 0 < C := lt_min (lt_min (by positivity) (by positivity)) hd
  refine finite_of_bounds (2 * (|R| / C) + 2) _ fun n hn => ?_
  have h := (lyap_ge κ n).trans hn
  have h1 : C * (((n 0 : ℝ) - n 1) ^ 2 + (n 2 : ℝ) ^ 2 + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2) ≤ R := by
    have a1 : C * ((n 0 : ℝ) - n 1) ^ 2 ≤ cB κ / 4 * ((n 0 : ℝ) - n 1) ^ 2 :=
      mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (sq_nonneg _)
    have a2 : C * (n 2 : ℝ) ^ 2 ≤ 32 / 3 * θ κ ^ 2 * (n 2 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (sq_nonneg _)
    have a3 : C * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤ cd κ * ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    nlinarith
  have hR : ((n 0 : ℝ) - n 1) ^ 2 + (n 2 : ℝ) ^ 2 + ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 ≤ |R| / C := by
    rw [le_div_iff₀ hC0]; nlinarith [le_abs_self R]
  have hx := cast_le_sq (n 2)
  have hm := cast_le_sq (min (n 0) (n 1))
  have hq : |(n 0 : ℝ) - n 1| ≤ ((n 0 : ℝ) - n 1) ^ 2 + 1 := by
    rcases le_or_gt |(n 0 : ℝ) - n 1| 1 with h' | h'
    · nlinarith [sq_nonneg ((n 0 : ℝ) - n 1)]
    · have : |(n 0 : ℝ) - n 1| ≤ |(n 0 : ℝ) - n 1| ^ 2 := by nlinarith
      rw [sq_abs] at this; linarith
  obtain ⟨c1, c2⟩ := coord_le_min_add (n 0) (n 1)
  have : (0 : ℝ) ≤ ((n 0 : ℝ) - n 1) ^ 2 := sq_nonneg _
  have : (0 : ℝ) ≤ (n 2 : ℝ) ^ 2 := sq_nonneg _
  have : (0 : ℝ) ≤ ((min (n 0) (n 1) : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hRe : 0 ≤ |R| / C := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Irreducibility -/

/-- The count `(a, b, c)`. -/
def mk3 (a b c : ℕ) : Fin 3 → ℕ := ![a, b, c]

theorem eq_mk3 (n : Fin 3 → ℕ) : n = mk3 (n 0) (n 1) (n 2) := by
  funext i; fin_cases i <;> rfl

theorem step (r : Fin 5) (n : Fin 3 → ℕ) (hr : 0 < closedLoop.stochasticMassActionRate κ n r) :
    (closedLoop.jumpSystem κ).ReachPos n (closedLoop.jumpNextCount n r) :=
  Relation.ReflTransGen.single ⟨r, hr, rfl⟩

theorem s_ref (a b c : ℕ) : (closedLoop.jumpSystem κ).ReachPos (mk3 a b c) (mk3 (a + 1) b c) := by
  have h := step κ 0 (mk3 a b c) (by rw [(rate_eq κ _).1]; exact (params_pos κ).1)
  convert h using 1
  funext i; fin_cases i <;> simp [mk3, jumpNextCount, closedLoop, rxn]

theorem s_ann (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 (a + 1) (b + 1) c) (mk3 a b c) := by
  have h := step κ 1 (mk3 (a + 1) (b + 1) c) (by
    rw [(rate_eq κ _).2.1]; have := (params_pos κ).2.1
    show 0 < η κ * ((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ); positivity)
  convert h using 1
  funext i; fin_cases i <;> simp [mk3, jumpNextCount, closedLoop, rxn]

theorem s_act (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 (a + 1) b c) (mk3 (a + 1) b (c + 1)) := by
  have h := step κ 2 (mk3 (a + 1) b c) (by
    rw [(rate_eq κ _).2.2.1]; have := (params_pos κ).2.2.1
    show 0 < kk κ * ((a + 1 : ℕ) : ℝ); positivity)
  convert h using 1
  funext i; fin_cases i <;> simp [mk3, jumpNextCount, closedLoop, rxn]

theorem s_deg (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b (c + 1)) (mk3 a b c) := by
  have h := step κ 3 (mk3 a b (c + 1)) (by
    rw [(rate_eq κ _).2.2.2.1]; have := (params_pos κ).2.2.2.1
    show 0 < γ κ * ((c + 1 : ℕ) : ℝ); positivity)
  convert h using 1
  funext i; fin_cases i <;> simp [mk3, jumpNextCount, closedLoop, rxn]

theorem s_sen (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b (c + 1)) (mk3 a (b + 1) (c + 1)) := by
  have h := step κ 4 (mk3 a b (c + 1)) (by
    rw [(rate_eq κ _).2.2.2.2]; have := (params_pos κ).2.2.2.2
    show 0 < θ κ * ((c + 1 : ℕ) : ℝ); positivity)
  convert h using 1
  funext i; fin_cases i <;> simp [mk3, jumpNextCount, closedLoop, rxn]

theorem refN (a b c j : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b c) (mk3 (a + j) b c) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih => exact ih.trans (by rw [← add_assoc]; exact s_ref κ _ _ _)

theorem actN (a b c j : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 (a + 1) b c) (mk3 (a + 1) b (c + j)) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih => exact ih.trans (by rw [← add_assoc]; exact s_act κ _ _ _)

theorem senN (a b c j : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b (c + 1)) (mk3 a (b + j) (c + 1)) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih => exact ih.trans (by rw [← add_assoc]; exact s_sen κ _ _ _)

theorem degN (a b c j : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b (c + j)) (mk3 a b c) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
      have h : (closedLoop.jumpSystem κ).ReachPos (mk3 a b (c + (j + 1))) (mk3 a b (c + j)) := by
        rw [← add_assoc]; exact s_deg κ _ _ _
      exact h.trans ih

theorem annN (a b c j : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 (a + j) (b + j) c) (mk3 a b c) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
      have h : (closedLoop.jumpSystem κ).ReachPos (mk3 (a + (j + 1)) (b + (j + 1)) c)
          (mk3 (a + j) (b + j) c) := by
        rw [← add_assoc, ← add_assoc]; exact s_ann κ _ _ _
      exact h.trans ih

/-- From the empty count to every count. -/
theorem reach_from_zero (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 0 0 0) (mk3 a b c) := by
  have h1 := s_ref κ 0 0 0
  have h2 := actN κ 0 0 0 (c + 1)
  have h3 := senN κ 1 0 c (b + 1)
  have h4 := s_ann κ 0 b (c + 1)
  have h5 := s_deg κ 0 b c
  have h6 := refN κ 0 b c a
  simp only [zero_add] at h1 h2 h3 h4 h5 h6
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem remove_z2 (j : ℕ) : (closedLoop.jumpSystem κ).ReachPos (mk3 0 j 0) (mk3 0 0 0) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
      have h1 := s_ref κ 0 (j + 1) 0
      have h2 := s_ann κ 0 j 0
      simp only [zero_add] at h1 h2
      exact h1.trans (h2.trans ih)

theorem remove_z1 (j : ℕ) : (closedLoop.jumpSystem κ).ReachPos (mk3 j 0 0) (mk3 0 0 0) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
      have h1 := s_act κ j 0 0
      have h2 := s_sen κ (j + 1) 0 0
      have h3 := s_ann κ j 0 1
      have h4 := s_deg κ j 0 0
      simp only [zero_add] at h1 h2 h3 h4
      exact h1.trans (h2.trans (h3.trans (h4.trans ih)))

/-- From every count to the empty count. -/
theorem reach_zero (a b c : ℕ) :
    (closedLoop.jumpSystem κ).ReachPos (mk3 a b c) (mk3 0 0 0) := by
  have h1 := degN κ a b 0 c
  simp only [zero_add] at h1
  refine h1.trans ?_
  rcases le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h2 := annN κ 0 d 0 a
    rw [zero_add, add_comm d a] at h2
    exact h2.trans (remove_z2 κ d)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h2 := annN κ d 0 0 b
    rw [zero_add, add_comm d b] at h2
    exact h2.trans (remove_z1 κ d)

/-- **The closed loop is irreducible on `ℕ³`.** -/
theorem irreducible (n m : Fin 3 → ℕ) : (closedLoop.jumpSystem κ).ReachPos n m := by
  rw [eq_mk3 n, eq_mk3 m]
  exact (reach_zero κ _ _ _).trans (reach_from_zero κ _ _ _)

/-! ## Moment bounds -/

/-- `f / ε`. -/
noncomputable def fRaw (n : Fin 3 → ℕ) : ℝ :=
  (n 2 : ℝ) ^ 2 + |(n 0 : ℝ) - n 1| + (max ((n 0 : ℝ) - n 1) 0) ^ 2 +
    (n 2 : ℝ) * |(n 0 : ℝ) - n 1| + (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1)

theorem fLyap_eq (n : Fin 3 → ℕ) : fLyap κ n = cε κ * fRaw n := rfl

theorem fRaw_nonneg (n : Fin 3 → ℕ) : 0 ≤ fRaw n := by
  unfold fRaw; have := annih_nonneg (n 0) (n 1); positivity

theorem prod_le_annih (z1 z2 : ℕ) : (z1 : ℝ) * z2 ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  rcases Nat.eq_zero_or_pos z1 with h | h
  · simp [h]
  rcases Nat.eq_zero_or_pos z2 with h' | h'
  · simp [h']
  have : (1 : ℝ) ≤ z1 := by exact_mod_cast h
  have : (1 : ℝ) ≤ z2 := by exact_mod_cast h'
  have h0 : 0 ≤ (z1 : ℝ) * z2 := by positivity
  nlinarith

theorem prod_abs_le_annih (z1 z2 : ℕ) :
    (z1 : ℝ) * z2 * |(z1 : ℝ) - z2| ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  rcases Nat.eq_zero_or_pos z1 with h | h
  · simp [h]
  rcases Nat.eq_zero_or_pos z2 with h' | h'
  · simp [h']
  have h1 : (1 : ℝ) ≤ z1 := by exact_mod_cast h
  have h2 : (1 : ℝ) ≤ z2 := by exact_mod_cast h'
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_le]; constructor <;> linarith

theorem z1_abs_le (z1 z2 : ℕ) :
    (z1 : ℝ) * |(z1 : ℝ) - z2| ≤ (max ((z1 : ℝ) - z2) 0) ^ 2 + (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  have hA := prod_abs_le_annih z1 z2
  rcases le_total z2 z1 with h | h
  · have hR : (z2 : ℝ) ≤ z1 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    rcases Nat.eq_zero_or_pos z2 with h0 | h0
    · simp [h0]; nlinarith
    · have : (1 : ℝ) ≤ z2 := by exact_mod_cast h0
      have hq : 0 ≤ (z1 : ℝ) - z2 := by linarith
      rw [abs_of_nonneg hq] at hA
      have : (z2 : ℝ) * ((z1 : ℝ) - z2) ≤ (z1 : ℝ) * z2 * ((z1 : ℝ) - z2) := by
        have : (z2 : ℝ) ≤ z1 * z2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hq
      nlinarith
  · have hR : (z1 : ℝ) ≤ z2 := by exact_mod_cast h
    rw [max_eq_right (by linarith)]
    rcases Nat.eq_zero_or_pos z1 with h0 | h0
    · simp [h0]
    · have : (1 : ℝ) ≤ z1 := by exact_mod_cast h0
      have hz2 : (1 : ℝ) ≤ z2 := by linarith
      have : (z1 : ℝ) * |(z1 : ℝ) - z2| ≤ (z1 : ℝ) * z2 * |(z1 : ℝ) - z2| := by
        have : (z1 : ℝ) ≤ z1 * z2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      nlinarith

theorem z_le (z1 z2 : ℕ) :
    (z1 : ℝ) ≤ |(z1 : ℝ) - z2| + (z1 : ℝ) * z2 * ((z1 : ℝ) + z2 - 1) := by
  have h1 := (coord_le_min_add z1 z2).1
  have h2 := min_cube_le z1 z2
  have h3 := cast_le_cube (min z1 z2)
  linarith

/-- The exit rate is dominated by `1 + f/ε`. -/
theorem exitRate_le (n : Fin 3 → ℕ) :
    closedLoop.exitRate κ n ≤ (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ n
  have hsum : closedLoop.exitRate κ n = μ κ + η κ * (n 0 : ℝ) * (n 1 : ℝ) + kk κ * (n 0 : ℝ) +
      γ κ * (n 2 : ℝ) + θ κ * (n 2 : ℝ) := by
    have := Fin.sum_univ_five (fun r : Fin 5 => closedLoop.stochasticMassActionRate κ n r)
    rw [r0, r1, r2, r3, r4] at this
    exact this
  rw [hsum]
  have a1 := prod_le_annih (n 0) (n 1)
  have a2 := z_le (n 0) (n 1)
  have a3 := cast_le_sq (n 2)
  have hP := annih_nonneg (n 0) (n 1)
  have hF : (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) + |(n 0 : ℝ) - n 1| + (n 2 : ℝ) ^ 2 ≤
      fRaw n := by
    unfold fRaw; have := sq_nonneg (max ((n 0 : ℝ) - n 1) 0)
    have : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
    linarith
  have hF0 := fRaw_nonneg n
  have hqa := abs_nonneg ((n 0 : ℝ) - n 1)
  have hx2 : 0 ≤ (n 2 : ℝ) ^ 2 := sq_nonneg _
  have e1 : η κ * (n 0 : ℝ) * (n 1 : ℝ) ≤ η κ * fRaw n := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
  have e2 : kk κ * (n 0 : ℝ) ≤ kk κ * fRaw n := mul_le_mul_of_nonneg_left (by linarith) hk.le
  have e3 : γ κ * (n 2 : ℝ) ≤ γ κ * fRaw n := mul_le_mul_of_nonneg_left (by linarith) hγ.le
  have e4 : θ κ * (n 2 : ℝ) ≤ θ κ * fRaw n := mul_le_mul_of_nonneg_left (by linarith) hθ.le
  have e5 : 0 ≤ μ κ * fRaw n := by positivity
  nlinarith

theorem charge_eq (n : Fin 3 → ℕ) : linearObservable charge n = (n 0 : ℝ) - n 1 := by
  simp [linearObservable, charge, Fin.sum_univ_three]; ring

/-- The fluxes of the charge are dominated by `1 + f/ε`. -/
theorem rate_mul_charge_le (n : Fin 3 → ℕ) (r : closedLoop.R) :
    |closedLoop.stochasticMassActionRate κ n r * linearObservable charge n| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ n
  rw [charge_eq, abs_mul, abs_of_nonneg (closedLoop.stochasticMassActionRate_nonneg κ n r)]
  have hF0 := fRaw_nonneg n
  have hP := annih_nonneg (n 0) (n 1)
  have hsq : 0 ≤ (max ((n 0 : ℝ) - n 1) 0) ^ 2 := sq_nonneg _
  have hxq : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
  have hx2 : 0 ≤ (n 2 : ℝ) ^ 2 := sq_nonneg _
  have hqa := abs_nonneg ((n 0 : ℝ) - n 1)
  have hbig : ∀ c : ℝ, 0 ≤ c → c ≤ μ κ + η κ + kk κ + γ κ + θ κ →
      c * fRaw n ≤ (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := fun c hc hc' => by
    nlinarith
  have hfq : |(n 0 : ℝ) - n 1| ≤ fRaw n := by unfold fRaw; linarith
  have hfP : (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤ fRaw n := by unfold fRaw; linarith
  have hfx : (n 2 : ℝ) * |(n 0 : ℝ) - n 1| ≤ fRaw n := by unfold fRaw; linarith
  have hfz : (max ((n 0 : ℝ) - n 1) 0) ^ 2 + (n 0 : ℝ) * (n 1 : ℝ) * ((n 0 : ℝ) + n 1 - 1) ≤
      fRaw n := by unfold fRaw; linarith
  have b0 : closedLoop.stochasticMassActionRate κ n (0 : Fin 5) * |(n 0 : ℝ) - n 1| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
    rw [r0]
    exact (mul_le_mul_of_nonneg_left hfq hμ.le).trans (hbig _ hμ.le (by linarith))
  have b1 : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) * |(n 0 : ℝ) - n 1| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
    rw [r1]
    have h := prod_abs_le_annih (n 0) (n 1)
    calc η κ * (n 0 : ℝ) * (n 1 : ℝ) * |(n 0 : ℝ) - n 1|
        = η κ * ((n 0 : ℝ) * (n 1 : ℝ) * |(n 0 : ℝ) - n 1|) := by ring
      _ ≤ η κ * fRaw n := mul_le_mul_of_nonneg_left (h.trans hfP) hη.le
      _ ≤ _ := hbig _ hη.le (by linarith)
  have b2 : closedLoop.stochasticMassActionRate κ n (2 : Fin 5) * |(n 0 : ℝ) - n 1| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
    rw [r2]
    have h := z1_abs_le (n 0) (n 1)
    calc kk κ * (n 0 : ℝ) * |(n 0 : ℝ) - n 1| = kk κ * ((n 0 : ℝ) * |(n 0 : ℝ) - n 1|) := by ring
      _ ≤ kk κ * fRaw n := mul_le_mul_of_nonneg_left (h.trans hfz) hk.le
      _ ≤ _ := hbig _ hk.le (by linarith)
  have b3 : closedLoop.stochasticMassActionRate κ n (3 : Fin 5) * |(n 0 : ℝ) - n 1| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
    rw [r3, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hfx hγ.le).trans (hbig _ hγ.le (by linarith))
  have b4 : closedLoop.stochasticMassActionRate κ n (4 : Fin 5) * |(n 0 : ℝ) - n 1| ≤
      (μ κ + η κ + kk κ + γ κ + θ κ) * (1 + fRaw n) := by
    rw [r4, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hfx hθ.le).trans (hbig _ hθ.le (by linarith))
  fin_cases r
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4

theorem rate_le_exitRate (n : Fin 3 → ℕ) (r : closedLoop.R) :
    closedLoop.stochasticMassActionRate κ n r ≤ closedLoop.exitRate κ n :=
  Finset.single_le_sum (f := fun r => closedLoop.stochasticMassActionRate κ n r)
    (fun r _ => closedLoop.stochasticMassActionRate_nonneg κ n r) (Finset.mem_univ r)

theorem cK_nonneg : 0 ≤ cK κ := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hα : 0 < cα κ := by unfold cα; positivity
  have hβ : 0 < cβ κ := by unfold cβ cc; positivity
  have hδ : 0 < cδ κ := by unfold cδ cd; positivity
  have hA := cA_pos κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hb : 0 < cb κ := by unfold cb; positivity
  have hd : 0 < cd κ := by unfold cd; positivity
  have hlm : 0 ≤ clm κ := by unfold clm; positivity
  have h1 : 0 ≤ μ κ * cA κ + μ κ * cB κ := by positivity
  have h2 : 0 ≤ 4 * (cE κ ^ 2 / (48 * cα κ) + clm κ) ^ 3 / (27 * (cδ κ / 4) ^ 2) := by
    positivity
  have h3 : 0 ≤ cLq κ ^ 2 / cβ κ := by positivity
  have h4 : 0 ≤ cLx κ ^ 2 / (48 * cα κ) := by positivity
  unfold cK; linarith

/-! ## Ergodicity and the setpoint -/

/-- **Ergodicity of the antithetic closed loop** (Briat–Gupta–Khammash 2016), for every choice
of positive rates: there is a unique stationary distribution `π`, it charges every count, the
law of the chain converges to it in total variation from every count, `π` has finite moments
`∑ π f ≤ K`, and the stationary mean output is the setpoint `μ / θ`. -/
theorem closedLoop_ergodic :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ n, 0 < π n) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' n, π n * closedLoop.transition κ t n m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |closedLoop.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      (∀ ν : (Fin 3 → ℕ) → ℝ, (∀ n, 0 ≤ ν n) → HasSum ν 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' n, ν n * closedLoop.transition κ t n m = ν m) → ν = π) ∧
      ∑' n, π n * fLyap κ n ≤ cK κ ∧
      ∑' n, π n * (n 2 : ℝ) = κ.k rRef / κ.k rSense := by
  classical
  set J := closedLoop.jumpSystem κ with hJ
  have hK : 0 ≤ cK κ := cK_nonneg κ
  have hstoch : ∀ t, 0 ≤ t → ∀ c, HasSum (fun b => J.Pmin t c b) 1 := fun t ht c =>
    J.hasSum_Pmin_one_of_drift_affine (lyap κ) (lyap_nonneg κ) (lyap_finite κ) le_rfl hK
      (fun a => by
        have h1 := drift_lyap_le κ a
        have h2 := fLyap_nonneg κ a
        linarith) ht c
  obtain ⟨π, hπ0, hπ1, hinv, -, hpos, hconv, huniq⟩ := J.foster_lyapunov_ergodic (lyap κ)
    (fLyap κ) (lyap_nonneg κ) (fLyap_nonneg κ) (fLyap_finite κ) hK (drift_lyap_le κ) hstoch
    (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => irreducible κ a b)
    (Set.mem_univ 0)
  obtain ⟨hfs, hfle⟩ := J.tsum_invariant_mul_le (lyap κ) (fLyap κ) (lyap_nonneg κ)
    (fLyap_nonneg κ) hK (drift_lyap_le κ) hπ0 hπ1 hinv
  have hε := cε_pos κ
  have hraw : Summable fun n => π n * (1 + fRaw n) := by
    have h : Summable fun n => π n * fRaw n :=
      (hfs.div_const (cε κ)).congr fun n => by rw [fLyap_eq]; field_simp
    exact (hπ1.summable.add h).congr fun n => by ring
  set Ctot := μ κ + η κ + kk κ + γ κ + θ κ with hCtot
  have hexit0 : ∀ n, 0 ≤ closedLoop.exitRate κ n := fun n =>
    Finset.sum_nonneg fun r _ => closedLoop.stochasticMassActionRate_nonneg κ n r
  have hexit : Summable fun n => π n * closedLoop.exitRate κ n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hexit0 n))
      (fun n => by
        calc π n * closedLoop.exitRate κ n ≤ π n * (Ctot * (1 + fRaw n)) :=
              mul_le_mul_of_nonneg_left (exitRate_le κ n) (hπ0 n)
          _ = Ctot * (π n * (1 + fRaw n)) := by ring) (hraw.mul_left Ctot)
  have hst := closedLoop.isCMEStationary_of_invariant κ hπ0 hπ1.summable hinv hexit
  have hs0 : ∀ r, Summable fun n => π n * closedLoop.stochasticMassActionRate κ n r := fun r =>
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hπ0 n) (closedLoop.stochasticMassActionRate_nonneg κ n r))
      (fun n => mul_le_mul_of_nonneg_left (rate_le_exitRate κ n r) (hπ0 n)) hexit
  have hs1 : ∀ r, Summable fun n =>
      π n * closedLoop.stochasticMassActionRate κ n r * linearObservable charge n := fun r =>
    Summable.of_norm_bounded (hraw.mul_left Ctot) fun n => by
      rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hπ0 n)]
      calc π n * |closedLoop.stochasticMassActionRate κ n r * linearObservable charge n|
          ≤ π n * (Ctot * (1 + fRaw n)) :=
            mul_le_mul_of_nonneg_left (rate_mul_charge_le κ n r) (hπ0 n)
        _ = Ctot * (π n * (1 + fRaw n)) := by ring
  have hstat := closedLoop.tsum_mul_observableGenerator_linear_eq_zero κ hst charge hs0 hs1
  have hout : Summable fun n => π n * (n 2 : ℝ) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (Nat.cast_nonneg _))
      (fun n => by
        refine mul_le_mul_of_nonneg_left ?_ (hπ0 n)
        have h1 := cast_le_sq (n 2)
        have h2 : (n 2 : ℝ) ^ 2 ≤ fRaw n := by
          unfold fRaw
          have := abs_nonneg ((n 0 : ℝ) - n 1)
          have := sq_nonneg (max ((n 0 : ℝ) - n 1) 0)
          have : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
          have := annih_nonneg (n 0) (n 1)
          linarith
        linarith) hraw
  have hset := closedLoop_stochastic_setpoint κ π hπ1.summable hπ1.tsum_eq hout hstat
  exact ⟨π, fun n => hpos n (Set.mem_univ n), hπ1, hinv, fun n => hconv n (Set.mem_univ n),
    fun ν hν0 hν1 hνinv => huniq ν hν0 (fun b hb => absurd (Set.mem_univ b) hb) hν1 hνinv,
    hfle, hset⟩

/-- Unit rates. -/
def unitRates : closedLoop.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- **Instance**: with unit rates the closed loop is ergodic and its stationary mean output is
`1`. -/
theorem unitRates_ergodic :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ n, 0 < π n) ∧ HasSum π 1 ∧
      (∀ n, Tendsto (fun t => ∑' m, |closedLoop.transition unitRates t n m - π m|) atTop (𝓝 0)) ∧
      ∑' n, π n * (n 2 : ℝ) = 1 := by
  obtain ⟨π, h0, h1, -, h3, -, -, h6⟩ := closedLoop_ergodic unitRates
  refine ⟨π, h0, h1, h3, ?_⟩
  rw [h6]; simp [unitRates]

end Antithetic
end CRNT
