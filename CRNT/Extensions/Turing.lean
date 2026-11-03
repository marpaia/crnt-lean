import CRNT.Dynamics.RouthHurwitz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Basic

/-!
# Turing instability for two-species reaction–diffusion systems

Linearize a two-species reaction–diffusion system `u_t = D u_xx + f(u)` at a homogeneous
steady state, with reaction Jacobian `J = [[a, b], [c, d]]` and diagonal diffusion
`D = diag(d₁, d₂)`, `d₁, d₂ > 0`. The Fourier mode `cos(k x) v` evolves under the matrix
`J - k² D`, whose characteristic polynomial is
`X² - (a + d - (d₁ + d₂) q) X + h(q)`, `q = k²`,
`h(q) = (a - d₁ q)(d - d₂ q) - b c = d₁ d₂ q² - (d₂ a + d₁ d) q + det J`.

**Turing's theorem** (Turing 1952; Murray, *Mathematical Biology II*, §2.3): suppose the
steady state is stable without diffusion (`J` Hurwitz, i.e. `a + d < 0`, `det J > 0`). Then
some mode `q ≥ 0` is unstable (`J - qD` has a positive real eigenvalue) iff
`d₂ a + d₁ d > 0` and `(d₂ a + d₁ d)² > 4 d₁ d₂ det J`.

Main results:
* `CRNT.Turing.reaction_hurwitz_iff`: stability without diffusion.
* `CRNT.Turing.diffusionDrivenInstability_iff`: the Turing conditions (strict instability).
* `CRNT.Turing.exists_nonHurwitz_mode_iff`: the same with marginal modes included.
* `CRNT.Turing.no_instability_of_equal_diffusion`, `CRNT.Turing.opposite_signs`: equal
  diffusion rules out Turing instability; an instability needs an activator and an inhibitor.
* `CRNT.Turing.exists_pos_eigen_of_det_neg`, `CRNT.Turing.fourierMode_solves`,
  `CRNT.Turing.fourierMode_unbounded`: an unstable mode is an explicit, exponentially
  growing solution of the linearized reaction–diffusion PDE.
-/

namespace CRNT

namespace Turing

open Polynomial

/-- The characteristic polynomial `X² - (p + r) X + (p r - b c)` of `[[p, b], [c, r]]`,
in the form used by `hurwitz_quadratic_iff`. -/
noncomputable def charPoly (p b c r : ℝ) : ℂ[X] :=
  X ^ 2 + C ((-(p + r) : ℝ) : ℂ) * X + C ((p * r - b * c : ℝ) : ℂ)

/-- The mode polynomial `h(q) = det(J - q D)`. -/
def modeDet (a b c d d₁ d₂ q : ℝ) : ℝ := (a - d₁ * q) * (d - d₂ * q) - b * c

theorem charPoly_hurwitz_iff (p b c r : ℝ) :
    IsHurwitz (charPoly p b c r) ↔ p + r < 0 ∧ 0 < p * r - b * c := by
  rw [charPoly, hurwitz_quadratic_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- **Stability without diffusion.** -/
theorem reaction_hurwitz_iff (a b c d : ℝ) :
    IsHurwitz (charPoly a b c d) ↔ a + d < 0 ∧ 0 < a * d - b * c :=
  charPoly_hurwitz_iff a b c d

/-- The trace of every mode matrix of a reaction-stable system is negative, so a mode is
unstable exactly when its determinant changes sign. -/
theorem mode_hurwitz_iff {a b c d d₁ d₂ q : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hq : 0 ≤ q)
    (htr : a + d < 0) :
    IsHurwitz (charPoly (a - d₁ * q) b c (d - d₂ * q)) ↔ 0 < modeDet a b c d d₁ d₂ q := by
  rw [charPoly_hurwitz_iff, modeDet]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    nlinarith [mul_nonneg hd₁.le hq, mul_nonneg hd₂.le hq]

/-- **Turing's diffusion-driven instability criterion.** For a reaction-stable steady state,
some mode `q ≥ 0` has `det(J - qD) < 0` (hence a positive real eigenvalue) iff
`d₂ a + d₁ d > 0` and `(d₂ a + d₁ d)² > 4 d₁ d₂ det J`. -/
theorem diffusionDrivenInstability_iff {a b c d d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hdet : 0 < a * d - b * c) :
    (∃ q : ℝ, 0 ≤ q ∧ modeDet a b c d d₁ d₂ q < 0) ↔
      0 < d₂ * a + d₁ * d ∧ 4 * d₁ * d₂ * (a * d - b * c) < (d₂ * a + d₁ * d) ^ 2 := by
  have hdd : 0 < d₁ * d₂ := mul_pos hd₁ hd₂
  constructor
  · rintro ⟨q, hq, hneg⟩
    unfold modeDet at hneg
    have hq0 : 0 < q := by
      rcases hq.lt_or_eq with h | h
      · exact h
      · subst h; nlinarith
    constructor
    · nlinarith [mul_nonneg (mul_nonneg hd₁.le hd₂.le) (sq_nonneg q)]
    · nlinarith [sq_nonneg (2 * d₁ * d₂ * q - (d₂ * a + d₁ * d))]
  · rintro ⟨hB, hdisc⟩
    refine ⟨(d₂ * a + d₁ * d) / (2 * (d₁ * d₂)), by positivity, ?_⟩
    unfold modeDet
    have hne : (d₁ * d₂) ≠ 0 := hdd.ne'
    have key : (a - d₁ * ((d₂ * a + d₁ * d) / (2 * (d₁ * d₂)))) *
        (d - d₂ * ((d₂ * a + d₁ * d) / (2 * (d₁ * d₂)))) - b * c =
        (a * d - b * c) - (d₂ * a + d₁ * d) ^ 2 / (4 * (d₁ * d₂)) := by
      field_simp
      ring
    rw [key, sub_neg, lt_div_iff₀ (by positivity)]
    linarith

/-- **Turing's criterion with marginal modes.** For a reaction-stable steady state, some
mode `q ≥ 0` fails to be Hurwitz iff `d₂ a + d₁ d > 0` and
`(d₂ a + d₁ d)² ≥ 4 d₁ d₂ det J`. -/
theorem exists_nonHurwitz_mode_iff {a b c d d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hstable : IsHurwitz (charPoly a b c d)) :
    (∃ q : ℝ, 0 ≤ q ∧ ¬ IsHurwitz (charPoly (a - d₁ * q) b c (d - d₂ * q))) ↔
      0 < d₂ * a + d₁ * d ∧ 4 * d₁ * d₂ * (a * d - b * c) ≤ (d₂ * a + d₁ * d) ^ 2 := by
  obtain ⟨htr, hdet⟩ := (reaction_hurwitz_iff a b c d).mp hstable
  have hdd : 0 < d₁ * d₂ := mul_pos hd₁ hd₂
  constructor
  · rintro ⟨q, hq, hnot⟩
    rw [mode_hurwitz_iff hd₁ hd₂ hq htr, not_lt] at hnot
    unfold modeDet at hnot
    have hq0 : 0 < q := by
      rcases hq.lt_or_eq with h | h
      · exact h
      · subst h; nlinarith
    constructor
    · nlinarith [mul_nonneg (mul_nonneg hd₁.le hd₂.le) (sq_nonneg q)]
    · nlinarith [sq_nonneg (2 * d₁ * d₂ * q - (d₂ * a + d₁ * d))]
  · rintro ⟨hB, hdisc⟩
    refine ⟨(d₂ * a + d₁ * d) / (2 * (d₁ * d₂)), by positivity, ?_⟩
    rw [mode_hurwitz_iff hd₁ hd₂ (by positivity) htr, not_lt]
    unfold modeDet
    have hne : (d₁ * d₂) ≠ 0 := hdd.ne'
    have key : (a - d₁ * ((d₂ * a + d₁ * d) / (2 * (d₁ * d₂)))) *
        (d - d₂ * ((d₂ * a + d₁ * d) / (2 * (d₁ * d₂)))) - b * c =
        (a * d - b * c) - (d₂ * a + d₁ * d) ^ 2 / (4 * (d₁ * d₂)) := by
      field_simp
      ring
    rw [key, sub_nonpos, le_div_iff₀ (by positivity)]
    linarith

/-- **Equal diffusivities rule out Turing instability.** -/
theorem no_instability_of_equal_diffusion {a b c d δ : ℝ} (hδ : 0 < δ)
    (hstable : IsHurwitz (charPoly a b c d)) (q : ℝ) (hq : 0 ≤ q) :
    IsHurwitz (charPoly (a - δ * q) b c (d - δ * q)) := by
  obtain ⟨htr, hdet⟩ := (reaction_hurwitz_iff a b c d).mp hstable
  rw [mode_hurwitz_iff hδ hδ hq htr, modeDet]
  nlinarith [mul_nonneg hδ.le hq, mul_nonneg (mul_nonneg hδ.le hq) (mul_nonneg hδ.le hq)]

/-- **Activator–inhibitor structure.** A Turing instability forces the self-interactions to
have opposite signs (`a d < 0`) and the cross-interactions as well (`b c < 0`). -/
theorem opposite_signs {a b c d d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (htr : a + d < 0) (hdet : 0 < a * d - b * c) (hB : 0 < d₂ * a + d₁ * d) :
    a * d < 0 ∧ b * c < 0 := by
  have had : a * d < 0 := by
    rcases lt_or_ge 0 a with ha | ha
    · have : d < 0 := by linarith
      nlinarith
    · rcases lt_or_ge 0 d with hd | hd
      · nlinarith
      · nlinarith [mul_nonneg hd₂.le (neg_nonneg.mpr ha), mul_nonneg hd₁.le (neg_nonneg.mpr hd)]
  exact ⟨had, by linarith⟩

/-! ## Unstable modes are growing solutions of the linearized PDE -/

/-- A `2 × 2` matrix `[[p, b], [c, r]]` with negative determinant has a positive real
eigenvalue with a nonzero eigenvector. -/
theorem exists_pos_eigen_of_det_neg {p b c r : ℝ} (h : p * r - b * c < 0) :
    ∃ μ v₁ v₂ : ℝ, 0 < μ ∧ (v₁ ≠ 0 ∨ v₂ ≠ 0) ∧
      p * v₁ + b * v₂ = μ * v₁ ∧ c * v₁ + r * v₂ = μ * v₂ := by
  set D := (p + r) ^ 2 - 4 * (p * r - b * c) with hD
  have hD0 : 0 ≤ D := by nlinarith [sq_nonneg (p + r)]
  set μ := (p + r + Real.sqrt D) / 2 with hμ
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0
  have hsqrt_gt : |p + r| < Real.sqrt D := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hμpos : 0 < μ := by
    have := neg_abs_le (p + r)
    rw [hμ]; linarith
  -- `μ` is a root of the characteristic polynomial
  have hroot : μ ^ 2 - (p + r) * μ + (p * r - b * c) = 0 := by
    rw [hμ]; nlinarith [hsq]
  refine ⟨μ, ?_⟩
  by_cases hb : b = 0
  · subst hb
    -- triangular case: eigenvalues `p` and `r`
    have hpr : p * r < 0 := by linarith
    by_cases hμr : μ = r
    · refine ⟨0, 1, hμpos, Or.inr one_ne_zero, by ring, by rw [hμr]; ring⟩
    · refine ⟨μ - r, c, hμpos, Or.inl (sub_ne_zero.mpr hμr), ?_, by ring⟩
      have : (μ - p) * (μ - r) = 0 := by nlinarith [hroot]
      rcases mul_eq_zero.mp this with h1 | h1
      · have : μ = p := by linarith
        rw [this]; ring
      · exact absurd (by linarith : μ = r) hμr
  · refine ⟨b, μ - p, hμpos, Or.inl hb, by ring, ?_⟩
    nlinarith [hroot]

/-- The Fourier mode `u(t, x) = e^{μ t} cos(k x) v`. -/
noncomputable def fourierMode (μ k v : ℝ) (t x : ℝ) : ℝ :=
  Real.exp (μ * t) * Real.cos (k * x) * v

theorem fourierMode_hasDerivAt_t (μ k v t x : ℝ) :
    HasDerivAt (fun t => fourierMode μ k v t x) (μ * fourierMode μ k v t x) t := by
  unfold fourierMode
  have h := ((hasDerivAt_id t).const_mul μ).exp
  have := (h.mul_const (Real.cos (k * x))).mul_const v
  simp only [id_eq, mul_one] at this
  convert this using 1
  ring

theorem fourierMode_deriv_x (μ k v t : ℝ) :
    deriv (fun x => fourierMode μ k v t x) =
      fun x => -(Real.exp (μ * t) * Real.sin (k * x) * k * v) := by
  funext x
  unfold fourierMode
  have h := ((hasDerivAt_id x).const_mul k).cos
  have := ((h.const_mul (Real.exp (μ * t))).mul_const v)
  simp only [id_eq, mul_one] at this
  rw [this.deriv]
  ring

theorem fourierMode_deriv2_x (μ k v t x : ℝ) :
    deriv (deriv (fun x => fourierMode μ k v t x)) x = -(k ^ 2) * fourierMode μ k v t x := by
  rw [fourierMode_deriv_x]
  unfold fourierMode
  have h := ((hasDerivAt_id x).const_mul k).sin
  have := (((h.const_mul (Real.exp (μ * t))).mul_const k).mul_const v).neg
  simp only [id_eq, mul_one] at this
  rw [show (fun x => -(Real.exp (μ * t) * Real.sin (k * x) * k * v)) =
    -(fun y => Real.exp (μ * t) * Real.sin (k * y) * k * v) from rfl, this.deriv]
  ring

/-- **An eigenvector of `J - k² D` gives an exact solution of the linearized
reaction–diffusion system** `u₁_t = d₁ u₁_xx + a u₁ + b u₂`, `u₂_t = d₂ u₂_xx + c u₁ + d u₂`. -/
theorem fourierMode_solves {a b c d d₁ d₂ μ k v₁ v₂ : ℝ}
    (h₁ : (a - d₁ * k ^ 2) * v₁ + b * v₂ = μ * v₁)
    (h₂ : c * v₁ + (d - d₂ * k ^ 2) * v₂ = μ * v₂) (t x : ℝ) :
    HasDerivAt (fun t => fourierMode μ k v₁ t x)
        (d₁ * deriv (deriv (fun x => fourierMode μ k v₁ t x)) x +
          a * fourierMode μ k v₁ t x + b * fourierMode μ k v₂ t x) t ∧
      HasDerivAt (fun t => fourierMode μ k v₂ t x)
        (d₂ * deriv (deriv (fun x => fourierMode μ k v₂ t x)) x +
          c * fourierMode μ k v₁ t x + d * fourierMode μ k v₂ t x) t := by
  rw [fourierMode_deriv2_x, fourierMode_deriv2_x]
  constructor
  · convert fourierMode_hasDerivAt_t μ k v₁ t x using 1
    unfold fourierMode
    linear_combination (Real.exp (μ * t) * Real.cos (k * x)) * h₁
  · convert fourierMode_hasDerivAt_t μ k v₂ t x using 1
    unfold fourierMode
    linear_combination (Real.exp (μ * t) * Real.cos (k * x)) * h₂

/-- An unstable mode with nonzero amplitude grows without bound at `x = 0`. -/
theorem fourierMode_unbounded {μ k v : ℝ} (hμ : 0 < μ) (hv : v ≠ 0) (M : ℝ) :
    ∃ t : ℝ, M < |fourierMode μ k v t 0| := by
  have hva : 0 < |v| := abs_pos.mpr hv
  obtain ⟨t, ht⟩ : ∃ t : ℝ, M / |v| < Real.exp (μ * t) := by
    refine ⟨(abs (M / abs v) + 1) / μ, ?_⟩
    rw [mul_div_cancel₀ _ hμ.ne']
    calc M / |v| ≤ abs (M / abs v) := le_abs_self _
      _ < abs (M / abs v) + 1 := lt_add_one _
      _ ≤ Real.exp (abs (M / abs v) + 1) := by
        linarith [Real.add_one_le_exp (abs (M / abs v) + 1)]
  refine ⟨t, ?_⟩
  simp only [fourierMode, mul_zero, Real.cos_zero, mul_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  rwa [div_lt_iff₀ hva] at ht

/-- **Turing patterns.** Under the Turing conditions, a reaction-stable steady state admits an
exponentially growing, spatially periodic solution of the linearized reaction–diffusion
system. -/
theorem exists_growing_mode {a b c d d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hdet : 0 < a * d - b * c) (hB : 0 < d₂ * a + d₁ * d)
    (hdisc : 4 * d₁ * d₂ * (a * d - b * c) < (d₂ * a + d₁ * d) ^ 2) :
    ∃ μ k v₁ v₂ : ℝ, 0 < μ ∧ (v₁ ≠ 0 ∨ v₂ ≠ 0) ∧ ∀ t x : ℝ,
      HasDerivAt (fun t => fourierMode μ k v₁ t x)
          (d₁ * deriv (deriv (fun x => fourierMode μ k v₁ t x)) x +
            a * fourierMode μ k v₁ t x + b * fourierMode μ k v₂ t x) t ∧
        HasDerivAt (fun t => fourierMode μ k v₂ t x)
          (d₂ * deriv (deriv (fun x => fourierMode μ k v₂ t x)) x +
            c * fourierMode μ k v₁ t x + d * fourierMode μ k v₂ t x) t := by
  obtain ⟨q, hq, hneg⟩ := (diffusionDrivenInstability_iff hd₁ hd₂ hdet).mpr ⟨hB, hdisc⟩
  obtain ⟨μ, v₁, v₂, hμ, hv, h₁, h₂⟩ := exists_pos_eigen_of_det_neg (p := a - d₁ * q) (b := b)
    (c := c) (r := d - d₂ * q) hneg
  refine ⟨μ, Real.sqrt q, v₁, v₂, hμ, hv, fun t x => fourierMode_solves ?_ ?_ t x⟩
  · rw [Real.sq_sqrt hq]; exact h₁
  · rw [Real.sq_sqrt hq]; exact h₂

/-! ## Any number of species: equal diffusivities never destabilize -/

/-- **No Turing instability with equal diffusion (`n` species).** If every eigenvalue of the
reaction Jacobian `J` has negative real part, then with a common diffusion coefficient `δ ≥ 0`
every eigenvalue of every mode matrix `J - k² δ I` has negative real part: the modes are `J`
shifted by `-k² δ`. -/
theorem modes_stable_of_equal_diffusion {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : ∀ (μ : ℂ) (v : n → ℂ), v ≠ 0 → J.mulVec v = μ • v → μ.re < 0)
    {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 ≤ q) (μ : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (heig : (J - ((q * δ : ℝ) : ℂ) • (1 : Matrix n n ℂ)).mulVec v = μ • v) : μ.re < 0 := by
  have hJv : J.mulVec v = (μ + ((q * δ : ℝ) : ℂ)) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at heig
    rw [add_smul, ← heig]
    abel
  have := hJ _ v hv hJv
  simp only [Complex.add_re, Complex.ofReal_re] at this
  nlinarith [mul_nonneg hq hδ]

end Turing

end CRNT
