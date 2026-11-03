import CRNT.Dynamics.HopfAveraging
import CRNT.Dynamics.NormalFormCubic
import CRNT.Dynamics.HopfLyapunovCalibration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# The `O(R⁴)` remainder of the angular average of a general reduced planar field

This module supplies the **`O(R⁴)` remainder** that the field map of leaf **D16 (Hopf
bifurcation)** records as the last missing piece of the "angular averaging" step.

## 1. What is computed here

`CRNT.Hopf.radialDrift` (in `CRNT.Dynamics.HopfAveraging`) is the *angular average of the radial
growth rate* of a planar field `F : ℂ → ℂ`:

```
radialDrift F R = (1 / (2π)) · (1/R) · ∫₀^{2π} Re ( w̄ · F w ) dθ ,   w = R e^{iθ} .
```

`CRNT.Dynamics.HopfAveraging` proves that this average is *exact* for the **truncated** Hopf
normal form `F w = (α + iω) w + c₁ w |w|²` (`radialDrift_normalForm`): the answer is
`α R + Re c₁ R³`.  What was missing is the statement for a **general reduced field**, whose
Taylor expansion at the origin is

```
F w = λ w + q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄² + c₃₀ w³ + c₂₁ w² w̄ + c₁₂ w w̄² + c₀₃ w̄³ + R(w) ,
|R(w)| ≤ C |w|⁴ ,
```

i.e. with a controlled remainder of order four.  This module proves the corresponding
estimate:

```
| radialDrift F R − (Re λ · R + Re c₂₁ · R³) | ≤ C · R⁴      (R ≥ 0) ,
```

`radialDrift_remainder`.  The cubic coefficient `c₂₁` is the **resonant** coefficient: the
coefficient of the resonant monomial `w² w̄ = w |w|²`, exactly the coefficient computed by
`CRNT.Dynamics.NormalFormCubic.pushB21` and calibrated against the real-coordinate first
Lyapunov coefficient in `CRNT.Dynamics.HopfLyapunovCalibration`.

Two specialisations are also proved:

* `radialDrift_remainder_holomorphic`: for a field whose Taylor data are `λ w + c₂ w² + c₃ w³`
  (the hypothesis suggested for leaf D16) the average is `Re λ · R` up to `O(R⁴)`; the
  *non-resonant* cubic term `c₃ w³` averages to zero, which is the content of
  `CRNT.Dynamics.NormalFormCubic.cubic_resonance_w2wbar`;
* `radialDrift_remainder_resonant`: for a field whose Taylor data are `λ w + c₃ w |w|²` the
  average is `Re λ · R + Re c₃ · R³` up to `O(R⁴)`.

For a *family* of reduced fields `F μ` the averaged remainder
`averagedRemainder F T μ R = radialDrift (F μ) R − (Re λ μ · R + Re c₂₁ μ · R³)` is `O(R⁴)`
by `averagedRemainder_bound`.

## 2. The averaging computation

Write `w = R e^{iθ}`.  The radial drift integrand is `Re ( w̄ · F w ) / R`.  Expanding:

* `λ w` contributes `Re λ · R²` (a constant in `θ`);
* `c₂₁ w² w̄` contributes `Re c₂₁ · R⁴` (also a constant — the **resonant** monomial);
* every other monomial of degree `≤ 3` contributes a *non-constant* multiple of
  `e^{i n θ}` with `n ≠ 0`, and hence integrates to zero over a full period.

The vanishing of the non-constant terms is the content of `integral_exp_int_mul_I`
(the generalisation of `CRNT.Hopf.integral_exp_one_I`, `integral_exp_two_I`,
`integral_exp_three_I`, `integral_exp_neg_two_I` to an arbitrary integer frequency), and the
pointwise expansion is `conj_mul_monomial` / `mul_star_monomial`.

The remainder contributes at most `C |w|⁵` to the integrand `Re ( w̄ · R(w) )`, and averaging
does not increase that bound, so the averaged remainder is `≤ C R⁴` after the division by `R`.

## 3. The `C¹` averaged field and `CRNT.PlanarHopfData.FullRadialField`

`CRNT.Dynamics.HopfAveraging.fullRadialFieldOf` builds the repository's
`CRNT.PlanarHopfData.FullRadialField` for the **truncated** normal form only.
`fullRadialFieldOf_remainder` builds one for a **general** field with a remainder: the
averaged radial field is `G μ R = α μ · R + ℓ₁ μ · R³ + S μ R`, where `S μ R` is the averaged
remainder (which, by `averagedRemainder_bound`, is `O(R⁴)`), and the `C¹` regularity of `S` is
carried as the hypothesis `RemainderRadialField` — exactly the way the repository already
carries the averaged field itself as data in `CRNT.PlanarHopfData.FullRadialField`.

## 4. A numerical instance

`CRNT.Hopf.Examples` runs the estimate on the concrete field `F w = i w + w³ + w⁴`: its
angular average is `Re λ · R + Re c₂₁ · R³ = 0` — the linear part `i w` is purely imaginary
and the cubic term `w³` is not resonant — up to an error of order `R⁴`, which is
`radialDrift_remainder_quartic`.

## 5. What is *not* proved here

Differentiating the averaged remainder `S` under the integral sign (which is what the `C¹`
hypothesis of `RemainderRadialField` amounts to) is not carried out: `Mathlib` has no
Taylor-series machinery for `ℂ → ℂ` and no general "differentiate under the integral sign"
for the angular average.  This is the same boundary that
`CRNT.Dynamics.HopfPersistentOrbit` records for the rotation closure.

Depends on: `CRNT.Dynamics.HopfAveraging`, `CRNT.Dynamics.NormalFormCubic`,
`CRNT.Dynamics.HopfLyapunovCalibration`.
-/

set_option linter.ambiguousOpen false

open Complex Real MeasureTheory intervalIntegral Filter Topology

open scoped BigOperators

namespace CRNT

namespace Hopf

/-! ## 1. Angular integrals -/

/-- **The complex exponential of a full period is `1`.** -/
lemma exp_two_pi (n : ℤ) : Complex.exp ((↑n * Complex.I) * ↑(2 * Real.pi)) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I n
  have harg : ((↑n * Complex.I) * ↑(2 * Real.pi)) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact h

/-- **The angular integral of an exponential of integer frequency vanishes.**  For every
nonzero integer `n`,

```
∫₀^{2π} e^{i n θ} dθ = 0 .
```

This is the generalisation, to an arbitrary integer frequency, of the four identities
`CRNT.Hopf.integral_exp_one_I`, `integral_exp_two_I`, `integral_exp_three_I` and
`integral_exp_neg_two_I` of `CRNT.Dynamics.HopfAveraging`. -/
theorem integral_exp_int_mul_I {n : ℤ} (hn : n ≠ 0) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp ((n : ℂ) * Complex.I * θ) = 0 := by
  have hc : ((n : ℂ) * Complex.I : ℂ) ≠ 0 := by
    intro h
    have h1 : (n : ℂ) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 Complex.I_ne_zero
    have h2 : n = 0 := by
      have h3 := congrArg Complex.re h1
      norm_cast at h3
    exact absurd h2 hn
  rw [integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) (c := (n : ℂ) * Complex.I) hc]
  rw [exp_two_pi n]
  simp

/-- **The negation of an integer frequency.** -/
lemma neg_int_mul_eq (n : ℤ) (θ : ℝ) :
    -((n : ℂ) * Complex.I * θ) = ((-n : ℤ) : ℂ) * Complex.I * θ := by
  simp only [Int.cast_neg, neg_mul]

/-- **The angular integral of an exponential of *negative* integer frequency vanishes.** -/
theorem integral_exp_neg_int_mul_I {n : ℤ} (hn : n ≠ 0) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp (-((n : ℂ) * Complex.I * θ)) = 0 := by
  have heq : ∀ θ : ℝ, Complex.exp (-((n : ℂ) * Complex.I * θ))
      = Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ) := by
    intro θ
    exact congrArg Complex.exp (neg_int_mul_eq n θ)
  rw [intervalIntegral.integral_congr
      (f := fun θ : ℝ => Complex.exp (-((n : ℂ) * Complex.I * θ)))
      (g := fun θ : ℝ => Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ))
      (fun θ _ => heq θ)]
  exact integral_exp_int_mul_I (by omega)

/-- **A continuous function on `[0, 2π]` is interval integrable.** -/
lemma intervalIntegrable_of_continuous' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Continuous f) :
    IntervalIntegrable f volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hab := by positivity)]
  exact hf.integrableOn_Icc (a := 0) (b := 2 * Real.pi)

/-- **Additivity of the angular integral.** -/
lemma integral_add' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (0:ℝ)..(2 * Real.pi), (f x + g x)
      = (∫ x in (0:ℝ)..(2 * Real.pi), f x) + (∫ x in (0:ℝ)..(2 * Real.pi), g x) := by
  exact intervalIntegral.integral_add (intervalIntegrable_of_continuous' f hf)
    (intervalIntegrable_of_continuous' g hg)

/-- **The norm of a point of the circle of radius `R`.** -/
lemma norm_circle (R : ℝ) (θ : ℝ) (hR : 0 ≤ R) :
    ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖ = R := by
  have hns : Complex.normSq (R * Complex.exp (Complex.I * θ)) = R ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have hexp : Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal]
      norm_num
    rw [hexp]
    ring
  rw [Complex.norm_def, hns, Real.sqrt_sq hR]

/-- **The angular integral of a monomial in the exponential.**  For `c : ℂ`, `R : ℝ`, `m : ℕ`
and `n : ℤ`,

```
∫₀^{2π} c R^m e^{i n θ} dθ = 2π c R^m   if n = 0,     0   otherwise.
```

The nonzero-frequency case is `integral_exp_int_mul_I`; the zero-frequency case is the
integral of a constant. -/
lemma integral_exp_coeff (c : ℂ) (R : ℝ) (m : ℕ) (n : ℤ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        (c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ)
      = if n = 0 then 2 * Real.pi * (c * (R ^ m : ℂ)) else 0 := by
  have hconv : Set.EqOn
        (fun θ : ℝ => (c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ))
        (fun θ : ℝ => (c * (R ^ m : ℂ)) *
          (fun θ : ℝ => Complex.exp ((n : ℂ) * Complex.I * θ)) θ)
        (Set.uIcc 0 (2 * Real.pi)) := by
    intro θ _
    rfl
  rw [intervalIntegral.integral_congr hconv]
  by_cases hn : n = 0
  · have hzero : ∀ θ : ℝ, Complex.exp ((n : ℂ) * Complex.I * θ) = 1 := by
      intro θ
      rw [hn]
      simp
    have hconv2 : Set.EqOn
        (fun θ : ℝ => (c * (R ^ m : ℂ)) *
          (fun θ : ℝ => Complex.exp ((n : ℂ) * Complex.I * θ)) θ)
        (fun _ : ℝ => c * (R ^ m : ℂ)) (Set.uIcc 0 (2 * Real.pi)) := by
      intro θ _
      dsimp only
      rw [hzero θ]
      ring
    rw [intervalIntegral.integral_congr hconv2]
    rw [intervalIntegral.integral_const]
    simp [hn, Complex.ofReal_mul, sub_zero, mul_comm, mul_left_comm]
  · rw [intervalIntegral.integral_const_mul _ _]
    rw [integral_exp_int_mul_I hn]
    simp [hn]

/-! ## 2. Pointwise identities on the circle of radius `R` -/

/-- **The real part as the average of a complex number and its conjugate.** -/
lemma re_eq_add_star (z : ℂ) : (z + star z) / 2 = ↑(z.re : ℝ) := by
  rw [show star z = starRingEnd ℂ z from rfl]
  rw [← RCLike.re_eq_add_conj]
  congr 1

/-- **The angular integral of the real part of a complex-valued function.**  The real part
commutes with the (interval) integral; this is recorded in the form that avoids any
integrability hypothesis. -/
lemma integral_re_eq (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, Complex.re (f x) = (∫ x in a..b, ((f x + star (f x)) / 2)).re := by
  have h : ∫ x in a..b, ((f x + star (f x)) / 2) = ↑(∫ x in a..b, Complex.re (f x)) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    exact re_eq_add_star (f x)
  rw [h]
  rfl

/-- Complex conjugation fixes the real numbers. -/
lemma star_ofReal_ℂ (r : ℝ) : star (↑r : ℂ) = (↑r : ℂ) := RCLike.conj_ofReal r

/-- Complex conjugation sends `i` to `−i`. -/
lemma star_I_ℂ : star Complex.I = -Complex.I := RCLike.conj_I (K := ℂ)

/-- Complex conjugation commutes with the complex exponential. -/
lemma star_exp_ℂ (z : ℂ) : star (Complex.exp z) = Complex.exp (star z) :=
  (Complex.exp_conj z).symm

/-- Complex conjugation fixes the integers (viewed as complex numbers). -/
lemma star_intCast_ℂ (n : ℤ) : star (↑n : ℂ) = (↑n : ℂ) := by
  have h : (starRingEnd ℂ) (Int.cast n) = Int.cast ((starRingEnd ℤ) n) := by
    exact map_intCast (starRingEnd ℂ) n
  rw [show star (↑n : ℂ) = (starRingEnd ℂ) (Int.cast n) from rfl]
  rw [h]
  rfl

/-- **Complex conjugation of an exponential of integer frequency.** -/
lemma star_exp_int (n : ℤ) (θ : ℝ) :
    star (Complex.exp ((n : ℂ) * Complex.I * θ)) = Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ) := by
  rw [star_exp_ℂ]
  have h : star ((n : ℂ) * Complex.I * θ) = ((-n : ℤ) : ℂ) * Complex.I * θ := by
    rw [star_mul, star_mul, star_intCast_ℂ, star_I_ℂ, star_ofReal_ℂ]
    rw [← neg_int_mul_eq]
    ring
  rw [h]

/-- **Complex conjugation of a point of the circle.**  For `w = R e^{iθ}` with `R` real,
`w̄ = R e^{-iθ}`. -/
lemma star_circle (R : ℝ) (θ : ℝ) :
    star (R * Complex.exp (Complex.I * θ)) = R * Complex.exp (-(Complex.I * θ)) := by
  rw [star_mul, star_ofReal_ℂ, star_exp_ℂ]
  have h : star (Complex.I * (θ : ℝ)) = -(Complex.I * (θ : ℝ)) := by
    rw [star_mul, star_I_ℂ, star_ofReal_ℂ]
    ring
  rw [h]
  ring

/-- **The positive powers of `e^{iθ}`.** -/
lemma exp_I_pow (θ : ℝ) (m : ℕ) :
    Complex.exp (Complex.I * θ) ^ m = Complex.exp ((m : ℂ) * Complex.I * θ) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- **The positive powers of `e^{-iθ}`.** -/
lemma exp_neg_I_pow (θ : ℝ) (m : ℕ) :
    Complex.exp (-(Complex.I * θ)) ^ m = Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- **The angular phase** of a product of `m` copies of `e^{iθ}` and `n` copies of `e^{-iθ}`:
the integer `m − n`. -/
def phaseDiff (m n : ℕ) : ℤ := (m : ℤ) - (n : ℤ)

/-- The angular phase, read as a complex number. -/
lemma phaseDiff_cast (m n : ℕ) :
    ((phaseDiff m n : ℤ) : ℂ) = ((m : ℂ) - (n : ℂ) : ℂ) := by
  unfold phaseDiff
  push_cast
  ring

/-- **The phase of a product of exponentials.** -/
lemma phase_mul (θ : ℝ) (m n : ℕ) :
    Complex.exp (Complex.I * θ) ^ m * Complex.exp (-(Complex.I * θ)) ^ n
      = Complex.exp ((phaseDiff m n : ℂ) * Complex.I * θ) := by
  rw [exp_I_pow, exp_neg_I_pow, ← Complex.exp_add]
  congr 1
  rw [phaseDiff_cast]
  ring

/-- **The angular phase of the monomial `w^p w̄^q`** in the average of `w̄ · ( w^p w̄^q )`:
the integer `p − q − 1`. -/
def phase (p q : ℕ) : ℤ := phaseDiff p (q + 1)

/-- **The resonant monomial.**  The phase `p − q − 1` vanishes exactly when `p = q + 1`, that
is when the monomial is `w^p w̄^{p-1} = w |w|^{2(p-1)}`; in particular `p = 2, q = 1` gives the
resonant monomial `w² w̄ = w |w|²`. -/
lemma phase_eq_zero_iff {p q : ℕ} : phase p q = 0 ↔ p = q + 1 := by
  simp only [phase, phaseDiff]
  constructor
  · intro h
    omega
  · intro h
    subst h
    push_cast
    ring

/-- **The angular phase of the `w̄`-conjugate monomial.** -/
def phaseStar (p q : ℕ) : ℤ := phaseDiff (q + 1) p

/-- **The phase of the `w̄`-conjugate monomial** is the opposite of `phase`. -/
lemma phaseStar_eq_neg_phase (p q : ℕ) : phaseStar p q = -phase p q := by
  unfold phaseStar phase phaseDiff
  push_cast
  ring

/-- **The powers of a point of the circle.** -/
lemma circle_pow (R : ℝ) (θ : ℝ) (m : ℕ) :
    (↑R * Complex.exp (Complex.I * θ)) ^ m
      = ↑(R ^ m) * Complex.exp ((m : ℂ) * Complex.I * θ) := by
  rw [mul_pow, Complex.ofReal_pow, exp_I_pow]

/-- **The powers of the conjugate of a point of the circle.** -/
lemma circle_neg_pow (R : ℝ) (θ : ℝ) (m : ℕ) :
    (↑R * Complex.exp (-(Complex.I * θ))) ^ m
      = ↑(R ^ m) * Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  rw [mul_pow, Complex.ofReal_pow, exp_neg_I_pow]

/-- **The powers of the conjugate of a point of the circle.** -/
lemma star_circle_pow (R : ℝ) (θ : ℝ) (m : ℕ) :
    star (↑R * Complex.exp (Complex.I * θ)) ^ m
      = ↑(R ^ m) * Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  rw [star_circle, mul_pow, Complex.ofReal_pow, exp_neg_I_pow]

/-- **The radial factors of a monomial.** -/
lemma ofReal_pow_mul (R : ℝ) (p q : ℕ) :
    (↑R : ℂ) * (↑(R ^ p) : ℂ) * (↑(R ^ q) : ℂ) = (↑(R ^ (p + q + 1)) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  calc R * R ^ p * R ^ q = R ^ p * R ^ q * R := by ring
    _ = R ^ (p + q) * R := by rw [← pow_add]
    _ = R ^ (p + q + 1) := by rw [← pow_succ]

/-- **The phase of the product `e^{-iθ} e^{ipθ} e^{-iqθ}`.** -/
lemma phase_neg_mul (θ : ℝ) (p q : ℕ) :
    Complex.exp (-(Complex.I * θ)) * Complex.exp (Complex.I * θ) ^ p
        * Complex.exp (-(Complex.I * θ)) ^ q
      = Complex.exp ((phase p q : ℂ) * Complex.I * θ) := by
  calc Complex.exp (-(Complex.I * θ)) * Complex.exp (Complex.I * θ) ^ p
      * Complex.exp (-(Complex.I * θ)) ^ q
      = Complex.exp (Complex.I * θ) ^ p
        * (Complex.exp (-(Complex.I * θ)) * Complex.exp (-(Complex.I * θ)) ^ q) := by ring
    _ = Complex.exp (Complex.I * θ) ^ p * Complex.exp (-(Complex.I * θ)) ^ (q + 1) := by
        rw [pow_succ]
        ring
    _ = Complex.exp ((phase p q : ℂ) * Complex.I * θ) := by
        rw [phase_mul θ p (q + 1)]
        rfl

/-- **A monomial `a · w^p · w̄^q` of the Taylor expansion of a reduced planar field.** -/
def monomial (a : ℂ) (p q : ℕ) (w : ℂ) : ℂ := a * w ^ p * star w ^ q

/-- **The pointwise value of `w̄ · (a w^p w̄^q)` on the circle of radius `R`.**  The monomial
`a w^p w̄^q` contributes `a R^{p+q+1} e^{i(p-q-1)θ}`; the *phase* `p − q − 1` is zero exactly
for the resonant monomials. -/
lemma conj_mul_monomial (R : ℝ) (θ : ℝ) (a : ℂ) (p q : ℕ) :
    star (R * Complex.exp (Complex.I * θ)) * monomial a p q (R * Complex.exp (Complex.I * θ))
      = (a * (R ^ (p + q + 1) : ℂ)) * Complex.exp ((phase p q : ℂ) * Complex.I * θ) := by
  unfold monomial
  rw [star_circle_pow, star_circle, circle_pow]
  calc (↑R * Complex.exp (-(Complex.I * θ))) *
        (a * (↑(R ^ p) * Complex.exp ((p : ℂ) * Complex.I * θ))
          * (↑(R ^ q) * Complex.exp (-((q : ℂ) * Complex.I * θ))))
      = a * (↑R * (↑(R ^ p) : ℂ) * (↑(R ^ q) : ℂ))
          * (Complex.exp (-(Complex.I * θ)) * Complex.exp ((p : ℂ) * Complex.I * θ)
            * Complex.exp (-((q : ℂ) * Complex.I * θ))) := by ring
    _ = a * (↑(R ^ (p + q + 1)) : ℂ) *
        (Complex.exp (-(Complex.I * θ)) * Complex.exp (Complex.I * θ) ^ p
          * Complex.exp (-(Complex.I * θ)) ^ q) := by
        rw [ofReal_pow_mul]
        rw [← exp_I_pow θ p, ← exp_neg_I_pow θ q]
    _ = (a * (R ^ (p + q + 1) : ℂ)) * Complex.exp ((phase p q : ℂ) * Complex.I * θ) := by
        rw [phase_neg_mul θ p q, Complex.ofReal_pow]

/-- **A product of a number with one of its powers.** -/
lemma mul_pow_succ' (X : ℂ) (n : ℕ) : X * X ^ n = X ^ (n + 1) := by
  rw [mul_comm, ← pow_succ]

/-- **Conjugation swaps the exponents of a monomial.** -/
lemma star_monomial (a : ℂ) (p q : ℕ) (w : ℂ) :
    star (monomial a p q w) = monomial (star a) q p w := by
  simp only [monomial, star_mul, star_pow, star_star]
  ring

/-- **The pointwise value of `w · conj (a w^p w̄^q)` on the circle of radius `R`.**  The phase
is the opposite of that of `conj_mul_monomial`. -/
lemma mul_star_monomial (R : ℝ) (θ : ℝ) (a : ℂ) (p q : ℕ) :
    (R * Complex.exp (Complex.I * θ)) *
        star (monomial a p q (R * Complex.exp (Complex.I * θ)))
      = (star a * (R ^ (p + q + 1) : ℂ)) * Complex.exp ((phaseStar p q : ℂ) * Complex.I * θ) := by
  rw [star_monomial]
  calc (↑R * Complex.exp (Complex.I * θ)) *
        (star a * (↑R * Complex.exp (Complex.I * θ)) ^ q
          * star (↑R * Complex.exp (Complex.I * θ)) ^ p)
      = star a * ((↑R * Complex.exp (Complex.I * θ)) *
          ((↑R * Complex.exp (Complex.I * θ)) ^ q
            * star (↑R * Complex.exp (Complex.I * θ)) ^ p)) := by ring
    _ = star a * ((↑R * Complex.exp (Complex.I * θ)) ^ (q + 1)
          * star (↑R * Complex.exp (Complex.I * θ)) ^ p) := by
        have hX : (↑R * Complex.exp (Complex.I * θ)) *
              ((↑R * Complex.exp (Complex.I * θ)) ^ q
                * star (↑R * Complex.exp (Complex.I * θ)) ^ p)
            = ((↑R * Complex.exp (Complex.I * θ)) * (↑R * Complex.exp (Complex.I * θ)) ^ q)
              * star (↑R * Complex.exp (Complex.I * θ)) ^ p := by ring
        rw [hX, mul_pow_succ']
    _ = star a * ((↑R * Complex.exp (Complex.I * θ)) * (↑R * Complex.exp (Complex.I * θ)) ^ q
          * star (↑R * Complex.exp (Complex.I * θ)) ^ p) := by
        rw [← mul_pow_succ']
    _ = star a * ((↑R * (↑(R ^ q) : ℂ) * (↑(R ^ p) : ℂ)) *
          (Complex.exp (Complex.I * θ) * Complex.exp ((q : ℂ) * Complex.I * θ)
            * Complex.exp (-((p : ℂ) * Complex.I * θ)))) := by
        rw [circle_pow, star_circle_pow]
        ring
    _ = star a * (↑(R ^ (q + p + 1)) : ℂ) *
        (Complex.exp (Complex.I * θ) ^ (q + 1) * Complex.exp (-(Complex.I * θ)) ^ p) := by
        rw [ofReal_pow_mul R q p]
        rw [← exp_I_pow θ q, ← exp_neg_I_pow θ p, mul_pow_succ']
        ring
    _ = star a * (↑(R ^ (q + p + 1)) : ℂ) *
        Complex.exp ((phaseDiff (q + 1) p : ℂ) * Complex.I * θ) := by
        rw [phase_mul θ (q + 1) p]
    _ = (star a * (R ^ (p + q + 1) : ℂ)) *
        Complex.exp ((phaseStar p q : ℂ) * Complex.I * θ) := by
      have h : q + p + 1 = p + q + 1 := by omega
      rw [h, Complex.ofReal_pow]
      rfl

/-- **The angular average of the real part of a monomial in the exponential vanishes.**  For
`n ≠ 0`,

```
∫₀^{2π} Re ( c R^m e^{i n θ} ) dθ = 0 .
```

This is the analytic counterpart of the fact that the non-resonant monomials average to
zero. -/
lemma integral_re_exp_coeff (c : ℂ) (R : ℝ) (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.re ((c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ)) = 0 := by
  rw [integral_re_eq]
  have hstar : ∀ θ : ℝ,
      star ((c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ))
        = (star c * (R ^ m : ℂ)) * Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ) := by
    intro θ
    rw [star_mul, star_mul, star_exp_int]
    simp only [star_pow, star_ofReal_ℂ]
    ring
  have hconv : ∀ θ : ℝ,
      ((c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ)
        + star ((c * (R ^ m : ℂ)) * Complex.exp ((n : ℂ) * Complex.I * θ))) / 2
        = ((c * (R ^ m : ℂ)) / 2) * Complex.exp ((n : ℂ) * Complex.I * θ)
          + ((star c * (R ^ m : ℂ)) / 2) * Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ) := by
    intro θ
    rw [hstar θ]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hconv θ)]
  rw [integral_add' (fun θ => ((c * (R ^ m : ℂ)) / 2) * Complex.exp ((n : ℂ) * Complex.I * θ))
      (fun θ => ((star c * (R ^ m : ℂ)) / 2) * Complex.exp (((-n : ℤ) : ℂ) * Complex.I * θ))
      (by fun_prop) (by fun_prop)]
  rw [intervalIntegral.integral_const_mul _ _, intervalIntegral.integral_const_mul _ _]
  rw [integral_exp_int_mul_I hn, integral_exp_int_mul_I (by omega)]
  simp

/-! ## 3. The cubic Taylor data of a general reduced planar field -/

/-- **The cubic Taylor data of a general reduced planar field.**  The field is, in complex
coordinates `w = u + i v`,

```
F w = λ w + q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄² + c₃₀ w³ + c₂₁ w² w̄ + c₁₂ w w̄² + c₀₃ w̄³ + O(|w|⁴) ,
```

`c₂₁` is the **resonant** cubic coefficient, the coefficient of the resonant monomial
`w² w̄ = w |w|²`; it is the coefficient computed by
`CRNT.Dynamics.NormalFormCubic.pushB21` and calibrated in
`CRNT.Dynamics.HopfLyapunovCalibration`. -/
structure CubicTaylorData where
  /-- The linear coefficient `λ`. -/ lam : ℂ
  /-- The coefficient of `w²`. -/ q20 : ℂ
  /-- The coefficient of `w w̄`. -/ q11 : ℂ
  /-- The coefficient of `w̄²`. -/ q02 : ℂ
  /-- The coefficient of `w³`. -/ c30 : ℂ
  /-- The coefficient of the resonant monomial `w² w̄ = w |w|²`. -/ c21 : ℂ
  /-- The coefficient of `w w̄²`. -/ c12 : ℂ
  /-- The coefficient of `w̄³`. -/ c03 : ℂ

/-- **The cubic Taylor polynomial of a general reduced planar field.** -/
def cubicTaylorPoly (T : CubicTaylorData) (w : ℂ) : ℂ :=
  monomial T.lam 1 0 w + monomial T.q20 2 0 w + monomial T.q11 1 1 w + monomial T.q02 0 2 w
    + monomial T.c30 3 0 w + monomial T.c21 2 1 w + monomial T.c12 1 2 w + monomial T.c03 0 3 w

/-- **The phases of the eight cubic monomials.**  The linear term and the resonant cubic term
have phase `0`; all the others have a nonzero phase and hence average to zero. -/
theorem phase_cubic :
    phase 1 0 = 0 ∧ phase 2 0 = 1 ∧ phase 1 1 = -1 ∧ phase 0 2 = -3
      ∧ phase 3 0 = 2 ∧ phase 2 1 = 0 ∧ phase 1 2 = -2 ∧ phase 0 3 = -4 := by
  simp only [phase, phaseDiff]
  decide

/-- **The real part of a power of a real number.** -/
lemma re_ofReal_pow (R : ℝ) (n : ℕ) : Complex.re ((↑R : ℂ) ^ n) = R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.mul_re, ih, Complex.ofReal_re, Complex.ofReal_im]
      ring_nf

/-- **The imaginary part of a power of a real number.** -/
lemma im_ofReal_pow (R : ℝ) (n : ℕ) : Complex.im ((↑R : ℂ) ^ n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.mul_im, ih, Complex.ofReal_re, Complex.ofReal_im]
      ring_nf

/-- **The real part of the resonant part of the cubic Taylor polynomial.** -/
lemma re_cubic_constant (T : CubicTaylorData) (R : ℝ) :
    Complex.re (T.lam * (R ^ 2 : ℂ)) + Complex.re (T.c21 * (R ^ 4 : ℂ))
      = T.lam.re * (R ^ 2) + T.c21.re * (R ^ 4) := by
  rw [Complex.mul_re, Complex.mul_re, re_ofReal_pow R 2, im_ofReal_pow R 2,
    re_ofReal_pow R 4, im_ofReal_pow R 4]
  ring_nf

/-- **The angular average of the cubic Taylor polynomial.**  The exact identity

```
∫₀^{2π} Re ( w̄ · (λ w + q₂₀ w² + … + c₀₃ w̄³) ) dθ = 2π ( Re λ · R² + Re c₂₁ · R⁴ ) ,
```

for `w = R e^{iθ}`: only the linear and the resonant cubic terms survive the angular
average, the resonant monomial `w² w̄ = w |w|²` being the only one whose phase vanishes. -/
theorem integral_re_conj_mul_cubicTaylorPoly (T : CubicTaylorData) (R : ℝ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.re (star (R * Complex.exp (Complex.I * θ))
          * cubicTaylorPoly T (R * Complex.exp (Complex.I * θ)))
      = 2 * Real.pi * (T.lam.re * (R ^ 2) + T.c21.re * (R ^ 4)) := by
  have hcomplex (θ : ℝ) :
      star (R * Complex.exp (Complex.I * θ)) * cubicTaylorPoly T (R * Complex.exp (Complex.I * θ))
        = (T.lam * (R ^ 2 : ℂ) + T.c21 * (R ^ 4 : ℂ))
          + ((T.q20 * (R ^ 3 : ℂ)) * Complex.exp ((1 : ℤ) * Complex.I * θ)
            + ((T.q11 * (R ^ 3 : ℂ)) * Complex.exp ((-1 : ℤ) * Complex.I * θ)
              + ((T.q02 * (R ^ 3 : ℂ)) * Complex.exp ((-3 : ℤ) * Complex.I * θ)
                + ((T.c30 * (R ^ 4 : ℂ)) * Complex.exp ((2 : ℤ) * Complex.I * θ)
                  + ((T.c12 * (R ^ 4 : ℂ)) * Complex.exp ((-2 : ℤ) * Complex.I * θ)
                    + (T.c03 * (R ^ 4 : ℂ)) * Complex.exp ((-4 : ℤ) * Complex.I * θ)))))) := by
    simp only [cubicTaylorPoly, mul_add]
    rw [conj_mul_monomial R θ T.lam 1 0, conj_mul_monomial R θ T.q20 2 0,
      conj_mul_monomial R θ T.q11 1 1, conj_mul_monomial R θ T.q02 0 2,
      conj_mul_monomial R θ T.c30 3 0, conj_mul_monomial R θ T.c21 2 1,
      conj_mul_monomial R θ T.c12 1 2, conj_mul_monomial R θ T.c03 0 3]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := phase_cubic
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
    ring
  have hre (θ : ℝ) :
      Complex.re (star (R * Complex.exp (Complex.I * θ))
          * cubicTaylorPoly T (R * Complex.exp (Complex.I * θ)))
        = (T.lam.re * (R ^ 2) + T.c21.re * (R ^ 4))
          + (Complex.re ((T.q20 * (R ^ 3 : ℂ)) * Complex.exp ((1 : ℤ) * Complex.I * θ))
            + (Complex.re ((T.q11 * (R ^ 3 : ℂ)) * Complex.exp ((-1 : ℤ) * Complex.I * θ))
              + (Complex.re ((T.q02 * (R ^ 3 : ℂ)) * Complex.exp ((-3 : ℤ) * Complex.I * θ))
                + (Complex.re ((T.c30 * (R ^ 4 : ℂ)) * Complex.exp ((2 : ℤ) * Complex.I * θ))
                  + (Complex.re ((T.c12 * (R ^ 4 : ℂ)) * Complex.exp ((-2 : ℤ) * Complex.I * θ))
                    + Complex.re ((T.c03 * (R ^ 4 : ℂ))
                      * Complex.exp ((-4 : ℤ) * Complex.I * θ))))))) := by
    rw [hcomplex]
    simp only [Complex.add_re]
    rw [re_cubic_constant]
  rw [intervalIntegral.integral_congr (fun θ _ => hre θ)]
  rw [integral_add' _ _ (by fun_prop) (by fun_prop), integral_add' _ _ (by fun_prop) (by fun_prop),
    integral_add' _ _ (by fun_prop) (by fun_prop), integral_add' _ _ (by fun_prop) (by fun_prop),
    integral_add' _ _ (by fun_prop) (by fun_prop), integral_add' _ _ (by fun_prop) (by fun_prop),
    integral_add' _ _ (by fun_prop) (by fun_prop)]
  rw [integral_re_exp_coeff T.q20 R 3 1 (by norm_num), integral_re_exp_coeff T.q11 R 3 (-1) (by norm_num),
    integral_re_exp_coeff T.q02 R 3 (-3) (by norm_num), integral_re_exp_coeff T.c30 R 4 2 (by norm_num),
    integral_re_exp_coeff T.c12 R 4 (-2) (by norm_num),
    integral_re_exp_coeff T.c03 R 4 (-4) (by norm_num)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]
  ring

/-! ## 4. The `O(R⁴)` remainder -/

/-- **The remainder of a reduced planar field** after its cubic Taylor expansion:
`remainder F T w = F w − cubicTaylorPoly T w`. -/
def remainder (F : ℂ → ℂ) (T : CubicTaylorData) (w : ℂ) : ℂ := F w - cubicTaylorPoly T w

/-- **The `O(R⁴)` remainder of the angular average of a general reduced field.**

Let `F : ℂ → ℂ` be a continuous reduced planar field whose Taylor expansion at the origin is
the cubic `cubicTaylorPoly T` up to a remainder of order four,

```
∀ w, ‖F w − cubicTaylorPoly T w‖ ≤ C |w|⁴ ,
```

then the angular average of the radial drift is

```
radialDrift F R = Re λ · R + Re c₂₁ · R³ + (error of order R⁴) ,
```

that is,

```
| radialDrift F R − (Re λ · R + Re c₂₁ · R³) | ≤ C · R⁴      (R ≥ 0) .
```

The cubic coefficient `c₂₁` is the resonant one, the coefficient of `w² w̄ = w |w|²`; the
quadratic and the non-resonant cubic terms of the Taylor expansion contribute nothing to the
average, because their phases are nonzero. -/
theorem radialDrift_remainder {F : ℂ → ℂ} {T : CubicTaylorData} {C : ℝ}
    (hcont : Continuous F)
    (hF : ∀ w : ℂ, ‖remainder F T w‖ ≤ C * ‖w‖ ^ 4) :
    ∀ R : ℝ, 0 ≤ R →
      |radialDrift F R - (T.lam.re * R + T.c21.re * R ^ 3)| ≤ C * R ^ 4 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    have h0 : radialDrift F 0 = 0 := by simp [radialDrift]
    simp [h0]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    have hsplit (θ : ℝ) :
        Complex.re (star (R * Complex.exp (Complex.I * θ)) * F (R * Complex.exp (Complex.I * θ)))
          = Complex.re (star (R * Complex.exp (Complex.I * θ))
              * cubicTaylorPoly T (R * Complex.exp (Complex.I * θ)))
            + Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ))) := by
      have h : star (R * Complex.exp (Complex.I * θ)) * F (R * Complex.exp (Complex.I * θ))
          = star (R * Complex.exp (Complex.I * θ))
              * cubicTaylorPoly T (R * Complex.exp (Complex.I * θ))
            + star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)) := by
          simp only [remainder]
          ring
      rw [h, Complex.add_re]
    have hid : ∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.re (star (R * Complex.exp (Complex.I * θ)) * F (R * Complex.exp (Complex.I * θ)))
      = 2 * Real.pi * (T.lam.re * (R ^ 2) + T.c21.re * (R ^ 4))
        + ∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ))) := by
      rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)]
      rw [integral_add' _ _ (by fun_prop) (by fun_prop)]
      rw [integral_re_conj_mul_cubicTaylorPoly T R]
    have hbound : ‖∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖
        ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), C * R ^ 5 := by
      refine intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 2 * Real.pi)
        (by positivity) ?_
        (intervalIntegrable_const (μ := volume) (a := 0) (b := 2 * Real.pi) (c := C * R ^ 5))
      refine Filter.Eventually.of_forall ?_
      intro θ hθ
      have hnorm : ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖ = R := norm_circle R θ hR
      have hE : ‖remainder F T (R * Complex.exp (Complex.I * θ))‖
          ≤ C * ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖ ^ 4 :=
        hF (R * Complex.exp (Complex.I * θ))
      have h1 : ‖Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖ ≤ ‖star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ))‖ :=
        Complex.abs_re_le_norm _
      have h2 : ‖star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ))‖
          = ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖
              * ‖remainder F T (R * Complex.exp (Complex.I * θ))‖ := by
        rw [norm_mul, norm_star]
      have hE' : ‖remainder F T (R * Complex.exp (Complex.I * θ))‖ ≤ C * R ^ 4 := by
        rw [hnorm] at hE
        exact hE
      have h3 : ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖
              * ‖remainder F T (R * Complex.exp (Complex.I * θ))‖
          ≤ R * (C * ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖ ^ 4) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left hE' (by positivity)
      calc ‖Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖ ≤ ‖star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ))‖ := h1
        _ = ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖
              * ‖remainder F T (R * Complex.exp (Complex.I * θ))‖ := h2
        _ ≤ R * (C * ‖(R * Complex.exp (Complex.I * θ) : ℂ)‖ ^ 4) := h3
        _ = C * R ^ 5 := by rw [hnorm]; ring
    have hE : ‖∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖
        ≤ 2 * Real.pi * (C * R ^ 5) := by
      calc ‖∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖
          ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), C * R ^ 5 := hbound
        _ = 2 * Real.pi * (C * R ^ 5) := by
          rw [intervalIntegral.integral_const]
          congr 1
          ring
    have hmain : radialDrift F R - (T.lam.re * R + T.c21.re * R ^ 3)
        = (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))) / (2 * Real.pi * R) := by
      rw [radialDrift, hid]
      field_simp
      ring
    calc |radialDrift F R - (T.lam.re * R + T.c21.re * R ^ 3)|
        = |(∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))) / (2 * Real.pi * R)| := by
          rw [hmain]
      _ = ‖∫ θ in (0:ℝ)..(2 * Real.pi), Complex.re (star (R * Complex.exp (Complex.I * θ)) * remainder F T (R * Complex.exp (Complex.I * θ)))‖ / (2 * Real.pi * R) := by
          rw [Real.norm_eq_abs, abs_div,
            abs_of_pos (mul_pos (by positivity : (0:ℝ) < 2 * Real.pi) hRpos)]
      _ ≤ (2 * Real.pi * (C * R ^ 5)) / (2 * Real.pi * R) := by
          rw [div_le_div_iff_of_pos_right (mul_pos (by positivity : (0:ℝ) < 2 * Real.pi) hRpos)]
          exact hE
      _ = C * R ^ 4 := by
          field_simp

/-! ## 5. The specialisations and the averaged field with remainder -/

/-- **The `O(R⁴)` remainder for a field with a holomorphic cubic Taylor expansion.**
For a field `F` whose Taylor expansion is `λ w + c₂ w² + c₃ w³` up to a remainder of order
four, the angular average is `Re λ · R` up to `O(R⁴)`: the cubic term `c₃ w³` is *not*
resonant and therefore contributes nothing to the average. -/
theorem radialDrift_remainder_holomorphic {F : ℂ → ℂ} {lam c₂ c₃ : ℂ} {C : ℝ}
    (hcont : Continuous F)
    (hF : ∀ w : ℂ, ‖F w - (lam * w + c₂ * w ^ 2 + c₃ * w ^ 3)‖ ≤ C * ‖w‖ ^ 4) :
    ∀ R : ℝ, 0 ≤ R → |radialDrift F R - lam.re * R| ≤ C * R ^ 4 := by
  intro R hR
  set T : CubicTaylorData := ⟨lam, c₂, 0, 0, c₃, 0, 0, 0⟩ with hT
  have hpoly : ∀ w : ℂ, cubicTaylorPoly T w = lam * w + c₂ * w ^ 2 + c₃ * w ^ 3 := by
    intro w
    simp [cubicTaylorPoly, monomial]
    ring
  have hrem : ∀ w : ℂ, ‖remainder F T w‖ ≤ C * ‖w‖ ^ 4 := by
    intro w
    rw [remainder, hpoly]
    exact hF w
  have h := radialDrift_remainder hcont hrem R hR
  rw [hT] at h
  simp only [Complex.zero_re, zero_mul, add_zero] at h
  exact h

/-- **The `O(R⁴)` remainder for a field with a resonant cubic term.**
For a field `F` whose Taylor expansion is `λ w + c₃ w |w|²` up to a remainder of order four,
the angular average is `Re λ · R + Re c₃ · R³` up to `O(R⁴)`. -/
theorem radialDrift_remainder_resonant {F : ℂ → ℂ} {lam c₃ : ℂ} {C : ℝ}
    (hcont : Continuous F)
    (hF : ∀ w : ℂ, ‖F w - (lam * w + c₃ * (w ^ 2 * star w))‖ ≤ C * ‖w‖ ^ 4) :
    ∀ R : ℝ, 0 ≤ R →
      |radialDrift F R - (lam.re * R + c₃.re * R ^ 3)| ≤ C * R ^ 4 := by
  intro R hR
  set T : CubicTaylorData := ⟨lam, 0, 0, 0, 0, c₃, 0, 0⟩ with hT
  have hpoly : ∀ w : ℂ, cubicTaylorPoly T w = lam * w + c₃ * (w ^ 2 * star w) := by
    intro w
    simp [cubicTaylorPoly, monomial]
    ring
  have hrem : ∀ w : ℂ, ‖remainder F T w‖ ≤ C * ‖w‖ ^ 4 := by
    intro w
    rw [remainder, hpoly]
    exact hF w
  have h := radialDrift_remainder hcont hrem R hR
  rwa [hT] at h

/-- **The averaged remainder of a general reduced field.**  For a family of reduced fields
`F μ` and a fixed cubic Taylor data `T`, the averaged remainder is

```
S μ R = radialDrift (F μ) R − (Re λ μ · R + Re c₂₁ μ · R³) ,
```

and `radialDrift_remainder` says exactly that `|S μ R| ≤ C R⁴`. -/
noncomputable def averagedRemainder (F : ℝ → (ℂ → ℂ)) (T : ℝ → CubicTaylorData)
    (μ : ℝ) (R : ℝ) : ℝ :=
  radialDrift (F μ) R - ((T μ).lam.re * R + (T μ).c21.re * R ^ 3)

/-- **The averaged remainder is `O(R⁴)`.** -/
theorem averagedRemainder_bound {F : ℝ → (ℂ → ℂ)} {T : ℝ → CubicTaylorData} {C : ℝ}
    (hcont : ∀ μ, Continuous (F μ))
    (hF : ∀ μ w, ‖remainder (F μ) (T μ) w‖ ≤ C * ‖w‖ ^ 4) :
    ∀ μ R, 0 ≤ R → |averagedRemainder F T μ R| ≤ C * R ^ 4 := by
  intro μ R hR
  have h := radialDrift_remainder (hcont μ) (hF μ) R hR
  simpa only [averagedRemainder] using h

/-! ### The `FullRadialField` of a general reduced field -/

/-- **A remainder field**: the averaged remainder `S μ R` of a general reduced planar field,
together with its `C¹` regularity (in the parameter and in the amplitude) and its `O(R⁴)`
bound.  The `C¹` regularity is what one needs to make the averaged field a
`CRNT.PlanarHopfData.FullRadialField`; it is carried as data, exactly as the repository
carries the averaged field itself. -/
structure RemainderRadialField (μ₁ R₀ : ℝ) (C : ℝ) where
  /-- The averaged remainder `S μ R`. -/ S : ℝ → ℝ → ℝ
  /-- The `μ`-partial of `S`. -/ S₁ : ℝ → ℝ → ℝ
  /-- The `R`-partial of `S`. -/ S₂ : ℝ → ℝ → ℝ
  /-- `S₁` is the `μ`-partial near the working point. -/
  hasDeriv_S₁ : ∀ᶠ v in 𝓝 (μ₁, R₀), HasDerivAt (fun μ => S μ v.2) (S₁ v.1 v.2) v.1
  /-- `S₂` is the `R`-partial near the working point. -/
  hasDeriv_S₂ : ∀ᶠ v in 𝓝 (μ₁, R₀), HasDerivAt (fun R => S v.1 R) (S₂ v.1 v.2) v.2
  /-- The `μ`-partial is continuous at the working point. -/
  cont_S₁ : ContinuousAt (Function.uncurry S₁) (μ₁, R₀)
  /-- The `R`-partial is continuous at the working point. -/
  cont_S₂ : ContinuousAt (Function.uncurry S₂) (μ₁, R₀)
  /-- The averaged remainder is of order `R⁴`. -/
  bound : ∀ μ R, |S μ R| ≤ C * R ^ 4

/-- **The averaged field of a general reduced field with a remainder is a
`FullRadialField`.**  The averaged radial field is

```
G μ R = α μ · R + ℓ₁ μ · R³ + S μ R
```

with `S` the averaged remainder (of order `R⁴`, by `RemainderRadialField.bound`); the `C¹`
regularity of `S` is the hypothesis `RemainderRadialField`.  This is the analogue of
`CRNT.Hopf.fullRadialFieldOf` (which is restricted to the truncated normal form) for a
*general* reduced field. -/
noncomputable def fullRadialFieldOf_remainder (α ℓ₁ : ℝ → ℝ) (dα dℓ : ℝ → ℝ)
    (hα : ∀ t, HasDerivAt α (dα t) t) (hℓ : ∀ t, HasDerivAt ℓ₁ (dℓ t) t)
    (hdα : Continuous dα) (hdℓ : Continuous dℓ)
    (Rem : RemainderRadialField μ₁ R₀ C)
    (hroot : α μ₁ * R₀ + ℓ₁ μ₁ * R₀ ^ 3 + Rem.S μ₁ R₀ = 0)
    (hnondeg : α μ₁ + 3 * ℓ₁ μ₁ * R₀ ^ 2 + Rem.S₂ μ₁ R₀ ≠ 0) :
    CRNT.PlanarHopfData.FullRadialField μ₁ R₀ := by
  have cα : Continuous α := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hα x).differentiableAt.continuousAt
  have cℓ : Continuous ℓ₁ := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hℓ x).differentiableAt.continuousAt
  refine
    { G := fun μ R => α μ * R + ℓ₁ μ * R ^ 3 + Rem.S μ R
      G₁ := fun μ R => dα μ * R + dℓ μ * R ^ 3 + Rem.S₁ μ R
      G₂ := fun μ R => α μ + 3 * ℓ₁ μ * R ^ 2 + Rem.S₂ μ R
      hasDeriv_G₁ := ?_
      hasDeriv_G₂ := ?_
      cont_G₁ := ?_
      cont_G₂ := ?_
      isRoot := ?_
      nondegenerate := ?_ }
  · filter_upwards [Rem.hasDeriv_S₁] with v hv
    have ha : HasDerivAt (fun μ => α μ * v.2) (dα v.1 * v.2) v.1 := by
      simpa using (hα v.1).mul_const v.2
    have hl : HasDerivAt (fun μ => ℓ₁ μ * v.2 ^ 3) (dℓ v.1 * v.2 ^ 3) v.1 := by
      simpa using (hℓ v.1).mul_const (v.2 ^ 3)
    have hs : HasDerivAt (fun μ => Rem.S μ v.2) (Rem.S₁ v.1 v.2) v.1 := hv
    have hsum := ha.add hl
    convert hsum.add hs using 1
  · filter_upwards [Rem.hasDeriv_S₂] with v hv
    have ha : HasDerivAt (fun R => α v.1 * R) (α v.1) v.2 := by
      simpa using (hasDerivAt_id v.2).const_mul (α v.1)
    have hl : HasDerivAt (fun R => ℓ₁ v.1 * R ^ 3) (3 * ℓ₁ v.1 * v.2 ^ 2) v.2 := by
      have h := hasDerivAt_pow 3 v.2
      simpa [mul_assoc, mul_left_comm, mul_comm] using h.const_mul (ℓ₁ v.1)
    have hs : HasDerivAt (fun R => Rem.S v.1 R) (Rem.S₂ v.1 v.2) v.2 := hv
    have hsum := ha.add hl
    convert hsum.add hs using 1
  · have ha : ContinuousAt (fun p : ℝ × ℝ => dα p.1 * p.2) (μ₁, R₀) := by
      exact ((hdα.comp continuous_fst).mul continuous_snd).continuousAt
    have hl : ContinuousAt (fun p : ℝ × ℝ => dℓ p.1 * p.2 ^ 3) (μ₁, R₀) := by
      exact ((hdℓ.comp continuous_fst).mul (continuous_snd.pow 3)).continuousAt
    have hs : ContinuousAt (fun p : ℝ × ℝ => Rem.S₁ p.1 p.2) (μ₁, R₀) := Rem.cont_S₁
    exact ha.add hl |>.add hs
  · have ha : ContinuousAt (fun p : ℝ × ℝ => α p.1) (μ₁, R₀) := by
      exact (cα.comp continuous_fst).continuousAt
    have hl : ContinuousAt (fun p : ℝ × ℝ => 3 * ℓ₁ p.1 * p.2 ^ 2) (μ₁, R₀) := by
      have h : Continuous (fun p : ℝ × ℝ => ℓ₁ p.1 * p.2 ^ 2) :=
        (cℓ.comp continuous_fst).mul (continuous_snd.pow 2)
      simpa [mul_assoc] using (h.const_mul 3).continuousAt
    have hs : ContinuousAt (fun p : ℝ × ℝ => Rem.S₂ p.1 p.2) (μ₁, R₀) := Rem.cont_S₂
    exact ha.add hl |>.add hs
  · exact hroot
  · exact hnondeg

/-! ## 6. A numerical instance -/

namespace Examples

/-- The example field `F w = i w + w³ + w⁴`: the Hopf normal form `i w` (whose linear part is
purely imaginary, so `Re λ = 0`), a *non-resonant* cubic term `w³`, and a quartic remainder
`w⁴`. -/
def quarticField : ℂ → ℂ := fun w => Complex.I * w + w ^ 3 + w ^ 4

/-- **The example field is continuous.** -/
theorem quarticField_cont : Continuous quarticField := by
  show Continuous (fun w : ℂ => Complex.I * w + w ^ 3 + w ^ 4)
  fun_prop

/-- **The `O(R⁴)` remainder for the example field `F w = i w + w³ + w⁴`.**  The angular average
of the radial drift of the example field is `Re λ · R + Re c₂₁ · R³ = 0` — the linear part is
purely imaginary and the cubic term `w³` is not resonant — up to an error of order `R⁴`:

```
| radialDrift quarticField R | ≤ R⁴      (R ≥ 0) .
```

This is the "numerical check" of the averaging estimate for a field that is neither the
truncated normal form nor resonant at cubic order. -/
theorem radialDrift_remainder_quartic (R : ℝ) (hR : 0 ≤ R) :
    |radialDrift quarticField R| ≤ R ^ 4 := by
  set T : CubicTaylorData := ⟨Complex.I, 0, 0, 0, 1, 0, 0, 0⟩ with hT
  have hpoly : ∀ w : ℂ, cubicTaylorPoly T w = Complex.I * w + w ^ 3 := by
    intro w
    simp [cubicTaylorPoly, monomial]
    ring
  have hrem : ∀ w : ℂ, ‖remainder quarticField T w‖ ≤ 1 * ‖w‖ ^ 4 := by
    intro w
    rw [remainder, hpoly]
    simp only [quarticField, sub_eq_add_neg]
    have heq : (Complex.I * w + w ^ 3 + w ^ 4 + -(Complex.I * w + w ^ 3)) = w ^ 4 := by ring
    rw [heq, norm_pow]
    simp
  have h := radialDrift_remainder quarticField_cont hrem R hR
  rw [hT] at h
  simp only [Complex.zero_re, Complex.I_re, zero_mul, add_zero, sub_zero, one_mul] at h
  exact h

end Examples

end Hopf

end CRNT
