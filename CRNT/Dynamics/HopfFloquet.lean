import CRNT.Dynamics.HopfLimitCycle
import CRNT.Oscillation.Basic

/-!
# Floquet multipliers of the Hopf limit cycle

The Hopf layer of this repository (`CRNT.Dynamics.HopfNormalForm`, `CRNT.Dynamics.HopfLimitCycle`)
knows the **normal form** of a Hopf crossing, the **first Lyapunov coefficient**
`ℓ₁ = Re c₁` (`CRNT.PlanarHopfData.firstLyapunov`), the **radial amplitude law**
`ṙ = α r + ℓ₁ r³` (`CRNT.PlanarHopfData.radialField`), and the **closed-form limit cycle** of the
truncated normal form, `w(t) = Rstar e^{i(θ₀ + Ω t)}`
(`CRNT.PlanarHopfData.hopfLimitCycle`).  What it does not have is any connection with the
**Floquet** vocabulary that the oscillation layer uses
(`CRNT.Oscillation.Floquet`: `MassActionFloquetData`, `monodromy`, `floquetPolynomial`,
`HasMultiplier`, `OneIsSimpleMultiplier`, `Nondegenerate`, `LinearlyStable`).

This module supplies that connection for the closed-form Hopf cycle.  The theory used is the
classical Hopf theory of Kuznetsov (*Elements of Applied Bifurcation Theory*, §3.5) and
Guckenheimer–Holmes (*Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector
Fields*, §3.4): the Poincaré normal form of a Hopf crossing is

`ẇ = (α(μ) + iω) w + c₁ w |w|²`,

the first Lyapunov coefficient is `ℓ₁ = Re c₁`, the radial equation is `ṙ = α r + ℓ₁ r³`, and the
nonzero radial equilibrium `Rstar` gives the bifurcating periodic orbit.  For that orbit the
Floquet theory says: the transverse (radial) Floquet exponent is the integral of the divergence of
the field along the orbit, and the transverse Floquet multiplier is its exponential over the
period.

## The classical Floquet/Lyapunov-coefficient connection

For the truncated normal form the divergence in polar coordinates is
`div F = 2α + 4 ℓ₁ r²`; on the cycle, where `α μ = −ℓ₁ Rstar²`, this is exactly

`div F |_{cycle} = 2 ℓ₁ Rstar²`,

so the **transverse Floquet exponent of the cycle is `2 ℓ₁ Rstar²`**, and the transverse Floquet
multiplier over the period `T = |2π/Ω|` is `exp (2 ℓ₁ Rstar² T)`.  Consequently the cycle is
**linearly stable exactly when `ℓ₁ < 0`** (supercritical: attracting transversally) and
**unstable when `ℓ₁ > 0`** (subcritical), and it is **Floquet nondegenerate exactly when
`ℓ₁ ≠ 0`**.  This is the classical Hopf/Floquet connection, and it is the content of
`hopfNontrivialMultiplier_norm_lt_one_iff`, `hopfTransverseMultiplier_ne_one_iff` and
`hopfCycle_floquetNondegenerate` below.

## What is computed here, and what is *not* available in Mathlib

`Mathlib` has **no `LinearMap.exp`** and **no theorem `det (exp A) = exp (trace A)`** (this is a
long-standing `Mathlib` TODO: the matrix exponential is not part of the library).  Consequently
the Floquet data of a *periodic* linear system with matrix coefficients — the monodromy matrix,
its characteristic polynomial, its roots — is **not available in `Mathlib` either**: the
oscillation layer has to *carry* such data as a structure
(`CRNT.Network.MassActionFloquetData`, whose `solves` field is the fundamental-matrix solution of
`Z' = J(P(t)) Z`).

For that reason the multiplier of the Hopf cycle is computed **directly in the complex
representation**: the normal form is a complex-linear ODE in `w ∈ ℂ`, the linearization of its
*complex-linear part* along the cycle is the complex multiplication by
`κ = λ + 3c₁ Rstar²` (with `λ = α μ + iω`), and the monodromy over the period is `exp (κ T)`.
The *transverse* multiplier of the planar cycle is the modulus
`‖exp (κ T)‖ = exp (Re κ · T)`, and `Re κ = α μ + 3 ℓ₁ Rstar² = 2 ℓ₁ Rstar²` on the cycle
(`hopfCycleExponent_re_lin`), which is exactly the divergence computation above.  The module
therefore computes the multiplier in closed form instead of assembling a
`MassActionFloquetData`, and states the stability and nondegeneracy criteria in the same shape
as the oscillation layer's `LinearlyStable` and `Nondegenerate`.

**A caveat about the complex multiplier.**  The *real* Jacobian of the cubic term
`w ↦ w |w|²` at `w` is the map `h ↦ |w|² h + 2 w Re(w̄ h)`, which is *not* complex-linear, so the
rotational part `Im κ` of the exponent above is not the angular Floquet exponent of the planar
cycle.  Only the *modulus* of the complex multiplier is the transverse multiplier of the
planar cycle, and this is why the nondegeneracy criterion below is stated for the transverse
multiplier (`hopfTransverseMultiplier`, `hopfTransverseMultiplier_ne_one_iff`) and why the
condition `hopfNontrivialMultiplier = 1` is strictly stronger than `ℓ₁ = 0`: it additionally
requires the rotational phase to be a multiple of `2π`
(`hopfNontrivialMultiplier_eq_one_iff`).

## What remains open

The cycle treated here is the cycle of the **truncated** normal form.  Its persistence for the
**full nonlinear mass-action field** is still open: that requires constructing
`CRNT.Dynamics.HopfRealizationData` (the transversal Poincaré section of the full field), which
needs the differentiable dependence of the flow on the initial point,
`CRNT.Network.MassActionFlowSmoothDependenceTarget`.  Moreover the nonlinear step from the
Floquet conditions to orbital asymptotic stability is still an open obligation in the oscillation
layer itself (`CRNT.Oscillation.FloquetOrbitalStabilityTarget`), and is not touched here.

Depends on: `CRNT.Dynamics.HopfLimitCycle`, `CRNT.Oscillation.Basic`.
-/

set_option maxHeartbeats 800000

open Complex

namespace CRNT

/-! ## A complex-exponential lemma: `exp z = 1` exactly on the lattice `2πi ℤ` -/

/-- Every complex number splits as its real part plus `i` times its imaginary part. -/
theorem complex_eq_re_add_im_mul_I (z : ℂ) : z = z.re + z.im * Complex.I := by
  apply Complex.ext <;> simp

/-- **The complex exponential takes the value `1` exactly on the imaginary lattice `2πi ℤ`.**
`exp z = 1` forces `Re z = 0` (because `‖exp z‖ = exp (Re z)`) and then forces
`cos (Im z) = 1`, i.e. `Im z` is an integer multiple of `2π`. -/
theorem complex_exp_eq_one_iff (z : ℂ) :
    Complex.exp z = 1 ↔ z.re = 0 ∧ ∃ n : ℤ, (n : ℝ) * (2 * Real.pi) = z.im := by
  constructor
  · intro h
    have hnorm : ‖Complex.exp z‖ = (1 : ℝ) := by rw [h]; simp
    rw [Complex.norm_exp] at hnorm
    have hz0 : z.re = 0 := (Real.exp_eq_one_iff _).mp hnorm
    have h' := h
    rw [complex_eq_re_add_im_mul_I z, Complex.exp_add, hz0, Complex.ofReal_zero,
      Complex.exp_zero, one_mul] at h'
    rw [Complex.exp_ofReal_mul_I] at h'
    have hparts := Complex.ext_iff.mp h'
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hparts
    exact ⟨hz0, Real.cos_eq_one_iff z.im |>.mp hparts.1⟩
  · rintro ⟨hz0, n, hn⟩
    have hcos : Real.cos z.im = 1 := by
      rw [← hn]
      exact Real.cos_int_mul_two_pi n
    have hsin : Real.sin z.im = 0 := by
      rw [← hn]
      have hcast : (n : ℝ) * (2 * Real.pi) = ((2 * n : ℤ) : ℝ) * Real.pi := by
        push_cast
        ring
      rw [hcast]
      exact Real.sin_int_mul_pi (2 * n)
    rw [complex_eq_re_add_im_mul_I z, Complex.exp_add, hz0, Complex.ofReal_zero,
      Complex.exp_zero, one_mul, Complex.exp_ofReal_mul_I, hcos, hsin]
    simp

namespace PlanarHopfData

variable (H : PlanarHopfData)

/-! ## The period, the Floquet exponent and the multiplier of the Hopf cycle -/

/-- **The period of the closed-form Hopf limit cycle.**  The cycle rotates at the constant
angular frequency `Ω = cycleFreq Rstar`, so its period is `T = |2π/Ω|`; it is strictly positive
whenever `Ω ≠ 0` (`hopfLimitCycle_period_pos`). -/
noncomputable def hopfCyclePeriod (Rstar : ℝ) : ℝ := |2 * Real.pi / H.cycleFreq Rstar|

/-- **The Floquet exponent of the closed-form Hopf limit cycle.**  The complex-linear part of the
linearized normal form along the cycle is the multiplication by `κ = λ + 3 c₁ Rstar²`, with
`λ = α μ + iω`; the real part of `κ` is `α μ + 3 ℓ₁ Rstar²`, which on the cycle
(`α μ = −ℓ₁ Rstar²`) is the classical transverse exponent `2 ℓ₁ Rstar²`
(`hopfCycleExponent_re`, `hopfCycleExponent_re_lin`). -/
noncomputable def hopfCycleExponent (Rstar : ℝ) : ℂ :=
  (2 : ℝ) * H.firstLyapunov * Rstar ^ 2 + Complex.I * (H.ω + 3 * H.c₁.im * Rstar ^ 2)

/-- **The nontrivial Floquet multiplier of the closed-form Hopf limit cycle of the truncated
normal form.**  The monodromy of the complex-linear variational equation along the cycle, over
the period `T = hopfCyclePeriod Rstar`, is the exponential of the Floquet exponent `κ T`.  Its
modulus is the *transverse* Floquet multiplier of the planar cycle, `exp (2 ℓ₁ Rstar² T)`
(`norm_hopfNontrivialMultiplier`, `hopfTransverseMultiplier_eq_norm`); the rotational part of
`κ` is recorded by the multiplier but is not the angular Floquet exponent of the planar cycle,
because the real Jacobian of `w ↦ w|w|²` is not complex-linear. -/
noncomputable def hopfNontrivialMultiplier (Rstar : ℝ) : ℂ :=
  Complex.exp (((2 : ℝ) * H.firstLyapunov * Rstar ^ 2
      + Complex.I * (H.ω + 3 * H.c₁.im * Rstar ^ 2)) * (H.hopfCyclePeriod Rstar))

/-- **The transverse Floquet multiplier of the closed-form Hopf limit cycle.**  In the planar
representation the cycle carries the trivial multiplier `1` (the direction tangent to the orbit)
and the transverse multiplier `exp (2 ℓ₁ Rstar² T)`; the latter is the modulus of the complex
multiplier `hopfNontrivialMultiplier`. -/
noncomputable def hopfTransverseMultiplier (Rstar : ℝ) : ℝ :=
  Real.exp (2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar))

/-- The multiplier is the exponential of the Floquet exponent over the period. -/
theorem hopfNontrivialMultiplier_eq_exp (Rstar : ℝ) :
    H.hopfNontrivialMultiplier Rstar
      = Complex.exp (H.hopfCycleExponent Rstar * (H.hopfCyclePeriod Rstar : ℂ)) := by
  rfl

/-- **The real part of the Floquet exponent is `2 ℓ₁ Rstar²`.**  This is the transverse Floquet
exponent of the cycle (the divergence of the truncated normal form on the cycle). -/
theorem hopfCycleExponent_re (Rstar : ℝ) :
    (H.hopfCycleExponent Rstar).re = 2 * H.firstLyapunov * Rstar ^ 2 := by
  simp only [hopfCycleExponent, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, ← Complex.ofReal_pow]
  ring

/-- **The imaginary part of the Floquet exponent is `ω + 3 (Im c₁) Rstar²`.**  It is the angular
part of the exponent; it does not affect the transverse stability of the cycle. -/
theorem hopfCycleExponent_im (Rstar : ℝ) :
    (H.hopfCycleExponent Rstar).im = H.ω + 3 * H.c₁.im * Rstar ^ 2 := by
  simp only [hopfCycleExponent, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, ← Complex.ofReal_pow]
  ring

/-- **The radial equilibrium condition on the cycle.**  `H.radialField μ Rstar = 0` with
`Rstar > 0` says `α μ = − ℓ₁ Rstar²`. -/
theorem radialEquilibrium_eq {μ Rstar : ℝ} (hrad : H.radialField μ Rstar = 0)
    (hR : 0 < Rstar) : H.α μ + H.firstLyapunov * Rstar ^ 2 = 0 := by
  have hrad0 : H.α μ * Rstar + H.firstLyapunov * Rstar ^ 3 = 0 := by
    rw [radialField_apply] at hrad; exact hrad
  have hfac : Rstar * (H.α μ + H.firstLyapunov * Rstar ^ 2) = 0 := by
    linear_combination hrad0
  rcases mul_eq_zero.1 hfac with h0 | h0
  · exact absurd h0 (ne_of_gt hR)
  · exact h0

/-- **The Floquet exponent of the cycle in the off-cycle form `α μ + 3 ℓ₁ Rstar²`.**  This is the
real part of the linearized coefficient `λ + 3 c₁ Rstar²`; on the cycle it is `2 ℓ₁ Rstar²`. -/
theorem hopfCycleExponent_re_lin {μ Rstar : ℝ} (hrad : H.radialField μ Rstar = 0)
    (hR : 0 < Rstar) :
    (H.hopfCycleExponent Rstar).re = H.α μ + 3 * H.firstLyapunov * Rstar ^ 2 := by
  have hre := H.hopfCycleExponent_re Rstar
  have hrad' := H.radialEquilibrium_eq hrad hR
  linarith

/-- **The transverse exponent of the cycle, over the period.**  This is the number whose
exponential is the transverse Floquet multiplier. -/
theorem hopfCycleExponent_period_re {μ Rstar : ℝ} (hrad : H.radialField μ Rstar = 0)
    (hR : 0 < Rstar) :
    (H.hopfCycleExponent Rstar * (H.hopfCyclePeriod Rstar : ℂ)).re
      = 2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar) := by
  have hre := H.hopfCycleExponent_re_lin hrad hR
  have hrad' := H.radialEquilibrium_eq hrad hR
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  have : H.α μ + 3 * H.firstLyapunov * Rstar ^ 2 = 2 * H.firstLyapunov * Rstar ^ 2 := by
    linarith
  rw [this]
  ring

/-! ## The modulus of the multiplier -/

/-- **The modulus of the nontrivial Floquet multiplier.**  `‖exp z‖ = exp (Re z)`, and the real
part of the exponent is `2 ℓ₁ Rstar²`. -/
theorem norm_hopfNontrivialMultiplier' (Rstar : ℝ) :
    ‖H.hopfNontrivialMultiplier Rstar‖
      = Real.exp (2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar)) := by
  rw [hopfNontrivialMultiplier_eq_exp, Complex.norm_exp]
  have hre := H.hopfCycleExponent_re Rstar
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  simp only [mul_zero, sub_zero]

/-- **The modulus of the nontrivial Floquet multiplier of the Hopf limit cycle.**  The hypothesis
`hΩ` records that the cycle has a genuine, finite, positive period `hopfCyclePeriod`; the
identity itself holds for every period. -/
theorem norm_hopfNontrivialMultiplier {Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0) :
    ‖H.hopfNontrivialMultiplier Rstar‖
      = Real.exp (2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar)) := by
  have hT : 0 < H.hopfCyclePeriod Rstar := H.hopfLimitCycle_period_pos hΩ
  exact H.norm_hopfNontrivialMultiplier' Rstar

/-- **The transverse Floquet multiplier is the modulus of the complex multiplier.** -/
theorem hopfTransverseMultiplier_eq_norm (Rstar : ℝ) :
    H.hopfTransverseMultiplier Rstar = ‖H.hopfNontrivialMultiplier Rstar‖ := by
  rw [hopfTransverseMultiplier]
  exact (H.norm_hopfNontrivialMultiplier' Rstar).symm

/-- **The transverse Floquet multiplier is the exponential of the transverse exponent.** -/
theorem hopfTransverseMultiplier_eq_exp_re {μ Rstar : ℝ} (hrad : H.radialField μ Rstar = 0)
    (hR : 0 < Rstar) :
    H.hopfTransverseMultiplier Rstar
      = Real.exp ((H.hopfCycleExponent Rstar * (H.hopfCyclePeriod Rstar : ℂ)).re) := by
  rw [hopfTransverseMultiplier]
  rw [H.hopfCycleExponent_period_re hrad hR]

/-! ## The Floquet stability and nondegeneracy criteria -/

/-- **The Hopf limit cycle is linearly stable exactly when the first Lyapunov coefficient is
negative.**  The transverse Floquet exponent is `2 ℓ₁ Rstar²`, so the cycle attracts
transversally when `ℓ₁ < 0` (supercritical) and repels when `ℓ₁ > 0`.  This is the classical
Hopf/Floquet connection. -/
theorem hopfNontrivialMultiplier_norm_lt_one_iff {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    ‖H.hopfNontrivialMultiplier Rstar‖ < 1 ↔ H.firstLyapunov < 0 := by
  have hrad' := H.radialEquilibrium_eq hrad hR
  have hre := H.hopfCycleExponent_re_lin hrad hR
  rw [hopfNontrivialMultiplier_eq_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  simp only [mul_zero, sub_zero]
  have hexp : H.α μ + 3 * H.firstLyapunov * Rstar ^ 2
      = 2 * H.firstLyapunov * Rstar ^ 2 := by linarith
  rw [hexp, Real.exp_lt_one_iff]
  have hT : 0 < H.hopfCyclePeriod Rstar := H.hopfLimitCycle_period_pos hΩ
  have hA : 0 < 2 * Rstar ^ 2 * (H.hopfCyclePeriod Rstar) := by
    have hR2 : 0 < Rstar ^ 2 := sq_pos_of_pos hR
    positivity
  constructor
  · intro h
    have hlt : H.firstLyapunov * (2 * Rstar ^ 2 * (H.hopfCyclePeriod Rstar)) < 0 := by
      linarith
    rcases mul_neg_iff.mp hlt with ⟨hpos, hneg⟩ | ⟨hneg', hA'⟩
    · exact absurd hneg (not_lt_of_ge (le_of_lt hA))
    · exact hneg'
  · intro h
    have hmain : (2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar))
        = H.firstLyapunov * (2 * Rstar ^ 2 * (H.hopfCyclePeriod Rstar)) := by ring
    rw [hmain]
    exact mul_neg_iff.mpr (Or.inr ⟨h, hA⟩)

/-- **The transverse Floquet multiplier is inside the unit circle exactly when `ℓ₁ < 0`.**  This
is the `LinearlyStable` condition of the oscillation layer, read for the Hopf cycle. -/
theorem hopfTransverseMultiplier_lt_one_iff {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    H.hopfTransverseMultiplier Rstar < 1 ↔ H.firstLyapunov < 0 := by
  rw [H.hopfTransverseMultiplier_eq_norm Rstar]
  exact H.hopfNontrivialMultiplier_norm_lt_one_iff hΩ hrad hR

/-- **The transverse Floquet multiplier is `1` exactly when the first Lyapunov coefficient
vanishes.**  This is the Floquet nondegeneracy condition of the cycle: the trivial multiplier
`1` is simple exactly when the transverse multiplier differs from `1`, i.e. exactly when
`ℓ₁ ≠ 0`. -/
theorem hopfTransverseMultiplier_eq_one_iff {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    H.hopfTransverseMultiplier Rstar = 1 ↔ H.firstLyapunov = 0 := by
  have hrad' := H.radialEquilibrium_eq hrad hR
  have hexp : H.α μ + 3 * H.firstLyapunov * Rstar ^ 2
      = 2 * H.firstLyapunov * Rstar ^ 2 := by linarith
  rw [hopfTransverseMultiplier, Real.exp_eq_one_iff]
  rw [← hexp]
  have hT : 0 < H.hopfCyclePeriod Rstar := H.hopfLimitCycle_period_pos hΩ
  have hR2 : 0 < Rstar ^ 2 := sq_pos_of_pos hR
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | h0
    · have h1 : 2 * H.firstLyapunov * Rstar ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact absurd h2 (ne_of_gt hR2)
    · exact absurd h0 (ne_of_gt hT)
  · intro h
    rw [h]
    have hα : H.α μ = 0 := by
      have hz := hrad'
      rw [h] at hz
      simpa using hz
    rw [hα]
    ring

/-- **The Hopf limit cycle is Floquet nondegenerate exactly when `ℓ₁ ≠ 0`.**  The trivial
multiplier is `1`; the transverse one is `exp (2 ℓ₁ Rstar² T)`, which equals `1` exactly when
`ℓ₁ = 0`.  This is the Floquet counterpart of the Hopf nondegeneracy hypothesis. -/
theorem hopfTransverseMultiplier_ne_one_iff {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    H.hopfTransverseMultiplier Rstar ≠ 1 ↔ H.firstLyapunov ≠ 0 := by
  constructor
  · intro h hzero
    exact h ((H.hopfTransverseMultiplier_eq_one_iff hΩ hrad hR).mpr hzero)
  · intro h hmeq
    exact h ((H.hopfTransverseMultiplier_eq_one_iff hΩ hrad hR).mp hmeq)

/-- **The exact criterion for the *complex* multiplier to be the trivial one.**  The complex
multiplier `exp (κ T)` equals `1` exactly when `Re (κ T) = 0` and `Im (κ T)` is an integer
multiple of `2π`; on the cycle `Re (κ T) = 2 ℓ₁ Rstar² T`, so the first condition is `ℓ₁ = 0`,
and the second one is the (rotational) condition `ω + 3 (Im c₁) Rstar²` times the period being a
multiple of `2π`.  Note that the second condition is *not* automatic: the complex multiplier
carries the rotational part of the exponent, while the transverse multiplier of the planar cycle
is its modulus. -/
theorem hopfNontrivialMultiplier_eq_one_iff {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    H.hopfNontrivialMultiplier Rstar = 1 ↔
      (H.firstLyapunov = 0 ∧ ∃ n : ℤ, (n : ℝ) * (2 * Real.pi)
          = (H.ω + 3 * H.c₁.im * Rstar ^ 2) * (H.hopfCyclePeriod Rstar)) := by
  have hrad' := H.radialEquilibrium_eq hrad hR
  have hre := H.hopfCycleExponent_re Rstar
  have him := H.hopfCycleExponent_im Rstar
  have hT : 0 < H.hopfCyclePeriod Rstar := H.hopfLimitCycle_period_pos hΩ
  have hR2 : 0 < Rstar ^ 2 := sq_pos_of_pos hR
  rw [hopfNontrivialMultiplier_eq_exp, complex_exp_eq_one_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, him]
  simp only [mul_zero, sub_zero]
  constructor
  · rintro ⟨hzero, n, hn⟩
    have hlt : 2 * H.firstLyapunov * Rstar ^ 2 * (H.hopfCyclePeriod Rstar) = 0 := by
      linarith
    have hℓ : H.firstLyapunov = 0 := by
      rcases mul_eq_zero.1 (by linarith : H.firstLyapunov * (2 * Rstar ^ 2
          * (H.hopfCyclePeriod Rstar)) = 0) with h0 | h0
      · linarith
      · exact absurd h0 (ne_of_gt (by positivity))
    refine ⟨hℓ, n, ?_⟩
    linarith
  · rintro ⟨hℓ, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · rw [hℓ]
      ring
    · linarith

/-! ## The Floquet multipliers of the cycle, in the vocabulary of the oscillation layer -/

/-- **The Floquet multipliers of the closed-form Hopf limit cycle.**  In the planar
representation the cycle carries the trivial multiplier `1` (tangent to the orbit) together with
the nontrivial multiplier computed above.  This is the object the oscillation layer calls the
Floquet data of a periodic orbit (`CRNT.Oscillation.Floquet.MassActionFloquetData`),
specialized to the two-dimensional Hopf cycle. -/
def hopfFloquetMultipliers (Rstar : ℝ) : Set ℂ := {1, H.hopfNontrivialMultiplier Rstar}

/-- The trivial multiplier `1` is a Floquet multiplier of the Hopf cycle. -/
theorem one_mem_hopfFloquetMultipliers (Rstar : ℝ) :
    (1 : ℂ) ∈ H.hopfFloquetMultipliers Rstar := Set.mem_insert _ _

/-- The nontrivial multiplier is a Floquet multiplier of the Hopf cycle. -/
theorem hopfNontrivialMultiplier_mem_hopfFloquetMultipliers (Rstar : ℝ) :
    H.hopfNontrivialMultiplier Rstar ∈ H.hopfFloquetMultipliers Rstar := by
  simp [hopfFloquetMultipliers]

/-- **The Hopf cycle is Floquet nondegenerate exactly when `ℓ₁ ≠ 0`.**  This is the counterpart
of `CRNT.Oscillation.Floquet`'s `MassActionFloquetData.Nondegenerate` (the trivial multiplier `1`
is simple): for the planar cycle the transverse multiplier is the modulus of the nontrivial
multiplier, and it differs from `1` exactly when the first Lyapunov coefficient does not
vanish. -/
theorem hopfCycle_floquetNondegenerate {μ Rstar : ℝ} (hΩ : H.cycleFreq Rstar ≠ 0)
    (hrad : H.radialField μ Rstar = 0) (hR : 0 < Rstar) :
    ‖H.hopfNontrivialMultiplier Rstar‖ ≠ 1 ↔ H.firstLyapunov ≠ 0 := by
  rw [← H.hopfTransverseMultiplier_eq_norm Rstar]
  exact H.hopfTransverseMultiplier_ne_one_iff hΩ hrad hR

/-- **The closed-form Hopf limit cycle is a periodic trajectory of the truncated normal-form
field.**  This reconnects the Hopf layer with `CRNT.PeriodicTrajectory`, the object the whole
oscillation layer is built on: the closed-form curve `t ↦ Rstar e^{i(θ₀ + Ω t)}` solves the
truncated field exactly (`hopfLimitCycle_solves`), closes after the period `|2π/Ω|`
(`hopfLimitCycle_periodic_abs`), and is nonconstant (`hopfLimitCycle_nonconstant`). -/
theorem truncatedCycle_isPeriodicTrajectory {μ Rstar : ℝ} (θ₀ : ℝ)
    (hR : 0 < Rstar) (hrad : H.radialField μ Rstar = 0)
    (hΩ : H.cycleFreq Rstar ≠ 0) :
    Nonempty (PeriodicTrajectory (H.normalForm μ)) := by
  refine ⟨{ orbit := H.hopfLimitCycle Rstar θ₀
            period := H.hopfCyclePeriod Rstar
            period_pos := H.hopfLimitCycle_period_pos hΩ
            solution := fun t => H.hopfLimitCycle_solves θ₀ (le_of_lt hR) hrad t
            periodic := H.hopfLimitCycle_periodic_abs θ₀ hΩ
            nonconstant := ?_ }⟩
  obtain ⟨s, t, hne⟩ := H.hopfLimitCycle_nonconstant θ₀ hR hΩ
  by_cases h : H.hopfLimitCycle Rstar θ₀ t = H.hopfLimitCycle Rstar θ₀ 0
  · refine ⟨s, ?_⟩
    rw [← h]
    exact hne
  · exact ⟨t, h⟩

end PlanarHopfData

/-- **The two multipliers of the canonical-rotation centre are conjugate and unimodular.**  The
mass-action Jacobian at a Hopf crossing is the canonical rotation `![0, -ω; ω, 0]`
(`CRNT.Hopf.MassActionHopfTaylorData.jacobian_rotation`); the multipliers of the linear centre dynamics
over a period `T` are `exp (iωT)` and `exp (-iωT)`, both of modulus exactly `1`.  This is the
classical statement that the Hopf crossing is a *purely imaginary* crossing. -/
theorem linearCentre_multiplier_norm (ω T : ℝ) :
    ‖Complex.exp (Complex.I * (ω * T))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (ω * T : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, Real.exp_zero]

end CRNT

/-! ## Axiom audit of the principal declarations -/

#print axioms CRNT.PlanarHopfData.norm_hopfNontrivialMultiplier
#print axioms CRNT.PlanarHopfData.hopfNontrivialMultiplier_norm_lt_one_iff
#print axioms CRNT.PlanarHopfData.hopfTransverseMultiplier_ne_one_iff
#print axioms CRNT.PlanarHopfData.hopfNontrivialMultiplier_eq_one_iff
#print axioms CRNT.PlanarHopfData.hopfCycle_floquetNondegenerate
#print axioms CRNT.PlanarHopfData.truncatedCycle_isPeriodicTrajectory
#print axioms CRNT.linearCentre_multiplier_norm
