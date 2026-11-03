import CRNT.Dynamics.HopfLyapunovCalibration
import CRNT.Dynamics.HopfLimitCycle
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.MassActionJacobian
import CRNT.Equilibria.SteadyState
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Mass-action Taylor calibration and a truncated Hopf branch

The mixed derivatives are calculated from the actual planar mass-action field.
`MassActionHopfTaylorData` packages a positive equilibrium branch, the calibrated
Taylor/normal-form data, transverse crossing, and nonzero Lyapunov coefficient.
`truncatedNormalForm_periodicBranch` constructs periodic curves of the cubic
truncated normal form. The worked network verifies this data explicitly.

The returned curves are not proved to satisfy the original mass-action ODE.
A full network Hopf theorem still needs the nonlinear transfer/return-map
argument with suitable joint parameter regularity and a genuine positive
periodic-orbit conclusion. Taylor calibration alone does not provide that bridge.
-/

namespace CRNT.Hopf

open scoped BigOperators

/-! ## 1. The calculus of iterated derivatives -/

/-- **A chain of `k` successive derivatives of a real function.** `fs i` is the `i`-th
derivative function, `fs 0 = f`, and the derivative of `fs i` at `x` is `(fs (i+1)) x`.
The chain carries the differentiation steps explicitly. -/
structure DerivChain (f : ℝ → ℝ) (k : ℕ) where
  /-- The `i`-th derivative function. -/
  fs : ℕ → (ℝ → ℝ)
  /-- The zeroth derivative is the function itself. -/
  fs_zero : fs 0 = f
  /-- Successive derivatives. -/
  fs_deriv : ∀ (i : ℕ) (_h : i < k) (x : ℝ), HasDerivAt (fs i) (fs (i + 1) x) x

namespace DerivChain

variable {f : ℝ → ℝ} {k : ℕ}

/-- The `i`-th derivative of `f` at `x`, read off the chain. -/
def derivAt (C : DerivChain f k) (i : ℕ) (x : ℝ) : ℝ := C.fs i x

/-- **Scalar multiples of a chain.** -/
def constMul (C : DerivChain f k) (c : ℝ) : DerivChain (fun t => c * f t) k where
  fs := fun i t => c * C.fs i t
  fs_zero := by
    funext t
    simp [C.fs_zero]
  fs_deriv := by
    intro i _h x
    have h1 := C.fs_deriv i _h x
    simpa using HasDerivAt.const_mul c h1

/-- **Finite sums of chains.** -/
def sum {I : Type} [Fintype I] {g : I → (ℝ → ℝ)} (C : ∀ i : I, DerivChain (g i) k)
    (c : I → ℝ) : DerivChain (fun t => ∑ i, c i * g i t) k where
  fs := fun i t => ∑ j, c j * (C j).fs i t
  fs_zero := by
    funext t
    apply Finset.sum_congr rfl
    intro j _
    rw [(C j).fs_zero]
  fs_deriv := by
    intro i _h x
    refine HasDerivAt.fun_sum (fun j _ => ?_)
    have h1 := (C j).fs_deriv i _h x
    simpa using HasDerivAt.const_mul (c j) h1

end DerivChain

/-- **The chain of derivatives of `t ↦ (c + t)^m`.** The `i`-th derivative function is
`m.descFactorial i * (c + t)^(m - i)`: the classical falling-factorial formula for the
iterated derivative of a power. -/
def powChain (m : ℕ) (c : ℝ) (k : ℕ) : DerivChain (fun t : ℝ => (c + t) ^ m) k where
  fs := fun i t => m.descFactorial i * (c + t) ^ (m - i)
  fs_zero := by
    funext t
    simp [Nat.descFactorial_zero]
  fs_deriv := by
    intro i _h x
    by_cases hi : i ≤ m
    · have hlin : HasDerivAt (fun t : ℝ => c + t) 1 x :=
        HasDerivAt.const_add c (hasDerivAt_id' x)
      have hcomp := HasDerivAt.comp x (hasDerivAt_pow (m - i) (c + x)) hlin
      have hfun : ((fun y : ℝ => y ^ (m - i)) ∘ (fun t : ℝ => c + t))
          = fun t : ℝ => (c + t) ^ (m - i) := by
        funext t; rfl
      rw [hfun] at hcomp
      have h1 : HasDerivAt (fun t : ℝ => (c + t) ^ (m - i))
          (((m - i : ℕ) : ℝ) * (c + x) ^ ((m - i) - 1)) x := by
        have h := hcomp
        rwa [mul_one] at h
      have h2 := HasDerivAt.const_mul (m.descFactorial i : ℝ) h1
      refine HasDerivAt.congr_deriv h2 ?_
      have hA : (m.descFactorial i : ℝ) * ((m - i : ℕ) : ℝ)
          = (m.descFactorial (i + 1) : ℝ) := by
        rw [Nat.descFactorial_succ, Nat.cast_mul]
        ring
      have hB : (m - i - 1 : ℕ) = m - (i + 1) := by omega
      have hX : (m.descFactorial i : ℝ) * (((m - i : ℕ) : ℝ) * (c + x) ^ (m - (i + 1)))
          = ((m.descFactorial i : ℝ) * ((m - i : ℕ) : ℝ)) * (c + x) ^ (m - (i + 1)) := by ring
      rw [hB, hX, hA]
    · have h0 : m.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have h0' : m.descFactorial (i + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [h0, h0', Nat.cast_zero, zero_mul]
      exact hasDerivAt_const x (0 : ℝ)

/-- **The `i`-th derivative of `t ↦ (c + t)^m` at `t = 0`** is
`m.descFactorial i * c^(m - i)`, the falling-factorial value of the `i`-th derivative. -/
theorem powChain_derivAt (m : ℕ) (c : ℝ) (k : ℕ) (i : ℕ) (_h : i ≤ k) :
    (powChain m c k).derivAt i 0 = m.descFactorial i * c ^ (m - i) := by
  simp [DerivChain.derivAt, powChain]

/-- **A chain of mixed partials of a bivariate real function.** `fs i j` is the function
obtained by differentiating `i` times in the first variable and `j` times in the second. -/
structure DerivChain2 (F : ℝ → ℝ → ℝ) (k l : ℕ) where
  /-- The `i`-fold first-variable and `j`-fold second-variable derivative. -/
  fs : ℕ → ℕ → (ℝ → ℝ → ℝ)
  /-- The zeroth mixed partial is the function itself. -/
  fs_zero : fs 0 0 = F
  /-- Differentiation in the first variable. -/
  fs_deriv_u : ∀ (i : ℕ) (hi : i < k) (j : ℕ) (hj : j < l) (x y : ℝ),
    HasDerivAt (fun t => fs i j t y) ((fs (i + 1) j) x y) x
  /-- Differentiation in the second variable. -/
  fs_deriv_v : ∀ (i : ℕ) (hi : i < k) (j : ℕ) (hj : j < l) (x y : ℝ),
    HasDerivAt (fun s => fs i j x s) ((fs i (j + 1)) x y) y

namespace DerivChain2

variable {F : ℝ → ℝ → ℝ} {k l : ℕ}

/-- The `i`-fold first-variable, `j`-fold second-variable partial at `(x, y)`. -/
def partialAt (C : DerivChain2 F k l) (i j : ℕ) (x y : ℝ) : ℝ := (C.fs i j) x y

/-- **The mixed-partial chain of a product of separated variables.** -/
def separated {A B : ℝ → ℝ} (Ac : DerivChain A k) (Bc : DerivChain B l) :
    DerivChain2 (fun u v => A u * B v) k l where
  fs := fun i j u v => (Ac.fs i u) * (Bc.fs j v)
  fs_zero := by
    funext u v
    rw [Ac.fs_zero, Bc.fs_zero]
  fs_deriv_u := by
    intro i _hi j _hj x y
    have h := Ac.fs_deriv i _hi x
    have h2 := HasDerivAt.mul_const h (Bc.fs j y)
    simpa using h2
  fs_deriv_v := by
    intro i _hi j _hj x y
    have h := Bc.fs_deriv j _hj y
    have h2 := HasDerivAt.const_mul (Ac.fs i x) h
    simpa using h2

/-- **The mixed-partial chain of a finite sum of separated products.** -/
def sum {I : Type} [Fintype I] {A B : I → (ℝ → ℝ)}
    (Ac : ∀ i : I, DerivChain (A i) k) (Bc : ∀ i : I, DerivChain (B i) l) (c : I → ℝ) :
    DerivChain2 (fun u v => ∑ i, c i * (A i u * B i v)) k l where
  fs := fun i j u v => ∑ idx, c idx * ((Ac idx).fs i u * (Bc idx).fs j v)
  fs_zero := by
    funext u v
    apply Finset.sum_congr rfl
    intro idx _
    rw [(Ac idx).fs_zero, (Bc idx).fs_zero]
  fs_deriv_u := by
    intro i _hi j _hj x y
    refine HasDerivAt.fun_sum (fun idx _ => ?_)
    have h1 := (Ac idx).fs_deriv i _hi x
    have h2 := HasDerivAt.mul_const h1 ((Bc idx).fs j y)
    simpa using HasDerivAt.const_mul (c idx) h2
  fs_deriv_v := by
    intro i _hi j _hj x y
    refine HasDerivAt.fun_sum (fun idx _ => ?_)
    have h1 := (Bc idx).fs_deriv j _hj y
    have h2 := HasDerivAt.const_mul ((Ac idx).fs i x) h1
    simpa using HasDerivAt.const_mul (c idx) h2

end DerivChain2

/-! ## 2. The mass-action Taylor data of a planar network -/

/-- **The mass-action monomial of a planar complex at a two-point concentration.** -/
theorem massActionMonomial_two (y : Complex (Fin 2)) (u v : ℝ) :
    y.massActionMonomial ![u, v] = (u ^ y 0) * (v ^ y 1) := by
  simp [Complex.massActionMonomial, Fin.prod_univ_two]

/-- **The mixed-partial chain of the mass-action field of a planar network at `xst`.** The
chain is the one of the *actual* mass-action vector field
`x ↦ N.massActionVectorField κ x s` evaluated at the shifted point `xst + (u, v)`. -/
def maChain (N : Network (Fin 2)) (κ : N.RateConstants) (xst : Concentration (Fin 2))
    (s : Fin 2) (k l : ℕ) :
    DerivChain2 (fun u v => N.massActionVectorField κ (![xst 0 + u, xst 1 + v]) s) k l where
  fs := fun i j u v => ∑ r : N.R, (κ.k r * N.reactionVector r s)
      * (((powChain ((N.reaction r).source 0) (xst 0) k).fs i u)
        * ((powChain ((N.reaction r).source 1) (xst 1) l).fs j v))
  fs_zero := by
    funext u v
    simp only [powChain, Nat.descFactorial_zero, Nat.sub_zero]
    rw [Network.massActionVectorField_apply]
    apply Finset.sum_congr rfl
    intro r _
    have hmono : (N.reaction r).source.massActionMonomial (![xst 0 + u, xst 1 + v])
        = ((xst 0 + u) ^ (N.reaction r).source 0) * ((xst 1 + v) ^ (N.reaction r).source 1) :=
      massActionMonomial_two _ _ _
    rw [Network.massActionRate, hmono]
    ring
  fs_deriv_u := by
    intro i _hi j _hj x y
    refine HasDerivAt.fun_sum (fun r _ => ?_)
    have h1 := (powChain ((N.reaction r).source 0) (xst 0) k).fs_deriv i _hi x
    have h2 := HasDerivAt.mul_const h1
      ((powChain ((N.reaction r).source 1) (xst 1) l).fs j y)
    simpa using HasDerivAt.const_mul (κ.k r * N.reactionVector r s) h2
  fs_deriv_v := by
    intro i _hi j _hj x y
    refine HasDerivAt.fun_sum (fun r _ => ?_)
    have h1 := (powChain ((N.reaction r).source 1) (xst 1) l).fs_deriv j _hj y
    have h2 := HasDerivAt.const_mul ((powChain ((N.reaction r).source 0) (xst 0) k).fs i x) h1
    simpa using HasDerivAt.const_mul (κ.k r * N.reactionVector r s) h2

/-- **The mass-action Taylor coefficient of a planar network.** `maTay N κ xst s k l` is the
mixed partial of the `s`-component of the mass-action field at `xst`, `k` times in the first
concentration and `l` times in the second, computed from the network: each reaction
contributes its rate, its reaction-vector entry and the falling factorials of its source
stoichiometric coefficients. -/
def maTay (N : Network (Fin 2)) (κ : N.RateConstants) (xst : Concentration (Fin 2))
    (s : Fin 2) (k l : ℕ) : ℝ :=
  ∑ r : N.R, κ.k r * N.reactionVector r s
    * ((N.reaction r).source 0).descFactorial k * (xst 0) ^ ((N.reaction r).source 0 - k)
    * ((N.reaction r).source 1).descFactorial l * (xst 1) ^ ((N.reaction r).source 1 - l)

/-- **The mass-action Taylor coefficient is the mixed partial of the mass-action field.**
This is the link between the *network* and the *Taylor data* used by the Hopf normal form:
the combinatorial sum over reactions is exactly the `k`-fold and `l`-fold partial derivative
of the genuine mass-action vector field at `xst`. -/
theorem maTay_eq (N : Network (Fin 2)) (κ : N.RateConstants) (xst : Concentration (Fin 2))
    (s : Fin 2) (k l : ℕ) :
    maTay N κ xst s k l
      = (maChain N κ xst s k l).partialAt k l 0 0 := by
  simp only [maTay, maChain, DerivChain2.partialAt, powChain, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- **The real partials of the mass-action field of a planar network at `xst`.** The fourteen
entries are the mixed partials of the two components of the mass-action vector field, in the
classical order of `CRNT.Hopf.PlanarPartials`. -/
def maPartials (N : Network (Fin 2)) (κ : N.RateConstants) (xst : Concentration (Fin 2)) :
    PlanarPartials where
  fxx := maTay N κ xst 0 2 0
  fxy := maTay N κ xst 0 1 1
  fyy := maTay N κ xst 0 0 2
  gxx := maTay N κ xst 1 2 0
  gxy := maTay N κ xst 1 1 1
  gyy := maTay N κ xst 1 0 2
  fxxx := maTay N κ xst 0 3 0
  fxxy := maTay N κ xst 0 2 1
  fxyy := maTay N κ xst 0 1 2
  fyyy := maTay N κ xst 0 0 3
  gxxx := maTay N κ xst 1 3 0
  gxxy := maTay N κ xst 1 2 1
  gxyy := maTay N κ xst 1 1 2
  gyyy := maTay N κ xst 1 0 3

/-- **The real partials of the mass-action field are its mixed partials.** Every entry of
`maPartials` is the corresponding mixed partial of the mass-action vector field at `xst`. -/
theorem maPartials_correct (N : Network (Fin 2)) (κ : N.RateConstants)
    (xst : Concentration (Fin 2)) :
    (maPartials N κ xst).fxx = (maChain N κ xst 0 2 0).partialAt 2 0 0 0 ∧
      (maPartials N κ xst).fxy = (maChain N κ xst 0 1 1).partialAt 1 1 0 0 ∧
      (maPartials N κ xst).fyy = (maChain N κ xst 0 0 2).partialAt 0 2 0 0 ∧
      (maPartials N κ xst).gxx = (maChain N κ xst 1 2 0).partialAt 2 0 0 0 ∧
      (maPartials N κ xst).gxy = (maChain N κ xst 1 1 1).partialAt 1 1 0 0 ∧
      (maPartials N κ xst).gyy = (maChain N κ xst 1 0 2).partialAt 0 2 0 0 ∧
      (maPartials N κ xst).fxxx = (maChain N κ xst 0 3 0).partialAt 3 0 0 0 ∧
      (maPartials N κ xst).fxxy = (maChain N κ xst 0 2 1).partialAt 2 1 0 0 ∧
      (maPartials N κ xst).fxyy = (maChain N κ xst 0 1 2).partialAt 1 2 0 0 ∧
      (maPartials N κ xst).fyyy = (maChain N κ xst 0 0 3).partialAt 0 3 0 0 ∧
      (maPartials N κ xst).gxxx = (maChain N κ xst 1 3 0).partialAt 3 0 0 0 ∧
      (maPartials N κ xst).gxxy = (maChain N κ xst 1 2 1).partialAt 2 1 0 0 ∧
      (maPartials N κ xst).gxyy = (maChain N κ xst 1 1 2).partialAt 1 2 0 0 ∧
      (maPartials N κ xst).gyyy = (maChain N κ xst 1 0 3).partialAt 0 3 0 0 := by
  simp [maPartials, maTay_eq]

/-- **The conjugate of the complex number `4`.** The repository provides `cconj_two` and
`cconj_three`; the numerical instance below needs `4` and `5` as well. -/
theorem cconj_four : cconj 4 = 4 := by
  show (starRingEnd ℂ) ((4 : ℕ) : ℂ) = 4
  rw [map_natCast]
  norm_num

/-- **The conjugate of the complex number `5`.** -/
theorem cconj_five : cconj 5 = 5 := by
  show (starRingEnd ℂ) ((5 : ℕ) : ℂ) = 5
  rw [map_natCast]
  norm_num

/-! ## 3. The mass-action Taylor/truncated-normal-form verdict -/

/-- **The Hopf data of a planar mass-action family.** The bundle of the hypotheses of the
Hopf theorem for a one-parameter mass-action family `κ (μ)` with a branch of steady states
`xst (μ)`:

* the mass-action Jacobian at the crossing `μ₀` is the **canonical rotation**
  `[[0, −ω], [ω, 0]]` — the conjugate pair `±iω` sits on the imaginary axis with `ω ≠ 0`;
* the planar Hopf normal-form data `H` of the mass-action field, whose resonant cubic
  coefficient `c₁` is **the one computed from the mass-action Taylor data** (the field
  `H_c₁`);
* the unfolding `α` of the normal form is the **real part of the crossing eigenvalue** of
  the mass-action Jacobian, and the crossing is **transversal** (`α' ≠ 0`);
* the **first Lyapunov coefficient is nonzero** (`ℓ₁ ≠ 0`).

With these, the Hopf theorem fires for the truncated normal form of the mass-action field
(`truncatedNormalForm_periodicBranch`). -/
structure MassActionHopfTaylorData (N : Network (Fin 2)) (κ : ℝ → N.RateConstants)
    (xst : ℝ → Concentration (Fin 2)) (μ₀ : ℝ) where
  /-- The Taylor expansion is taken along an actual equilibrium branch. -/
  steady_state : ∀ μ, N.IsMassActionSteadyState (κ μ) (xst μ)
  /-- The equilibrium branch lies in the positive orthant. -/
  positive : ∀ μ, (xst μ).Positive
  /-- The Hopf frequency at the crossing. -/
  ω : ℝ
  /-- The frequency is nonzero: the linear part is genuinely a rotation, not a double zero. -/
  ω_ne : ω ≠ 0
  /-- **The mass-action Jacobian at the crossing is the canonical rotation.** -/
  jacobian_rotation : N.massActionJacobian (κ μ₀) (xst μ₀) = !![0, -ω; ω, 0]
  /-- The planar Hopf normal-form data of the mass-action field at the crossing. -/
  H : PlanarHopfData
  /-- The crossing parameter of the normal-form data is the family's crossing. -/
  H_μ₀ : H.μ₀ = μ₀
  /-- The frequency of the normal-form data is the Hopf frequency. -/
  H_ω : H.ω = ω
  /-- **The normal-form data is the one computed from the mass-action Taylor data.** The
      resonant cubic coefficient `c₁` is the resonant coefficient of the Poincaré–Dulac normal
      form of the mass-action field at the crossing `λ = iω`, the complex Taylor data being
      those of the mass-action field's real partials. -/
  H_c₁ : H.c₁ = resonantCoefficientSol ((ω : ℂ) * Complex.I)
      (realTaylorQ20 (maPartials N (κ μ₀) (xst μ₀)))
      (realTaylorQ11 (maPartials N (κ μ₀) (xst μ₀)))
      (realTaylorQ02 (maPartials N (κ μ₀) (xst μ₀)))
      (realTaylorC21 (maPartials N (κ μ₀) (xst μ₀)))
  /-- The unfolding of the normal-form data is the real part of the crossing eigenvalue of
      the mass-action Jacobian. -/
  H_α : ∀ μ, H.α μ = (N.massActionJacobian (κ μ) (xst μ)).trace / 2
  /-- The crossing is transversal. -/
  H_α' : H.α' ≠ 0
  /-- The first Lyapunov coefficient is nonzero: the nondegeneracy hypothesis of the Hopf
      theorem. -/
  H_ℓ₁ : H.firstLyapunov ≠ 0

namespace MassActionHopfTaylorData

variable {N : Network (Fin 2)} {κ : ℝ → N.RateConstants} {xst : ℝ → Concentration (Fin 2)}
variable {μ₀ : ℝ}

/-- **The mass-action Taylor data at the crossing.** The real partials of the mass-action
field of the network at the crossing, computed from the network by `maPartials`. -/
def partials (h : MassActionHopfTaylorData N κ xst μ₀) : PlanarPartials :=
  maPartials N (κ μ₀) (xst μ₀)

/-- **The Guckenheimer–Holmes calibration of the mass-action Taylor data.** The classical
real-coordinate first Lyapunov coefficient formula, applied to the *original* real partials
of the mass-action field at the crossing, gives the first Lyapunov coefficient of the
normal form: the resonant cubic coefficient computed by the Poincaré–Dulac machinery **is**
the repository's real-coordinate `ℓ₁`. -/
theorem calibration (h : MassActionHopfTaylorData N κ xst μ₀) :
    h.H.lyapunovFromPartials (h.partials.fxxx) (h.partials.fxyy) (h.partials.gxxy)
      (h.partials.gyyy) (h.partials.fxy) (h.partials.fxx) (h.partials.fyy) (h.partials.gxy)
      (h.partials.gxx) (h.partials.gyy) = h.H.firstLyapunov :=
  classical_lyapunov (ω := h.ω) h.ω_ne h.partials h.H h.H_ω h.H_c₁

/-- Calibrated mass-action data and the associated cubic truncated-normal-form
periodic branch. No solution of the original mass-action ODE is asserted here. -/
theorem truncatedNormalForm_periodicBranch (h : MassActionHopfTaylorData N κ xst μ₀)
    (branch : Set ℝ) (hclosure : h.H.μ₀ ∈ closure branch)
    (hbranch : ∀ ν ∈ branch, h.H.α ν / h.H.firstLyapunov < 0)
    (hfreq : ∀ ν ∈ branch,
      h.H.cycleFreq (Real.sqrt (-h.H.α ν / h.H.firstLyapunov)) ≠ 0) :
    h.H.μ₀ ∈ closure branch ∧
      ∀ μ ∈ branch,
        0 < |2 * Real.pi / h.H.cycleFreq (Real.sqrt (-h.H.α μ / h.H.firstLyapunov))|
        ∧ Function.Periodic
            (h.H.hopfLimitCycle (Real.sqrt (-h.H.α μ / h.H.firstLyapunov)) 0)
            |2 * Real.pi / h.H.cycleFreq (Real.sqrt (-h.H.α μ / h.H.firstLyapunov))|
        ∧ (∃ s t,
            (h.H.hopfLimitCycle (Real.sqrt (-h.H.α μ / h.H.firstLyapunov)) 0) s
              ≠ (h.H.hopfLimitCycle (Real.sqrt (-h.H.α μ / h.H.firstLyapunov)) 0) t)
        ∧ (∃ s,
            ‖(h.H.hopfLimitCycle (Real.sqrt (-h.H.α μ / h.H.firstLyapunov)) 0) s‖
              = Real.sqrt (-h.H.α μ / h.H.firstLyapunov)) :=
  h.H.hopf_andronov_truncated h.H_α' h.H_ℓ₁ branch hclosure hbranch hfreq

/-- Existence of calibrated Taylor and truncated-Hopf data, including a positive
equilibrium branch. This predicate does not assert network oscillatory capacity. -/
def hasTruncatedHopfData (N : Network (Fin 2)) (κ : ℝ → N.RateConstants)
    (xst : ℝ → Concentration (Fin 2)) (μ₀ : ℝ) : Prop :=
  Nonempty (MassActionHopfTaylorData N κ xst μ₀)

end MassActionHopfTaylorData

end CRNT.Hopf

/-! ## 4. A concrete planar mass-action network with a Hopf bifurcation -/

namespace CRNT.Examples.HopfPlanar2

open CRNT CRNT.Hopf Matrix

/-- **The source complexes of the planar Hopf network**, one per reaction:
`∅`, `∅`, `X`, `Y`, `X+Y`, `X`, `2X`, `X+Y`, `2Y`. -/
def source : Fin 9 → Complex (Fin 2)
  | 0 => ![0, 0]
  | 1 => ![0, 0]
  | 2 => ![1, 0]
  | 3 => ![0, 1]
  | 4 => ![1, 1]
  | 5 => ![1, 0]
  | 6 => ![2, 0]
  | 7 => ![1, 1]
  | 8 => ![0, 2]

/-- **The target complexes of the planar Hopf network**: `X`, `Y`, `∅`, `∅`, `∅`, `X+Y`, `3X`,
`2Y`, `3Y`. -/
def target : Fin 9 → Complex (Fin 2)
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![0, 0]
  | 3 => ![0, 0]
  | 4 => ![0, 0]
  | 5 => ![1, 1]
  | 6 => ![3, 0]
  | 7 => ![0, 2]
  | 8 => ![0, 3]

/-- The reaction map of the network. -/
def rxn (r : Fin 9) : Reaction (Fin 2) := { source := source r, target := target r }

/-- **The genuine two-species mass-action network** of the example. -/
def N : Network (Fin 2) :=
  { R := Fin 9, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- **The critical rate.** The trace of the mass-action Jacobian of the network at the
equilibrium `(1,1)` is `μ² − 1`, which vanishes at `μ₀ = 1`. -/
def μ₀ : ℝ := 1

/-- **The Hopf frequency at the crossing**: the conjugate pair is `±2i`. -/
def ω : ℝ := 2

/-- **The rate constants as a function of the autocatalytic parameter `μ`**:
`(2, 1, μ²+1, 6, 1, 2, μ²+1, 1, 3)`.  The two autocatalytic rates are `μ² + 1`, so that they
are strictly positive for every `μ` and the family is defined on all of `ℝ`. -/
def rate (μ : ℝ) : Fin 9 → ℝ
  | 0 => 2
  | 1 => 1
  | 2 => μ ^ 2 + 1
  | 3 => 6
  | 4 => 1
  | 5 => 2
  | 6 => μ ^ 2 + 1
  | 7 => 1
  | 8 => 3

/-- The positive rate constants of the family. -/
def κ (μ : ℝ) : Network.RateConstants N where
  k := rate μ
  positive := by
    intro r
    fin_cases r <;> simp only [rate] <;> positivity

/-- **The steady state `(1,1)`**, a positive equilibrium for every `μ`. -/
def xeq : Concentration (Fin 2) := ![1, 1]

/-- The branch of steady states: the constant branch `(1,1)`. -/
def xst : ℝ → Concentration (Fin 2) := fun _ => xeq

theorem xeq_positive : xeq.Positive := by
  intro s; fin_cases s <;> simp [xeq]

theorem xeq_eq_one (s : Fin 2) : xeq s = 1 := by fin_cases s <;> rfl

/-- **At the equilibrium `(1,1)` the monomial gradient of a complex `y` in direction `j` is the
source stoichiometric coefficient `y j`**, since every concentration factor is one. -/
theorem grad_at_xeq (y : Complex (Fin 2)) (j : Fin 2) :
    massActionMonomialGrad y xeq j = (y j : ℝ) := by
  simp only [massActionMonomialGrad]
  rw [Finset.prod_congr rfl (fun s _ => by rw [xeq_eq_one s, one_pow]), xeq_eq_one j]
  simp

/-- **The mass-action field of the network at the equilibrium is zero**: `(1,1)` is a steady
state for every `μ`. -/
theorem equilibrium (μ : ℝ) :
    N.massActionVectorField (κ μ) xeq = 0 := by
  funext s
  rw [Network.massActionVectorField_apply]
  fin_cases s
  · change (∑ r : Fin 9, (κ μ).k r * (N.reaction r).source.massActionMonomial xeq
        * N.reactionVector r 0) = 0
    simp [κ, N, rxn, source, target, rate, xeq_eq_one, Network.reactionVector, Reaction.vector,
      Complex.massActionMonomial, Fin.sum_univ_succ]
    ring
  · change (∑ r : Fin 9, (κ μ).k r * (N.reaction r).source.massActionMonomial xeq
        * N.reactionVector r 1) = 0
    simp [κ, N, rxn, source, target, rate, xeq_eq_one, Network.reactionVector, Reaction.vector,
      Complex.massActionMonomial, Fin.sum_univ_succ]
    ring

/-- **The mass-action Jacobian of the network at the equilibrium** is
`[[μ² − 1, −2], [2, 0]]`. -/
theorem jacobian_eq (μ : ℝ) :
    N.massActionJacobian (κ μ) xeq = !![μ ^ 2 - 1, -2; 2, 0] := by
  ext i j
  rw [Network.massActionJacobian]
  fin_cases i <;> fin_cases j
  · change (∑ r : Fin 9, (κ μ).k r * massActionMonomialGrad (N.reaction r).source xeq 0
        * N.reactionVector r 0) = _
    simp [κ, N, rxn, source, target, rate, grad_at_xeq, Network.reactionVector,
      Reaction.vector, Fin.sum_univ_succ]
    ring
  · change (∑ r : Fin 9, (κ μ).k r * massActionMonomialGrad (N.reaction r).source xeq 1
        * N.reactionVector r 0) = _
    simp [κ, N, rxn, source, target, rate, grad_at_xeq, Network.reactionVector,
      Reaction.vector, Fin.sum_univ_succ]
    ring
  · change (∑ r : Fin 9, (κ μ).k r * massActionMonomialGrad (N.reaction r).source xeq 0
        * N.reactionVector r 1) = _
    simp [κ, N, rxn, source, target, rate, grad_at_xeq, Network.reactionVector,
      Reaction.vector, Fin.sum_univ_succ]
    ring
  · change (∑ r : Fin 9, (κ μ).k r * massActionMonomialGrad (N.reaction r).source xeq 1
        * N.reactionVector r 1) = _
    simp [κ, N, rxn, source, target, rate, grad_at_xeq, Network.reactionVector,
      Reaction.vector, Fin.sum_univ_succ]
    ring

/-- **The mass-action Taylor coefficient at the equilibrium, as a sum over the reactions.**
At the equilibrium `(1,1)` every concentration factor is one, so the powers of the Taylor
expansion are trivial and the coefficient is the finite sum
`∑_r κ_r ν_r(s) (source_r)_0^{\underline k} (source_r)_1^{\underline l}`. -/
theorem maTay_at_xeq (μ : ℝ) (s : Fin 2) (k l : ℕ) :
    maTay N (κ μ) xeq s k l
      = ∑ r : Fin 9, rate μ r * N.reactionVector r s
        * ((N.reaction r).source 0).descFactorial k
        * ((N.reaction r).source 1).descFactorial l := by
  unfold maTay
  have hpow0 : ∀ r : N.R, (xeq 0) ^ ((N.reaction r).source 0 - k) = 1 := by
    intro r
    simp [xeq_eq_one, one_pow]
  have hpow1 : ∀ r : N.R, (xeq 1) ^ ((N.reaction r).source 1 - l) = 1 := by
    intro r
    simp [xeq_eq_one, one_pow]
  simp_rw [hpow0, hpow1, mul_one]
  change (∑ r : Fin 9, (κ μ).k r * N.reactionVector r s
        * ((N.reaction r).source 0).descFactorial k
        * ((N.reaction r).source 1).descFactorial l) = _
  rfl

set_option maxHeartbeats 800000 in
/-- **The real partials of the mass-action field at the equilibrium.** The field is
`ẋ = 2 − (μ²+1)x − 2xy + (μ²+1)x²`, `ẏ = 1 + 2x − 6y + 3y²`: quadratic, so every third-order
partial vanishes. -/
theorem partials_eq (μ : ℝ) :
    maPartials N (κ μ) xeq =
      { fxx := 2 * (μ ^ 2 + 1), fxy := -2, fyy := 0, gxx := 0, gxy := 0, gyy := 6,
        fxxx := 0, fxxy := 0, fxyy := 0, fyyy := 0,
        gxxx := 0, gxxy := 0, gxyy := 0, gyyy := 0 } := by
  simp only [maPartials]
  rw [PlanarPartials.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [maTay_at_xeq]
    all_goals
      simp [N, rxn, source, target, rate, Network.reactionVector, Reaction.vector,
        Fin.sum_univ_succ]
      all_goals ring

/-- **The complex Taylor coefficients of the mass-action field at the crossing.** At the
critical rate `μ₀ = 1` the field is `ẋ = 2 − 2x − 2xy + 2x²`, `ẏ = 1 + 2x − 6y + 3y²`:
quadratic, so all four cubic Taylor coefficients vanish; the quadratic ones are
`q₂₀ = 1/2 − i/4`, `q₁₁ = 1 + 3i/2`, `q₀₂ = 1/2 − 5i/4`. -/
theorem taylor_eq :
    realTaylorQ20 (maPartials N (κ μ₀) xeq) = 1 / 2 - Complex.I / 4 ∧
      realTaylorQ11 (maPartials N (κ μ₀) xeq) = 1 + 3 * Complex.I / 2 ∧
      realTaylorQ02 (maPartials N (κ μ₀) xeq) = 1 / 2 - 5 * Complex.I / 4 ∧
      realTaylorC30 (maPartials N (κ μ₀) xeq) = 0 ∧
      realTaylorC21 (maPartials N (κ μ₀) xeq) = 0 ∧
      realTaylorC12 (maPartials N (κ μ₀) xeq) = 0 ∧
      realTaylorC03 (maPartials N (κ μ₀) xeq) = 0 := by
  rw [partials_eq μ₀]
  simp only [μ₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [realTaylorQ20, realTaylorQ11, realTaylorQ02, realTaylorC30, realTaylorC21, realTaylorC12,
      realTaylorC03, quadA20, quadA11, quadA02, cubicA30, cubicA21, cubicA12, cubicA03] <;>
    ring

/-- **The resonant cubic coefficient of the Poincaré–Dulac normal form of the mass-action
field at the crossing** is `−1/4 − 43i/24`: its real part `−1/4` is the first Lyapunov
coefficient, and its imaginary part is the frequency shift of the normal form. -/
theorem c₁_eq :
    resonantCoefficientSol ((ω : ℂ) * Complex.I)
        (realTaylorQ20 (maPartials N (κ μ₀) xeq))
        (realTaylorQ11 (maPartials N (κ μ₀) xeq))
        (realTaylorQ02 (maPartials N (κ μ₀) xeq))
        (realTaylorC21 (maPartials N (κ μ₀) xeq))
      = (-1 / 4 : ℂ) + (-43 / 24 : ℂ) * Complex.I := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := taylor_eq
  rw [h1, h2, h3, h5]
  simp only [resonantCoefficientSol, pushB21, h20Sol, h11Sol, h02Sol, ω]
  simp [cconj_div, cconj_inv, cconj_four, cconj_five]
  field_simp
  apply Complex.ext
  · norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.I_sq]
  · norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.I_sq]

/-- **The unfolding of the real part of the crossing eigenvalue.** The trace of the
mass-action Jacobian at the equilibrium is `μ² − 1`, so the real part of the conjugate pair
is `(μ² − 1)/2`, which vanishes at `μ₀ = 1` with derivative `1 ≠ 0`: the crossing is
transversal. -/
noncomputable def αfun : ℝ → ℝ := fun μ => (μ ^ 2 - 1) / 2

/-- The resonant cubic coefficient of the normal form of the mass-action field at the
crossing. -/
noncomputable def c₁val : ℂ :=
  resonantCoefficientSol ((ω : ℂ) * Complex.I)
    (realTaylorQ20 (maPartials N (κ μ₀) xeq))
    (realTaylorQ11 (maPartials N (κ μ₀) xeq))
    (realTaylorQ02 (maPartials N (κ μ₀) xeq))
    (realTaylorC21 (maPartials N (κ μ₀) xeq))

/-- **The planar Hopf normal-form data of the mass-action field at the crossing.** -/
noncomputable def HopfData : PlanarHopfData where
  μ₀ := μ₀
  ω := ω
  ω_ne := by norm_num [ω]
  α := fun μ => (μ ^ 2 - 1) / 2
  α_crossing := by simp [μ₀]
  α' := 1
  hasDeriv_α := by
    have hsq : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      intro x
      simpa using (hasDerivAt_pow 2 x)
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * μ₀) μ₀ := by
      have h2 := hsq μ₀
      simpa [μ₀] using (h2.sub_const 1)
    have h3 : (fun y : ℝ => (1 / 2 : ℝ) * (y ^ 2 - 1)) = fun y : ℝ => (y ^ 2 - 1) / 2 := by
      funext y; ring
    have h4 := HasDerivAt.const_mul (1 / 2 : ℝ) h1
    rw [h3] at h4
    simpa [μ₀] using h4
  c₁ := c₁val
  normalForm := fun μ w => ((αfun μ : ℂ) + ω * Complex.I) * w
      + c₁val * (w * (Complex.normSq w : ℂ))
  normalForm_eq := by
    intro _ w
    rfl

/-- Calibrated mass-action data and the associated cubic truncated-normal-form
periodic branch. No solution of the original mass-action ODE is asserted here. -/
noncomputable def hopfData : MassActionHopfTaylorData N κ xst μ₀ where
  steady_state μ s := congrFun (equilibrium μ) s
  positive _ := xeq_positive
  ω := ω
  ω_ne := by norm_num [ω]
  jacobian_rotation := by
    simp only [xst]
    rw [jacobian_eq μ₀]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [μ₀, ω, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val_fin_one]
  H := HopfData
  H_μ₀ := rfl
  H_ω := rfl
  H_c₁ := rfl
  H_α := by
    intro μ
    simp only [HopfData, αfun, xst] <;>
    rw [jacobian_eq μ] <;>
    simp [Matrix.trace_fin_two]
  H_α' := by norm_num [HopfData]
  H_ℓ₁ := by
    rw [PlanarHopfData.firstLyapunov]
    simp [HopfData, c₁val, c₁_eq, Complex.I_re, Complex.I_im]

/-- Calibrated mass-action data and the associated cubic truncated-normal-form
periodic branch. No solution of the original mass-action ODE is asserted here. -/
def branch : Set ℝ := Set.Ioi 1 ∩ Set.Ioo 1 (6 / 5)

/-- **The crossing is a limit point of the branch.** -/
theorem branch_closure : 1 ∈ closure branch := by
  have h : branch = Set.Ioo 1 (6 / 5) := by
    ext x
    simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hx⟩
  rw [h, closure_Ioo]
  all_goals norm_num

/-- **On the branch the ratio `α/ℓ₁` is negative**, so the bifurcating amplitude
`√(−α/ℓ₁)` is positive. -/
theorem branch_sign (ν : ℝ) (hν : ν ∈ branch) :
    HopfData.α ν / HopfData.firstLyapunov < 0 := by
  have hα : HopfData.α ν = (ν ^ 2 - 1) / 2 := by simp [HopfData, αfun]
  have hℓ : HopfData.firstLyapunov = -1 / 4 := by
    rw [PlanarHopfData.firstLyapunov]
    simp [HopfData, c₁val, c₁_eq, Complex.I_re, Complex.I_im]
  rw [hα, hℓ]
  have hν' : 1 < ν := by
    have := hν
    simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
    exact this.1
  have hpos : 0 < (ν ^ 2 - 1) / 2 := by nlinarith
  have heq : (ν ^ 2 - 1) / 2 / (-1 / 4 : ℝ) = -2 * (ν ^ 2 - 1) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- **The angular frequency of the bifurcating cycle is nonzero on the branch**: on the branch
the amplitude satisfies `R² = 2(ν² − 1) < 1`, and `ω + (Im c₁) R² ≥ 2 − 43/24 > 0`. -/
theorem branch_freq (ν : ℝ) (hν : ν ∈ branch) :
    HopfData.cycleFreq (Real.sqrt (-HopfData.α ν / HopfData.firstLyapunov)) ≠ 0 := by
  have hα : HopfData.α ν = (ν ^ 2 - 1) / 2 := by simp [HopfData, αfun]
  have hℓ : HopfData.firstLyapunov = -1 / 4 := by
    rw [PlanarHopfData.firstLyapunov]
    simp [HopfData, c₁val, c₁_eq, Complex.I_re, Complex.I_im]
  have him : (HopfData.c₁).im = -43 / 24 := by
    simp [HopfData, c₁val, c₁_eq, Complex.I_re, Complex.I_im]
  have hω : HopfData.ω = 2 := by simp [HopfData, ω]
  have hR2 : Real.sqrt (-HopfData.α ν / HopfData.firstLyapunov) ^ 2 = 2 * (ν ^ 2 - 1) := by
    rw [hα, hℓ]
    have hν' : 1 < ν := by
      have := hν
      simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
      exact this.1
    have hpos : 0 ≤ -((ν ^ 2 - 1) / 2) / (-1 / 4) := by
      have hnum : 0 ≤ (ν ^ 2 - 1) := by nlinarith
      linarith
    rw [Real.sq_sqrt hpos]
    field_simp
    ring
  have hR2lt : Real.sqrt (-HopfData.α ν / HopfData.firstLyapunov) ^ 2 < 1 := by
    rw [hR2]
    have hν'' : ν < 6 / 5 := by
      have := hν
      simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
      exact this.2.2
    have hν' : 1 < ν := by
      have := hν
      simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
      exact this.1
    nlinarith
  rw [PlanarHopfData.cycleFreq, hω, him, hR2]
  have hpos : 0 < 2 + (-43 / 24) * (2 * (ν ^ 2 - 1)) := by
    have hν'' : ν < 6 / 5 := by
      have := hν
      simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
      exact this.2.2
    have hν' : 1 < ν := by
      have := hν
      simp only [branch, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo] at this
      exact this.1
    nlinarith
  linarith

/-- Calibrated mass-action data and the associated cubic truncated-normal-form
periodic branch. No solution of the original mass-action ODE is asserted here. -/
theorem verdict :
    hopfData.H.μ₀ ∈ closure branch ∧
      ∀ μ ∈ branch,
        0 < |2 * Real.pi / hopfData.H.cycleFreq
              (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov))|
        ∧ Function.Periodic
              (hopfData.H.hopfLimitCycle
                (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov)) 0)
              |2 * Real.pi / hopfData.H.cycleFreq
                (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov))|
        ∧ (∃ s t,
              (hopfData.H.hopfLimitCycle
                (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov)) 0) s
                ≠ (hopfData.H.hopfLimitCycle
                (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov)) 0) t)
        ∧ (∃ s,
              ‖(hopfData.H.hopfLimitCycle
                (Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov)) 0) s‖
                = Real.sqrt (-hopfData.H.α μ / hopfData.H.firstLyapunov)) := by
  have hcl : hopfData.H.μ₀ ∈ closure branch := by
    rw [hopfData.H_μ₀]
    exact branch_closure
  exact MassActionHopfTaylorData.truncatedNormalForm_periodicBranch hopfData branch hcl
    (fun ν hν => branch_sign ν hν) (fun ν hν => branch_freq ν hν)

end CRNT.Examples.HopfPlanar2
