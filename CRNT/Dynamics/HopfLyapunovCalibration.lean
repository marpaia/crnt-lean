import CRNT.Dynamics.NormalFormCubic

/-!
# The Guckenheimer–Holmes calibration of the resonant cubic coefficient

This module supplies the **calibration** that the field map of leaf **D16 (Hopf bifurcation)**
records as pending: the identification of the resonant cubic coefficient computed by the
Poincaré–Dulac machinery of `CRNT.Dynamics.NormalFormCubic` with the **classical
real-coordinate formula for the first Lyapunov coefficient** carried by
`CRNT.PlanarHopfData.lyapunovFromPartials`.

## 1. The complex/real Taylor relations

Write the planar field in the complex coordinate `w = u + i v` as `F = f + i g`, with `f, g` the
real components, and expand it in the pair `(w, w̄)`:

```
F w = λ w + q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄² + c₃₀ w³ + c₂₁ w² w̄ + c₁₂ w w̄² + c₀₃ w̄³ + O(w⁴).
```

The complex Taylor coefficients `q₂₀, q₁₁, q₀₂, c₃₀, c₂₁, c₁₂, c₀₃` are determined by the real
partial derivatives of `f` and `g` at the origin.  The relations are the classical ones obtained
by expanding `F(u + i v)` and matching coefficients of `u, v, u², uv, v², u³, u²v, uv², v³`:

* **Quadratic part.**  With `A₂₀ = q₂₀ + q₁₁ + q₀₂` (the coefficient of `u²`),
  `A₁₁ = 2i (q₂₀ - q₀₂)` (of `uv`) and `A₀₂ = -(q₂₀ - q₁₁ + q₀₂)` (of `v²`),

  ```
  f_xx = 2 Re A₂₀,  f_xy = -2 Im (q₂₀ - q₀₂),  f_yy = -2 Re (q₂₀ - q₁₁ + q₀₂),
  g_xx = 2 Im A₂₀,  g_xy =  2 Re (q₂₀ - q₀₂),  g_yy = -2 Im (q₂₀ - q₁₁ + q₀₂).
  ```

* **Cubic part.**  With `A₃₀ = c₃₀ + c₂₁ + c₁₂ + c₀₃` (the coefficient of `u³`),
  `A₂₁ = i(3c₃₀ + c₂₁ - c₁₂ - 3c₀₃)`, `A₁₂ = -3c₃₀ + c₂₁ + c₁₂ - 3c₀₃` and
  `A₀₃ = i(-c₃₀ + c₂₁ - c₁₂ + c₀₃)`,

  ```
  f_xxx = 6 Re A₃₀,     f_xxy = -2 Im (3c₃₀ + c₂₁ - c₁₂ - 3c₀₃),
  f_xyy = 2 Re A₁₂,     f_yyy =  6 Im (c₃₀ - c₂₁ + c₁₂ - c₀₃),
  g_xxx = 6 Im A₃₀,     g_xxy =  2 Re (3c₃₀ + c₂₁ - c₁₂ - 3c₀₃),
  g_xyy = 2 Im A₁₂,     g_yyy =  6 Re (-c₃₀ + c₂₁ - c₁₂ + c₀₃).
  ```

`realTaylorCoeffs` inverts these relations: it computes the complex Taylor coefficients of a
planar field from its real partial derivatives.  `quadForm_expansion` and `cubicForm_expansion`
are the *explicit expansions* which verify the relations; `planarPartialsOf` is the inverse
map, and `cubicCombination_eq` is the key consequence:

```
f_xxx + f_xyy + g_xxy + g_yyy = 16 Re c₂₁ ,
```

the harmonic combination appearing in the first Lyapunov coefficient is *exactly* sixteen times
the real part of the coefficient of the resonant monomial `w² w̄ = w |w|²`.

## 2. The Taylor data of the normal form

The normal form of `CRNT.Dynamics.NormalFormCubic` removes the quadratic part of a planar field
by the homological equation and computes the cubic part of the push-forward
(`pushB30, pushB21, pushB12, pushB03`); the resonant coefficient of the normal form is
`pushB21`, the coefficient of the resonant monomial `w² w̄`.  `normalFormTaylorData` collects
the Taylor data of that normal form, `normalForm_quadratic_removed` proves that its quadratic
part vanishes, and `normalForm_pushForward` is the push-forward identity of
`CRNT.Dynamics.NormalFormCubic` specialised to the quadratic removal: the quadratic part *and*
the correction coming from the composition of the quadratic part with the change of variables
both drop out, leaving the cubic part `cubicForm (pushB30 …) (pushB21 …) (pushB12 …)
(pushB03 …)`.

## 3. The calibration

`hopf_lyapunov_calibration` discharges, for the normal form at the crossing `λ = iω`
(`ω ≠ 0`), the two hypotheses of `CRNT.PlanarHopfData.lyapunovFromPartials_eq` for the real
partials of the normal form:

* the cubic group is `16 ℓ₁` (`normalForm_hcubic`, an instance of the key relation of §1),
* the harmonic correction vanishes (`normalForm_hquad`), because the quadratic part of the
  normal form has been removed and hence all its second-order partials vanish.

Consequently

```
H.lyapunovFromPartials … = H.firstLyapunov ,
```

i.e. the resonant cubic coefficient computed by the normal-form machinery **is** the
repository's real-coordinate first Lyapunov coefficient.

## 4. The classical Guckenheimer–Holmes formula

The same calibration, in its classical form, uses the *original* real partials of the field
(the quadratic part of which has *not* been removed).  `classical_formula` and
`classical_lyapunov_formula` prove the identity

```
Re (resonant coefficient of the normal form at λ = iω)
  = (1/16) (f_xxx + f_xyy + g_xxy + g_yyy)
    + (1/(16ω)) (f_xy (f_xx + f_yy) - g_xy (g_xx + g_yy) - f_xx g_xx + f_yy g_yy) ,
```

the classical expression for the first Lyapunov coefficient (Guckenheimer & Holmes,
*Nonlinear Oscillations, Dynamical Systems, and Bifurcations of Vector Fields*, §3.4; Kuznetsov,
*Elements of Applied Bifurcation Theory*, §3.5).  `classical_lyapunov` concludes that

```
H.lyapunovFromPartials … = H.firstLyapunov
```

for the *original* partials, i.e. the two descriptions of `ℓ₁` carried by the repository —
the complex normal-form coefficient `Re c₁` and the real-coordinate combination — agree.

## 5. A numerical instance

`CRNT.Hopf.Examples` runs the whole chain on the field `F w = w² + w² w̄` at the crossing
`λ = i`: its complex Taylor data are `q₂₀ = 1`, `q₁₁ = q₀₂ = 0`, `c₂₁ = 1`; the quadratic part
is removed by `h₂ = i w²`; the resonant coefficient of the normal form is `1`, so that the
first Lyapunov coefficient is `1`; and the classical real-coordinate formula applied to the
original partials gives `1` as well.

Depends on: `CRNT.Dynamics.NormalFormCubic`.
-/

namespace CRNT

namespace Hopf

open scoped BigOperators

/-! ## Part 1: the complex Taylor coefficients of a real planar field -/

/-- **The real partial derivatives of a planar field** `f + i g` at the origin, through third
order.  `fxx` is `∂_u² f`, `fxy` is `∂_u ∂_v f`, `fxxx` is `∂_u³ f`, and so on; the `g`‑fields
are the corresponding partials of the imaginary component `g`. -/
structure PlanarPartials where
  /-- `∂_u² f` -/ fxx : ℝ
  /-- `∂_u ∂_v f` -/ fxy : ℝ
  /-- `∂_v² f` -/ fyy : ℝ
  /-- `∂_u² g` -/ gxx : ℝ
  /-- `∂_u ∂_v g` -/ gxy : ℝ
  /-- `∂_v² g` -/ gyy : ℝ
  /-- `∂_u³ f` -/ fxxx : ℝ
  /-- `∂_u² ∂_v f` -/ fxxy : ℝ
  /-- `∂_u ∂_v² f` -/ fxyy : ℝ
  /-- `∂_v³ f` -/ fyyy : ℝ
  /-- `∂_u³ g` -/ gxxx : ℝ
  /-- `∂_u² ∂_v g` -/ gxxy : ℝ
  /-- `∂_u ∂_v² g` -/ gxyy : ℝ
  /-- `∂_v³ g` -/ gyyy : ℝ

/-- The coefficient of `u²` in the complex Taylor expansion of a real planar field:
`A₂₀ = (f_xx + i g_xx)/2`. -/
noncomputable def quadA20 (fxx gxx : ℝ) : ℂ := (fxx / 2) + (gxx / 2) * Complex.I

/-- The coefficient of `uv` in the complex Taylor expansion of a real planar field:
`A₁₁ = f_xy + i g_xy`. -/
noncomputable def quadA11 (fxy gxy : ℝ) : ℂ := fxy + gxy * Complex.I

/-- The coefficient of `v²` in the complex Taylor expansion of a real planar field:
`A₀₂ = (f_yy + i g_yy)/2`. -/
noncomputable def quadA02 (fyy gyy : ℝ) : ℂ := (fyy / 2) + (gyy / 2) * Complex.I

/-- The coefficient of `u³` in the complex Taylor expansion of a real planar field:
`A₃₀ = (f_xxx + i g_xxx)/6`. -/
noncomputable def cubicA30 (fxxx gxxx : ℝ) : ℂ := fxxx / 6 + gxxx / 6 * Complex.I

/-- The coefficient of `u²v` in the complex Taylor expansion of a real planar field:
`A₂₁ = (f_xxy + i g_xxy)/2`. -/
noncomputable def cubicA21 (fxxy gxxy : ℝ) : ℂ := fxxy / 2 + gxxy / 2 * Complex.I

/-- The coefficient of `uv²` in the complex Taylor expansion of a real planar field:
`A₁₂ = (f_xyy + i g_xyy)/2`. -/
noncomputable def cubicA12 (fxyy gxyy : ℝ) : ℂ := fxyy / 2 + gxyy / 2 * Complex.I

/-- The coefficient of `v³` in the complex Taylor expansion of a real planar field:
`A₀₃ = (f_yyy + i g_yyy)/6`. -/
noncomputable def cubicA03 (fyyy gyyy : ℝ) : ℂ := fyyy / 6 + gyyy / 6 * Complex.I

/-- **The quadratic Taylor coefficient `q₂₀`** of the real planar field with partials `P`:
`q₂₀ = (A₂₀ - A₀₂)/4 - i A₁₁/4`. -/
noncomputable def realTaylorQ20 (P : PlanarPartials) : ℂ :=
  (quadA20 P.fxx P.gxx - quadA02 P.fyy P.gyy) / 4 - Complex.I * quadA11 P.fxy P.gxy / 4

/-- **The quadratic Taylor coefficient `q₁₁`** of the real planar field with partials `P`:
`q₁₁ = (A₂₀ + A₀₂)/2`. -/
noncomputable def realTaylorQ11 (P : PlanarPartials) : ℂ :=
  (quadA20 P.fxx P.gxx + quadA02 P.fyy P.gyy) / 2

/-- **The quadratic Taylor coefficient `q₀₂`** of the real planar field with partials `P`:
`q₀₂ = (A₂₀ - A₀₂)/4 + i A₁₁/4`. -/
noncomputable def realTaylorQ02 (P : PlanarPartials) : ℂ :=
  (quadA20 P.fxx P.gxx - quadA02 P.fyy P.gyy) / 4 + Complex.I * quadA11 P.fxy P.gxy / 4

/-- **The cubic Taylor coefficient `c₃₀`** of the real planar field with partials `P`:
`c₃₀ = (A₃₀ + i A₀₃ - i A₂₁ - A₁₂)/8`. -/
noncomputable def realTaylorC30 (P : PlanarPartials) : ℂ :=
  (cubicA30 P.fxxx P.gxxx + Complex.I * cubicA03 P.fyyy P.gyyy
    - Complex.I * cubicA21 P.fxxy P.gxxy - cubicA12 P.fxyy P.gxyy) / 8

/-- **The cubic Taylor coefficient `c₂₁`** of the real planar field with partials `P`:
`c₂₁ = (3 A₃₀ - 3i A₀₃ - i A₂₁ + A₁₂)/8`.  This is the coefficient of the *resonant* monomial
`w² w̄ = w |w|²`. -/
noncomputable def realTaylorC21 (P : PlanarPartials) : ℂ :=
  (3 * cubicA30 P.fxxx P.gxxx - 3 * Complex.I * cubicA03 P.fyyy P.gyyy
    - Complex.I * cubicA21 P.fxxy P.gxxy + cubicA12 P.fxyy P.gxyy) / 8

/-- **The cubic Taylor coefficient `c₁₂`** of the real planar field with partials `P`:
`c₁₂ = (3 A₃₀ + 3i A₀₃ + i A₂₁ + A₁₂)/8`. -/
noncomputable def realTaylorC12 (P : PlanarPartials) : ℂ :=
  (3 * cubicA30 P.fxxx P.gxxx + 3 * Complex.I * cubicA03 P.fyyy P.gyyy
    + Complex.I * cubicA21 P.fxxy P.gxxy + cubicA12 P.fxyy P.gxyy) / 8

/-- **The cubic Taylor coefficient `c₀₃`** of the real planar field with partials `P`:
`c₀₃ = (A₃₀ - i A₀₃ + i A₂₁ - A₁₂)/8`. -/
noncomputable def realTaylorC03 (P : PlanarPartials) : ℂ :=
  (cubicA30 P.fxxx P.gxxx - Complex.I * cubicA03 P.fyyy P.gyyy
    + Complex.I * cubicA21 P.fxxy P.gxxy - cubicA12 P.fxyy P.gxyy) / 8

/-- **The quadratic Taylor coefficients** `(q₂₀, q₁₁, q₀₂)` of the real planar field with
partials `P`. -/
noncomputable def realTaylorQuad (P : PlanarPartials) : ℂ × ℂ × ℂ :=
  (realTaylorQ20 P, realTaylorQ11 P, realTaylorQ02 P)

/-- **The cubic Taylor coefficients** `(c₃₀, c₂₁, c₁₂, c₀₃)` of the real planar field with
partials `P`. -/
noncomputable def realTaylorCubic (P : PlanarPartials) : ℂ × ℂ × ℂ × ℂ :=
  (realTaylorC30 P, realTaylorC21 P, realTaylorC12 P, realTaylorC03 P)

/-- **The complex Taylor coefficients of a real planar field.**  The first component is the
quadratic triple `(q₂₀, q₁₁, q₀₂)`, the second the cubic quadruple `(c₃₀, c₂₁, c₁₂, c₀₃)`: the
coefficients of the expansion of `F w = f + i g` in the pair `(w, w̄)`, where `w = u + i v`. -/
noncomputable def realTaylorCoeffs
    (fxx fxy fyy gxx gxy gyy fxxx fxxy fxyy fyyy gxxx gxxy gxyy gyyy : ℝ) :
    (ℂ × ℂ × ℂ) × (ℂ × ℂ × ℂ × ℂ) :=
  (realTaylorQuad ⟨fxx, fxy, fyy, gxx, gxy, gyy, fxxx, fxxy, fxyy, fyyy, gxxx, gxxy, gxyy, gyyy⟩,
   realTaylorCubic ⟨fxx, fxy, fyy, gxx, gxy, gyy, fxxx, fxxy, fxyy, fyyy, gxxx, gxxy, gxyy, gyyy⟩)

/-- **The real partial derivatives recovered from the complex Taylor coefficients.**  The
quadratic partials are read off from `(q₂₀, q₁₁, q₀₂)` and the cubic ones from
`(c₃₀, c₂₁, c₁₂, c₀₃)` by the relations of §1. -/
noncomputable def planarPartialsOf
    (q20 q11 q02 c30 c21 c12 c03 : ℂ) : PlanarPartials where
  fxx := 2 * (q20 + q11 + q02).re
  fxy := -2 * (q20 - q02).im
  fyy := -2 * (q20 - q11 + q02).re
  gxx := 2 * (q20 + q11 + q02).im
  gxy := 2 * (q20 - q02).re
  gyy := -2 * (q20 - q11 + q02).im
  fxxx := 6 * (c30 + c21 + c12 + c03).re
  fxxy := -2 * (3 * c30 + c21 - c12 - 3 * c03).im
  fxyy := 2 * (-3 * c30 + c21 + c12 - 3 * c03).re
  fyyy := 6 * (c30 - c21 + c12 - c03).im
  gxxx := 6 * (c30 + c21 + c12 + c03).im
  gxxy := 2 * (3 * c30 + c21 - c12 - 3 * c03).re
  gxyy := 2 * (-3 * c30 + c21 + c12 - 3 * c03).im
  gyyy := 6 * (-c30 + c21 - c12 + c03).re

/-! ### The explicit expansions -/

/-- **The expansion of the quadratic part of a planar field in real coordinates.**  With
`w = u + i v`,

```
q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄²
  = (q₂₀+q₁₁+q₀₂) u² + 2i (q₂₀-q₀₂) u v - (q₂₀-q₁₁+q₀₂) v² ,
```

so that the real part is the quadratic polynomial with coefficients `f_xx/2, f_xy, f_yy/2` and
the imaginary part the one with coefficients `g_xx/2, g_xy, g_yy/2` (the relations of §1). -/
theorem quadForm_expansion (q20 q11 q02 : ℂ) (u v : ℝ) :
    quadForm q20 q11 q02 ((u : ℂ) + (v : ℂ) * Complex.I)
      = (((q20 + q11 + q02).re) * u ^ 2 - 2 * ((q20 - q02).im) * u * v
        - ((q20 - q11 + q02).re) * v ^ 2 : ℝ)
        + Complex.I * (((q20 + q11 + q02).im) * u ^ 2 + 2 * ((q20 - q02).re) * u * v
          - ((q20 - q11 + q02).im) * v ^ 2) := by
  apply Complex.ext <;>
    simp [quadForm, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, cconj, pow_succ] <;> ring

/-- **The expansion of the cubic part of a planar field in real coordinates.**  With
`w = u + i v`,

```
c₃₀ w³ + c₂₁ w² w̄ + c₁₂ w w̄² + c₀₃ w̄³
  = (c₃₀+c₂₁+c₁₂+c₀₃) u³ + i(3c₃₀+c₂₁-c₁₂-3c₀₃) u² v
    + (-3c₃₀+c₂₁+c₁₂-3c₀₃) u v² + i(-c₃₀+c₂₁-c₁₂+c₀₃) v³ ,
```

so that the real part is the cubic polynomial with coefficients `f_xxx/6, f_xxy/2, f_xyy/2,
f_yyy/6` and the imaginary part the one with coefficients `g_xxx/6, g_xxy/2, g_xyy/2, g_yyy/6`
(the relations of §1). -/
theorem cubicForm_expansion (c30 c21 c12 c03 : ℂ) (u v : ℝ) :
    cubicForm c30 c21 c12 c03 ((u : ℂ) + (v : ℂ) * Complex.I)
      = (((c30 + c21 + c12 + c03).re) * u ^ 3
        - ((3 * c30 + c21 - c12 - 3 * c03).im) * u ^ 2 * v
        + ((-3 * c30 + c21 + c12 - 3 * c03).re) * u * v ^ 2
        - ((-c30 + c21 - c12 + c03).im) * v ^ 3 : ℝ)
        + Complex.I * (((c30 + c21 + c12 + c03).im) * u ^ 3
          + ((3 * c30 + c21 - c12 - 3 * c03).re) * u ^ 2 * v
          + ((-3 * c30 + c21 + c12 - 3 * c03).im) * u * v ^ 2
          + ((-c30 + c21 - c12 + c03).re) * v ^ 3) := by
  apply Complex.ext <;>
    simp [cubicForm, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, cconj, pow_succ] <;> ring

/-! ### The relations are inverse to each other -/

/-- **The two Taylor maps are inverse.**  The complex Taylor coefficients computed from the real
partial derivatives (`realTaylorQ20`, …) determine those partials again, through
`planarPartialsOf`: the relations of §1 are exactly the statement that the two descriptions of
the Taylor expansion of a planar field agree. -/
theorem planarPartialsOf_realTaylor (P : PlanarPartials) :
    planarPartialsOf (realTaylorQ20 P) (realTaylorQ11 P) (realTaylorQ02 P)
      (realTaylorC30 P) (realTaylorC21 P) (realTaylorC12 P) (realTaylorC03 P) = P := by
  cases P with
  | mk fxx fxy fyy gxx gxy gyy fxxx fxxy fxyy fyyy gxxx gxxy gxyy gyyy =>
    simp [planarPartialsOf, realTaylorQ20, realTaylorQ11, realTaylorQ02, realTaylorC30,
      realTaylorC21, realTaylorC12, realTaylorC03, quadA20, quadA11, quadA02, cubicA30,
      cubicA21, cubicA12, cubicA03, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    repeat' constructor
    all_goals ring

/-- **The key relation: the harmonic combination is sixteen times the resonant coefficient.**
For a planar field whose complex cubic Taylor coefficients are `c₃₀, c₂₁, c₁₂, c₀₃`, the real
partials of §1 satisfy

```
f_xxx + f_xyy + g_xxy + g_yyy = 16 Re c₂₁ ,
```

the left-hand side being exactly the combination that appears in the classical formula for the
first Lyapunov coefficient. -/
theorem cubicCombination_eq (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxxx
      + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxyy
      + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gxxy
      + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gyyy
      = 16 * c21.re := by
  simp [planarPartialsOf, Complex.add_re, Complex.mul_re]
  ring

/-! ## Part 2: the Taylor data of the normal form -/

/-- **The Taylor data of the normal form** of a planar field: the quadratic part (which the
homological equation removes) and the cubic part of the push-forward computed by
`CRNT.Dynamics.NormalFormCubic`.  The resonant coefficient is `c21`, the coefficient of the
resonant monomial `w² w̄ = w |w|²`. -/
structure NormalFormData where
  /-- The `w²` coefficient of the quadratic part of the transformed field. -/ q20 : ℂ
  /-- The `w w̄` coefficient of the quadratic part of the transformed field. -/ q11 : ℂ
  /-- The `w̄²` coefficient of the quadratic part of the transformed field. -/ q02 : ℂ
  /-- The `w³` coefficient of the cubic part of the transformed field. -/ c30 : ℂ
  /-- The `w² w̄` coefficient of the cubic part of the transformed field: the resonant
  coefficient of the normal form. -/ c21 : ℂ
  /-- The `w w̄²` coefficient of the cubic part of the transformed field. -/ c12 : ℂ
  /-- The `w̄³` coefficient of the cubic part of the transformed field. -/ c03 : ℂ

/-- **The Taylor data of the normal form of a planar field.**  The field is the one with linear
part `lam w`, quadratic part `q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄²` and cubic part `c₃₀ w³ + c₂₁ w² w̄ +
c₁₂ w w̄² + c₀₃ w̄³`; the normal form is obtained by the quadratic change of variables solving
the degree-two homological equation, so its quadratic part is `Q - L h₂` and its cubic part is
the cubic part of the push-forward. -/
noncomputable def normalFormTaylorData (lam : ℂ) (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    NormalFormData where
  q20 := pushA20 lam q20 (h20Sol lam q20)
  q11 := pushA11 lam q11 (h11Sol lam q11)
  q02 := pushA02 lam q02 (h02Sol lam q02)
  c30 := pushB30 lam q20 q11 q02 c30 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)
  c21 := pushB21 lam q20 q11 q02 c21 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)
  c12 := pushB12 lam q20 q11 q02 c12 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)
  c03 := pushB03 lam q20 q11 q02 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)

/-- **The quadratic part of the normal form vanishes.**  For `lam ≠ 0` the solution of the
degree-two homological equation removes the quadratic terms: `Q - L h₂ = 0`. -/
theorem normalForm_quadratic_removed {lam : ℂ} (hlam : lam ≠ 0) (q20 q11 q02 : ℂ) :
    pushA20 lam q20 (h20Sol lam q20) = 0
      ∧ pushA11 lam q11 (h11Sol lam q11) = 0
      ∧ pushA02 lam q02 (h02Sol lam q02) = 0 := by
  have hc : cconj lam ≠ 0 := by
    intro hc
    exact hlam (cconj_eq_zero.mp hc)
  have hd : lam - 2 * cconj lam ≠ 0 := by
    intro hz
    exact hlam (lam_sub_two_cconj_eq_zero.mp hz)
  refine ⟨?_, ?_, ?_⟩
  · simp [pushA20, h20Sol]
    field_simp
    ring
  · simp [pushA11, h11Sol]
    field_simp
    ring
  · simp [pushA02, h02Sol]
    field_simp
    ring

/-- **The cubic correction of the push-forward vanishes once the quadratic part is removed.**
The coefficients `pushD30, pushD21, pushD12, pushD03` are the cubic part of the quadratic part
of the transformed field composed with the change of variables; when the quadratic part
vanishes, so do they. -/
theorem pushD_eq_zero {lam : ℂ} {q20 q11 q02 h20 h11 h02 : ℂ}
    (hq20 : q20 + lam * h20 = 0) (hq11 : q11 + cconj lam * h11 = 0)
    (hq02 : q02 - (lam - 2 * cconj lam) * h02 = 0) :
    pushD30 lam q20 q11 q02 h20 h11 h02 = 0
      ∧ pushD21 lam q20 q11 q02 h20 h11 h02 = 0
      ∧ pushD12 lam q20 q11 q02 h20 h11 h02 = 0
      ∧ pushD03 lam q20 q11 q02 h20 h11 h02 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pushD30]
    linear_combination (cconj h02) * hq11 + (2 * h20) * hq20
  · simp only [pushD21]
    linear_combination (cconj h11 + h20) * hq11 + (2 * h11) * hq20 + (2 * cconj h02) * hq02
  · simp only [pushD12]
    linear_combination (cconj h20 + h11) * hq11 + (2 * h02) * hq20 + (2 * cconj h11) * hq02
  · simp only [pushD03]
    linear_combination h02 * hq11 + (2 * cconj h20) * hq02

/-- **The push-forward identity for the normal form.**  Let the planar field have linear part
`lam w`, quadratic part `Q` and cubic part `C`, and let `φ w = w + h₂(w)` be the quadratic change
of variables solving the degree-two homological equation.  Then the push-forward of the field is

```
lam φ w + (cubic part) + (quartic remainder) ,
```

the quadratic part having vanished.  This is `CRNT.Dynamics.NormalFormCubic.cubic_pushForward`
specialised to the homological solution: the quadratic coefficients `pushA20, pushA11, pushA02`
and the cubic coefficients `pushD30, pushD21, pushD12, pushD03` all vanish, and the cubic part
of the transformed field is `cubicForm (pushB30 …) (pushB21 …) (pushB12 …) (pushB03 …)`, whose
resonant coefficient is `pushB21`. -/
theorem normalForm_pushForward {lam : ℂ} (hlam : lam ≠ 0)
    (q20 q11 q02 c30 c21 c12 c03 : ℂ) (w : ℂ) :
    (1 + quadW (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02) w)
        * planarField3 lam q20 q11 q02 c30 c21 c12 c03 w
      + quadWbar (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02) w
        * cconj (planarField3 lam q20 q11 q02 c30 c21 c12 c03 w)
    = lam * (w + quadForm (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02) w)
      + cubicForm (pushB30 lam q20 q11 q02 c30 (h20Sol lam q20) (h11Sol lam q11)
          (h02Sol lam q02))
        (pushB21 lam q20 q11 q02 c21 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushB12 lam q20 q11 q02 c12 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushB03 lam q20 q11 q02 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)) w
      + quarticForm (pushR40 c30 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushR31 c30 c21 c12 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushR22 c30 c21 c12 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushR13 c30 c21 c12 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02))
        (pushR04 c30 c21 c12 c03 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)) w := by
  rw [cubic_pushForward]
  have hq20 : q20 + lam * (h20Sol lam q20) = 0 := by
    simp [h20Sol]
    field_simp
    ring
  have hq11 : q11 + cconj lam * (h11Sol lam q11) = 0 := by
    have hc : cconj lam ≠ 0 := by
      intro hc
      exact hlam (cconj_eq_zero.mp hc)
    simp [h11Sol]
    field_simp
    ring
  have hq02 : q02 - (lam - 2 * cconj lam) * (h02Sol lam q02) = 0 := by
    have hd : lam - 2 * cconj lam ≠ 0 := by
      intro hz
      exact hlam (lam_sub_two_cconj_eq_zero.mp hz)
    simp [h02Sol]
    field_simp
    ring
  have hd := pushD_eq_zero hq20 hq11 hq02
  simp only [pushA20, pushA11, pushA02]
  rw [hq20, hq11, hq02, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  simp [quadForm, cubicForm]

/-! ## Part 3: the calibration -/

/-- **The real partials of the normal form** of the planar field with the given Taylor data.
They are the partials of the transformed field, i.e. of the field in the *normal-form*
coordinates. -/
noncomputable def normalFormPartials (lam : ℂ) (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    PlanarPartials :=
  planarPartialsOf (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q20
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q11
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q02
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c30
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c21
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c12
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c03

/-- **The harmonic correction vanishes for the normal form.**  The quadratic part of the normal
form is zero, so all second-order partials of the transformed field vanish and the quadratic
combination

```
f_xy (f_xx + f_yy) - g_xy (g_xx + g_yy) - f_xx g_xx + f_yy g_yy
```

of the classical first Lyapunov formula is zero. -/
theorem normalForm_hquad {lam : ℂ} (hlam : lam ≠ 0)
    (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fxy
        * ((normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fxx
          + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fyy)
      - (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gxy
        * ((normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gxx
          + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gyy)
      - (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fxx
        * (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gxx
      + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fyy
        * (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gyy = 0 := by
  obtain ⟨h0, h1, h2⟩ := normalForm_quadratic_removed hlam q20 q11 q02
  simp [normalFormPartials, planarPartialsOf, normalFormTaylorData, h0, h1, h2]

/-- **The cubic group of the normal form is sixteen times the resonant coefficient.**  By the
key relation of §1, applied to the cubic part of the normal form. -/
theorem normalForm_hcubic {lam : ℂ} (_hlam : lam ≠ 0)
    (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fxxx
      + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).fxyy
      + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gxxy
      + (normalFormPartials lam q20 q11 q02 c30 c21 c12 c03).gyyy
      = 16 * (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c21.re := by
  exact cubicCombination_eq (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q20
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q11
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).q02
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c30
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c21
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c12
    (normalFormTaylorData lam q20 q11 q02 c30 c21 c12 c03).c03

/-- **The Hopf normal-form data of a planar field at the crossing `λ = iω`.**  The linear part is
purely imaginary with frequency `ω ≠ 0`, the unfolding is `α μ = μ` (so the crossing is at
`μ₀ = 0` and the crossing speed is `1`), and the resonant cubic coefficient is `c₁`. -/
noncomputable def hopfNormalFormData (ω : ℝ) (hω : ω ≠ 0) (c₁ : ℂ) : PlanarHopfData where
  μ₀ := 0
  ω := ω
  ω_ne := hω
  α := fun μ => μ
  α_crossing := by simp
  α' := 1
  hasDeriv_α := hasDerivAt_id 0
  c₁ := c₁
  normalForm := fun μ w => ((μ : ℂ) + ω * Complex.I) * w + c₁ * (w * (Complex.normSq w : ℂ))
  normalForm_eq := by
    intro _ w
    rfl

/-- **The Guckenheimer–Holmes calibration.**  Let `ω ≠ 0`, let a planar field have the complex
Taylor data `(q₂₀, q₁₁, q₀₂, c₃₀, c₂₁, c₁₂, c₀₃)`, and let `H` be Hopf normal-form data whose
resonant cubic coefficient `c₁` is the resonant coefficient `resonantCoefficientSol` of the
Poincaré–Dulac normal form of that field at the crossing `λ = iω` — the coefficient computed by
`CRNT.Dynamics.NormalFormCubic`.  Then the two hypotheses of
`CRNT.PlanarHopfData.lyapunovFromPartials_eq` hold for the real partials `P` of the normal
form:

* the cubic group is `16 ℓ₁`, where `ℓ₁ = Re c₁` is the first Lyapunov coefficient;
* the harmonic correction vanishes, the quadratic part of the normal form having been removed.

Consequently `H.lyapunovFromPartials … = H.firstLyapunov`: the resonant cubic coefficient of
the normal form **is** the classical real-coordinate first Lyapunov coefficient. -/
theorem hopf_lyapunov_calibration {ω : ℝ} (hω : ω ≠ 0)
    (q20 q11 q02 c30 c21 c12 c03 : ℂ) (H : PlanarHopfData)
    (hH : H.c₁ = resonantCoefficientSol ((ω : ℂ) * Complex.I) q20 q11 q02 c21) :
    let P := normalFormPartials ((ω : ℂ) * Complex.I) q20 q11 q02 c30 c21 c12 c03
    H.lyapunovFromPartials P.fxxx P.fxyy P.gxxy P.gyyy P.fxy P.fxx P.fyy P.gxy P.gxx P.gyy
      = H.firstLyapunov := by
  dsimp only
  have hω' : ((ω : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have h1 := congrArg Complex.im hz
    simp at h1
    exact hω h1
  refine H.lyapunovFromPartials_eq ?_ ?_
  · rw [normalForm_hcubic hω' q20 q11 q02 c30 c21 c12 c03]
    have h21 : (normalFormTaylorData ((ω : ℂ) * Complex.I) q20 q11 q02 c30 c21 c12 c03).c21
        = resonantCoefficientSol ((ω : ℂ) * Complex.I) q20 q11 q02 c21 := by
      simp [normalFormTaylorData, resonantCoefficientSol]
    rw [h21]
    simp [PlanarHopfData.firstLyapunov, hH]
  · exact normalForm_hquad hω' q20 q11 q02 c30 c21 c12 c03

/-! ## Part 4: the classical Guckenheimer–Holmes formula -/

/-- **The harmonic (quadratic) combination** of the real partials of a planar field, written in
terms of the complex quadratic Taylor coefficients `q₂₀, q₁₁, q₀₂`:

```
f_xy (f_xx + f_yy) - g_xy (g_xx + g_yy) - f_xx g_xx + f_yy g_yy ,
```

the correction term of the classical first Lyapunov formula. -/
noncomputable def quadCombination (q20 q11 q02 : ℂ) : ℝ :=
  (-2 * (q20 - q02).im) * (2 * (q20 + q11 + q02).re - 2 * (q20 - q11 + q02).re)
    - (2 * (q20 - q02).re) * (2 * (q20 + q11 + q02).im - 2 * (q20 - q11 + q02).im)
    - (2 * (q20 + q11 + q02).re) * (2 * (q20 + q11 + q02).im)
    + (2 * (q20 - q11 + q02).re) * (2 * (q20 - q11 + q02).im)

/-- **The harmonic combination is the quadratic combination of the partials.**  The relation of
§1 for the quadratic Taylor coefficients. -/
theorem quadCombination_eq (q20 q11 q02 c30 c21 c12 c03 : ℂ) :
    quadCombination q20 q11 q02
      = (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxy
          * ((planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxx
            + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fyy)
        - (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gxy
          * ((planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gxx
            + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gyy)
        - (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fxx
          * (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gxx
        + (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).fyy
          * (planarPartialsOf q20 q11 q02 c30 c21 c12 c03).gyy := by
  simp [quadCombination, planarPartialsOf, Complex.add_re, Complex.sub_re, Complex.mul_re]
  ring

set_option maxHeartbeats 800000 in
/-- **The Guckenheimer–Holmes formula for the resonant coefficient.**  At the crossing
`λ = iω` (`ω ≠ 0`), the real part of the resonant coefficient of the Poincaré–Dulac normal form
of a planar field with complex quadratic Taylor coefficients `q₂₀, q₁₁, q₀₂` and resonant cubic
coefficient `c₂₁` is

```
Re c₂₁ + (1/(16ω)) · (the harmonic combination) ,
```

that is: the resonant coefficient of the normal form is the resonant cubic Taylor coefficient of
the *original* field, corrected by the quadratic term that the normal-form transformation
removes. -/
theorem classical_formula {ω : ℝ} (hω : ω ≠ 0) (q20 q11 q02 c21 : ℂ) :
    (resonantCoefficientSol ((ω : ℂ) * Complex.I) q20 q11 q02 c21).re
      = c21.re + (1/(16 * ω)) * quadCombination q20 q11 q02 := by
  simp only [resonantCoefficientSol, pushB21, h20Sol, h11Sol, h02Sol]
  simp [cconj, Complex.conj_re, Complex.conj_im, div_eq_mul_inv, Complex.inv_I, quadCombination,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-- **The classical real-coordinate formula for the first Lyapunov coefficient.**  For a planar
field with the real partials `P`, the real part of the resonant coefficient of its
Poincaré–Dulac normal form at the crossing `λ = iω` is

```
(1/16) (f_xxx + f_xyy + g_xxy + g_yyy)
  + (1/(16ω)) (f_xy (f_xx + f_yy) - g_xy (g_xx + g_yy) - f_xx g_xx + f_yy g_yy) ,
```

the classical Guckenheimer–Holmes expression for the first Lyapunov coefficient (Kuznetsov,
*Elements of Applied Bifurcation Theory*, §3.5). -/
theorem classical_lyapunov_formula {ω : ℝ} (hω : ω ≠ 0) (P : PlanarPartials) :
    (resonantCoefficientSol ((ω : ℂ) * Complex.I) (realTaylorQ20 P) (realTaylorQ11 P)
      (realTaylorQ02 P) (realTaylorC21 P)).re
      = (1/16) * (P.fxxx + P.fxyy + P.gxxy + P.gyyy)
        + (1/(16 * ω)) * (P.fxy * (P.fxx + P.fyy) - P.gxy * (P.gxx + P.gyy)
            - P.fxx * P.gxx + P.fyy * P.gyy) := by
  rw [classical_formula hω _ _ _ _]
  have hkey : (1/16) * (P.fxxx + P.fxyy + P.gxxy + P.gyyy) = (realTaylorC21 P).re := by
    have h := cubicCombination_eq (realTaylorQ20 P) (realTaylorQ11 P) (realTaylorQ02 P)
      (realTaylorC30 P) (realTaylorC21 P) (realTaylorC12 P) (realTaylorC03 P)
    rw [planarPartialsOf_realTaylor P] at h
    rw [h]
    field_simp
  have hquad : quadCombination (realTaylorQ20 P) (realTaylorQ11 P) (realTaylorQ02 P)
      = P.fxy * (P.fxx + P.fyy) - P.gxy * (P.gxx + P.gyy) - P.fxx * P.gxx + P.fyy * P.gyy := by
    have h := quadCombination_eq (realTaylorQ20 P) (realTaylorQ11 P) (realTaylorQ02 P)
      (realTaylorC30 P) (realTaylorC21 P) (realTaylorC12 P) (realTaylorC03 P)
    rw [planarPartialsOf_realTaylor P] at h
    exact h
  rw [hkey, hquad]

/-- **The calibration in the classical form.**  Let `H` be Hopf normal-form data whose resonant
cubic coefficient is the resonant coefficient of the Poincaré–Dulac normal form of a planar
field with the real partials `P`, at the crossing `λ = iω`.  Then the classical real-coordinate
expression `lyapunovFromPartials` evaluated at the *original* partials of the field equals the
first Lyapunov coefficient `ℓ₁ = Re c₁` of the normal form: the resonant cubic coefficient
computed by the normal-form machinery **is** the repository's real-coordinate first Lyapunov
coefficient. -/
theorem classical_lyapunov {ω : ℝ} (hω : ω ≠ 0) (P : PlanarPartials) (H : PlanarHopfData)
    (hωH : H.ω = ω)
    (hH : H.c₁ = resonantCoefficientSol ((ω : ℂ) * Complex.I) (realTaylorQ20 P)
      (realTaylorQ11 P) (realTaylorQ02 P) (realTaylorC21 P)) :
    H.lyapunovFromPartials P.fxxx P.fxyy P.gxxy P.gyyy P.fxy P.fxx P.fyy P.gxy P.gxx P.gyy
      = H.firstLyapunov := by
  rw [PlanarHopfData.lyapunovFromPartials, hωH]
  have h := classical_lyapunov_formula hω P
  simp only [PlanarHopfData.firstLyapunov]
  rw [hH]
  exact h.symm

/-! ## Part 5: a numerical instance -/

/-- **Complex conjugation commutes with inversion.** -/
lemma cconj_inv (z : ℂ) : cconj z⁻¹ = (cconj z)⁻¹ := by
  simp [cconj]

/-- **Complex conjugation commutes with division.** -/
lemma cconj_div (z w : ℂ) : cconj (z / w) = cconj z / cconj w := by
  rw [div_eq_mul_inv, cconj_mul, cconj_inv]
  ring

namespace Examples

/-- The Hopf frequency of the example: `ω = 1`, i.e. the purely imaginary linear part `λ = i`. -/
def ωex : ℝ := 1

/-- The example field: `F w = w² + w² w̄`, i.e. `f(u,v) = u² - v² + u³ + u v²` and
`g(u,v) = 2uv + u²v + v³`.  Its partials are `f_xx = 2, f_xy = 0, f_yy = -2`,
`g_xx = 0, g_xy = 2, g_yy = 0`, `f_xxx = 6, f_xxy = 0, f_xyy = 2, f_yyy = 0`,
`g_xxx = 0, g_xxy = 2, g_xyy = 0, g_yyy = 6`. -/
def partialsEx : PlanarPartials :=
  ⟨2, 0, -2, 0, 2, 0, 6, 0, 2, 0, 0, 2, 0, 6⟩

/-- **The Taylor coefficients of the example field.**  The complex Taylor data of
`F w = w² + w² w̄` are `q₂₀ = 1`, `q₁₁ = q₀₂ = 0` and `c₂₁ = 1`, all the other cubic
coefficients vanishing; the resonant monomial `w² w̄` carries the coefficient `1`. -/
theorem taylorCoefficients_ex :
    realTaylorQ20 partialsEx = 1 ∧ realTaylorQ11 partialsEx = 0 ∧
      realTaylorQ02 partialsEx = 0 ∧ realTaylorC30 partialsEx = 0 ∧
      realTaylorC21 partialsEx = 1 ∧ realTaylorC12 partialsEx = 0 ∧
      realTaylorC03 partialsEx = 0 := by
  simp [realTaylorQ20, realTaylorQ11, realTaylorQ02, realTaylorC30, realTaylorC21, realTaylorC12,
    realTaylorC03, quadA20, quadA11, quadA02, cubicA30, cubicA21, cubicA12, cubicA03,
    partialsEx]
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

/-- **The resonant coefficient of the normal form of the example field.**  For `λ = i`, the
quadratic part `w²` is removed by the homological equation (the correction is `h₂ = i w²`) and
the resonant cubic coefficient of the transformed field is `1`: the quadratic part `w²` does not
contribute to the resonant monomial `w² w̄`.  Its real part `1` is the first Lyapunov
coefficient of the example. -/
theorem resonantCoefficient_ex :
    resonantCoefficientSol Complex.I 1 0 0 1 = 1 := by
  simp [resonantCoefficientSol, pushB21, h20Sol, h11Sol, h02Sol, div_eq_mul_inv, Complex.inv_I]

/-- **The first Lyapunov coefficient of the example.**  It is the real part of the resonant
coefficient of the normal form, `1`. -/
theorem firstLyapunov_ex :
    (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).firstLyapunov = 1 := by
  rw [resonantCoefficient_ex]
  simp [hopfNormalFormData, PlanarHopfData.firstLyapunov]

/-- **The classical real-coordinate formula for the example.**  The formula
`lyapunovFromPartials` applied to the *original* real partials of the example field — whose
quadratic part has *not* been removed — gives `1`, the same number as the real part of the
resonant coefficient of the normal form: this is the Guckenheimer–Holmes calibration on a
concrete instance. -/
theorem lyapunovFromPartials_ex :
    (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).lyapunovFromPartials
      6 2 2 6 0 2 (-2) 2 0 0 = 1 := by
  simp [hopfNormalFormData, PlanarHopfData.lyapunovFromPartials, ωex]
  ring

/-- **The calibration for the example.**  The two hypotheses of
`CRNT.PlanarHopfData.lyapunovFromPartials_eq` hold for the real partials of the normal form of
the example field, so that `lyapunovFromPartials` of those partials is the first Lyapunov
coefficient. -/
theorem calibration_ex :
    (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).lyapunovFromPartials
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).fxxx
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).fxyy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).gxxy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).gyyy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).fxy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).fxx
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).fyy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).gxy
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).gxx
      (normalFormPartials Complex.I 1 0 0 0 1 0 0).gyy
    = (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).firstLyapunov := by
  have h := hopf_lyapunov_calibration (ω := ωex) (by norm_num [ωex])
    (q20 := 1) (q11 := 0) (q02 := 0) (c30 := 0) (c21 := 1) (c12 := 0) (c03 := 0)
    (H := hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1))
    (by simp [hopfNormalFormData, ωex])
  simpa [ωex] using h

/-- **The classical calibration for the example.**  The classical real-coordinate expression
`lyapunovFromPartials`, evaluated at the *original* partials of the example field, equals the
first Lyapunov coefficient of its normal form: this is `classical_lyapunov` applied to the
example. -/
theorem classical_lyapunov_ex :
    (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).lyapunovFromPartials
      (partialsEx.fxxx) (partialsEx.fxyy) (partialsEx.gxxy) (partialsEx.gyyy)
      (partialsEx.fxy) (partialsEx.fxx) (partialsEx.fyy) (partialsEx.gxy)
      (partialsEx.gxx) (partialsEx.gyy)
    = (hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1)).firstLyapunov := by
  have h := classical_lyapunov (ω := ωex) (by norm_num [ωex]) (P := partialsEx)
    (H := hopfNormalFormData ωex (by norm_num [ωex])
      (resonantCoefficientSol Complex.I 1 0 0 1))
    (by rfl)
    (by simp [hopfNormalFormData, taylorCoefficients_ex, ωex])
  simpa [ωex] using h

/-- The second example field: `f(u,v) = u² + u v` and `g(u,v) = 0`.  Its second order partials are
`f_xx = 2, f_xy = 1, f_yy = 0` and `g_xx = g_xy = g_yy = 0`, and all third order partials
vanish. -/
def partials2Ex : PlanarPartials :=
  ⟨2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **A second instance: the quadratic correction.**  For the field `f(u,v) = u² + u v`,
`g(u,v) = 0` the resonant cubic Taylor coefficient of the *original* field is `c₂₁ = 0`, but the
quadratic part `q₂₀ = (1-i)/4`, `q₁₁ = 1/2`, `q₀₂ = (1+i)/4` is not removed by the field itself:
the normal form acquires a resonant cubic coefficient whose real part is `1/8`, exactly the
classical value `(1/(16ω))(f_xy(f_xx+f_yy)) = 1/8` of the first Lyapunov coefficient.  This
instance exercises the quadratic (harmonic) correction of the calibration. -/
theorem classical_formula_2Ex :
    (resonantCoefficientSol (((1 : ℝ) : ℂ) * Complex.I) (realTaylorQ20 partials2Ex)
      (realTaylorQ11 partials2Ex) (realTaylorQ02 partials2Ex)
      (realTaylorC21 partials2Ex)).re = 1 / 8 := by
  rw [classical_lyapunov_formula (by norm_num) partials2Ex]
  simp [partials2Ex]
  ring

end Examples

end Hopf
end CRNT
