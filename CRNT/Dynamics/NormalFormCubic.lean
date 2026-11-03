import CRNT.Dynamics.HopfNormalForm

/-!
# Poincaré–Dulac normal form to cubic order (the algebraic content of center-manifold averaging)

This module formalizes the **Poincaré–Dulac normal form to cubic order** for planar (two-dimensional)
vector fields, together with the **homological equation** that removes the quadratic terms at a Hopf
crossing.  It is the concrete mathematical content of the "center-manifold averaging" step that the
field map of leaf **D16 (Hopf bifurcation)** still records as pending: the near-identity
transformations, the homological equation and its solution, the uniqueness of the quadratic removal,
and the explicit resonant cubic coefficient.

## 1. Conventions (and why they are the ones used here)

**Push-forward.**  For a near-identity change of variables `z = φ(w)` (`φ(0) = 0`, `Dφ(0) = I`) the
transformed field `G` is the push-forward of `F` by `φ`:

```
G (φ w) = Dφ(w) · F w .
```

For a *complex-holomorphic* field (`ẇ = F(w)`, `w ∈ ℂ`) this reads `G (φ w) = φ'(w) F w`; for a
*real planar* field written in complex coordinates (`F(w, w̄) = f + i g`) it reads
`G (φ w) = φ_w · F(w) + φ_{w̄} · conj (F w)`, the two Wirtinger derivatives acting on the field.

This convention is the one for which the classical quadratic correction is `c = −a/λ`: it is the
convention in which the change of variables is `z = φ(w)` (the *new* coordinate is `φ` of the old
one).  The Taylor expansion of `G` at the origin is the expansion of `G ∘ φ`, because `φ` is tangent
to the identity; the two are compared in this module through **explicit polynomial identities**, so
that no `O(·)` notation is needed.

**Remark on the naive formula.**  The composition `φ' ∘ F ∘ φ` that sometimes appears in the
literature is *not* the normal-form transformation (it is the push-forward composed with the
substitution instead of the pull-back); with `φ w = w + c w²` and `c = −a/λ` it leaves a quadratic
term `−2a w²`.  The push-forward used here removes it exactly.

### 1.1 The complex-holomorphic cubic field (Parts 1 and 2)

For `F w = λ w + a w² + b w³` (`λ ≠ 0`) and the quadratic change of variables `φ w = w + c w²` the
push-forward satisfies the explicit polynomial identity

```
quadJet λ a b c (φ w) = φ'(w) F w + w⁶ * quadJetRem λ a b c w ,
```

where `quadJet` is the Taylor polynomial of the push-forward through degree `5`.  Taking
`c = −a/λ` — the solution of the degree-two homological equation `−λ c = −a` — gives the **Poincaré
normal form to cubic order**

```
G z = λ z + e₃ z³ + e₄ z⁴ + e₅ z⁵ + O(z⁶),
e₃ = b − 2a²/λ,   e₄ = ab/λ − 6a³/λ²,   e₅ = a²b/λ² − 18a⁴/λ³.
```

Adding the cubic correction `φ w = w + c w² + d w³` with `d = (6a²/λ² − b/λ)/9` (the solution of
the degree-four homological equation) kills the quartic term as well and yields the **cubic
Poincaré normal form**

```
G z = λ z + E₃ z³ + E₅ z⁵ + O(z⁶),
E₃ = (7bλ − 6a²) / (9λ),   E₅ = (90a⁴ − 57a²bλ − 2b²λ²) / (27λ³).
```

### 1.2 The real planar (Hopf) normal form (Part 3)

For a real planar field with linear part `λ w` (`λ = α + i ω`) and quadratic part
`Q w = q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄²` the degree-two part of the push-forward by `φ w = w + h₂(w)` is
`Q − L h₂`, where the **homological operator** at quadratic order is

```
L h = λ h − λ w ∂_w h − λ̄ w̄ ∂_{w̄} h .
```

On the basis `w², w w̄, w̄²` it is diagonal, with eigenvalues `−λ`, `−λ̄`, `λ − 2λ̄`; these are the
Poincaré–Dulac eigenvalues `λ − p λ − q λ̄` for `p + q = 2`.  The *resonance condition*
`p λ + q λ̄ = λ` therefore has **no degree-two solution** as soon as `λ ≠ 0`, and the quadratic part
of the field is removable by a near-identity change of variables.  The solution is explicit and
unique:

```
h₂₀ = −q₂₀/λ,   h₁₁ = −q₁₁/λ̄,   h₀₂ = q₀₂/(λ − 2λ̄).
```

This is the classical statement (Guckenheimer & Holmes, *Nonlinear Oscillations, Dynamical Systems,
and Bifurcations of Vector Fields*, §3.4; Hassard, Kazarinoff & Wan, *Theory and Applications of Hopf
Bifurcation*, Ch. 3; Kuznetsov, *Elements of Applied Bifurcation Theory*, §3.4) that the Hopf normal
form starts at cubic order.

The operator `λ h − λ̄ (h ∘ conj)` that appears in some formulations of the homological equation is
**not** the homological operator of a real planar field: on the space of quadratic forms it has
eigenvalues `λ − λ̄, λ − λ̄, λ + λ̄`, and is therefore singular exactly at a Hopf crossing, where the
classical theory says the quadratic terms *are* removable.  This is recorded in
`naiveHomological_kernel` and `naiveHomological_not_injective`.

### 1.3 The cubic resonant coefficient (Part 4)

After the quadratic removal, the cubic part of the transformed field is an explicit cubic form
(`cubic_pushForward`), whose **resonant** coefficient — the coefficient of the resonant monomial
`w² w̄ = w |w|²` — is `pushB21`, an explicit polynomial expression in the cubic Taylor coefficients
and in the quadratic-removal coefficients `h₂₀, h₁₁, h₀₂`.  The resonance analysis is in
`cubic_resonance_w2wbar` (the monomial `w² w̄` is resonant iff `λ` is purely imaginary, i.e. at a
Hopf crossing) and in `w3_not_resonant`, `wwbar2_not_resonant`, `wbar3_not_resonant` (the other
three cubic monomials are never resonant for `λ ≠ 0`).

`CRNT.PlanarHopfData.c₁` of the repository is exactly this resonant coefficient, and
`resonantMonomial_eq` identifies the resonant term `c₁ * (w * (Complex.normSq w : ℂ))` of
`CRNT.PlanarHopfData.normalForm_eq` with the monomial `w² w̄` computed here.

**What is *not* proved here.**  The bridge between the complex normal-form coefficient `c₁` and the
classical real-coordinate formula `CRNT.PlanarHopfData.lyapunovFromPartials` — which would discharge
the hypotheses `hcubic` and `hquad` of `CRNT.PlanarHopfData.lyapunovFromPartials_eq` — is *not*
established: it requires translating the complex Taylor data `q₂₀, q₁₁, q₀₂, c₃₀, c₂₁, c₁₂, c₀₃`
into the real partial derivatives `fxx, fxy, fyy, gxx, gxy, gyy, fxxx, …` and then performing the
classical Guckenheimer–Holmes calibration.  Everything needed for that calibration *is* in this
module: the quadratic-removal coefficients `h₂₀, h₁₁, h₀₂` and the resonant coefficient `c₁` are
explicit rational functions of the Taylor data.

### 1.4 A numerical instance (Part 5)

`CRNT.Hopf.Examples` checks the whole chain on the concrete instance `λ = i` (Hopf frequency
`ω = 1`), `a = 1`, `b = 1`: the corrections `c = i` and `d = (−6 + i)/9`, the normal-form
coefficients `e₃ = 1 + 2i`, `e₄ = 6 − i`, `e₅ = −1 − 18i`, `E₃ = (7 + 6i)/9`, `E₅ = (57 + 92i)/27`,
and the normal-form identities themselves.

## 2. What is *not* in this module

`Mathlib` carries neither center-manifold theory nor the normal-form transformation nor the
Lyapunov–Schmidt construction of the periodic orbit, so — exactly as `CRNT.Dynamics.HopfAdmissible`
records the center manifold through `CenterManifoldSeed` — the *existence* of the center manifold and
the averaging of the reduced field along it remain carried as data (`CRNT.Dynamics.HopfPersistentOrbit`
carries the averaged radial field `FullRadialField.G` as data).  What is proved here is the genuine
algebraic substance of the normal-form step.

Depends on: `CRNT.Dynamics.HopfNormalForm`.
-/

namespace CRNT

namespace Hopf

/-! ## Complex conjugation -/

/-- Complex conjugation on `ℂ`.  In this version of `Mathlib` the involution `starRingEnd ℂ` has
replaced the former `Complex.conj`. -/
def cconj (z : ℂ) : ℂ := starRingEnd ℂ z

@[simp] theorem cconj_mul (z w : ℂ) : cconj (z * w) = cconj z * cconj w := by
  simp [cconj]

@[simp] theorem cconj_add (z w : ℂ) : cconj (z + w) = cconj z + cconj w := by
  simp [cconj]

@[simp] theorem cconj_pow (z : ℂ) (n : ℕ) : cconj (z ^ n) = (cconj z) ^ n := by
  simp [cconj]

@[simp] theorem cconj_cconj (z : ℂ) : cconj (cconj z) = z := by
  simp [cconj]

@[simp] theorem cconj_ofReal (r : ℝ) : cconj (r : ℂ) = r := by
  simp [cconj]

@[simp] theorem cconj_sub (z w : ℂ) : cconj (z - w) = cconj z - cconj w := by
  simp [cconj]

@[simp] theorem cconj_smul (r : ℝ) (z : ℂ) : cconj (r • z) = r • cconj z := by
  simp [cconj]

@[simp] theorem cconj_one : cconj 1 = 1 := by
  simp [cconj]

@[simp] theorem cconj_zero : cconj 0 = 0 := by
  simp [cconj]

@[simp] theorem cconj_neg (z : ℂ) : cconj (-z) = -cconj z := by
  simp [cconj]

@[simp] theorem cconj_I : cconj Complex.I = -Complex.I := by
  simp [cconj]

@[simp] theorem cconj_natCast (n : ℕ) : cconj (n : ℂ) = n := by
  simp [cconj]

@[simp] theorem cconj_two : cconj 2 = 2 := by
  show (starRingEnd ℂ) ((2 : ℕ) : ℂ) = 2
  rw [map_natCast]
  norm_num

@[simp] theorem cconj_three : cconj 3 = 3 := by
  show (starRingEnd ℂ) ((3 : ℕ) : ℂ) = 3
  rw [map_natCast]
  norm_num

/-! ## Part 1: the complex-holomorphic cubic field and its quadratic push-forward -/

/-- The complex-holomorphic cubic field `F w = λ w + a w² + b w³`. -/
def cubicField (lam a b : ℂ) (w : ℂ) : ℂ := lam * w + a * w ^ 2 + b * w ^ 3

/-- The quadratic near-identity change of variables `φ w = w + c w²`. -/
def quadChange (c : ℂ) (w : ℂ) : ℂ := w + c * w ^ 2

/-- The derivative `φ' w = 1 + 2 c w` of `quadChange c`. -/
def quadChangeDeriv (c : ℂ) (w : ℂ) : ℂ := 1 + 2 * c * w

/-- The first Taylor coefficient of the push-forward of `cubicField λ a b` by `quadChange c`. -/
def jetG1 (lam : ℂ) (_a _b _c : ℂ) : ℂ := lam

/-- The second Taylor coefficient of the push-forward of `cubicField λ a b` by `quadChange c`.  It
vanishes exactly for `c = −a/λ`, the solution of the degree-two homological equation. -/
def jetG2 (lam a _b c : ℂ) : ℂ := a + lam * c

/-- The third Taylor coefficient of the push-forward of `cubicField λ a b` by `quadChange c`. -/
def jetG3 (lam _a b c : ℂ) : ℂ := b - 2 * lam * c ^ 2

/-- The fourth Taylor coefficient of the push-forward of `cubicField λ a b` by `quadChange c`. -/
def jetG4 (lam a b c : ℂ) : ℂ := 5 * lam * c ^ 3 - a * c ^ 2 - b * c

/-- The fifth Taylor coefficient of the push-forward of `cubicField λ a b` by `quadChange c`. -/
def jetG5 (lam a b c : ℂ) : ℂ := b * c ^ 2 + 4 * a * c ^ 3 - 14 * lam * c ^ 4

/-- The Taylor polynomial (through degree `5`) of the push-forward of `cubicField λ a b` by
`quadChange c`. -/
def quadJet (lam a b c : ℂ) (z : ℂ) : ℂ :=
  jetG1 lam a b c * z + jetG2 lam a b c * z ^ 2 + jetG3 lam a b c * z ^ 3 + jetG4 lam a b c * z ^ 4
    + jetG5 lam a b c * z ^ 5

/-- The remainder (the terms of order `≥ 6`) of the push-forward of `cubicField λ a b` by
`quadChange c`: explicitly, `quadJet λ a b c (quadChange c w) − quadChangeDeriv c w *
cubicField λ a b (quadChange c w) = w⁶ * quadJetRem λ a b c w`. -/
def quadJetRem (lam a b c : ℂ) (w : ℂ) : ℂ :=
  (c ^ 3 * jetG3 lam a b c + 6 * c ^ 2 * jetG4 lam a b c + 5 * c * jetG5 lam a b c)
    + (4 * c ^ 3 * jetG4 lam a b c + 10 * c ^ 2 * jetG5 lam a b c) * w
    + (c ^ 4 * jetG4 lam a b c + 10 * c ^ 3 * jetG5 lam a b c) * w ^ 2
    + 5 * c ^ 4 * jetG5 lam a b c * w ^ 3
    + c ^ 5 * jetG5 lam a b c * w ^ 4

/-- **The push-forward identity for the quadratic change of variables.**  If `G` is the push-forward
of the cubic field `F w = λ w + a w² + b w³` by `φ w = w + c w²` (that is, `G (φ w) = φ'(w) F w`),
then the difference between `G ∘ φ` and `φ' ∘ F` is a multiple of `w⁶`; explicitly,

`G (φ w) = φ'(w) F w + w⁶ * quadJetRem λ a b c w`.

Since `φ w = w + O(w²)` is tangent to the identity, the Taylor expansion of `G` at the origin is the
one of `quadJet λ a b c` (through degree `5`). -/
theorem quadJet_pushForward (lam a b c : ℂ) (w : ℂ) :
    quadJet lam a b c (quadChange c w)
      = quadChangeDeriv c w * cubicField lam a b w + w ^ 6 * quadJetRem lam a b c w := by
  simp only [quadJet, quadJetRem, jetG1, jetG2, jetG3, jetG4, jetG5, quadChange, quadChangeDeriv,
    cubicField]
  ring

/-- **The cubic coefficient of the Poincaré normal form obtained by the quadratic change.** -/
noncomputable def e3 (lam a b : ℂ) : ℂ := b - 2 * a ^ 2 / lam

/-- **The quartic coefficient of the Poincaré normal form obtained by the quadratic change.** -/
noncomputable def e4 (lam a b : ℂ) : ℂ := a * b / lam - 6 * a ^ 3 / lam ^ 2

/-- **The quintic coefficient of the Poincaré normal form obtained by the quadratic change.** -/
noncomputable def e5 (lam a b : ℂ) : ℂ := a ^ 2 * b / lam ^ 2 - 18 * a ^ 4 / lam ^ 3

theorem jetG1_neg (lam a b : ℂ) : jetG1 lam a b (-a / lam) = lam := by
  simp [jetG1]

theorem jetG2_neg {lam a b : ℂ} (hlam : lam ≠ 0) : jetG2 lam a b (-a / lam) = 0 := by
  simp only [jetG2]
  field_simp [hlam]; ring

theorem jetG3_neg {lam a b : ℂ} (hlam : lam ≠ 0) : jetG3 lam a b (-a / lam) = e3 lam a b := by
  simp only [jetG3, e3]
  field_simp [hlam]

theorem jetG4_neg {lam a b : ℂ} (hlam : lam ≠ 0) : jetG4 lam a b (-a / lam) = e4 lam a b := by
  simp only [jetG4, e4]
  field_simp [hlam]; ring

theorem jetG5_neg {lam a b : ℂ} (hlam : lam ≠ 0) : jetG5 lam a b (-a / lam) = e5 lam a b := by
  simp only [jetG5, e5]
  field_simp [hlam]; ring

/-- **The quadratic term of the cubic field is removed by the quadratic change of variables.**
The solution of the degree-two homological equation `−λ c = −a` is `c = −a/λ`. -/
theorem quadratic_removed {lam a b : ℂ} (hlam : lam ≠ 0) : jetG2 lam a b (-a / lam) = 0 :=
  jetG2_neg hlam

/-- **The Poincaré normal form of the complex-holomorphic cubic field to cubic order.**  For
`λ ≠ 0`, the push-forward of `F w = λ w + a w² + b w³` by the quadratic change of variables
`φ w = w − (a/λ) w²` has Taylor expansion

`G z = λ z + e₃ z³ + e₄ z⁴ + e₅ z⁵ + O(z⁶)`

with `e₃ = b − 2a²/λ`, `e₄ = ab/λ − 6a³/λ²`, `e₅ = a²b/λ² − 18a⁴/λ³`.  In particular the
quadratic coefficient vanishes. -/
theorem cubic_normal_form {lam a b : ℂ} (hlam : lam ≠ 0) (w : ℂ) :
    quadJet lam a b (-a / lam) w
      = lam * w + e3 lam a b * w ^ 3 + e4 lam a b * w ^ 4 + e5 lam a b * w ^ 5 := by
  rw [quadJet, jetG1_neg, jetG2_neg hlam, jetG3_neg hlam, jetG4_neg hlam, jetG5_neg hlam]
  ring

/-- **The normal form identity, in the shape "the transformed field minus the normal form
vanishes".** -/
theorem cubic_normal_form_sub {lam a b : ℂ} (hlam : lam ≠ 0) (w : ℂ) :
    quadJet lam a b (-a / lam) w - (lam * w + e3 lam a b * w ^ 3 + e4 lam a b * w ^ 4 + e5 lam a b * w ^ 5) = 0 :=
  sub_eq_zero.mpr (cubic_normal_form hlam w)

/-! ## Part 2: the full normal form to cubic order (the quartic term is removed as well) -/

/-- The cubic near-identity change of variables `φ w = w + c w² + d w³`. -/
def cubicChange (c d : ℂ) (w : ℂ) : ℂ := w + c * w ^ 2 + d * w ^ 3

/-- The derivative `φ' w = 1 + 2 c w + 3 d w²` of `cubicChange c d`. -/
def cubicChangeDeriv (c d : ℂ) (w : ℂ) : ℂ := 1 + 2 * c * w + 3 * d * w ^ 2

/-- The first Taylor coefficient of the push-forward of `cubicField lam a b` by `cubicChange c d`. -/
def cubJetG1 (lam : ℂ) (_a _b _c _d : ℂ) : ℂ := lam

/-- The second Taylor coefficient of the push-forward of `cubicField lam a b` by `cubicChange c d`. -/
def cubJetG2 (lam a _b c _d : ℂ) : ℂ := a + lam * c

/-- The third Taylor coefficient of the push-forward of `cubicField lam a b` by `cubicChange c d`. -/
def cubJetG3 (lam _a b c d : ℂ) : ℂ := b - 2 * lam * c ^ 2 + 2 * lam * d

/-- The fourth Taylor coefficient of the push-forward of `cubicField lam a b` by
`cubicChange c d`. -/
def cubJetG4 (lam a b c d : ℂ) : ℂ :=
  -a * c ^ 2 + a * d - b * c + 5 * lam * c ^ 3 - 8 * lam * c * d

/-- The fifth Taylor coefficient of the push-forward of `cubicField lam a b` by
`cubicChange c d`. -/
def cubJetG5 (lam a b c d : ℂ) : ℂ :=
  4 * a * c ^ 3 - 6 * a * c * d + b * c ^ 2 - 14 * lam * c ^ 4 + 30 * lam * c ^ 2 * d - 6 * lam * d ^ 2

/-- The Taylor polynomial (through degree `5`) of the push-forward of `cubicField lam a b` by
`cubicChange c d`. -/
def cubicJet (lam a b c d : ℂ) (z : ℂ) : ℂ :=
  cubJetG1 lam a b c d * z + cubJetG2 lam a b c d * z ^ 2 + cubJetG3 lam a b c d * z ^ 3
    + cubJetG4 lam a b c d * z ^ 4 + cubJetG5 lam a b c d * z ^ 5

/-- The remainder (the terms of order `≥ 6`) of the push-forward of `cubicField lam a b` by
`cubicChange c d`. -/
def cubicJetRem (lam a b c d : ℂ) (w : ℂ) : ℂ :=
  (c ^ 3 * cubJetG3 lam a b c d + 6 * c ^ 2 * cubJetG4 lam a b c d + 6 * c * d * cubJetG3 lam a b c d
      + 5 * c * cubJetG5 lam a b c d + d ^ 2 * cubJetG2 lam a b c d + 4 * d * cubJetG4 lam a b c d)
    + (4 * c ^ 3 * cubJetG4 lam a b c d + 3 * c ^ 2 * d * cubJetG3 lam a b c d
        + 10 * c ^ 2 * cubJetG5 lam a b c d + 12 * c * d * cubJetG4 lam a b c d
        + 3 * d ^ 2 * cubJetG3 lam a b c d + 5 * d * cubJetG5 lam a b c d) * w
    + (c ^ 4 * cubJetG4 lam a b c d + 10 * c ^ 3 * cubJetG5 lam a b c d
        + 12 * c ^ 2 * d * cubJetG4 lam a b c d + 3 * c * d ^ 2 * cubJetG3 lam a b c d
        + 20 * c * d * cubJetG5 lam a b c d + 6 * d ^ 2 * cubJetG4 lam a b c d) * w ^ 2
    + (5 * c ^ 4 * cubJetG5 lam a b c d + 4 * c ^ 3 * d * cubJetG4 lam a b c d
        + 30 * c ^ 2 * d * cubJetG5 lam a b c d + 12 * c * d ^ 2 * cubJetG4 lam a b c d
        + d ^ 3 * cubJetG3 lam a b c d + 10 * d ^ 2 * cubJetG5 lam a b c d) * w ^ 3
    + (c ^ 5 * cubJetG5 lam a b c d + 20 * c ^ 3 * d * cubJetG5 lam a b c d
        + 6 * c ^ 2 * d ^ 2 * cubJetG4 lam a b c d + 30 * c * d ^ 2 * cubJetG5 lam a b c d
        + 4 * d ^ 3 * cubJetG4 lam a b c d) * w ^ 4
    + (5 * c ^ 4 * d * cubJetG5 lam a b c d + 30 * c ^ 2 * d ^ 2 * cubJetG5 lam a b c d
        + 4 * c * d ^ 3 * cubJetG4 lam a b c d + 10 * d ^ 3 * cubJetG5 lam a b c d) * w ^ 5
    + (10 * c ^ 3 * d ^ 2 * cubJetG5 lam a b c d + 20 * c * d ^ 3 * cubJetG5 lam a b c d
        + d ^ 4 * cubJetG4 lam a b c d) * w ^ 6
    + (10 * c ^ 2 * d ^ 3 * cubJetG5 lam a b c d + 5 * d ^ 4 * cubJetG5 lam a b c d) * w ^ 7
    + 5 * c * d ^ 4 * cubJetG5 lam a b c d * w ^ 8
    + d ^ 5 * cubJetG5 lam a b c d * w ^ 9

/-- **The push-forward identity for the cubic change of variables.**  If `G` is the push-forward of
the cubic field `F w = lam w + a w² + b w³` by `φ w = w + c w² + d w³`, then

`G (φ w) = φ'(w) F w + w⁶ * cubicJetRem lam a b c d w`,

so the Taylor expansion of `G` at the origin is `cubicJet lam a b c d` through degree `5`. -/
theorem cubicJet_pushForward (lam a b c d : ℂ) (w : ℂ) :
    cubicJet lam a b c d (cubicChange c d w)
      = cubicChangeDeriv c d w * cubicField lam a b w + w ^ 6 * cubicJetRem lam a b c d w := by
  simp only [cubicJet, cubicJetRem, cubJetG1, cubJetG2, cubJetG3, cubJetG4, cubJetG5, cubicChange,
    cubicChangeDeriv, cubicField]
  ring

/-- **The cubic correction that kills the quartic term.**  With the quadratic correction
`c = −a/lam` already in place, the quartic coefficient of the push-forward is
`−6a³/lam² + ab/lam + 9 a d`; it vanishes for `d = (6a²/lam² − b/lam)/9`. -/
noncomputable def cubicCorrection (lam a b : ℂ) : ℂ := (6 * a ^ 2 / lam ^ 2 - b / lam) / 9

/-- **The cubic coefficient of the Poincaré normal form obtained by the cubic change.** -/
noncomputable def E3 (lam a b : ℂ) : ℂ := (7 * b * lam - 6 * a ^ 2) / (9 * lam)

/-- **The quintic coefficient of the Poincaré normal form obtained by the cubic change.** -/
noncomputable def E5 (lam a b : ℂ) : ℂ :=
  (90 * a ^ 4 - 57 * a ^ 2 * b * lam - 2 * b ^ 2 * lam ^ 2) / (27 * lam ^ 3)

theorem cubJetG1_neg (lam a b : ℂ) : cubJetG1 lam a b (-a / lam) (cubicCorrection lam a b) = lam := by
  simp [cubJetG1]

theorem cubJetG2_neg {lam a b : ℂ} (hlam : lam ≠ 0) :
    cubJetG2 lam a b (-a / lam) (cubicCorrection lam a b) = 0 := by
  simp only [cubJetG2]
  field_simp [hlam]; ring

theorem cubJetG3_neg {lam a b : ℂ} (hlam : lam ≠ 0) :
    cubJetG3 lam a b (-a / lam) (cubicCorrection lam a b) = E3 lam a b := by
  simp only [cubJetG3, cubicCorrection, E3]
  field_simp [hlam]; ring

theorem cubJetG4_neg {lam a b : ℂ} (hlam : lam ≠ 0) :
    cubJetG4 lam a b (-a / lam) (cubicCorrection lam a b) = 0 := by
  simp only [cubJetG4, cubicCorrection]
  field_simp [hlam]; ring

theorem cubJetG5_neg {lam a b : ℂ} (hlam : lam ≠ 0) :
    cubJetG5 lam a b (-a / lam) (cubicCorrection lam a b) = E5 lam a b := by
  simp only [cubJetG5, cubicCorrection, E5]
  field_simp [hlam]; ring

/-- **The Poincaré normal form to cubic order of the complex-holomorphic cubic field.**  For
`lam ≠ 0`, the push-forward of `F w = lam w + a w² + b w³` by the cubic change of variables
`φ w = w − (a/lam) w² + ((6a²/lam² − b/lam)/9) w³` has Taylor expansion

`G z = lam z + E₃ z³ + E₅ z⁵ + O(z⁶)`

with `E₃ = (7 b lam − 6 a²)/(9 lam)` and `E₅ = (90 a⁴ − 57 a² b lam − 2 b² lam²)/(27 lam³)`.  Both
the quadratic and the quartic coefficients vanish: this is the classical Poincaré normal form to
cubic order in the non-resonant case. -/
theorem cubic_normal_form_cubic {lam a b : ℂ} (hlam : lam ≠ 0) (w : ℂ) :
    cubicJet lam a b (-a / lam) (cubicCorrection lam a b) w
      = lam * w + E3 lam a b * w ^ 3 + E5 lam a b * w ^ 5 := by
  rw [cubicJet, cubJetG1_neg, cubJetG2_neg hlam, cubJetG3_neg hlam, cubJetG4_neg hlam,
    cubJetG5_neg hlam]
  ring

/-- **The normal form identity for the cubic normal form, in the shape "the transformed field minus
the normal form vanishes".** -/
theorem cubic_normal_form_cubic_sub {lam a b : ℂ} (hlam : lam ≠ 0) (w : ℂ) :
    cubicJet lam a b (-a / lam) (cubicCorrection lam a b) w
      - (lam * w + E3 lam a b * w ^ 3 + E5 lam a b * w ^ 5) = 0 :=
  sub_eq_zero.mpr (cubic_normal_form_cubic hlam w)

/-! ## Part 3: the real planar (Hopf) normal form — the quadratic part is removable -/

/-- The quadratic form `h₂₀ w² + h₁₁ w w̄ + h₀₂ w̄²` in the pair `(w, w̄)`.  Such forms are the
quadratic parts of the Taylor expansion of a complex-valued function of the real plane. -/
def quadForm (h20 h11 h02 : ℂ) (w : ℂ) : ℂ :=
  h20 * w ^ 2 + h11 * w * cconj w + h02 * (cconj w) ^ 2

/-- The cubic form `a₃₀ w³ + a₂₁ w² w̄ + a₁₂ w w̄² + a₀₃ w̄³`. -/
def cubicForm (a30 a21 a12 a03 : ℂ) (w : ℂ) : ℂ :=
  a30 * w ^ 3 + a21 * w ^ 2 * cconj w + a12 * w * (cconj w) ^ 2 + a03 * (cconj w) ^ 3

/-- The Wirtinger derivative `∂/∂w` of the quadratic form `quadForm h20 h11 h02`. -/
def quadW (h20 h11 _h02 : ℂ) (w : ℂ) : ℂ := 2 * h20 * w + h11 * cconj w

/-- The Wirtinger derivative `∂/∂w̄` of the quadratic form `quadForm h20 h11 h02`. -/
def quadWbar (_h20 h11 h02 : ℂ) (w : ℂ) : ℂ := h11 * w + 2 * h02 * cconj w

/-- The real planar field with linear part `lam w` and quadratic part
`q₂₀ w² + q₁₁ w w̄ + q₀₂ w̄²`, in complex representation. -/
def planarField (lam : ℂ) (q20 q11 q02 : ℂ) (w : ℂ) : ℂ := lam * w + quadForm q20 q11 q02 w

/-- **The homological operator at quadratic order** for a real planar field with linear part
`lam w`:

`L h = lam h − lam w ∂_w h − cconj lam w̄ ∂_{w̄} h`.

On the basis `w², w w̄, w̄²` it is diagonal, with eigenvalues `−lam`, `−cconj lam`,
`lam − 2 cconj lam`; these are the Poincaré–Dulac eigenvalues `lam − p lam − q cconj lam` for
`p + q = 2`. -/
def homologicalQuad (lam : ℂ) (h20 h11 h02 : ℂ) (w : ℂ) : ℂ :=
  -lam * h20 * w ^ 2 - cconj lam * h11 * w * cconj w + (lam - 2 * cconj lam) * h02 * (cconj w) ^ 2

/-- **The homological operator is the linearization of the push-forward.** -/
theorem homologicalQuad_eq (lam h20 h11 h02 w : ℂ) :
    homologicalQuad lam h20 h11 h02 w
      = lam * quadForm h20 h11 h02 w
        - (lam * w * quadW h20 h11 h02 w + cconj lam * cconj w * quadWbar h20 h11 h02 w) := by
  simp only [homologicalQuad, quadForm, quadW, quadWbar]
  ring

/-- **The coefficients of the solution of the degree-two homological equation** `L h₂ = Q`. -/
noncomputable def h20Sol (lam q20 : ℂ) : ℂ := -q20 / lam

/-- **The coefficient `h₁₁` of the solution of the degree-two homological equation.** -/
noncomputable def h11Sol (lam q11 : ℂ) : ℂ := -q11 / cconj lam

/-- **The coefficient `h₀₂` of the solution of the degree-two homological equation.** -/
noncomputable def h02Sol (lam q02 : ℂ) : ℂ := q02 / (lam - 2 * cconj lam)

/-- **`cconj lam = 0` iff `lam = 0`.** -/
theorem cconj_eq_zero {z : ℂ} : cconj z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hc : cconj (cconj z) = cconj 0 := congrArg cconj h
    simpa only [cconj_cconj, cconj_zero] using hc
  · intro h
    have hc : cconj z = cconj 0 := congrArg cconj h
    rw [hc]
    simp

/-- **`lam − 2 cconj lam = 0` iff `lam = 0`.**  Hence the third Poincaré–Dulac eigenvalue
`lam − 2 cconj lam` vanishes only in the degenerate case `lam = 0`. -/
theorem lam_sub_two_cconj_eq_zero {lam : ℂ} : lam - 2 * cconj lam = 0 ↔ lam = 0 := by
  constructor
  · intro h
    have h' : cconj lam - 2 * lam = 0 := by
      have hc : cconj (lam - 2 * cconj lam) = 0 := by rw [h, cconj_zero]
      simpa only [cconj_sub, cconj_mul, cconj_two, cconj_cconj] using hc
    have h1 : lam = 2 * cconj lam := by linear_combination h
    have h2 : cconj lam = 2 * lam := by linear_combination h'
    have h3 : lam = 4 * lam := by
      calc lam = 2 * cconj lam := h1
        _ = 2 * (2 * lam) := by rw [h2]
        _ = 4 * lam := by ring
    have h4 : 3 * lam = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp h4 with h4 | h4
    · exact absurd h4 (by norm_num)
    · exact h4
  · intro h
    simp [h]

/-- **The degree-two homological equation has the explicit solution.**  For `lam ≠ 0` the quadratic
part `Q` of the field is removed by the quadratic change of variables `φ w = w + h₂(w)` with

`h₂₀ = −q₂₀/lam`,   `h₁₁ = −q₁₁/cconj lam`,   `h₀₂ = q₀₂/(lam − 2 cconj lam)`,

that is, `L h₂ = Q`. -/
theorem homologicalQuad_solution {lam q20 q11 q02 : ℂ} (hlam : lam ≠ 0) (w : ℂ) :
    homologicalQuad lam (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02) w
      = quadForm q20 q11 q02 w := by
  have hc : cconj lam ≠ 0 := by
    intro hc
    apply hlam
    exact cconj_eq_zero.mp hc
  have hd : lam - 2 * cconj lam ≠ 0 := by
    intro hz
    exact hlam (lam_sub_two_cconj_eq_zero.mp hz)
  have h20e : -lam * h20Sol lam q20 = q20 := by
    simp only [h20Sol]
    field_simp [hlam]
  have h11e : -cconj lam * h11Sol lam q11 = q11 := by
    simp only [h11Sol]
    field_simp [hc]
  have h02e : (lam - 2 * cconj lam) * h02Sol lam q02 = q02 := by
    simp only [h02Sol]
    field_simp [hd]
  simp only [homologicalQuad, quadForm]
  linear_combination h20e * w ^ 2 + h11e * (w * cconj w) + h02e * (cconj w) ^ 2

/-- **A quadratic form vanishing identically has all its coefficients zero.**  The three
evaluation points `1`, `Complex.I` and `1 + Complex.I` give a nonsingular linear system for the
three coefficients. -/
theorem quadForm_eq_zero {α β γ : ℂ} (h : ∀ w : ℂ, α * w ^ 2 + β * w * cconj w + γ * (cconj w) ^ 2 = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h1 := h 1
  have h2 := h Complex.I
  have h3 := h (1 + Complex.I)
  simp only [cconj_one, cconj_I, cconj_add] at h1 h2 h3
  ring_nf at h1 h2 h3
  simp only [Complex.I_sq] at h1 h2 h3
  have hβ : β = 0 := by linear_combination (h1 + h2) / 2
  have h3' : Complex.I * (α - γ) = 0 := by linear_combination h3 / 2 - hβ
  have hαγ : α - γ = 0 := by
    rcases mul_eq_zero.mp h3' with hI | h
    · exact absurd hI Complex.I_ne_zero
    · exact h
  have h1' : α + γ = 0 := by linear_combination h1 - hβ
  have h2α : 2 * α = 0 := by linear_combination h1' + hαγ
  have hα : α = 0 := by
    rcases mul_eq_zero.mp h2α with h2 | h
    · exact absurd h2 (by norm_num)
    · exact h
  refine ⟨hα, hβ, ?_⟩
  have hγ : γ = α := by linear_combination -hαγ
  rw [hγ, hα]

/-- **The degree-two homological equation has a unique solution.** -/
theorem homologicalQuad_unique {lam q20 q11 q02 h20 h11 h02 : ℂ} (hlam : lam ≠ 0)
    (h : ∀ w : ℂ, homologicalQuad lam h20 h11 h02 w = quadForm q20 q11 q02 w) :
    h20 = h20Sol lam q20 ∧ h11 = h11Sol lam q11 ∧ h02 = h02Sol lam q02 := by
  have hd : ∀ w : ℂ,
      (-lam * h20 - q20) * w ^ 2 + (-cconj lam * h11 - q11) * w * cconj w
        + ((lam - 2 * cconj lam) * h02 - q02) * (cconj w) ^ 2 = 0 := by
    intro w
    have hw := h w
    simp only [homologicalQuad, quadForm] at hw
    have hd' : (-lam * h20 - q20) * w ^ 2 + (-cconj lam * h11 - q11) * w * cconj w
        + ((lam - 2 * cconj lam) * h02 - q02) * (cconj w) ^ 2
        = -lam * h20 * w ^ 2 - cconj lam * h11 * w * cconj w
          + (lam - 2 * cconj lam) * h02 * (cconj w) ^ 2
          - (q20 * w ^ 2 + q11 * w * cconj w + q02 * (cconj w) ^ 2) := by ring
    rw [hd', hw]
    ring
  rcases quadForm_eq_zero hd with ⟨hα, hβ, hγ⟩
  have hc : cconj lam ≠ 0 := by
    intro hc
    apply hlam
    exact cconj_eq_zero.mp hc
  have hd2 : lam - 2 * cconj lam ≠ 0 := by
    intro hz
    exact hlam (lam_sub_two_cconj_eq_zero.mp hz)
  refine ⟨?_, ?_, ?_⟩
  · simp only [h20Sol]
    refine (eq_div_iff hlam).2 ?_
    linear_combination -hα
  · simp only [h11Sol]
    refine (eq_div_iff hc).2 ?_
    linear_combination -hβ
  · simp only [h02Sol]
    refine (eq_div_iff hd2).2 ?_
    linear_combination hγ

/-- **The quadratic part of a real planar field is removable iff `lam ≠ 0`.**  This is the
degree-two non-resonance statement: the Poincaré–Dulac eigenvalues `−lam`, `−cconj lam`,
`lam − 2 cconj lam` are all nonzero as soon as `lam ≠ 0`, so the homological equation `L h₂ = Q` is
solvable for every `Q`; at a Hopf crossing `lam = i ω` with `ω ≠ 0` this is the case. -/
theorem quadratic_removable_iff {lam : ℂ} :
    lam ≠ 0 ↔ ∀ q20 q11 q02 : ℂ, ∃ h20 h11 h02 : ℂ,
      ∀ w : ℂ, homologicalQuad lam h20 h11 h02 w = quadForm q20 q11 q02 w := by
  constructor
  · intro hlam q20 q11 q02
    refine ⟨h20Sol lam q20, h11Sol lam q11, h02Sol lam q02, ?_⟩
    exact homologicalQuad_solution hlam
  · intro h hlam
    obtain ⟨h20, h11, h02, hh⟩ := h 1 0 0
    have h1 := hh 1
    simp only [homologicalQuad, quadForm, cconj_one, one_mul] at h1
    rw [hlam, cconj_zero] at h1
    norm_num at h1

/-- The `w³` coefficient of the cubic remainder of the push-forward. -/
def pushC30 (q20 _q11 q02 h20 h11 _h02 : ℂ) : ℂ := 2 * h20 * q20 + h11 * cconj q02

/-- The `w² w̄` coefficient of the cubic remainder of the push-forward. -/
def pushC21 (q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  2 * h20 * q11 + h11 * q20 + h11 * cconj q11 + 2 * h02 * cconj q02

/-- The `w w̄²` coefficient of the cubic remainder of the push-forward. -/
def pushC12 (q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  2 * h20 * q02 + h11 * q11 + h11 * cconj q20 + 2 * h02 * cconj q11

/-- The `w̄³` coefficient of the cubic remainder of the push-forward. -/
def pushC03 (q20 _q11 q02 _h20 h11 h02 : ℂ) : ℂ := h11 * q02 + 2 * h02 * cconj q20

/-- **The push-forward identity for a real planar field.**  If `G` is the push-forward of the
truncated field `F₂ w = lam w + Q(w)` by the change of variables `φ w = w + h₂(w)` — that is,
`G (φ w) = (1 + ∂_w h₂) F₂ w + ∂_{w̄} h₂ · conj (F₂ w)` — then

`G (φ w) = lam φ w + (Q − L h₂)(w) + (cubic remainder)`,

the cubic remainder being the cubic form `∂_w h₂ · Q + ∂_{w̄} h₂ · conj Q`.  In particular the
quadratic part of the transformed field is the quadratic form `Q − L h₂`. -/
theorem planar_pushForward (lam q20 q11 q02 h20 h11 h02 w : ℂ) :
    (1 + quadW h20 h11 h02 w) * planarField lam q20 q11 q02 w
        + quadWbar h20 h11 h02 w * cconj (planarField lam q20 q11 q02 w)
      = lam * (w + quadForm h20 h11 h02 w)
        + quadForm (q20 + lam * h20) (q11 + cconj lam * h11)
          (q02 - (lam - 2 * cconj lam) * h02) w
        + cubicForm (pushC30 q20 q11 q02 h20 h11 h02) (pushC21 q20 q11 q02 h20 h11 h02)
          (pushC12 q20 q11 q02 h20 h11 h02) (pushC03 q20 q11 q02 h20 h11 h02) w := by
  simp only [planarField, quadForm, quadW, quadWbar, cubicForm, pushC30, pushC21, pushC12, pushC03,
    cconj_add, cconj_mul, cconj_pow, cconj_cconj]
  ring

/-- **The quadratic part of the transformed field is `Q − L h₂`.** -/
theorem quadPart_eq_sub_homological (lam q20 q11 q02 h20 h11 h02 w : ℂ) :
    quadForm (q20 + lam * h20) (q11 + cconj lam * h11) (q02 - (lam - 2 * cconj lam) * h02) w
      = quadForm q20 q11 q02 w - homologicalQuad lam h20 h11 h02 w := by
  simp only [quadForm, homologicalQuad]
  ring

/-- **The quadratic terms of the reduced field are removed at a Hopf crossing.**  If `h₂` solves the
degree-two homological equation `L h₂ = Q`, then the quadratic part `Q − L h₂` of the transformed
field vanishes, and the push-forward identity degenerates to

`(1 + ∂_w h₂) F₂ + ∂_{w̄} h₂ · conj (F₂) = lam φ + (cubic remainder)`,

i.e. the transformed field is `lam` times the new coordinate plus a cubic form: the Hopf normal form
starts at cubic order. -/
theorem planar_quadratic_removed {lam q20 q11 q02 h20 h11 h02 : ℂ} (_hlam : lam ≠ 0)
    (hsol : ∀ w : ℂ, homologicalQuad lam h20 h11 h02 w = quadForm q20 q11 q02 w) (w : ℂ) :
    (1 + quadW h20 h11 h02 w) * planarField lam q20 q11 q02 w
        + quadWbar h20 h11 h02 w * cconj (planarField lam q20 q11 q02 w)
      = lam * (w + quadForm h20 h11 h02 w)
        + cubicForm (pushC30 q20 q11 q02 h20 h11 h02) (pushC21 q20 q11 q02 h20 h11 h02)
          (pushC12 q20 q11 q02 h20 h11 h02) (pushC03 q20 q11 q02 h20 h11 h02) w := by
  rw [planar_pushForward]
  have hz : quadForm (q20 + lam * h20) (q11 + cconj lam * h11)
      (q02 - (lam - 2 * cconj lam) * h02) w = 0 := by
    rw [quadPart_eq_sub_homological]
    rw [hsol w]
    simp
  rw [hz, add_zero]

/-! ## Part 4: the cubic part of the transformed field and the resonant coefficient -/

/-- The quartic form `a₄₀ w⁴ + a₃₁ w³ w̄ + a₂₂ w² w̄² + a₁₃ w w̄³ + a₀₄ w̄⁴`. -/
def quarticForm (a40 a31 a22 a13 a04 : ℂ) (w : ℂ) : ℂ :=
  a40 * w ^ 4 + a31 * w ^ 3 * cconj w + a22 * w ^ 2 * (cconj w) ^ 2 + a13 * w * (cconj w) ^ 3
    + a04 * (cconj w) ^ 4

/-- The real planar field with linear part `lam w`, quadratic part `Q` and cubic part `C`, in
complex representation. -/
def planarField3 (lam : ℂ) (q20 q11 q02 c30 c21 c12 c03 : ℂ) (w : ℂ) : ℂ :=
  lam * w + quadForm q20 q11 q02 w
    + cubicForm c30 c21 c12 c03 w

set_option linter.unusedVariables false

/-- The `w²` coefficient of the quadratic part of the transformed field. -/
def pushA20 (lam q20 h20 : ℂ) : ℂ := q20 + lam * h20

/-- The `w w̄` coefficient of the quadratic part of the transformed field. -/
def pushA11 (lam q11 h11 : ℂ) : ℂ := q11 + cconj lam * h11

/-- The `w̄²` coefficient of the quadratic part of the transformed field. -/
def pushA02 (lam q02 h02 : ℂ) : ℂ := q02 - (lam - 2 * cconj lam) * h02

/-- The `w³` coefficient of the cubic part of the transformed field. -/
def pushB30 (lam q20 q11 q02 c30 h20 h11 h02 : ℂ) : ℂ :=
  c30 + (cconj q02 * h11) + (-((cconj h02 * q11))) + (-2 * lam * (h20) ^ 2)
    + (-((cconj h02 * cconj lam * h11)))

/-- **The resonant cubic coefficient** of the transformed field: the coefficient of the resonant
monomial `w² w̄ = w |w|²`.  It is a polynomial expression in the cubic Taylor coefficients and in
the quadratic-removal coefficients `h₂₀, h₁₁, h₀₂`. -/
def pushB21 (lam q20 q11 q02 c21 h20 h11 h02 : ℂ) : ℂ :=
  c21 + (cconj q11 * h11) + (h20 * q11) + (-((cconj h11 * q11))) + (-((h11 * q20)))
    + (-2 * cconj h02 * q02) + (2 * cconj q02 * h02) + (-((cconj h11 * cconj lam * h11)))
    + (-((cconj lam * h11 * h20))) + (-4 * cconj h02 * cconj lam * h02)
    + (-2 * h11 * h20 * lam) + (2 * cconj h02 * h02 * lam)

/-- The `w w̄²` coefficient of the cubic part of the transformed field. -/
def pushB12 (lam q20 q11 q02 c12 h20 h11 h02 : ℂ) : ℂ :=
  c12 + (cconj q20 * h11) + (-((cconj h20 * q11))) + (-((cconj lam * (h11) ^ 2)))
    + (-2 * cconj h11 * q02) + (-2 * h02 * q20) + (2 * cconj q11 * h02) + (2 * h20 * q02)
    + (-((cconj h20 * cconj lam * h11))) + (-4 * cconj h11 * cconj lam * h02)
    + (-2 * h02 * h20 * lam) + (2 * cconj h11 * h02 * lam)

/-- The `w̄³` coefficient of the cubic part of the transformed field. -/
def pushB03 (lam q20 q11 q02 c03 h20 h11 h02 : ℂ) : ℂ :=
  c03 + (h11 * q02) + (-((h02 * q11))) + (-2 * cconj h20 * q02) + (2 * cconj q20 * h02)
    + (-((cconj lam * h02 * h11))) + (-4 * cconj h20 * cconj lam * h02)
    + (2 * cconj h20 * h02 * lam)

/-- The `w³` coefficient of the cubic part of `A (φ w)`, where `A` is the quadratic part of the
transformed field. -/
def pushD30 (lam q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  (cconj h02 * q11) + (2 * h20 * q20) + (2 * lam * (h20) ^ 2) + (cconj h02 * cconj lam * h11)

/-- The `w² w̄` coefficient of the cubic part of `A (φ w)`. -/
def pushD21 (lam q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  (cconj h11 * q11) + (h20 * q11) + (2 * cconj h02 * q02) + (2 * h11 * q20)
    + (cconj h11 * cconj lam * h11) + (cconj lam * h11 * h20) + (-2 * cconj h02 * h02 * lam)
    + (2 * h11 * h20 * lam) + (4 * cconj h02 * cconj lam * h02)

/-- The `w w̄²` coefficient of the cubic part of `A (φ w)`. -/
def pushD12 (lam q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  (cconj h20 * q11) + (cconj lam * (h11) ^ 2) + (h11 * q11) + (2 * cconj h11 * q02)
    + (2 * h02 * q20) + (cconj h20 * cconj lam * h11) + (-2 * cconj h11 * h02 * lam)
    + (2 * h02 * h20 * lam) + (4 * cconj h11 * cconj lam * h02)

/-- The `w̄³` coefficient of the cubic part of `A (φ w)`. -/
def pushD03 (lam q20 q11 q02 h20 h11 h02 : ℂ) : ℂ :=
  (h02 * q11) + (2 * cconj h20 * q02) + (cconj lam * h02 * h11) + (-2 * cconj h20 * h02 * lam)
    + (4 * cconj h20 * cconj lam * h02)

/-- The `w⁴` coefficient of the quartic remainder of the cubic-order push-forward. -/
def pushR40 (c30 c03 h20 h11 h02 : ℂ) : ℂ := (cconj c03 * h11) + (2 * c30 * h20)

/-- The `w³ w̄` coefficient of the quartic remainder of the cubic-order push-forward. -/
def pushR31 (c30 c21 c12 c03 h20 h11 h02 : ℂ) : ℂ :=
  (c30 * h11) + (cconj c12 * h11) + (2 * c21 * h20) + (2 * cconj c03 * h02)

/-- The `w² w̄²` coefficient of the quartic remainder of the cubic-order push-forward. -/
def pushR22 (c30 c21 c12 c03 h20 h11 h02 : ℂ) : ℂ :=
  (c21 * h11) + (cconj c21 * h11) + (2 * c12 * h20) + (2 * cconj c12 * h02)

/-- The `w w̄³` coefficient of the quartic remainder of the cubic-order push-forward. -/
def pushR13 (c30 c21 c12 c03 h20 h11 h02 : ℂ) : ℂ :=
  (c12 * h11) + (cconj c30 * h11) + (2 * c03 * h20) + (2 * cconj c21 * h02)

/-- The `w̄⁴` coefficient of the quartic remainder of the cubic-order push-forward. -/
def pushR04 (c30 c21 c12 c03 h20 h11 h02 : ℂ) : ℂ :=
  (c03 * h11) + (2 * cconj c30 * h02)

set_option linter.unusedVariables true

set_option maxHeartbeats 800000 in
/-- **The cubic-order push-forward identity.**  Let the real planar field have linear part `lam w`,
quadratic part `Q` and cubic part `C`, and let `φ w = w + h₂(w)` be the quadratic change of
variables.  Then the push-forward of the field is

`lam φ w + (quadratic part) + (cubic part) + (cubic part of A (φ w)) + (quartic remainder)`,

where the quadratic part of the transformed field is `A = Q − L h₂` and the cubic part is the cubic
form with coefficients `pushB30, pushB21, pushB12, pushB03`.  In particular the **resonant** cubic
coefficient, the coefficient of `w² w̄ = w |w|²`, is `pushB21`. -/
theorem cubic_pushForward (lam q20 q11 q02 c30 c21 c12 c03 h20 h11 h02 w : ℂ) :
    (1 + quadW h20 h11 h02 w) * planarField3 lam q20 q11 q02 c30 c21 c12 c03 w
        + quadWbar h20 h11 h02 w * cconj (planarField3 lam q20 q11 q02 c30 c21 c12 c03 w)
      = lam * (w + quadForm h20 h11 h02 w)
        + quadForm (pushA20 lam q20 h20) (pushA11 lam q11 h11) (pushA02 lam q02 h02) w
        + cubicForm (pushB30 lam q20 q11 q02 c30 h20 h11 h02) (pushB21 lam q20 q11 q02 c21 h20 h11 h02)
            (pushB12 lam q20 q11 q02 c12 h20 h11 h02) (pushB03 lam q20 q11 q02 c03 h20 h11 h02) w
        + cubicForm (pushD30 lam q20 q11 q02 h20 h11 h02) (pushD21 lam q20 q11 q02 h20 h11 h02)
            (pushD12 lam q20 q11 q02 h20 h11 h02) (pushD03 lam q20 q11 q02 h20 h11 h02) w
        + quarticForm (pushR40 c30 c03 h20 h11 h02) (pushR31 c30 c21 c12 c03 h20 h11 h02)
            (pushR22 c30 c21 c12 c03 h20 h11 h02) (pushR13 c30 c21 c12 c03 h20 h11 h02)
            (pushR04 c30 c21 c12 c03 h20 h11 h02) w := by
  simp only [planarField3, quadForm, quadW, quadWbar, cubicForm, quarticForm, pushA20, pushA11,
    pushA02, pushB30, pushB21, pushB12, pushB03, pushD30, pushD21, pushD12, pushD03, pushR40,
    pushR31, pushR22, pushR13, pushR04, cconj_add, cconj_mul, cconj_pow, cconj_cconj]
  ring

/-! ### The cubic resonance -/

/-- **The cubic resonance condition for `w² w̄`.**  The monomial `w² w̄ = w |w|²` is resonant for the
eigenvalue `lam` iff `2 lam + cconj lam = lam`, i.e. iff `lam` is purely imaginary — which is
exactly the situation at a Hopf crossing. -/
theorem cubic_resonance_w2wbar {lam : ℂ} : 2 * lam + cconj lam = lam ↔ lam + cconj lam = 0 := by
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- **The monomial `w³` is never resonant** (for `lam ≠ 0`). -/
theorem w3_not_resonant {lam : ℂ} (h : lam ≠ 0) : 3 * lam ≠ lam := by
  intro hc
  have h2 : 2 * lam = 0 := by linear_combination hc
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact absurd h2 (by norm_num)
  · exact h h2

/-- **The monomial `w w̄²` is never resonant** (for `lam ≠ 0`). -/
theorem wwbar2_not_resonant {lam : ℂ} (h : lam ≠ 0) : lam + 2 * cconj lam ≠ lam := by
  intro hc
  have h2 : 2 * cconj lam = 0 := by linear_combination hc
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact absurd h2 (by norm_num)
  · exact h (cconj_eq_zero.mp h2)

/-- **The monomial `w̄³` is never resonant** (for `lam ≠ 0`). -/
theorem wbar3_not_resonant {lam : ℂ} (h : lam ≠ 0) : 3 * cconj lam ≠ lam := by
  intro hc
  have hc' : 3 * lam = cconj lam := by
    have h2 := congrArg cconj hc
    simpa only [cconj_mul, cconj_three, cconj_cconj] using h2
  have h3 : 8 * lam = 0 := by linear_combination hc + 3 * hc'
  rcases mul_eq_zero.mp h3 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact h h3

/-- **At a Hopf crossing the monomial `w² w̄` is resonant.**  With `lam = i ω` and `ω ≠ 0` the
linear part is purely imaginary, so `lam + cconj lam = 0` and the resonant monomial is exactly
`w |w|²`. -/
theorem hopf_cubic_resonance {ω : ℝ} (_hω : ω ≠ 0) :
    2 * ((ω : ℂ) * Complex.I) + cconj ((ω : ℂ) * Complex.I) = ((ω : ℂ) * Complex.I) := by
  simp [cconj_mul, cconj_ofReal, cconj_I]
  ring

/-- **The resonant cubic coefficient of the transformed field**, i.e. the coefficient of the
resonant monomial `w² w̄ = w |w|²` in the cubic part of the push-forward of a real planar field by
the quadratic change of variables `φ w = w + h₂(w)`. -/
def resonantCoefficient (lam q20 q11 q02 c21 h20 h11 h02 : ℂ) : ℂ :=
  pushB21 lam q20 q11 q02 c21 h20 h11 h02

/-- **The resonant cubic coefficient in terms of the homological solution.**  Substituting the
solution `h₂₀ = −q₂₀/lam`, `h₁₁ = −q₁₁/cconj lam`, `h₀₂ = q₀₂/(lam − 2 cconj lam)` of the
degree-two homological equation, the resonant coefficient of the transformed field is the
corresponding explicit rational expression in the Taylor data. -/
noncomputable def resonantCoefficientSol (lam q20 q11 q02 c21 : ℂ) : ℂ :=
  pushB21 lam q20 q11 q02 c21 (h20Sol lam q20) (h11Sol lam q11) (h02Sol lam q02)

theorem normSq_eq_mul_conj (z : ℂ) : (Complex.normSq z : ℂ) = z * cconj z := by
  apply Complex.ext
  · simp [cconj, Complex.normSq_apply, Complex.mul_re, Complex.conj_re]
  · simp [cconj, Complex.normSq_apply, Complex.mul_im, Complex.conj_im]
    ring

/-- **The resonant monomial of the repository's Hopf normal form.**  The resonant term
`c₁ * (w * (Complex.normSq w : ℂ))` of `CRNT.PlanarHopfData.normalForm_eq` is exactly the resonant
monomial `w² w̄` of the normal form computed in this module; `CRNT.PlanarHopfData.c₁` is the
resonant coefficient `pushB21` of the transformed field. -/
theorem resonantMonomial_eq (w : ℂ) : w * (Complex.normSq w : ℂ) = w ^ 2 * cconj w := by
  rw [normSq_eq_mul_conj w]
  ring

/-! ## A remark on the naive homological operator -/

/-- **The naive operator** `lam h − cconj lam (h ∘ cconj)` that appears in some formulations of the
homological equation.  On the three-dimensional space of quadratic forms it is *not* the
homological operator of a real planar field: it is singular exactly at a Hopf crossing, where the
classical theory says the quadratic terms *are* removable. -/
def naiveHomological (lam : ℂ) (h20 h11 h02 : ℂ) (w : ℂ) : ℂ :=
  lam * quadForm h20 h11 h02 w - cconj lam * quadForm h20 h11 h02 (cconj w)

/-- **The naive operator is singular at a Hopf crossing.**  For `cconj lam = −lam` (that is, for a
purely imaginary `lam`) the quadratic form `(1, 0, −1)` lies in its kernel. -/
theorem naiveHomological_kernel {lam : ℂ} (h : cconj lam = -lam) (w : ℂ) :
    naiveHomological lam 1 0 (-1) w = 0 := by
  simp only [naiveHomological, quadForm, cconj_cconj]
  rw [h]
  ring

/-- **The naive operator kills the quadratic form `(1, 0, −1)` only when `lam` is purely
imaginary.**  In particular, at a Hopf crossing `lam = i ω` with `ω ≠ 0` it has a nontrivial kernel,
so it cannot be the homological operator (whose kernel is trivial for `lam ≠ 0`). -/
theorem naiveHomological_not_injective {ω : ℝ} (_hω : ω ≠ 0) :
    naiveHomological ((ω : ℂ) * Complex.I) 1 0 (-1) = 0 := by
  funext w
  refine naiveHomological_kernel ?_ w
  simp [cconj_mul, cconj_ofReal, cconj_I]

/-! ## Part 5: a concrete numerical instance -/

namespace Examples

/-- The linear coefficient `λ = i` of the numerical instance: the Hopf frequency is `ω = 1`. -/
def lam0 : ℂ := Complex.I

/-- The quadratic coefficient `a = 1` of the numerical instance. -/
def a0 : ℂ := 1

/-- The cubic coefficient `b = 1` of the numerical instance. -/
def b0 : ℂ := 1

/-- **The quadratic correction.**  For `λ = i`, `a = 1` the solution of the degree-two homological
equation is `c = −a/λ = i`. -/
example : -a0 / lam0 = Complex.I := by
  simp [a0, lam0, div_eq_mul_inv, Complex.inv_I]

/-- **The cubic coefficient of the normal form.**  `e₃ = b − 2a²/λ = 1 + 2i`. -/
example : e3 lam0 a0 b0 = 1 + 2 * Complex.I := by
  simp [e3, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]

/-- **The quartic coefficient of the normal form.**  `e₄ = ab/λ − 6a³/λ² = 6 − i`. -/
example : e4 lam0 a0 b0 = 6 - Complex.I := by
  simp [e4, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]
  ring

/-- **The quintic coefficient of the normal form.**  `e₅ = a²b/λ² − 18a⁴/λ³ = −1 − 18i`. -/
example : e5 lam0 a0 b0 = -1 - 18 * Complex.I := by
  simp [e5, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]

/-- **The cubic correction.**  `d = (6a²/λ² − b/λ)/9 = (−6 + i)/9`. -/
example : cubicCorrection lam0 a0 b0 = ((-6 : ℂ) + Complex.I) / 9 := by
  simp [cubicCorrection, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]

/-- **The cubic coefficient of the cubic normal form.**  `E₃ = (7bλ − 6a²)/(9λ) = (7 + 6i)/9`. -/
example : E3 lam0 a0 b0 = ((7 : ℂ) + 6 * Complex.I) / 9 := by
  simp [E3, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **The quintic coefficient of the cubic normal form.**
`E₅ = (90a⁴ − 57a²bλ − 2b²λ²)/(27λ³) = (57 + 92i)/27`. -/
example : E5 lam0 a0 b0 = ((57 : ℂ) + 92 * Complex.I) / 27 := by
  simp [E5, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **The normal form identity, checked at `w = 1`.**  The Taylor jet of the push-forward of
`F w = i w + w² + w³` by the quadratic change `φ w = w + i w²` is
`i + (1 + 2i) + (6 − i) + (−1 − 18i)`. -/
example : quadJet lam0 a0 b0 (-a0 / lam0) 1
    = lam0 + e3 lam0 a0 b0 + e4 lam0 a0 b0 + e5 lam0 a0 b0 := by
  have h := cubic_normal_form (lam := lam0) (a := a0) (b := b0) (by simp [lam0]) 1
  simpa [e3, e4, e5, lam0, a0, b0, div_eq_mul_inv, Complex.inv_I] using h

/-- **The cubic normal form identity, checked at `w = 1`.**  The Taylor jet of the push-forward of
`F w = i w + w² + w³` by the cubic change `φ w = w + i w² + ((−6 + i)/9) w³` is
`i + (7 + 6i)/9 + (57 + 92i)/27`. -/
example : cubicJet lam0 a0 b0 (-a0 / lam0) (cubicCorrection lam0 a0 b0) 1
    = lam0 + E3 lam0 a0 b0 + E5 lam0 a0 b0 := by
  have h := cubic_normal_form_cubic (lam := lam0) (a := a0) (b := b0) (by simp [lam0]) 1
  simpa [lam0, a0, b0] using h

/-- **The quadratic terms are removed at the Hopf crossing `λ = i`.**  With the quadratic part
`Q w = w²` the solution of the degree-two homological equation is `h₂ = i w²`, and the quadratic
part of the transformed field vanishes. -/
example (w : ℂ) : homologicalQuad lam0 (h20Sol lam0 1) (h11Sol lam0 0) (h02Sol lam0 0) w
    = quadForm 1 0 0 w := by
  exact homologicalQuad_solution (lam := lam0) (q20 := 1) (q11 := 0) (q02 := 0) (by simp [lam0]) w

/-- **The resonant cubic coefficient at the Hopf crossing.**  For `λ = i`, the quadratic part
`Q w = w²` and the cubic part `C w = w² w̄`, the resonant coefficient of the transformed field is
`1`: the quadratic part `w²` does not contribute to the resonant monomial `w² w̄` (only the
coefficients `q₁₁, q₀₂` and `h₁₁, h₀₂` do), so the resonant coefficient is the cubic Taylor
coefficient `c₂₁ = 1` itself. -/
example : resonantCoefficient lam0 1 0 0 1 (h20Sol lam0 1) 0 0 = 1 := by
  simp [resonantCoefficient, pushB21, lam0]

/-- **The cubic-order push-forward identity, checked numerically.**  For `λ = i`, the quadratic part
`Q w = w²`, the cubic part `C w = w² w̄` and the quadratic removal `h₂ = i w²`, the push-forward
of the field at `w = 1` is `5i`. -/
example :
    (1 + quadW (h20Sol lam0 1) 0 0 1) * planarField3 lam0 1 0 0 0 1 0 0 1
        + quadWbar (h20Sol lam0 1) 0 0 1 * cconj (planarField3 lam0 1 0 0 0 1 0 0 1)
      = 5 * Complex.I := by
  simp [h20Sol, planarField3, quadW, quadWbar, quadForm, cubicForm, lam0, div_eq_mul_inv,
    Complex.inv_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Examples

end Hopf
end CRNT
