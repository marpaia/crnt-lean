import CRNT.Dynamics.TikhonovLocal
import CRNT.Dynamics.ExponentialDecay
import Mathlib.Analysis.ODE.Gronwall

/-!
# The tube hypothesis of the local Tikhonov theorem

`CRNT.Dynamics.TikhonovLocal` proves the **local** (Hurwitz) form of Tikhonov's theorem for the
singularly perturbed system

```
ẋ = f (x, y),      ε ẏ = g (x, y)
```

with a local slow manifold `y = h (x)` (`g (x, h x) = 0`), a local one-sided contraction of the fast
field toward the slow manifold (a consequence of the Hurwitz linearisation
`CRNT.local_contraction_of_hurwitz`), the `ε`-scaled frozen system and its collapse, and the
quantitative estimate `CRNT.fast_deviation_le_local`

```
‖y t - h (x t)‖² ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G / ν)²
```

for the **coupled** solution — but that estimate is stated *under* the **tube hypothesis**

```
(htube : ∀ t, dist (y t) (h (x t)) ≤ δ)
```

that the coupled solution stays within distance `δ` of the (moving) slow manifold. This module
**discharges the tube hypothesis**: the coupled solution that starts inside the tube *stays* inside
it, and the quantitative fast-deviation estimate then follows without any further assumption.

## The tube argument

Write `e t = y t - h (x t)` for the **fast deviation** and `w t = ‖e t‖` for its norm. The
deviation satisfies

```
ė = (1/ε) g (x t, y t) - D h (x t) (f (x t, y t))
```

because the slow manifold moves with the slow field. As long as the solution stays in the tube
(`w t ≤ δ`), the local one-sided contraction of the fast field toward the slow manifold gives

```
⟪g (x t, y t) - g (x t, h (x t)), e t⟫ ≤ -ν ‖e t‖²,     g (x t, h (x t)) = 0,
```

and the bounded speed of the slow manifold (`‖D h (x t) (f (x t, y t))‖ ≤ G`) gives, by the
arithmetic–geometric mean estimate `2 G w ≤ (ν/ε) w² + (ε/ν) G²`,

```
(1/2) (w²)' ≤ -(ν/ε) w² + (ε/ν) G².
```

With the **shifted** Lyapunov function `φ t = w t² - (ε G/ν)²` this is the *exact* differential
inequality `φ' ≤ -(ν/ε) φ`, because `(ν/ε)(ε G/ν)² = (ε/ν) G²`. Grönwall therefore yields

```
φ t ≤ e^{-(ν/ε) t} φ 0        (on any interval on which the tube holds)
```

i.e. `w t ≤ max (w 0, ε G/ν)`: **the fast deviation never exceeds the larger of its initial value
and the tracking-error scale `ε G/ν`.**

Two consequences:

* the tube of radius `δ` is **forward invariant** as soon as `ε G/ν < δ` and the solution starts
  inside it. Indeed, if the deviation left the tube for the first time at `τ`, then `w τ ≥ δ` while
  `w s ≤ δ` for `s < τ`; the Grönwall estimate on `[0, τ]` gives
  `φ τ ≤ e^{-(ν/ε) τ} φ 0 ≤ e^{-(ν/ε) τ} φ τ < φ τ`, a contradiction (`φ τ = δ² - (ε G/ν)² > 0`).
  This is `CRNT.tikhonov_local_tube`.
* the fast-deviation estimate of `CRNT.Dynamics.TikhonovLocal` then holds **unconditionally**
  (`CRNT.tikhonov_local_tube_deviation`).

## The slow error

With the tube in place, the *reduced* (slow) system `Ż = f (Z, h Z)` started at `Z 0 = x 0`
approximates the slow variable: `CRNT.tikhonov_local_slow_error` gives

```
‖x t - Z t‖ ≤ (L_f / L) * max (‖y 0 - h (x 0)‖, ε G/ν) * (e^{L t} - 1),
```

which is `O (ε)` as soon as the initial fast deviation is `O (ε)` — the classical statement that
"the reduced system approximates the slow motion". The proof is the usual comparison
`Q' ≤ 2 L_f √Q w + 2 L Q` for the squared slow error `Q = ‖x - Z‖²`, read through
`Ψ = √(Q + κ)` so that the square root is differentiable everywhere.

## What is proved, and what remains

**Proved here.**

* `CRNT.fast_deviation_deriv_le` — the differential inequality for the fast deviation, valid as
  long as the coupled solution is inside the tube.
* `CRNT.fast_deviation_le_local_on` — the Grönwall estimate on a *finite* interval on which the
  tube holds (this is the version of `CRNT.fast_deviation_le_local` that does not presuppose the
  tube hypothesis for all time).
* `CRNT.tikhonov_local_tube` — **the tube hypothesis is discharged**: the coupled solution that
  starts inside the tube stays inside it.
* `CRNT.tikhonov_local_tube_deviation` — the tube hypothesis *and* the quantitative fast-deviation
  estimate.
* `CRNT.tikhonov_local_slow_error` — the `O (ε)` error of the reduced slow dynamics: the coupled
  slow variable stays within `(L_f / L) * max (‖y 0 - h (x 0)‖, ε G/ν) * (e^{L t} - 1)` of the
  solution `Z` of the reduced system `Ż = f (Z, h Z)`.

**Still missing (not proved here).**

* **Entry into the tube.** The argument above shows that a coupled solution *starting inside* the
  tube stays inside it. It does **not** show that a solution starting *outside* the tube enters it:
  that is the genuine Fenichel step (the graph transform / Lyapunov–Perron operator of
  `CRNT.Dynamics.FenichelPersistence`, whose `flow_mapsTo` hypothesis is still a hypothesis for a
  general coupled field). Locally, entry is available for the *frozen* fast system
  (`CRNT.frozen_attraction_of_hurwitz`), not yet for the coupled one.
* **The `ε`-dependent (Fenichel) manifold.** The manifold used here is the *reduced* slow manifold
  `g (x, h x) = 0`; the `ε`-dependent invariant manifold `h_ε` with `h_ε → h` is the persistence
  theorem of `CRNT.Dynamics.FenichelPersistence` and is not reproduced here.
* **Spectral Hurwitz.** As in `CRNT.Dynamics.TikhonovLocal`, the Hurwitz hypothesis is used in its
  Lyapunov–Krasovskii (symmetric-part) form.

Depends on: `CRNT.Dynamics.TikhonovLocal`, `CRNT.Dynamics.ExponentialDecay`,
`Mathlib.Analysis.ODE.Gronwall`.
-/

open Filter Set
open scoped Topology BigOperators RealInnerProductSpace

namespace CRNT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## 1. The differential inequality for the fast deviation -/

omit [CompleteSpace X] in
/-- **The fast-deviation differential inequality.** Let `ẋ = f (x, y)`, `ε ẏ = g (x, y)` be a
singularly perturbed system, let `y = h (x)` be a slow manifold (`g (z, h z) = 0` for `z ∈ Kx`),
assume that the fast field is one-sided contracting toward the slow manifold at rate `ν > 0` on the
`δ`-neighbourhood of the manifold, and that the slow manifold moves with bounded speed
`‖D h z (f z u)‖ ≤ G`.

If the coupled solution stays inside the tube (`dist (y t) (h (x t)) ≤ δ`), then the fast deviation
`e t = y t - h (x t)` satisfies

```
2 ⟪e t, (1/ε) g (x t, y t) - D h (x t) (f (x t, y t))⟫
    ≤ -(ν/ε) ‖e t‖² + (ε/ν) G².
```

This is the differential inequality from which the tube and the fast-deviation estimate follow; the
arithmetic–geometric mean step `2 G ‖e‖ ≤ (ν/ε) ‖e‖² + (ε/ν) G²` is the only place where the two
rates `ν` (contraction) and `G` (speed of the manifold) are combined. -/
theorem fast_deviation_deriv_le {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {ν G ε δ T : ℝ}
    (hν : 0 < ν) (hε : 0 < ε)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (x : ℝ → X) (y : ℝ → E)
    (hxK : ∀ t, x t ∈ Kx)
    (htube : ∀ t ∈ Ico 0 T, dist (y t) (h (x t)) ≤ δ) :
    ∀ t ∈ Ico 0 T,
      2 * ⟪y t - h (x t), (1 / ε) • g (x t) (y t) - Dh (x t) (f (x t) (y t))⟫
        ≤ -(ν / ε) * ‖y t - h (x t)‖ ^ 2 + (ε / ν) * G ^ 2 := by
  intro t ht
  -- the contraction at the slow-manifold point, with the roles of the two inner-product
  -- arguments exchanged
  have hcon : ⟪y t - h (x t), g (x t) (y t) - g (x t) (h (x t))⟫
      ≤ -ν * ‖y t - h (x t)‖ ^ 2 := by
    have h5 := hmono (x t) (hxK t) (y t) (htube t ht)
    rwa [real_inner_comm] at h5
  have hzero' : g (x t) (h (x t)) = 0 := hzero (x t) (hxK t)
  -- the fast field is pulled toward the manifold: `⟪e, g (x, y)⟫ ≤ -ν ‖e‖²`
  have hinner : ⟪y t - h (x t), g (x t) (y t)⟫ ≤ -ν * ‖y t - h (x t)‖ ^ 2 := by
    have h1 : ⟪y t - h (x t), g (x t) (y t) - g (x t) (h (x t))⟫
        = ⟪y t - h (x t), g (x t) (y t)⟫ - ⟪y t - h (x t), g (x t) (h (x t))⟫ := by
      rw [inner_sub_right]
    have h2 : ⟪y t - h (x t), g (x t) (h (x t))⟫ = 0 := by rw [hzero', inner_zero_right]
    rw [h2, sub_zero] at h1
    rw [← h1]
    exact hcon
  -- the speed of the slow manifold
  have hG' : ‖Dh (x t) (f (x t) (y t))‖ ≤ G := hGb (x t) (hxK t) (y t)
  have hcs' : -⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫
      ≤ ‖y t - h (x t)‖ * ‖Dh (x t) (f (x t) (y t))‖ := by
    have habs := abs_real_inner_le_norm (y t - h (x t)) (Dh (x t) (f (x t) (y t)))
    have hneg : -⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫
        ≤ |⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫| :=
      neg_le_abs _
    linarith
  -- arithmetic–geometric mean: `2 G w ≤ (ν/ε) w² + (ε/ν) G²`
  have hAMGM : ∀ (w : ℝ), 0 ≤ w →
      2 * G * w ≤ (ν / ε) * w ^ 2 + (ε / ν) * G ^ 2 := by
    intro w hw
    have hk : 0 < ν / ε := div_pos hν hε
    have hkm : (ν / ε) * (ε / ν) = 1 := by field_simp
    set A := Real.sqrt (ν / ε) with hAdef
    set B := Real.sqrt (ε / ν) with hBdef
    have hAsq : A ^ 2 = ν / ε := by
      rw [hAdef]; rw [Real.sq_sqrt (by positivity)]
    have hBsq : B ^ 2 = ε / ν := by
      rw [hBdef]; rw [Real.sq_sqrt (by positivity)]
    have hAB : A * B = 1 := by
      rw [hAdef, hBdef, ← Real.sqrt_mul hk.le (ε / ν), hkm, Real.sqrt_one]
    have hsq : 0 ≤ (A * w - B * G) ^ 2 := sq_nonneg _
    calc 2 * G * w = 2 * (A * B) * (G * w) := by rw [hAB]; ring
      _ ≤ A ^ 2 * w ^ 2 + B ^ 2 * G ^ 2 := by nlinarith [hsq]
      _ = (ν / ε) * w ^ 2 + (ε / ν) * G ^ 2 := by rw [hAsq, hBsq]
  -- the assembly
  have h1 : (1 / ε) * ⟪y t - h (x t), g (x t) (y t)⟫
      ≤ -(ν / ε) * ‖y t - h (x t)‖ ^ 2 := by
    calc (1 / ε) * ⟪y t - h (x t), g (x t) (y t)⟫
        ≤ (1 / ε) * (-ν * ‖y t - h (x t)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = -(ν / ε) * ‖y t - h (x t)‖ ^ 2 := by field_simp
  have h2 : -⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫
      ≤ ‖y t - h (x t)‖ * G := by
    have h3 : ‖y t - h (x t)‖ * ‖Dh (x t) (f (x t) (y t))‖
        ≤ ‖y t - h (x t)‖ * G :=
      mul_le_mul_of_nonneg_left hG' (norm_nonneg _)
    linarith
  have h3 : 2 * G * ‖y t - h (x t)‖
      ≤ (ν / ε) * ‖y t - h (x t)‖ ^ 2 + (ε / ν) * G ^ 2 :=
    hAMGM ‖y t - h (x t)‖ (norm_nonneg _)
  have hsmul : ⟪y t - h (x t), (1 / ε) • g (x t) (y t)⟫
      = (1 / ε) * ⟪y t - h (x t), g (x t) (y t)⟫ := by
    rw [real_inner_smul_right]
  have hsub : ⟪y t - h (x t), (1 / ε) • g (x t) (y t) - Dh (x t) (f (x t) (y t))⟫
      = ⟪y t - h (x t), (1 / ε) • g (x t) (y t)⟫
        - ⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫ := by
    rw [inner_sub_right]
  calc 2 * ⟪y t - h (x t), (1 / ε) • g (x t) (y t) - Dh (x t) (f (x t) (y t))⟫
      = 2 * ((1 / ε) * ⟪y t - h (x t), g (x t) (y t)⟫
          - ⟪y t - h (x t), Dh (x t) (f (x t) (y t))⟫) := by
        rw [hsub, hsmul]
    _ ≤ 2 * (-(ν / ε) * ‖y t - h (x t)‖ ^ 2 + ‖y t - h (x t)‖ * G) := by
        have := add_le_add h1 h2
        linarith
    _ = -(2 * (ν / ε)) * ‖y t - h (x t)‖ ^ 2 + 2 * G * ‖y t - h (x t)‖ := by ring
    _ ≤ -(ν / ε) * ‖y t - h (x t)‖ ^ 2 + (ε / ν) * G ^ 2 := by
        have := h3
        nlinarith

/-! ## 2. The fast-deviation estimate on an interval on which the tube holds -/

omit [CompleteSpace X] in
/-- **The fast-deviation estimate on a finite interval.** This is the version of
`CRNT.fast_deviation_le_local` that does *not* presuppose the tube hypothesis for all time: it only
requires the coupled solution to stay inside the tube on `(0, T]`, and it concludes the estimate on
`[0, T]`.

With the hypotheses of `CRNT.fast_deviation_deriv_le`,

```
‖y t - h (x t)‖² - (ε G/ν)² ≤ e^{-(ν/ε) t} (‖y 0 - h (x 0)‖² - (ε G/ν)²)      (t ∈ [0, T]),
‖y t - h (x t)‖²           ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G/ν)²           (t ∈ [0, T]).
```

The proof is the shifted-Lyapunov argument: `φ t = ‖y t - h (x t)‖² - (ε G/ν)²` satisfies
`φ' ≤ -(ν/ε) φ`, whence Grönwall. -/
theorem fast_deviation_le_local_on {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {ν G ε δ T : ℝ}
    (hν : 0 < ν) (hε : 0 < ε)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (x : ℝ → X) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (htube : ∀ t ∈ Ico 0 T, dist (y t) (h (x t)) ≤ δ) :
    ∀ t ∈ Icc 0 T,
      ‖y t - h (x t)‖ ^ 2 - (ε * G / ν) ^ 2 ≤
        Real.exp (-(ν / ε * t)) * (‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2) ∧
      ‖y t - h (x t)‖ ^ 2 ≤
        Real.exp (-(ν / ε * t)) * ‖y 0 - h (x 0)‖ ^ 2 + (ε * G / ν) ^ 2 := by
  intro t ht
  -- the fast deviation
  set e : ℝ → E := fun t => y t - h (x t) with he
  have hcomp : ∀ s, HasDerivAt (fun r : ℝ => h (x r)) (Dh (x s) (f (x s) (y s))) s := by
    intro s
    exact (hh (x s) (hxK s)).comp_hasDerivAt s (hx s)
  have hed : ∀ s, HasDerivAt e
      ((1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))) s := by
    intro s
    exact (hy s).sub (hcomp s)
  -- the squared deviation
  set Edev : ℝ → ℝ := fun t => ‖e t‖ ^ 2 with hE
  have hEder : ∀ s, HasDerivAt Edev
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) s := by
    intro s
    have h := (hed s).inner ℝ (hed s)
    have hsym : ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫
        + ⟪(1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s)), e s⟫
        = 2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫ := by
      rw [real_inner_comm]
      ring
    rw [hsym] at h
    rw [show (fun r : ℝ => ⟪e r, e r⟫) = fun r : ℝ => ‖e r‖ ^ 2 by
      funext r; rw [real_inner_self_eq_norm_sq]] at h
    simpa [hE] using h
  -- the shifted Lyapunov function
  set φ : ℝ → ℝ := fun t => Edev t - (ε * G / ν) ^ 2 with hφ
  have hφder : ∀ s, HasDerivAt φ
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) s := by
    intro s
    have h2 := hEder s
    have h3 := h2.sub_const ((ε * G / ν) ^ 2)
    simpa [hφ] using h3
  have hφs (s : ℝ) : φ s = ‖e s‖ ^ 2 - (ε * G / ν) ^ 2 := by
    simp only [hφ, hE]
  have hφbound : ∀ s ∈ Ico 0 t,
      (2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫) ≤ -(ν / ε) * φ s := by
    intro s hs
    have hb := fast_deviation_deriv_le (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
      (ν := ν) (G := G) (ε := ε) (δ := δ) (T := t) hν hε hzero hmono hGb x y hxK
      (fun u hu => htube u ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩) s hs
    have heq : y s - h (x s) = e s := by simp only [he]
    rw [heq] at hb
    have hc : (ν / ε) * (ε * G / ν) ^ 2 = ε / ν * G ^ 2 := by field_simp
    have hRHS : -(ν / ε) * ‖e s‖ ^ 2 + (ε / ν) * G ^ 2 = -(ν / ε) * φ s := by
      calc -(ν / ε) * ‖e s‖ ^ 2 + (ε / ν) * G ^ 2
          = -(ν / ε) * ‖e s‖ ^ 2 + (ν / ε) * (ε * G / ν) ^ 2 := by rw [← hc]
        _ = -(ν / ε) * (‖e s‖ ^ 2 - (ε * G / ν) ^ 2) := by ring
        _ = -(ν / ε) * φ s := by rw [hφs s]
    rw [← hRHS]
    exact hb
  have hgron := CRNT.ExponentialDecay.le_mul_exp_of_deriv_le (V := φ)
    (V' := fun s => 2 * ⟪e s, (1 / ε) • g (x s) (y s) - Dh (x s) (f (x s) (y s))⟫)
    (K := -(ν / ε)) (b := t) hφder hφbound t ⟨ht.1, le_rfl⟩
  have hexp : 0 ≤ Real.exp (-(ν / ε) * t) := (Real.exp_pos _).le
  have hexp_eq : Real.exp (-(ν / ε) * t) = Real.exp (-(ν / ε * t)) := by
    congr 1
    ring
  -- the shifted estimate
  have hshift : ‖e t‖ ^ 2 - (ε * G / ν) ^ 2 ≤
      Real.exp (-(ν / ε * t)) * (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2) := by
    have h1 : ‖e t‖ ^ 2 - (ε * G / ν) ^ 2 ≤
        (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2) * Real.exp (-(ν / ε) * t) := by
      simpa [hφ, hE] using hgron
    have h2 : (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2) * Real.exp (-(ν / ε) * t)
        = Real.exp (-(ν / ε * t)) * (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2) := by
      rw [hexp_eq]
      ring
    rw [h2] at h1
    exact h1
  -- the usual estimate
  have hplain : ‖e t‖ ^ 2 ≤
      Real.exp (-(ν / ε * t)) * ‖e 0‖ ^ 2 + (ε * G / ν) ^ 2 := by
    have h1 : ‖e t‖ ^ 2 ≤
        Real.exp (-(ν / ε * t)) * (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2) + (ε * G / ν) ^ 2 := by
      have := hshift
      nlinarith
    have h2 : Real.exp (-(ν / ε * t)) * (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2)
        ≤ Real.exp (-(ν / ε * t)) * ‖e 0‖ ^ 2 := by
      have h3 : 0 ≤ Real.exp (-(ν / ε * t)) * (ε * G / ν) ^ 2 :=
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      have h4 : Real.exp (-(ν / ε * t)) * (‖e 0‖ ^ 2 - (ε * G / ν) ^ 2)
          = Real.exp (-(ν / ε * t)) * ‖e 0‖ ^ 2
            - Real.exp (-(ν / ε * t)) * (ε * G / ν) ^ 2 := by ring
      rw [h4]
      nlinarith
    nlinarith
  have hEt : ‖e t‖ ^ 2 = ‖y t - h (x t)‖ ^ 2 := by simp only [he]
  have hE0 : ‖e 0‖ ^ 2 = ‖y 0 - h (x 0)‖ ^ 2 := by simp only [he]
  rw [hEt, hE0] at hshift hplain
  exact ⟨hshift, hplain⟩

/-! ## 3. The tube hypothesis is discharged -/

omit [CompleteSpace X] in
/-- **The tube lemma: the coupled solution stays in the tube.** Let `ẋ = f (x, y)`, `ε ẏ = g (x, y)`
be a singularly perturbed system, let `y = h (x)` be a `C¹` slow manifold (`g (z, h z) = 0` for
`z ∈ Kx`), and assume

* the fast field is one-sided contracting toward the slow manifold at rate `ν > 0` on the
  `δ`-neighbourhood of the manifold:
  `⟪g z u - g z (h z), u - h z⟫ ≤ -ν ‖u - h z‖²` for `dist u (h z) ≤ δ`;
* the slow manifold moves with bounded speed: `‖D h z (f z u)‖ ≤ G`;
* the **tube radius dominates the tracking-error scale**: `ε G / ν < δ`.

If the coupled solution starts *strictly inside* the tube (`dist (y 0) (h (x 0)) < δ`), then it
**stays** inside the tube for all forward time:

```
∀ t ≥ 0, dist (y t) (h (x t)) ≤ δ.
```

This is the missing step of `CRNT.Dynamics.TikhonovLocal`: the *tube hypothesis* of
`CRNT.fast_deviation_le_local` is a theorem here, not an assumption.

The proof is a first-exit argument. If the deviation left the tube for the first time at `τ`, then
the tube holds on `[0, τ)`, the shifted Grönwall estimate
`φ τ ≤ e^{-(ν/ε) τ} φ 0` applies on `[0, τ]`, and — because `w τ ≥ δ > ε G/ν` — the shifted
Lyapunov function `φ = w² - (ε G/ν)²` is strictly positive at `τ` while `φ 0 ≤ φ τ`, which is
contradictory. -/
theorem tikhonov_local_tube {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {ν G ε δ : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hG : 0 ≤ G)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (x : ℝ → X) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (hinit : dist (y 0) (h (x 0)) < δ)
    (hsmall : ε * G / ν < δ) :
    ∀ t, 0 ≤ t → dist (y t) (h (x t)) ≤ δ := by
  intro t ht
  by_contra hcon
  have hgt : δ < dist (y t) (h (x t)) := not_le.mp hcon
  -- continuity of the deviation
  have hycont : Continuous y := (continuous_iff_continuousAt.2 fun s => (hy s).continuousAt)
  have hxcont : Continuous x := (continuous_iff_continuousAt.2 fun s => (hx s).continuousAt)
  have hhat : ∀ z ∈ Kx, ContinuousAt h z := fun z hz => (hh z hz).continuousAt
  have hcomp : Continuous (fun s => h (x s)) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hhat (x s) (hxK s)).comp' hxcont.continuousAt
  have hwcont : Continuous (fun s => dist (y s) (h (x s))) := hycont.dist hcomp
  -- the exit set and its infimum
  set E : Set ℝ := {s | 0 ≤ s ∧ δ < dist (y s) (h (x s))} with hE
  have hEne : E.Nonempty := ⟨t, ht, hgt⟩
  have hEbdd : BddBelow E := ⟨0, fun s hs => hs.1⟩
  set τ : ℝ := sInf E with hτ
  have hτ0 : 0 ≤ τ := le_csInf hEne (fun s hs => hs.1)
  -- the tube holds strictly before τ
  have hstrict : ∀ s, 0 ≤ s → s < τ → dist (y s) (h (x s)) ≤ δ := by
    intro s hs hst
    by_contra hnot
    have hmem : s ∈ E := ⟨hs, not_le.mp hnot⟩
    exact absurd (csInf_le hEbdd hmem) (not_le.mpr hst)
  -- the tube holds on a neighbourhood of 0, hence τ > 0
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.mp hwcont.continuousAt
    (δ - dist (y 0) (h (x 0))) (by linarith [hinit])
  have hnear : ∀ s ∈ Ioo 0 η, dist (y s) (h (x s)) ≤ δ := by
    intro s hs
    have hdist : dist s 0 < η := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      exact hs.2
    have hws := hη' hdist
    have habs : dist (y s) (h (x s)) - dist (y 0) (h (x 0))
        ≤ dist (dist (y s) (h (x s))) (dist (y 0) (h (x 0))) := by
      have h1 := le_abs_self (dist (y s) (h (x s)) - dist (y 0) (h (x 0)))
      have h2 : dist (dist (y s) (h (x s))) (dist (y 0) (h (x 0)))
          = |dist (y s) (h (x s)) - dist (y 0) (h (x 0))| := by
        rw [dist_eq_norm, Real.norm_eq_abs]
      linarith
    linarith
  have hτη : η ≤ τ := by
    refine le_csInf hEne ?_
    intro s hs
    by_contra hnot
    have hlt : s < η := lt_of_not_ge hnot
    have hs0 : 0 < s := by
      have hne : s ≠ 0 := by
        rintro rfl
        exact absurd hs.2 (not_lt_of_ge hinit.le)
      exact lt_of_le_of_ne hs.1 (Ne.symm hne)
    have := hnear s ⟨hs0, hlt⟩
    exact absurd this (not_le_of_gt hs.2)
  have hτpos : 0 < τ := lt_of_lt_of_le hη hτη
  -- the deviation at the exit time is at least δ
  have hwτ : δ ≤ dist (y τ) (h (x τ)) := by
    by_contra hnot
    have hlt : dist (y τ) (h (x τ)) < δ := lt_of_not_ge hnot
    obtain ⟨ξ, hξ, hξ'⟩ := Metric.continuousAt_iff.mp hwcont.continuousAt
      (δ - dist (y τ) (h (x τ))) (by linarith)
    have hexists : ∃ s ∈ E, τ ≤ s ∧ s < τ + ξ := by
      by_contra hcon
      have hnot : ∀ s ∈ E, ¬(s < τ + ξ) := by
        intro s hs hlt
        exact hcon ⟨s, hs, csInf_le hEbdd hs, hlt⟩
      have hlb : τ + ξ ≤ sInf E := by
        refine le_csInf hEne ?_
        intro s hs
        exact le_of_not_gt (hnot s hs)
      linarith [hτ]
    obtain ⟨s, hsE, hsτ, hslt⟩ := hexists
    have hdist : dist s τ < ξ := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsτ)]
      linarith
    have hws := hξ' hdist
    have habs : dist (y s) (h (x s)) - dist (y τ) (h (x τ))
        ≤ dist (dist (y s) (h (x s))) (dist (y τ) (h (x τ))) := by
      have h1 := le_abs_self (dist (y s) (h (x s)) - dist (y τ) (h (x τ)))
      have h2 : dist (dist (y s) (h (x s))) (dist (y τ) (h (x τ)))
          = |dist (y s) (h (x s)) - dist (y τ) (h (x τ))| := by
        rw [dist_eq_norm, Real.norm_eq_abs]
      linarith
    have hlt2 : dist (y s) (h (x s)) < δ := by linarith
    exact absurd hlt2 (not_lt_of_gt hsE.2)
  -- the shifted Grönwall estimate on [0, τ]
  have hgron := fast_deviation_le_local_on (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
    (ν := ν) (G := G) (ε := ε) (δ := δ) (T := τ) hν hε hh hzero hmono hGb x y hx hy hxK
    (fun s hs => hstrict s hs.1 hs.2) τ ⟨hτ0, le_rfl⟩
  have hshift := hgron.1
  -- the contradiction
  set A : ℝ := ‖y τ - h (x τ)‖ ^ 2 - (ε * G / ν) ^ 2 with hA
  set B : ℝ := ‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2 with hB
  set e : ℝ := Real.exp (-(ν / ε * τ)) with he
  have hc : 0 ≤ ε * G / ν := by positivity
  have hδ : 0 ≤ δ := le_of_lt (lt_of_le_of_lt hc hsmall)
  have h1 : δ ≤ ‖y τ - h (x τ)‖ := by
    rw [← dist_eq_norm]
    exact hwτ
  have h1' : δ ^ 2 ≤ ‖y τ - h (x τ)‖ ^ 2 := by
    have := mul_self_le_mul_self hδ h1
    simpa [pow_two] using this
  have hApos : 0 < A := by
    have h2 : (ε * G / ν) ^ 2 < δ ^ 2 := (sq_lt_sq₀ hc hδ).mpr hsmall
    simp only [hA]
    linarith
  have hB_le : B ≤ A := by
    have h3 : ‖y 0 - h (x 0)‖ < δ := by
      rw [dist_eq_norm] at hinit
      exact hinit
    have h4 : ‖y 0 - h (x 0)‖ ^ 2 < δ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hδ).mpr h3
    simp only [hB, hA]
    linarith
  have hshift' : A ≤ e * B := by simpa [hA, hB, he] using hshift
  have he_lt : e < 1 := by
    have h1 : -(ν / ε * τ) < 0 := by
      have hνε : 0 < ν / ε := div_pos hν hε
      have h2 : 0 < ν / ε * τ := mul_pos hνε hτpos
      linarith
    have := Real.exp_lt_one_iff.mpr h1
    simpa [he] using this
  have he_pos : 0 ≤ e := by simp only [he]; positivity
  have hstep : A ≤ e * A := le_trans hshift' (mul_le_mul_of_nonneg_left hB_le he_pos)
  have hlt : e * A < A := by
    have h1 := mul_lt_mul_of_pos_right he_lt hApos
    simpa using h1
  exact absurd hstep (not_le_of_gt hlt)

/-! ## 4. The tube hypothesis and the fast-deviation estimate -/

omit [CompleteSpace X] in
/-- **The tube hypothesis and the fast-deviation estimate, unconditionally.** Under the hypotheses
of `CRNT.tikhonov_local_tube` (so the tube hypothesis is a *theorem*, not an assumption), the coupled
solution satisfies, for every `t ≥ 0`,

```
dist (y t) (h (x t)) ≤ δ,
‖y t - h (x t)‖² ≤ e^{-(ν/ε) t} ‖y 0 - h (x 0)‖² + (ε G/ν)²,
‖y t - h (x t)‖ ≤ max (‖y 0 - h (x 0)‖, ε G/ν).
```

The last line is the quantitative content of the tube: the fast deviation never exceeds the larger
of its initial value and the tracking-error scale `ε G/ν`. -/
theorem tikhonov_local_tube_deviation {f : X → E → X} {g : X → E → E} {h : X → E}
    (Dh : X → (X →L[ℝ] E)) {Kx : Set X} {ν G ε δ : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hG : 0 ≤ G)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    (x : ℝ → X) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (hinit : dist (y 0) (h (x 0)) < δ)
    (hsmall : ε * G / ν < δ) :
    (∀ t, 0 ≤ t → dist (y t) (h (x t)) ≤ δ) ∧
    (∀ t, 0 ≤ t → ‖y t - h (x t)‖ ^ 2 ≤
      Real.exp (-(ν / ε * t)) * ‖y 0 - h (x 0)‖ ^ 2 + (ε * G / ν) ^ 2) ∧
    (∀ t, 0 ≤ t → ‖y t - h (x t)‖ ≤ max ‖y 0 - h (x 0)‖ (ε * G / ν)) := by
  have htube := tikhonov_local_tube (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
    (ν := ν) (G := G) (ε := ε) (δ := δ) hν hε hG hh hzero hmono hGb x y hx hy hxK hinit hsmall
  have hgron : ∀ t, 0 ≤ t →
      (‖y t - h (x t)‖ ^ 2 - (ε * G / ν) ^ 2 ≤
        Real.exp (-(ν / ε * t)) * (‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2)) ∧
      ‖y t - h (x t)‖ ^ 2 ≤
        Real.exp (-(ν / ε * t)) * ‖y 0 - h (x 0)‖ ^ 2 + (ε * G / ν) ^ 2 := by
    intro t ht
    exact fast_deviation_le_local_on (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
      (ν := ν) (G := G) (ε := ε) (δ := δ) (T := t) hν hε hh hzero hmono hGb x y hx hy hxK
      (fun s hs => htube s hs.1) t ⟨ht, le_rfl⟩
  -- the deviation never exceeds the larger of the initial deviation and the tracking-error scale
  have hbound : ∀ t, 0 ≤ t → ‖y t - h (x t)‖ ^ 2 ≤
      max (‖y 0 - h (x 0)‖ ^ 2) ((ε * G / ν) ^ 2) := by
    intro t ht
    have hshift := (hgron t ht).1
    have hexp0 : 0 ≤ Real.exp (-(ν / ε * t)) := (Real.exp_pos _).le
    have hexp1 : Real.exp (-(ν / ε * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hνε : 0 < ν / ε := div_pos hν hε
      nlinarith [ht]
    rcases le_total ‖y 0 - h (x 0)‖ (ε * G / ν) with hle | hle
    · -- the initial deviation is below the tracking-error scale
      have h1 : ‖y 0 - h (x 0)‖ ^ 2 ≤ (ε * G / ν) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hle
      have hnonpos : ‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2 ≤ 0 := by linarith [h1]
      have h2 : Real.exp (-(ν / ε * t)) *
          (‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hexp0 hnonpos
      have h3 : ‖y t - h (x t)‖ ^ 2 ≤ (ε * G / ν) ^ 2 := by linarith [hshift, h2]
      rw [max_eq_right h1]
      exact h3
    · -- the initial deviation is above the tracking-error scale
      have h1 : (ε * G / ν) ^ 2 ≤ ‖y 0 - h (x 0)‖ ^ 2 :=
        (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hle
      have h2 : Real.exp (-(ν / ε * t)) *
          (‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2) ≤
          ‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2 := by
        have hnonneg : 0 ≤ ‖y 0 - h (x 0)‖ ^ 2 - (ε * G / ν) ^ 2 := by linarith [h1]
        have := mul_le_mul_of_nonneg_right hexp1 hnonneg
        simpa using this
      have h3 : ‖y t - h (x t)‖ ^ 2 ≤ ‖y 0 - h (x 0)‖ ^ 2 := by linarith [hshift, h2]
      rw [max_eq_left h1]
      exact h3
  -- the maximum of the squares is the square of the maximum
  have hmaxsq : max (‖y 0 - h (x 0)‖ ^ 2) ((ε * G / ν) ^ 2)
      = (max ‖y 0 - h (x 0)‖ (ε * G / ν)) ^ 2 := by
    have hM : 0 ≤ max ‖y 0 - h (x 0)‖ (ε * G / ν) := by positivity
    apply le_antisymm
    · exact max_le ((sq_le_sq₀ (norm_nonneg _) hM).mpr (le_max_left _ _))
        ((sq_le_sq₀ (by positivity) hM).mpr (le_max_right _ _))
    · by_cases hc : max ‖y 0 - h (x 0)‖ (ε * G / ν) = ‖y 0 - h (x 0)‖
      · rw [hc]; exact le_max_left _ _
      · have hle : ‖y 0 - h (x 0)‖ ≤ ε * G / ν := by
          by_contra hcon
          exact hc (max_eq_left (le_of_not_ge hcon))
        rw [max_eq_right hle]
        exact le_max_right _ _
  refine ⟨htube, ?_, ?_⟩
  · intro t ht
    exact (hgron t ht).2
  · intro t ht
    have h1 : ‖y t - h (x t)‖ ^ 2 ≤
        (max ‖y 0 - h (x 0)‖ (ε * G / ν)) ^ 2 := by
      rw [← hmaxsq]
      exact hbound t ht
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1

/-! ## 5. The slow error of the reduced dynamics -/

section SlowError

/-- **The slow error of the reduced dynamics.** Let `ẋ = f (x, y)`, `ε ẏ = g (x, y)` be a
singularly perturbed system with the local slow manifold `y = h (x)`, and let `Z` be the solution of
the **reduced** system `Ż = f (Z, h Z)` started at `Z 0 = x 0`. Assume

* the hypotheses of `CRNT.tikhonov_local_tube` (in particular the tube radius dominates the
  tracking-error scale `ε G/ν`);
* `f` is Lipschitz in the fast variable with constant `L_f`:
  `‖f z u - f z v‖ ≤ L_f ‖u - v‖`;
* the **reduced** field is Lipschitz with constant `L`:
  `‖f z (h z) - f z' (h z')‖ ≤ L ‖z - z'‖`.

Then the slow variable of the coupled system stays within `O (ε)` of the reduced one:

```
‖x t - Z t‖ ≤ (L_f / L) * max (‖y 0 - h (x 0)‖, ε G/ν) * (e^{L t} - 1).
```

In particular, if the initial fast deviation is `O (ε)` then so is the slow error: the reduced
system approximates the slow motion, which is the classical conclusion of Tikhonov's theorem.

The proof is the standard comparison for the squared slow error `Q = ‖x - Z‖²`,
`Q' ≤ 2 L_f √Q w + 2 L Q` with `w = ‖y - h (x)‖` the fast deviation, read through the shifted
square root `Ψ = √(Q + κ)` (so that the square root is differentiable everywhere) and shifted
Grönwall; the final `κ → 0` limit removes the shift. -/
theorem tikhonov_local_slow_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {f : S → E → S} {g : S → E → E} {h : S → E}
    (Dh : S → (S →L[ℝ] E)) {Kx : Set S} {ν G ε δ : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hG : 0 ≤ G)
    (hh : ∀ z ∈ Kx, HasFDerivAt h (Dh z) z)
    (hzero : ∀ z ∈ Kx, g z (h z) = 0)
    (hmono : ∀ z ∈ Kx, ∀ u, dist u (h z) ≤ δ →
      ⟪g z u - g z (h z), u - h z⟫ ≤ -ν * ‖u - h z‖ ^ 2)
    (hGb : ∀ z ∈ Kx, ∀ u, ‖Dh z (f z u)‖ ≤ G)
    {Lf L : ℝ} (hLf : 0 ≤ Lf) (hL : 0 < L)
    (hlipy : ∀ z ∈ Kx, ∀ u v, ‖f z u - f z v‖ ≤ Lf * ‖u - v‖)
    (hlipred : ∀ z ∈ Kx, ∀ z' ∈ Kx, ‖f z (h z) - f z' (h z')‖ ≤ L * ‖z - z'‖)
    (x : ℝ → S) (y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (f (x t) (y t)) t)
    (hy : ∀ t, HasDerivAt y ((1 / ε) • g (x t) (y t)) t)
    (hxK : ∀ t, x t ∈ Kx)
    (Z : ℝ → S) (hZ : ∀ t, HasDerivAt Z (f (Z t) (h (Z t))) t)
    (hZK : ∀ t, Z t ∈ Kx)
    (hZ0 : Z 0 = x 0)
    (hinit : dist (y 0) (h (x 0)) < δ)
    (hsmall : ε * G / ν < δ) :
    ∀ t, 0 ≤ t → ‖x t - Z t‖ ≤
      (Lf / L) * max ‖y 0 - h (x 0)‖ (ε * G / ν) * (Real.exp (L * t) - 1) := by
  -- the tube, and the bound on the fast deviation
  have hdev := tikhonov_local_tube_deviation (f := f) (g := g) (h := h) (Dh := Dh) (Kx := Kx)
    (ν := ν) (G := G) (ε := ε) (δ := δ) hν hε hG hh hzero hmono hGb x y hx hy hxK hinit hsmall
  have hmaxdev : ∀ t, 0 ≤ t → ‖y t - h (x t)‖ ≤ max ‖y 0 - h (x 0)‖ (ε * G / ν) :=
    hdev.2.2
  set M : ℝ := max ‖y 0 - h (x 0)‖ (ε * G / ν) with hMdef
  have hM : 0 ≤ M := by positivity
  -- the slow error
  set d : ℝ → S := fun t => x t - Z t with hd
  have hdd : ∀ s, HasDerivAt d (f (x s) (y s) - f (Z s) (h (Z s))) s := by
    intro s
    exact (hx s).sub (hZ s)
  set Q : ℝ → ℝ := fun t => ‖d t‖ ^ 2 with hQ
  have hQs (s : ℝ) : Q s = ‖d s‖ ^ 2 := by simp only [hQ]
  have hQder : ∀ s, HasDerivAt Q
      (2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫) s := by
    intro s
    have h1 := (hdd s).norm_sq
    simpa [hQ] using h1
  have hQ0 : Q 0 = 0 := by
    have h1 : d 0 = 0 := by
      show x 0 - Z 0 = 0
      rw [hZ0]
      simp
    rw [hQs, h1]
    simp
  -- the comparison, for each shift `κ > 0`
  have hcmp : ∀ (κ : ℝ), 0 < κ → ∀ t, 0 ≤ t → ‖x t - Z t‖ ≤
      Real.sqrt κ * Real.exp (L * t) + (Lf / L) * M * (Real.exp (L * t) - 1) := by
    intro κ hκ t ht
    have hΨder : ∀ s, HasDerivAt (fun u => Real.sqrt (Q u + κ))
        ((2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫) / (2 * Real.sqrt (Q s + κ))) s := by
      intro s
      have h1 := (hQder s).add_const κ
      have h2 := h1.sqrt (by positivity : (Q s + κ) ≠ 0)
      simpa using h2
    -- the inner-product bound
    have hIP : ∀ s, 0 ≤ s → ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
        ≤ ‖d s‖ * (Lf * ‖y s - h (x s)‖ + L * ‖x s - Z s‖) := by
      intro s hs
      have hsplit : f (x s) (y s) - f (Z s) (h (Z s))
          = (f (x s) (y s) - f (x s) (h (x s))) + (f (x s) (h (x s)) - f (Z s) (h (Z s))) := by
        abel
      have h4 : ⟪d s, f (x s) (y s) - f (x s) (h (x s))⟫
          ≤ ‖d s‖ * ‖f (x s) (y s) - f (x s) (h (x s))‖ := real_inner_le_norm _ _
      have h5 : ⟪d s, f (x s) (h (x s)) - f (Z s) (h (Z s))⟫
          ≤ ‖d s‖ * ‖f (x s) (h (x s)) - f (Z s) (h (Z s))‖ := real_inner_le_norm _ _
      have h6 : ‖f (x s) (y s) - f (x s) (h (x s))‖ ≤ Lf * ‖y s - h (x s)‖ :=
        hlipy (x s) (hxK s) (y s) (h (x s))
      have h7 : ‖f (x s) (h (x s)) - f (Z s) (h (Z s))‖ ≤ L * ‖x s - Z s‖ :=
        hlipred (x s) (hxK s) (Z s) (hZK s)
      calc ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
          = ⟪d s, f (x s) (y s) - f (x s) (h (x s))⟫
              + ⟪d s, f (x s) (h (x s)) - f (Z s) (h (Z s))⟫ := by
              rw [hsplit, inner_add_right]
        _ ≤ ‖d s‖ * ‖f (x s) (y s) - f (x s) (h (x s))‖
              + ‖d s‖ * ‖f (x s) (h (x s)) - f (Z s) (h (Z s))‖ := add_le_add h4 h5
        _ = ‖d s‖ * (‖f (x s) (y s) - f (x s) (h (x s))‖
              + ‖f (x s) (h (x s)) - f (Z s) (h (Z s))‖) := by ring
        _ ≤ ‖d s‖ * (Lf * ‖y s - h (x s)‖ + L * ‖x s - Z s‖) := by
            apply mul_le_mul_of_nonneg_left
            · exact add_le_add h6 h7
            · exact norm_nonneg (d s)
    -- the differential inequality for `Ψ = √(Q + κ)`
    have hΨbound : ∀ s, 0 ≤ s →
        (2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫) / (2 * Real.sqrt (Q s + κ))
          ≤ L * (Real.sqrt (Q s + κ) + (Lf / L) * M) := by
      intro s hs
      have hw : ‖y s - h (x s)‖ ≤ M := hmaxdev s hs
      have hA : Lf * ‖y s - h (x s)‖ ≤ Lf * M := mul_le_mul_of_nonneg_left hw hLf
      have hB : Lf * ‖y s - h (x s)‖ + L * ‖x s - Z s‖ ≤ Lf * M + L * ‖d s‖ := by
        have h6 : ‖x s - Z s‖ = ‖d s‖ := by simp only [hd]
        linarith [hA]
      have hC : 2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
          ≤ 2 * (‖d s‖ * (Lf * M + L * ‖d s‖)) := by
        have h7 := hIP s hs
        have h8 : 2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
            ≤ 2 * (‖d s‖ * (Lf * ‖y s - h (x s)‖ + L * ‖x s - Z s‖)) :=
          mul_le_mul_of_nonneg_left h7 (by norm_num)
        have h9 : 2 * (‖d s‖ * (Lf * ‖y s - h (x s)‖ + L * ‖x s - Z s‖))
            ≤ 2 * (‖d s‖ * (Lf * M + L * ‖d s‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hB (norm_nonneg (d s))) (by norm_num)
        exact le_trans h8 h9
      have hD : ‖d s‖ ≤ Real.sqrt (Q s + κ) := by
        have h9 : ‖d s‖ ^ 2 ≤ (Real.sqrt (Q s + κ)) ^ 2 := by
          rw [← hQs s]
          have := Real.sq_sqrt (by positivity : 0 ≤ Q s + κ)
          linarith [hκ]
        exact (sq_le_sq₀ (norm_nonneg (d s)) (Real.sqrt_nonneg _)).mp h9
      have hE : Q s ≤ (Real.sqrt (Q s + κ)) ^ 2 := by
        have := Real.sq_sqrt (by positivity : 0 ≤ Q s + κ)
        linarith
      have hF : 2 * (‖d s‖ * (Lf * M + L * ‖d s‖))
          ≤ 2 * (Lf * M) * Real.sqrt (Q s + κ) + 2 * L * Q s := by
        calc 2 * (‖d s‖ * (Lf * M + L * ‖d s‖))
            = 2 * (Lf * M) * ‖d s‖ + 2 * L * ‖d s‖ ^ 2 := by ring
          _ ≤ 2 * (Lf * M) * Real.sqrt (Q s + κ) + 2 * L * ‖d s‖ ^ 2 := by
              have h16 : 2 * (Lf * M) * ‖d s‖ ≤ 2 * (Lf * M) * Real.sqrt (Q s + κ) :=
                mul_le_mul_of_nonneg_left hD (by positivity)
              linarith
          _ = 2 * (Lf * M) * Real.sqrt (Q s + κ) + 2 * L * Q s := by rw [← hQs s]
      have hG : (2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫)
          / (2 * Real.sqrt (Q s + κ)) ≤ Lf * M + L * Real.sqrt (Q s + κ) := by
        have h10 : 2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
            ≤ 2 * Real.sqrt (Q s + κ) * (Lf * M + L * Real.sqrt (Q s + κ)) := by
          have h11 := hC
          have h12 : 2 * (Lf * M) * Real.sqrt (Q s + κ) + 2 * L * Q s
              ≤ 2 * Real.sqrt (Q s + κ) * (Lf * M + L * Real.sqrt (Q s + κ)) := by
            have h13 : Q s ≤ (Real.sqrt (Q s + κ)) ^ 2 := hE
            have h14 : 2 * L * Q s ≤ 2 * L * ((Real.sqrt (Q s + κ)) ^ 2) :=
              mul_le_mul_of_nonneg_left h13 (by positivity)
            linarith
          calc 2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
              ≤ 2 * (‖d s‖ * (Lf * M + L * ‖d s‖)) := h11
            _ ≤ 2 * Real.sqrt (Q s + κ) * (Lf * M + L * Real.sqrt (Q s + κ)) := by
                have h15 := hF
                linarith
        rw [div_le_iff₀ (by positivity)]
        have h16 : 2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫
            ≤ (Lf * M + L * Real.sqrt (Q s + κ)) * (2 * Real.sqrt (Q s + κ)) := by
          have := h10
          (convert this using 1; ring)
        exact h16
      have h21 : Lf * M + L * Real.sqrt (Q s + κ)
          = L * (Real.sqrt (Q s + κ) + (Lf / L) * M) := by
        have h22 : L * ((Lf / L) * M) = Lf * M := by
          rw [div_eq_mul_inv]
          calc L * (Lf * L⁻¹ * M) = (L * L⁻¹) * (Lf * M) := by ac_rfl
            _ = 1 * (Lf * M) := by rw [mul_inv_cancel₀ (ne_of_gt hL)]
            _ = Lf * M := by ring
        calc Lf * M + L * Real.sqrt (Q s + κ)
            = L * Real.sqrt (Q s + κ) + L * ((Lf / L) * M) := by rw [h22]; ring
          _ = L * (Real.sqrt (Q s + κ) + (Lf / L) * M) := by ring
      linarith [hG, h21]
    -- Grönwall on the shifted quantity `Ψ + L_f M / L`
    have hVder : ∀ s, HasDerivAt (fun u => Real.sqrt (Q u + κ) + (Lf / L) * M)
        ((2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫) / (2 * Real.sqrt (Q s + κ))) s := by
      intro s
      have h1 := (hΨder s).add_const ((Lf / L) * M)
      simpa using h1
    have hVbound : ∀ s ∈ Ico 0 t,
        (2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫) / (2 * Real.sqrt (Q s + κ))
          ≤ L * (Real.sqrt (Q s + κ) + (Lf / L) * M) := by
      intro s hs
      exact hΨbound s hs.1
    have hgron := CRNT.ExponentialDecay.le_mul_exp_of_deriv_le
      (V := fun u => Real.sqrt (Q u + κ) + (Lf / L) * M)
      (V' := fun s => (2 * ⟪d s, f (x s) (y s) - f (Z s) (h (Z s))⟫)
          / (2 * Real.sqrt (Q s + κ)))
      (K := L) (b := t) hVder hVbound t ⟨ht, le_rfl⟩
    -- unpack
    have hV0 : Real.sqrt (Q 0 + κ) + (Lf / L) * M = Real.sqrt κ + (Lf / L) * M := by
      simp [hQ0]
    have hmain : ‖x t - Z t‖ ≤
        Real.sqrt κ * Real.exp (L * t) + (Lf / L) * M * (Real.exp (L * t) - 1) := by
      have h1 : ‖x t - Z t‖ ≤ Real.sqrt (Q t + κ) := by
        have heq : ‖x t - Z t‖ = Real.sqrt (Q t) := by
          have h1 : Q t = ‖x t - Z t‖ ^ 2 := by
            rw [hQs]
          rw [h1]
          exact (Real.sqrt_sq (norm_nonneg (x t - Z t))).symm
        rw [heq]
        exact Real.sqrt_le_sqrt (by linarith [hκ])
      have h2 : Real.sqrt (Q t + κ) ≤ Real.sqrt κ * Real.exp (L * t)
          + (Lf / L) * M * (Real.exp (L * t) - 1) := by
        have h3 := hgron
        rw [hV0] at h3
        have h4 : (Real.sqrt κ + (Lf / L) * M) * Real.exp (L * t)
            = Real.sqrt κ * Real.exp (L * t) + (Lf / L) * M * Real.exp (L * t) := by ring
        rw [h4] at h3
        linarith
      linarith
    exact hmain
  -- the shift `κ → 0`
  intro t ht
  by_contra hcon
  have hα : 0 < ‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1) := by linarith
  have hE : 0 < Real.exp (L * t) := Real.exp_pos _
  set κ : ℝ := ((‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1))
      / (2 * Real.exp (L * t))) ^ 2 with hκdef
  have hκ : 0 < κ := by
    simp only [hκdef]
    positivity
  have h1 := hcmp κ hκ t ht
  have hsqrt : Real.sqrt κ
      = (‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1)) / (2 * Real.exp (L * t)) := by
    rw [hκdef, Real.sqrt_sq (by positivity)]
  rw [hsqrt] at h1
  have h2 : (‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1)) / (2 * Real.exp (L * t))
      * Real.exp (L * t) + (Lf / L) * M * (Real.exp (L * t) - 1) < ‖x t - Z t‖ := by
    have h3 : 0 < ‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1) := hα
    have h4 : (‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1))
        / (2 * Real.exp (L * t)) * Real.exp (L * t)
        = (‖x t - Z t‖ - (Lf / L) * M * (Real.exp (L * t) - 1)) / 2 := by
      field_simp
    rw [h4]
    linarith
  linarith

end SlowError

end

end CRNT
