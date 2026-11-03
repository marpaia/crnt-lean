import CRNT.Dynamics.PersistenceConfined
import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# Discharging the box hypothesis of confined siphon-face invariance

`Network.siphonFace_forwardInvariant_confined` keeps a nonnegative mass-action integral curve
on the face `SiphonFace P` of a siphon `P` provided the orbit is confined to a box `[0,B]^S`
for all forward time (`hbox`). That confinement hypothesis is the residual analytic input. This
module discharges it from **relative-entropy confinement** against a positive reference, using
no infrastructure beyond the coercivity estimate `relEntropy_coord_le`, and lands an
unconditional-on-box siphon-face invariance theorem for orbits whose relative entropy is
controlled.

## The mechanism

Coercivity (`relEntropy_coord_le`) turns a relative-entropy bound into a coordinate bound: for a
nonnegative `x` with `relEntropy x* x ≤ C` and positive reference `x*`,

```
x s ≤ max (e² · x*_s) C  ≤  uniformBox x* C
```

where `uniformBox x* C := max (∑_s e² · x*_s) C` is a single `s`-free box radius. So any orbit
along which the relative entropy stays `≤ C` is automatically confined to `[0, uniformBox x* C]^S`,
which is exactly the `hbox` that `siphonFace_forwardInvariant_confined` consumes.

## Two ways the relative-entropy bound arises

* **As a supplied certificate** (`siphonFace_forwardInvariant_of_relEntropy_le`): the bound
  `relEntropy x* (γ t) ≤ C` is a hypothesis. This is the clean, fully general statement — it
  applies verbatim to the cutoff-orbit relative-entropy bound `orbit_relEntropy_le` produced in
  the asymptotic-stability development.

* **From Lyapunov descent** (`siphonFace_forwardInvariant_of_complexBalanced`): for a *positive*
  genuine orbit with a complex-balanced reference, `relEntropy_antitone_along_solution` gives the
  bound with `C = relEntropy x* (γ 0)` for free, yielding an unconditional (no `hbox`, no `hrele`)
  siphon-face invariance theorem.

  Lyapunov descent is available only where the orbit is positive (the relative
  entropy is differentiable only in the open orthant), so `siphonFace_forwardInvariant_of_complexBalanced`
  carries a positivity hypothesis on the orbit. A genuinely *face-confined* orbit is by definition
  not positive (it vanishes on `P`), so the two regimes do not overlap: a self-contained theorem
  combining face confinement with a complex-balanced reference and no positivity input would need
  the relative-entropy descent extended to the boundary, or a separate boundary-face dissipation
  certificate — neither present here. The general `_of_relEntropy_le` form is the central
  export: it discharges `hbox` from any relative-entropy bound, however that bound is obtained
  (cutoff-orbit `orbit_relEntropy_le`, or genuine-orbit descent), which is the persistence input
  that feeds GAC.

## Main results

* `Network.uniformBox`: an `s`-free box radius dominating every coercivity bound of a sublevel.
* `Network.coord_le_uniformBox`: coercivity packaged as the uniform coordinate bound.
* `Network.siphonFace_forwardInvariant_of_relEntropy_le`: siphon-face forward-invariance for a
  nonnegative orbit whose relative entropy stays `≤ C`, with `hbox` discharged internally.
* `Network.siphonFace_forwardInvariant_of_complexBalanced`: the same for a positive genuine orbit
  with a complex-balanced reference, with the relative-entropy bound supplied by Lyapunov descent.

Depends on: `CRNT.Dynamics.PersistenceConfined`,
`CRNT.Theorems.DeficiencyZero.AsymptoticStability`.
-/

open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **An `s`-free box radius for a relative-entropy sublevel set.** Coercivity bounds the `s`-th
coordinate of a sublevel-`C` point by `max (e²·x*_s) C`; summing the reference contributions
over all species gives the single, coordinate-independent radius `max (∑_s e²·x*_s) C` that
dominates every per-coordinate coercivity bound. -/
noncomputable def uniformBox (xstar : Concentration S) (C : ℝ) : ℝ :=
  max (∑ s, Real.exp 2 * xstar s) C

omit [DecidableEq S] in
/-- `0 ≤ uniformBox x* C` whenever the reference is positive. -/
theorem uniformBox_nonneg {xstar : Concentration S} (hxs : xstar.Positive) (C : ℝ) :
    0 ≤ uniformBox xstar C :=
  le_trans (Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le)
    (le_max_left _ _)

omit [DecidableEq S] in
/-- **Coercivity as a uniform coordinate bound.** A nonnegative point of the relative-entropy
sublevel `{relEntropy x* · ≤ C}` has every coordinate bounded by the `s`-free radius
`uniformBox x* C`. This packages `relEntropy_coord_le` so its bound no longer depends on the
species `s`, which is the shape the box hypothesis `hbox` of `siphonFace_forwardInvariant_confined`
demands. -/
theorem coord_le_uniformBox {xstar x : Concentration S} (hxs : xstar.Positive)
    (hx : x.Nonnegative) {C : ℝ} (h : relEntropy xstar x ≤ C) (s : S) :
    x s ≤ uniformBox xstar C := by
  refine le_trans (relEntropy_coord_le hxs hx h s) (max_le_max ?_ (le_refl C))
  exact Finset.single_le_sum
    (f := fun s' => Real.exp 2 * xstar s') (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le)
    (Finset.mem_univ s)

/-- **Confined siphon-face invariance from a relative-entropy bound.** A nonnegative mass-action
integral curve `γ` starting on `SiphonFace P` of a siphon `P`, along which the relative entropy
to a positive reference `x*` stays `≤ C` for all forward time, stays on `SiphonFace P` for all
forward time.

The box hypothesis of `siphonFace_forwardInvariant_confined` is discharged here: coercivity
(`coord_le_uniformBox`) turns the relative-entropy bound `hrele` into the uniform coordinate
bound `γ t s ≤ uniformBox x* C`, supplying `hbox` with `B = uniformBox x* C`. No box confinement
is assumed — only control of the Lyapunov functional. -/
theorem siphonFace_forwardInvariant_of_relEntropy_le_forward (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {C : ℝ}
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ C)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_confined_forward κ hP (B := uniformBox xstar C) hderiv hnn
    (fun t ht s => coord_le_uniformBox hxs (hnn t ht) (hrele t ht) s) h0

/-- Relative-entropy-confined siphon-face invariance for a solution defined at every real time. -/
theorem siphonFace_forwardInvariant_of_relEntropy_le (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    {γ : ℝ → Concentration S} {C : ℝ}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ C)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
  N.siphonFace_forwardInvariant_of_relEntropy_le_forward κ hP hxs
    (fun t _ => hderiv t) hnn hrele h0

/-- **Unconditional confined siphon-face invariance for a positive complex-balanced orbit.** A
*positive* genuine mass-action integral curve `γ` with a positive complex-balanced reference
`x*`, starting on `SiphonFace P` of a siphon `P`, stays on `SiphonFace P` for all forward time —
with neither a box hypothesis nor a relative-entropy bound assumed.

The relative-entropy bound `relEntropy x* (γ t) ≤ relEntropy x* (γ 0)` is supplied by Lyapunov
descent (`relEntropy_antitone_along_solution`), which holds because `x*` is complex-balanced; the
resulting bound discharges the box hypothesis via `siphonFace_forwardInvariant_of_relEntropy_le`.

The positivity hypothesis `hpos` is irreducible here: the relative entropy is differentiable only
in the open orthant, so Lyapunov descent is unavailable on the boundary. -/
theorem siphonFace_forwardInvariant_of_complexBalanced (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hpos : ∀ t, (γ t).Positive)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P := by
  have hanti : Antitone (fun t => relEntropy xstar (γ t)) :=
    relEntropy_antitone_along_solution N κ hxs hcb hpos
      (fun t s => (hasDerivAt_pi.mp (hderiv t)) s)
  exact N.siphonFace_forwardInvariant_of_relEntropy_le κ hP hxs (C := relEntropy xstar (γ 0))
    hderiv (fun t _ => (hpos t).nonnegative) (fun t ht => hanti ht) h0

end Network

end CRNT
