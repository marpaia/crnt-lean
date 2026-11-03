import CRNT.Dynamics.ConfinedInvariance

/-!
# Relative-entropy descent for orbits positive on the open forward ray

`relEntropy_antitone_along_solution` proves Lyapunov descent of `t ↦ relEntropy x* (γ t)`
along a mass-action solution that is **strictly positive at every time**, because the chain
rule `relEntropy_hasDerivAt` is available only in the open orthant. That positivity-everywhere
hypothesis is stronger than the descent conclusion needs: the derivative is only used on the
*interior* of the time interval, while the endpoint contributes through continuity alone, and
`relEntropy` is continuous on the whole closed orthant (`relEntropy_continuous`).

This module relaxes the time-zero positivity. It proves descent for an orbit that is positive
only on the **open** ray `(0, ∞)`, allowing the orbit to sit on the boundary at `t = 0`:

```
relEntropy x* (γ t) ≤ relEntropy x* (γ 0)   for all t ≥ 0,
```

obtained by `antitoneOn_of_deriv_nonpos` on each `Icc 0 b`, taking continuity at the endpoint
from `relEntropy_continuous` and the nonpositive derivative on the open interval from
`relEntropy_hasDerivAt` + `dissipation_nonpos`. Feeding the resulting bound into
`siphonFace_forwardInvariant_of_relEntropy_le` yields a siphon-face invariance theorem whose
positivity hypothesis is weakened from positive-everywhere to positive-on-`(0,∞)`.

## Scope

This does **not** cover a genuinely face-confined orbit (one that vanishes on the siphon `P`,
hence is not positive, at *all* times including positive `t`). Along such an orbit `relEntropy`
is never differentiable, so no descent follows from the chain rule; establishing descent there
would need a boundary dissipation certificate or an interior-approximation/continuous-dependence
argument (solutions through nearby interior points), neither of which is available here. The
relaxation delivered is exactly: the orbit may touch the boundary at the initial instant `t = 0`
but must be interior thereafter. A single theorem subsuming both the positive and the
face-confined regimes with no positivity input remains a strictly larger, open gap (full
Anderson persistence — interior orbits repelled from critical-siphon faces — needs Farkas/LP
feasibility and ω-limit theory absent from the library).

## Main results

* `Network.relEntropy_antitone_along_solution_of_pos_pos`: Lyapunov descent for an orbit
  positive on the open ray `(0, ∞)`.
* `Network.relEntropy_le_zero_along_solution_of_pos_pos`: the sublevel bound
  `relEntropy x* (γ t) ≤ relEntropy x* (γ 0)` for `t ≥ 0`, the form consumed downstream.
* `Network.siphonFace_forwardInvariant_of_complexBalanced_pos_pos`: siphon-face forward
  invariance for a complex-balanced-referenced orbit positive on `(0, ∞)`, with neither a box
  hypothesis, a relative-entropy bound, nor positivity at `t = 0` assumed.

Depends on: `CRNT.Dynamics.ConfinedInvariance`.
-/

open scoped BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Lyapunov descent under open-ray positivity.** Relative to a positive complex-balanced
reference `x*`, the relative entropy is antitone on `[0, ∞)` along a mass-action solution that
is strictly positive for every `t > 0` — positivity at `t = 0` is *not* required.

The derivative `d/dt relEntropy x* (γ t) = ∑_s (log γ_s − log x*_s)·γ'_s` is taken only on the
interior `(0, b)` of each `Icc 0 b`, where positivity holds, and is nonpositive by
`dissipation_nonpos`; continuity at the left endpoint `0` (the one boundary instant) comes from
`relEntropy_continuous`. So `antitoneOn_of_deriv_nonpos` yields antitonicity on every `Icc 0 b`,
hence on `Ici 0`. -/
theorem relEntropy_antitone_along_solution_of_pos_pos (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, 0 < t → (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    AntitoneOn (fun t => relEntropy xstar (γ t)) (Set.Ici 0) := by
  have hdiff : Differentiable ℝ γ := fun t => (hasDerivAt_pi.mpr (fun s => hsol t s)).differentiableAt
  have hhcont : Continuous (fun t => relEntropy xstar (γ t)) :=
    (relEntropy_continuous hxs).comp hdiff.continuous
  -- Antitonicity on each `Icc 0 b`; the global `Ici 0` claim then follows by membership.
  have hanti : ∀ b : ℝ, AntitoneOn (fun τ => relEntropy xstar (γ τ)) (Set.Icc 0 b) := by
    intro b
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) hhcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      have hchain : HasDerivAt (fun τ => relEntropy xstar (γ τ))
          (∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s) t :=
        relEntropy_hasDerivAt hxs (hpos t ht.1) (fun s => hsol t s)
      exact hchain.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      have hchain : HasDerivAt (fun τ => relEntropy xstar (γ τ))
          (∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s) t :=
        relEntropy_hasDerivAt hxs (hpos t ht.1) (fun s => hsol t s)
      rw [hchain.deriv]
      exact dissipation_nonpos N κ (hpos t ht.1) hxs hcb
  intro a ha c hc hac
  exact hanti c ⟨Set.mem_Ici.mp ha, hac⟩ ⟨Set.mem_Ici.mp hc, le_refl c⟩ hac

/-- **Sublevel descent bound under open-ray positivity.** For an orbit positive on `(0, ∞)` with
a positive complex-balanced reference, the relative entropy never exceeds its initial value:
`relEntropy x* (γ t) ≤ relEntropy x* (γ 0)` for all `t ≥ 0`. This is the
`siphonFace_forwardInvariant_of_relEntropy_le`-ready packaging of
`relEntropy_antitone_along_solution_of_pos_pos`. -/
theorem relEntropy_le_zero_along_solution_of_pos_pos (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hpos : ∀ t, 0 < t → (γ t).Positive)
    (hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ relEntropy xstar (γ 0) :=
  fun _ ht =>
    relEntropy_antitone_along_solution_of_pos_pos N κ hxs hcb hpos hsol
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-- **Siphon-face invariance for a complex-balanced orbit positive on the open ray.** A genuine
mass-action integral curve `γ` with a positive complex-balanced reference `x*`, starting on
`SiphonFace P` of a siphon `P` and strictly positive for every `t > 0`, stays on `SiphonFace P`
for all forward time — with no box hypothesis, no supplied relative-entropy bound, and *no
positivity assumption at `t = 0`*.

The Lyapunov bound `relEntropy x* (γ t) ≤ relEntropy x* (γ 0)` is supplied by
`relEntropy_le_zero_along_solution_of_pos_pos`, which holds because `x*` is complex-balanced; the
bound discharges the box hypothesis through `siphonFace_forwardInvariant_of_relEntropy_le`. The
nonnegativity input needed by that theorem at `t = 0` comes from `γ 0 ∈ SiphonFace P` being a
boundary point of the closed orthant; at positive times it is the positivity hypothesis. -/
theorem siphonFace_forwardInvariant_of_complexBalanced_pos_pos (N : Network S)
    (κ : N.RateConstants) {P : Finset S} (hP : N.IsSiphon P) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) {γ : ℝ → Concentration S}
    (hderiv : ∀ t, HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hpos : ∀ t, 0 < t → (γ t).Positive) (hnn0 : (γ 0).Nonnegative)
    (h0 : γ 0 ∈ N.SiphonFace P) :
    ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P := by
  have hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t :=
    fun t s => (hasDerivAt_pi.mp (hderiv t)) s
  have hnn : ∀ t, 0 ≤ t → (γ t).Nonnegative := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; exact hnn0
    · exact (hpos t h).nonnegative
  exact N.siphonFace_forwardInvariant_of_relEntropy_le_forward κ hP hxs
    (C := relEntropy xstar (γ 0)) (fun t _ => hderiv t) hnn
    (relEntropy_le_zero_along_solution_of_pos_pos N κ hxs hcb hpos hsol) h0

end Network

end CRNT
