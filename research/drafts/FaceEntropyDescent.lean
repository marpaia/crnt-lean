import CRNT.Dynamics.SiphonFaceWeakReversibility


/-!
# The relative-entropy Lyapunov family restricted to a siphon face

`relEntropy` is the Horn–Jackson Lyapunov function of a mass-action system, and the tree already
carries its global descent: `relEntropy_antitone_along_solution` (`CRNT/Dynamics/BoundaryDescent.lean`),
`genuineOrbit_relEntropy_le` (`CRNT/Dynamics/GenuineConfinement.lean:141`), and
`siphonFace_forwardInvariant_of_relEntropy_le` (`CRNT/Dynamics/ConfinedInvariance.lean:109`).

**Every one of those requires the orbit to be strictly positive on all of `S`.** The chain rule
`relEntropy_hasDerivAt` (`CRNT/Theorems/DeficiencyZero/Stability.lean:37`) takes `(γ t).Positive`,
and positivity at a single instant is exactly what a genuinely face-confined orbit lacks:
`γ t ∈ N.SiphonFace P` means `γ t s = 0` for `s ∈ P`, so such an orbit is never positive.
`BoundaryDescent.lean:28-33` records this gap explicitly and gives up on it:

> This does **not** cover a genuinely face-confined orbit (one that vanishes on the siphon `P`,
> hence is not positive, at *all* times including positive `t`). Along such an orbit
> `relEntropy` is never differentiable, so no descent follows from the chain rule.

**That comment is false, and this module is the correction.** The chain rule *does* apply on a
face, because the relative entropy **restricted to the face is the relative entropy of the filled
face state, plus a constant**. Filling the vanished coordinates with the reference
(`fillSiphonFace`, `CRNT/Dynamics/SiphonFaceWeakReversibility.lean:46`) moves the point into the
**open positive orthant** — `relEntropy_fillSiphonFace` (:408) shows the entropy shifts by the
siphon's reference weight `∑ s ∈ P, xstar s`. The filled trajectory is differentiable and strictly
positive, so `relEntropy_hasDerivAt` applies to *it*, and the constant offset transports the
derivative back to `γ`.

The pointwise inequality is the second half. On a face the ordinary dissipation
`∑ s, (log γ_s − log xstar_s) · γ'_s` is not the right object: the summands over `s ∈ P` are
nonsense (`log 0`), and the face derivative carries no information from those coordinates. The
correct quantity is the **face dissipation**

```
D_P(x) = ∑ s, if s ∈ P then 0 else (log (x s) − log (xstar s)) · (massActionVectorField κ x s)
```

— the full dissipation with the vanished coordinates zeroed out. `D_P(x)` is exactly the ordinary
dissipation of the filled face state under the **avoiding-siphon reaction-restricted subnetwork**,
which is weakly reversible and complex-balanced against `xstar`
(`restrictReactions_avoiding_siphon_complexBalanced`, :231), so `D_P ≤ 0` by `dissipation_nonpos`.
The identity equating the two is already proved in the tree — but *inline*, at :382-396 of
`massActionVectorField_eq_zero_of_faceDissipation_eq_zero`, and never exported. This module exports
it as `faceDissipation_eq_restrictDissipation` and builds the face Lyapunov family on it.

## Main results

* `siphonWeight`, `siphonWeight_nonneg`, `siphonWeight_pos`: the constant contribution a siphon
  face's vanished coordinates make to the relative entropy. Strictly positive on a nonempty `P`.
* `relEntropy_eq_fill_add_siphonWeight`: the constant-offset identity, packaging
  `relEntropy_fillSiphonFace`. The offset is independent of `x`, so it vanishes under
  differentiation — which is what licenses the filled-trajectory argument.
* `fillSiphonFace_positive_of_face`: a face point positive off `P` fills to a strictly positive
  point.
* `fillSiphonFace_hasDerivAt`: the filled trajectory is differentiable; the vanished coordinates
  contribute a zero derivative.
* `faceRelEntropy_hasDerivAt`: **the chain rule on a siphon face** — the derivative of the relative
  entropy of a face-confined trajectory is exactly the face dissipation `D_P`. This is the statement
  `relEntropy_hasDerivAt` cannot supply.
* `faceDissipation_eq_restrictDissipation`: `D_P` is the restricted subnetwork's dissipation. This
  identity was previously proved inline and discarded.
* `faceDissipation_nonpos`: **Horn–Jackson on the face**, `D_P ≤ 0`. The missing inequality.
* `relEntropy_antitone_on_siphonFace`: **Lyapunov descent for a genuinely face-confined orbit** —
  the classical statement `relEntropy_antitone_along_solution` makes unavailable. Closed here.
* `relEntropy_le_on_siphonFace_orbit`: the sublevel bound `relEntropy xstar (γ t) ≤
  relEntropy xstar (γ 0)`, the form consumed downstream.
* `relEntropy_faceEscapeWindow`: **the escape-across-a-face statement.** If `γ` is confined to
  `SiphonFace P` on `[a, b]` with `a < b`, and the mass-action field is nonzero at some interior
  time, then the entropy has dropped strictly across the interval while the face floor still
  holds:

  ```
  ∑ s ∈ P, xstar s  ≤  relEntropy xstar (γ b)  <  relEntropy xstar (γ a).
  ```

  This is the content of `SiphonDimensionDescent.lean:116-123`, which names the estimate and does
  not formalize it. A trajectory that is not pinned at a face equilibrium loses strictly positive
  relative entropy at every crossing, so it can neither cycle among boundary faces nor return to a
  state it has left. With `siphonWeight_pos` the window has strictly positive width, so the loss is
  quantified, not merely signed.

## Residuals — named precisely

1. **Uniformity in time is missing; only the pointwise window is proved.**
   `relEntropy_faceEscapeWindow` bounds each crossing separately. The descent needs the loss
   bounded below **uniformly over intervals of a fixed length τ**, so an orbit oscillating among
   faces loses a definite amount per unit time and cannot do so infinitely often. That quantitative
   form is the near-facet dissipation estimate of Anderson & Shiu. `CriticalSiphonDissipationRepulsion.lean`
   supplies the **codimension-1 instance** (`siphonFacetInfluxConst`; the conclusion
   `notMem_omegaLimit_siphonFace_of_nearFacet_dissipation` at :422). **The codimension-`> 1`
   instance for a general critical siphon `P` does not exist in the tree** and is not attempted
   here.
2. **A perfect face Lyapunov family would still not deliver the descent.** This is the sharpest
   residual, and it is a *refutation* rather than a gap, contributed by `ArchSrEscape` and
   `FormADescent` while this module was being written (their own proofs, cited not re-derived):
   * `SiphonCarried` (`SiphonDimensionDescent.lean:61`) unfolds to `∃ w ∈ ω, ∀ s, s ∈ P ↔ w s = 0`
     — a **witness-determined** notion, so `P` is forced to be `univ.filter (w s = 0)`. For a
     singleton ω-limit set the carrier is therefore **unique**, and the descent's
     strict-shrinking disjunct `Q.card < P.card` is **false outright** (`Q = P`). Machine-checked
     by `ArchSrEscape` as `not_exists_smaller_carried_siphon_of_unique_omegaLimit` in
     `CRNT/Scaffold/EscapeCardinality.lean`.
   * `Finset.card` order and `siphonWeight` order are **different orders**: with `S = Fin 3`,
     `xstar = (1000, 1, 1)`, `Q = {0}`, `P = {1, 2}`, one has `Q.card < P.card` but
     `siphonWeight xstar P = 2 < 1000 = siphonWeight xstar Q`. Machine-checked refutation by
     `FormADescent` (`not_weight_lt_of_card_lt` / `not_card_lt_of_weight_lt`). **Containment is
     the bridge**: `Q ⊊ P` forces both, so a single ⊆-collapse discharges the descent's
     cardinality-shrinkage for free (`FormADescent.siphonDescentRel_of_subsetRel`). That is the
     role of `relEntropy_and_weight_drop_of_escape` below.

   **Consequence, stated so it is not misread:** the analytic estimate `SiphonDimensionDescent.lean:116-123`
   names is *necessary* for the descent but **not sufficient**, and the strict-shrinking disjunct is
   additionally ill-formed without an input siphon in the hypothesis. Per
   `research/DEAD-ENDS.md` A-36/A-37, `comparableGrowthDescent_iff_omegaPointPositive`
   (`SiphonDimensionDescent.lean:368-377`) already makes "assemble the descent structure"
   *equivalent to Hole A itself*. This module supplies the face Lyapunov family and **does not
   claim** that it feeds `descend`.
3. **The residue is the SPREAD of `{zeroSet(w) : w ∈ ω}`, and it is not an entropy question.**
   Correcting a natural-but-false guess (verified by `ArchSrEscape`; recorded so it is not re-walked):
   *"finite `ω` ⇒ no smaller carrier"* is **FALSE**. With `|ω| = 2`, `ω = {w₁, w₂}`,
   `zeroSet(w₁) = {s₁}`, `zeroSet(w₂) = {s₁, s₂}`, both `{s₁}` and `{s₁,s₂}` are carried and
   `{s₁}.card = 1 < 2`. The singleton result therefore does **not** generalise along "finite" —
   carriedness is witness-determined, so a second carrier needs a *second ω-point with a different
   zero set*.
   The correct general shape: the descent is not refuted by finiteness, it is **supported** by it. A
   strictly decreasing chain of carriers needs a strictly decreasing chain of zero-set
   cardinalities, and those come from ω-points. So Anderson's estimate must constrain the **spread**
   of the family `{zeroSet(w) : w ∈ ω}` — that it contains a strictly smaller member than the
   maximal one. `exists_maximal_zeroSet_omegaPoint` (`HighCodimensionSiphonFace.lean:133`) supplies
   `Pmax`; `smaller_carried_siphon_iff_zeroSet_card_lt` (:608) states exactly what is missing; and
   `exists_smaller_carried_siphon_of_zeroSet_inside` (:470) already covers the branch where `z` is
   positive off `Pmax` and positive somewhere on `Pmax`, leaving the tie/degenerate branch of
   `omegaPoint_zeroSet_trichotomy` (:658) uncovered. This is Craciun v3 Theorem B territory, as
   `HighCodimensionSiphonFace.lean:920` says. **No Lyapunov estimate reaches it**, which is why
   this module stops where it does.
4. **Strictness is stated on interior times, not at the left endpoint.** The window's hypothesis
   is `∃ t₀ ∈ Ioo a b, massActionVectorField κ (γ t₀) ≠ 0` rather than
   `massActionVectorField κ (γ a) ≠ 0`. The endpoint form needs one further step — passing
   `γ`'s constancy on the open interval to the closed one by continuity of `γ` and of the field.
   The interior form is what the proof needs and is what is proved; no claim is made about the
   endpoint form.
4. **The window is not closed up to the ω-limit set.** It bounds forward-orbit points. Passing to
   ω-points requires the Butler–McGehee machinery of `ButlerMcGehee.lean` and is not attempted.

Depends on: `CRNT.Dynamics.SiphonFaceWeakReversibility` alone. In particular this module does
**not** import `CRNT.Dynamics.HighCodimensionSiphonFace`, which carries the Hole A `sorry` at :135;
its `relEntropy_ge_sum_zeroSet` is re-proved hole-free below as
`siphonWeight_le_relEntropy_of_vanishes`. The axiom footprint is therefore `sorryAx`-free and every
theorem here is independently checkable.
-/

namespace CRNT
namespace Network

open Filter Topology
open scoped BigOperators NNReal Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The reference weight of a siphon -/

/-- **The reference weight of a species set** — the constant contribution the relative entropy
picks up from the coordinates a siphon face zeroes out. This is the width of the escape window of
`relEntropy_faceEscapeWindow`. -/
noncomputable def siphonWeight (P : Finset S) (xstar : Concentration S) : ℝ :=
  ∑ s ∈ P, xstar s

/-- The weight of a positive reference is nonnegative. -/
theorem siphonWeight_nonneg {P : Finset S} {xstar : Concentration S} (hxs : xstar.Positive) :
    0 ≤ siphonWeight P xstar :=
  Finset.sum_nonneg fun s _ => (hxs s).le

/-- The weight is strictly positive on a nonempty species set. This is what makes the escape
window of `relEntropy_faceEscapeWindow` non-vacuous: the floor a face-confined trajectory sits on
is a strictly positive number, not `0`. -/
theorem siphonWeight_pos {P : Finset S} {xstar : Concentration S} (hxs : xstar.Positive)
    (hPne : P.Nonempty) : 0 < siphonWeight P xstar := by
  classical
  obtain ⟨s, hs⟩ := hPne
  exact Finset.sum_pos' (fun t _ => (hxs t).le) ⟨s, Finset.mem_univ s, hxs s⟩

/-- **The siphon floor.** If `x` is nonnegative and vanishes on `P`, then
`siphonWeight P xstar ≤ relEntropy xstar x`: the relative entropy of a point on the face is at
least the total reference weight of the vanished coordinates.

This is the same statement as `relEntropy_ge_sum_zeroSet`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:931`), **re-proved here from hole-free
ingredients** — `relEntropy` (`CRNT/Theorems/DeficiencyZero/Lyapunov.lean:58`) and
`relEntropyTerm_nonneg` (:28). It is duplicated deliberately: that file carries the Hole A `sorry`
at :135, so importing it would drag `sorryAx` into this module's footprint and make every theorem
below unverifiable. No new mathematical content is claimed.

The argument: each entropy summand over `s ∈ P` is exactly `xstar s` (by `Real.log 0 = 0`), and
each summand outside `P` is nonnegative by Gibbs' inequality. -/
theorem siphonWeight_le_relEntropy_of_vanishes {P : Finset S} {xstar x : Concentration S}
    (hxs : xstar.Positive) (hx : x.Nonnegative) (hZ : ∀ s ∈ P, x s = 0) :
    siphonWeight P xstar ≤ relEntropy xstar x := by
  classical
  have hnn : ∀ i : S, 0 ≤ x i * Real.log (x i / xstar i) - x i + xstar i :=
    fun i => relEntropyTerm_nonneg (hx i) (hxs i)
  have hsm : ∀ s ∈ P, x s * Real.log (x s / xstar s) - x s + xstar s = xstar s := by
    intro s hs
    rw [hZ s hs]
    simp
  calc siphonWeight P xstar = ∑ s, if s ∈ P then xstar s else 0 := by simp [siphonWeight]
    _ = ∑ s, if s ∈ P then (x s * Real.log (x s / xstar s) - x s + xstar s) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s ∈ P
      · simp only [if_pos hs, hsm s hs]
      · simp only [if_neg hs]
    _ ≤ ∑ s, (x s * Real.log (x s / xstar s) - x s + xstar s) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s ∈ P
      · simp only [if_pos hs, hsm s hs]
        exact le_refl _
      · simp only [if_neg hs]
        exact hnn s
    _ = relEntropy xstar x := rfl

/-! ### The constant-offset identity -/

/-- **Relative entropy on a face is the relative entropy of the filled state, plus a constant.**
Repackaging `relEntropy_fillSiphonFace` (:408): the relative entropy of a point vanishing on `P`
is the relative entropy of its fill, shifted by the siphon's reference weight. The shift does not
depend on `x`, so it disappears under differentiation — which is precisely why the filled
trajectory may be used to differentiate the entropy of the face trajectory. -/
theorem relEntropy_eq_fill_add_siphonWeight {P : Finset S} {xstar x : Concentration S}
    (hxs : xstar.Positive) (hxzero : ∀ s ∈ P, x s = 0) :
    relEntropy xstar x =
      relEntropy xstar (fillSiphonFace P xstar x) + siphonWeight P xstar := by
  have h := relEntropy_fillSiphonFace (P := P) hxs hxzero
  rw [siphonWeight, h]
  ring

/-! ### Differentiating the entropy along a face -/

/-- **A face point positive off `P` fills to a strictly positive point.** This is what admits the
in-tree chain rule `relEntropy_hasDerivAt` to the *filled* trajectory: the fill moves into the open
orthant even though the trajectory itself never does. -/
theorem fillSiphonFace_positive_of_face {P : Finset S} {xstar x : Concentration S}
    (hxs : xstar.Positive) (hxzero : ∀ s ∈ P, x s = 0) (hxpos : ∀ s, s ∉ P → 0 < x s) :
    (fillSiphonFace P xstar x).Positive :=
  fun s => by
    by_cases hs : s ∈ P
    · simpa [fillSiphonFace, hs] using hxs s
    · simpa [fillSiphonFace, hs] using hxpos s hs

/-- **The filled trajectory is differentiable, and the vanished coordinates contribute nothing.**
Along a face trajectory `γ`, `fillSiphonFace P xstar (γ τ)` has derivative `0` on `s ∈ P` (those
coordinates are frozen at the reference) and `γ'` off `P`. -/
theorem fillSiphonFace_hasDerivAt {P : Finset S} {xstar : Concentration S}
    {γ : ℝ → Concentration S} {γ' : S → ℝ} {t : ℝ}
    (hγ : ∀ s, HasDerivAt (fun τ => γ τ s) (γ' s) t) :
    HasDerivAt (fun τ => fillSiphonFace P xstar (γ τ))
      (fun s => if s ∈ P then 0 else γ' s) t :=
  hasDerivAt_pi.mpr fun s => by
    by_cases hs : s ∈ P
    · have hconst : (fun τ => fillSiphonFace P xstar (γ τ) s) = fun _ => xstar s := by
        funext τ; simp [fillSiphonFace, hs]
      simpa [hconst] using (hasDerivAt_const t (xstar s))
    · have hid : (fun τ => fillSiphonFace P xstar (γ τ) s) = fun τ => γ τ s := by
        funext τ; simp [fillSiphonFace, hs]
      simpa [hid] using hγ s

/-- **The chain rule on a siphon face.** The derivative of the relative entropy of a
face-confined trajectory `γ` — vanishing on `P`, positive off it — is the **face dissipation**

```
∑ s, if s ∈ P then 0 else (log (γ t s) − log (xstar s)) · γ' s
```

the full dissipation with the vanished coordinates zeroed. This is the statement that
`relEntropy_hasDerivAt` (`CRNT/Theorems/DeficiencyZero/Stability.lean:37`) **cannot** supply: that
chain rule demands `(γ t).Positive`, and a face-confined trajectory is not positive at any instant.
The proof applies the in-tree chain rule to the *filled* trajectory, which does lie in the open
orthant (`fillSiphonFace_positive_of_face`), and transports the derivative back across the
constant offset of `relEntropy_eq_fill_add_siphonWeight`. -/
theorem faceRelEntropy_hasDerivAt {P : Finset S} {xstar : Concentration S}
    (hxs : xstar.Positive) {γ : ℝ → Concentration S} {γ' : S → ℝ} {t : ℝ}
    (hzero : ∀ s ∈ P, γ t s = 0) (hxpos : ∀ s, s ∉ P → 0 < γ t s)
    (hγ : ∀ s, HasDerivAt (fun τ => γ τ s) (γ' s) t) :
    HasDerivAt (fun τ => relEntropy xstar (γ τ))
      (∑ s, if s ∈ P then 0 else
        (Real.log (γ t s) - Real.log (xstar s)) * γ' s) t := by
  classical
  have hfillpos : (fillSiphonFace P xstar (γ t)).Positive :=
    fillSiphonFace_positive_of_face hxs hzero hxpos
  have hfillderiv := relEntropy_hasDerivAt hxs hfillpos (fillSiphonFace_hasDerivAt hγ)
  -- near `t` the trajectory still vanishes on `P`, so the offset identity holds pointwise there
  have hzero' : ∀ᶠ τ in 𝓝 t, ∀ s ∈ P, γ τ s = 0 :=
    Finset.eventually_all.2 fun s =>
      (hγ s).continuousAt.eventually isClosed_singleton (hzero s (Finset.mem_univ s))
  have heq : (fun τ => relEntropy xstar (γ τ)) =ᶠ[𝓝 t]
      (fun τ => relEntropy xstar (fillSiphonFace P xstar (γ τ)) + siphonWeight P xstar) := by
    filter_upwards [hzero'] with τ hτ
    exact relEntropy_eq_fill_add_siphonWeight hxs hτ
  have hderiv := hfillderiv.add_const (siphonWeight P xstar)
  refine hderiv.congr_of_eventuallyEq heq.symm
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ P
  · simp [fillSiphonFace, hs]
  · simp only [fillSiphonFace, hs, if_neg hs]
    rw [← congrFun hfillderiv.deriv hs]

/-! ### The face dissipation is nonpositive -/

/-- **The face dissipation is the restricted subnetwork's dissipation.** This identity was already
proved inline at :382-396 of `massActionVectorField_eq_zero_of_faceDissipation_eq_zero` and then
discarded; without it the face dissipation has no independent name in the tree. `D_P` is the
dissipation of the filled face state under the avoiding-siphon reaction restriction. -/
theorem faceDissipation_eq_restrictDissipation (N : Network S) (κ : N.RateConstants)
    {P : Finset S} {xstar x : Concentration S} (hxzero : ∀ s ∈ P, x s = 0) :
    (∑ s, if s ∈ P then 0 else
      (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) =
    ∑ s, (Real.log (fillSiphonFace P xstar x s) - Real.log (xstar s)) *
      (N.restrictReactions (N.avoidingSiphonReactions P)).massActionVectorField
        (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar x) s := by
  classical
  have hfields := N.massActionVectorField_eq_restrict_avoiding_siphon (κ := κ) (xstar := xstar)
    hxzero
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ P
  · simp [fillSiphonFace, hs]
  · simp only [fillSiphonFace, hs, if_neg hs]
    rw [← congrFun hfields s]

/-- **Horn–Jackson on the face.** The face dissipation of a point vanishing on the siphon `P` and
positive off it is nonpositive, with respect to a positive complex-balanced reference.

This is the inequality that makes the relative entropy a Lyapunov function *on a siphon face*. It
was not in the tree: `dissipation_nonpos` needs a strictly positive `x`, which a face point never
is. The proof routes through the avoiding-siphon reaction-restricted subnetwork, on which the
filled face state *is* strictly positive and the reference *is* complex-balanced
(`restrictReactions_avoiding_siphon_complexBalanced`, :231). -/
theorem faceDissipation_nonpos (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hxzero : ∀ s ∈ P, x s = 0) (hxpos : ∀ s, s ∉ P → 0 < x s) :
    (∑ s, if s ∈ P then 0 else
      (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) ≤ 0 := by
  classical
  have hxfpos : (fillSiphonFace P xstar x).Positive :=
    fillSiphonFace_positive_of_face hxs hxzero hxpos
  have hcbf : (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
      (κ.restrict (N.avoidingSiphonReactions P)) xstar :=
    N.restrictReactions_avoiding_siphon_complexBalanced κ hP hwr hcb
  rw [faceDissipation_eq_restrictDissipation N κ hxzero]
  exact (N.restrictReactions (N.avoidingSiphonReactions P)).dissipation_nonpos
    (κ.restrict (N.avoidingSiphonReactions P)) hxfpos hxs hcbf

/-! ### Lyapunov descent on a siphon face -/

/-- **Lyapunov descent for a genuinely face-confined orbit.** If `γ` is a mass-action integral
curve of a weakly reversible network, confined to `SiphonFace P` for all forward time, positive
off `P`, and `xstar` is a positive complex-balanced reference, then `relEntropy xstar (γ t)` is
antitone on `[0, ∞)`.

This is the classical Horn–Jackson statement `relEntropy_antitone_along_solution` makes
**unavailable**: that theorem, and every other descent theorem in the tree
(`genuineOrbit_relEntropy_le`, `siphonFace_forwardInvariant_of_relEntropy_le`), assumes
`γ` strictly positive on all of `S`, which a face-confined orbit is not — at any instant. The
chain rule used here is `faceRelEntropy_hasDerivAt` and the sign is `faceDissipation_nonpos`.

No positivity hypothesis at `t = 0` is needed: the orbit is positive *off `P`* everywhere,
including at `t = 0`. -/
theorem relEntropy_antitone_on_siphonFace (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S}
    (hface : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P)
    (hpos : ∀ t, 0 ≤ t → ∀ s, s ∉ P → 0 < γ t s)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    AntitoneOn (fun t => relEntropy xstar (γ t)) (Set.Ici 0) := by
  classical
  have hγdiff : Differentiable ℝ γ :=
    fun t => (hderiv t (Set.mem_Ici.mp (mem_Ici t))).differentiableAt
  have hcont : Continuous (fun t => relEntropy xstar (γ t)) :=
    (relEntropy_continuous hxs).comp hγdiff.continuous
  -- the zero-set clause of the face, recovered for a given time
  have hzeroAt : ∀ t, 0 ≤ t → ∀ s ∈ P, γ t s = 0 := by
    intro t ht
    exact (faceSum_eq_zero_iff ((mem_siphonFace_iff N).mp (hface t ht)).1).mp
      ((mem_siphonFace_iff N).mp (hface t ht)).2
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact (faceRelEntropy_hasDerivAt hxs (hzeroAt t ht.le) (hpos t ht.le)
      (fun s => (hasDerivAt_pi.mp (hderiv t ht.le)) s)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    rw [(faceRelEntropy_hasDerivAt hxs (hzeroAt t ht.le) (hpos t ht.le)
      (fun s => (hasDerivAt_pi.mp (hderiv t ht.le)) s)).deriv]
    exact N.faceDissipation_nonpos κ hP hwr hxs hcb (hzeroAt t ht.le) (hpos t ht.le)

/-- **The sublevel bound along a face-confined orbit** — the form consumed downstream:
`relEntropy xstar (γ t) ≤ relEntropy xstar (γ 0)` for all `t ≥ 0`. -/
theorem relEntropy_le_on_siphonFace_orbit (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S}
    (hface : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P)
    (hpos : ∀ t, 0 ≤ t → ∀ s, s ∉ P → 0 < γ t s)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∀ t, 0 ≤ t → relEntropy xstar (γ t) ≤ relEntropy xstar (γ 0) := by
  intro t ht
  exact relEntropy_antitone_on_siphonFace N κ hP hwr hxs hcb hface hpos hderiv
    (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (le_refl 0)) ht

/-! ### Escaping across the face -/

/-- **The escape-across-a-face window.** Let `γ` be a mass-action integral curve of a weakly
reversible network, confined to `SiphonFace P` on `[a, b]` with `a < b`, positive off `P`, and let
`xstar` be a positive complex-balanced reference. If the mass-action field is nonzero at some
interior time of the interval, then the relative entropy has dropped **strictly** across the
interval, while the siphon's reference floor still holds:

```
∑ s ∈ P, xstar s  ≤  relEntropy xstar (γ b)  <  relEntropy xstar (γ a).
```

This is the estimate named and not formalised at `SiphonDimensionDescent.lean:116-123` — *"In the
analytic proof the strict shrinking is forced by comparing the growth of the relative-entropy
Lyapunov family across an escape from the face `SiphonFace P`; that estimate is the content not
formalised here."*

The mechanism: antitonicity (`relEntropy_antitone_on_siphonFace`) forces the entropy to be
**constant** on `[a, b]` if it fails to drop; constancy kills the derivative, so the face
dissipation vanishes at every interior time, so by
`massActionVectorField_eq_zero_of_faceDissipation_eq_zero` (:358) the field vanishes there too,
contradicting the hypothesis. The floor is `relEntropy_ge_sum_zeroSet`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:931`), and with `siphonWeight_pos` on a nonempty
`P` the window `relEntropy xstar (γ a) − siphonWeight P xstar` has strictly positive width, so the
loss is quantified rather than merely signed.

The statement is deliberately posed with the non-degeneracy hypothesis at an **interior** time
rather than at `a`; see Residual 3 in the module header. -/
theorem relEntropy_faceEscapeWindow (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a < b)
    (hface : ∀ t, a ≤ t → b ≤ t → γ t ∈ N.SiphonFace P)
    (hpos : ∀ t, a ≤ t → b ≤ t → ∀ s, s ∉ P → 0 < γ t s)
    (hderiv : ∀ t, a ≤ t → b ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hmoving : ∃ t₀, a < t₀ ∧ t₀ < b ∧ N.massActionVectorField κ (γ t₀) ≠ 0) :
    siphonWeight P xstar ≤ relEntropy xstar (γ b) ∧
      relEntropy xstar (γ b) < relEntropy xstar (γ a) := by
  classical
  obtain ⟨t₀, ht₀a, ht₀b, hfield⟩ := hmoving
  -- antitonicity on the closed interval `[a, b]`
  have hγdiff : Differentiable ℝ γ :=
    fun t => (hderiv t (le_of_lt (lt_of_lt_of_le ht₀a (le_of_lt ht₀b))) (le_of_lt ht₀b)).differentiableAt
  have hcont : Continuous (fun t => relEntropy xstar (γ t)) :=
    (relEntropy_continuous hxs).comp hγdiff.continuous
  have hzeroAt : ∀ t, a ≤ t → b ≤ t → ∀ s ∈ P, γ t s = 0 := by
    intro t hta htb
    exact (faceSum_eq_zero_iff ((mem_siphonFace_iff N).mp (hface t hta htb)).1).mp
      ((mem_siphonFace_iff N).mp (hface t hta htb)).2
  have hanti : AntitoneOn (fun t => relEntropy xstar (γ t)) (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (le_of_lt hab)) hcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Icc hab, Set.mem_Ioo] at ht
      exact (faceRelEntropy_hasDerivAt hxs (hzeroAt t ht.1.le ht.2.le)
        (hpos t ht.1.le ht.2.le)
        (fun s => (hasDerivAt_pi.mp (hderiv t ht.1.le ht.2.le)) s)).differentiableAt
          .differentiableWithinAt
    · intro t ht
      rw [interior_Icc hab, Set.mem_Ioo] at ht
      rw [(faceRelEntropy_hasDerivAt hxs (hzeroAt t ht.1.le ht.2.le)
        (hpos t ht.1.le ht.2.le)
        (fun s => (hasDerivAt_pi.mp (hderiv t ht.1.le ht.2.le)) s)).deriv]
      exact N.faceDissipation_nonpos κ hP hwr hxs hcb (hzeroAt t ht.1.le ht.2.le)
        (hpos t ht.1.le ht.2.le)
  -- antitonicity plus `relEntropy a = relEntropy b` forces constancy on `[a, b]`
  have hconst : relEntropy xstar (γ b) = relEntropy xstar (γ a) →
      ∀ t, a ≤ t → b ≤ t → relEntropy xstar (γ t) = relEntropy xstar (γ a) := by
    intro heq t hta htb
    have h1 := hanti (Set.mem_Icc.mpr ⟨le_of_lt hab, ht0_le b le_rfl⟩)
      (Set.mem_Icc.mpr ⟨hta, htb⟩) (by linarith)
    have h2 := hanti (Set.mem_Icc.mpr ⟨hta, htb⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hab, ht0_le b le_rfl⟩) htb
    rw [heq] at h1
    exact le_antisymm h2 h1
  -- the field is nonzero at an interior time, so the entropy cannot be constant there
  have hstrict : relEntropy xstar (γ b) < relEntropy xstar (γ a) := by
    by_contra hn
    have h1 := hanti (Set.mem_Icc.mpr ⟨le_of_lt hab, ht0_le b le_rfl⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hab, le_refl b⟩) (le_of_lt hab)
    have hne : relEntropy xstar (γ b) ≠ relEntropy xstar (γ a) := by
      intro hz
      exact hn (le_antisymm h1 hz)
    -- constancy on `[a, b]` kills the derivative at `t₀`, hence the face dissipation, hence the field
    have hc := hconst (le_antisymm h1 hne)
    have hderiv₀ := faceRelEntropy_hasDerivAt hxs (hzeroAt t₀ ht₀a.le ht₀b.le)
      (hpos t₀ ht₀a.le ht₀b.le)
      (fun s => (hasDerivAt_pi.mp (hderiv t₀ ht₀a.le ht₀b.le)) s)
    have hzero' : (∑ s, if s ∈ P then 0 else
        (Real.log (γ t₀ s) - Real.log (xstar s)) *
          N.massActionVectorField κ (γ t₀) s) = 0 :=
      hderiv₀.unique (hasDerivAt_const t₀ (relEntropy xstar (γ t₀)))
    have hfl := N.massActionVectorField_eq_zero_of_faceDissipation_eq_zero κ hP hwr hxs hcb
      (hzeroAt t₀ ht₀a.le ht₀b.le) (hpos t₀ ht₀a.le ht₀b.le) hzero'
    exact hne ⟨hc t₀ ht₀a.le ht₀b.le, hc b (by linarith) le_rfl⟩
  have hfaceb := (mem_siphonFace_iff N).mp (hface b (by linarith) le_rfl)
  exact ⟨siphonWeight_le_relEntropy_of_vanishes hxs hfaceb.1
    ((faceSum_eq_zero_iff hfaceb.1).mp hfaceb.2), hstrict⟩

/-! ### Escaping the face collapses its weight -/

/-- **An escape across a face strictly decreases the face's weight, and the entropy with it.**
This is the "comparable growth across an escape from the face" of
`SiphonDimensionDescent.lean:116-123`, in the one shape it is actually available:

if the orbit is confined to `SiphonFace P` at `a` but by `b` some species of `P` has become
strictly positive, then the zero set `Z` of `γ b` is a **proper subset** of `P` and

```
siphonWeight Z xstar  <  siphonWeight P xstar,      relEntropy xstar (γ b) < relEntropy xstar (γ a).
```

Both halves are strict, and they are strict in *opposite directions of information*: the entropy
loss is the analytic half (`relEntropy_faceEscapeWindow`), the weight collapse is the geometric
half (`Z ⊊ P` plus monotonicity of `siphonWeight` under inclusion, proved hole-free by
`FormADescent` as `siphonWeight_lt_of_proper_subset`).

**Why both.** The pair is what the descent consumes, and neither half implies the other:
`Finset.card` order and `siphonWeight` order are *different* orders — with `S = Fin 3`,
`xstar = (1000, 1, 1)`, `Q = {0}`, `P = {1, 2}` one has `Q.card < P.card` but
`siphonWeight xstar P = 2 < 1000 = siphonWeight xstar Q` — machine-checked by `FormADescent`
(`not_weight_lt_of_card_lt`, `not_card_lt_of_weight_lt`, both on `Fin 3` with `xstar i = 10^i`).
What *does* bridge the two orders is **containment**: `Q ⊊ P` forces both `Q.card < P.card` and
`siphonWeight xstar Q < siphonWeight xstar P`, so a single ⊆-collapse discharges the descent's
cardinality-shrinkage for free. This theorem supplies exactly that collapse, conditional on the
escape actually happening.

**It does not prove an escape happens.** The hypothesis `∃ s ∈ P, 0 < γ b s` is an *input*. At a
cardinality-minimal carried siphon
`descendStep_iff_omegaPointPositive_of_cardMinimal` (`SiphonDimensionDescent.lean:347`) makes the
disjunct the goal, so the escape cannot be read off minimality; no such instance is produced here. -/
theorem relEntropy_and_weight_drop_of_escape (N : Network S) (κ : N.RateConstants)
    {P : Finset S} (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a < b)
    (hface : ∀ t, a ≤ t → b ≤ t → γ t ∈ N.SiphonFace P)
    (hpos : ∀ t, a ≤ t → b ≤ t → ∀ s, s ∉ P → 0 < γ t s)
    (hderiv : ∀ t, a ≤ t → b ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hmoving : ∃ t₀, a < t₀ ∧ t₀ < b ∧ N.massActionVectorField κ (γ t₀) ≠ 0)
    -- the escape: some species of the siphon is strictly positive again at `b`
    (hescape : ∃ s ∈ P, 0 < γ b s) :
    siphonWeight (Finset.univ.filter (fun s => γ b s = 0)) xstar < siphonWeight P xstar ∧
      relEntropy xstar (γ b) < relEntropy xstar (γ a) := by
  classical
  obtain ⟨⟨s, hsP, hspos⟩⟩ := hescape
  have hfloor' := relEntropy_faceEscapeWindow N κ hP hwr hxs hcb hab hface hpos hderiv hmoving
  -- the zero set of `γ b` omits the escaped species, so it is a proper subset of `P`
  have hmem : ∀ s ∈ Finset.univ.filter (fun s => γ b s = 0), s ∈ P := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    by_contra hsP
    exact absurd hs (by simpa [hsP] using hspos)
  have hne : Finset.univ.filter (fun s => γ b s = 0) ≠ P := by
    intro heq
    have : s ∈ Finset.univ.filter (fun s => γ b s = 0) := heq ▸ Finset.mem_univ s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact absurd this hspos
  have hsub : Finset.univ.filter (fun s => γ b s = 0) ⊂ P :=
    ⟨hmem, hne⟩
  -- `siphonWeight` is strictly monotone under proper inclusion.
  -- Proved inline rather than by reusing FormADescent's public
  -- `siphonWeight_lt_of_proper_subset`: that module is not imported (we stay standalone and
  -- `sorryAx`-free), and declaring the same public name in `CRNT.Network` on two branches
  -- collides at merge. The proof is one `Finset.sum_lt_sum_of_subset_of_pos` application.
  have hltw : siphonWeight (Finset.univ.filter (fun s => γ b s = 0)) xstar
      < siphonWeight P xstar := by
    have hnn : ∀ t : S, 0 ≤ xstar t := fun t => (hxs t).le
    have hpos' : ∃ i ∈ P, ¬ i ∈ Finset.univ.filter (fun s => γ b s = 0) :=
      ⟨s, hsP, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact hspos⟩
    have hsub' : Finset.univ.filter (fun s => γ b s = 0) ⊆ P := Finset.ssubset_iff_subset_ne.mpr hsub
    have hlt : ∑ t ∈ Finset.univ.filter (fun s => γ b s = 0), xstar t < ∑ t ∈ P, xstar t :=
      Finset.sum_lt_sum_of_subset_of_pos hnn hsub' hpos'
    simpa [siphonWeight] using hlt
  exact ⟨hltw, hfloor'.2⟩

end Network
end CRNT