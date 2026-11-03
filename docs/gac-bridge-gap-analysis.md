# Gap analysis: what still separates the blueprint criterion from the residual

`docs/gac-bridge-gap-analysis.lean` in this directory is a runnable check, not part of the build.
It attempts to derive the residual obligation

    CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

from the blueprint criterion

    CRNT.Network.exists_positive_omegaPoint_of_blueprintData

given the blueprint data, and leaves a `sorry` for each bridge the residual's own context does not
supply.  Run it with

```sh
lake env lean docs/gac-bridge-gap-analysis.lean
```

It elaborates with **no `sorry` and no errors** (verified: the command exits 0 and prints nothing).
All three bridges are discharged from the
residual's own hypotheses:

| bridge | statement | discharged by |
| --- | --- | --- |
| 1 | `ContinuousOn (γ x₀) (Set.Ici 0)` | forward differentiability, after weakening the Dini lemmas |
| 2 | `∀ t ≥ 0, (γ x₀ t).Positive` | `Network.orbit_pos_forward`, ceiling from `hK`/`hmaps` |
| 3 | `∀ t ≥ 0, N.StoichCompatible (γ x₀ 0) (γ x₀ t)` | `Network.stoichCompatible_of_forward_solution` |

**So the residual obligation now follows from the blueprint data alone.**  Nothing about the orbit
is missing.

## Correction to an earlier claim

Earlier notes said the blueprint criterion concludes "exactly the conclusion" of the residual and
that only `hm`, `hstart` and `hregime` remained.  The conclusion does match on the nose, but the
*hypotheses* do not: these three bridges are additional obligations.  They are stated here rather
than hidden inside a convenience lemma.

## Bridge 1: fixed

`PositiveOmegaPointForRates` supplies `hsol` only for `t ≥ 0`, so global continuity of `γ x₀` is
not available.  `PolyhedralBarrier.le_of_dini_slope_nonpos_at_level` and
`eventually_barrier_lt_of_active_descent` used to ask for `Continuous`, which is stronger than
needed.  Both now take `ContinuousOn · (Set.Ici 0)`, and the weakening is propagated through the
chain, so bridge 1 is immediate from `hsol`:

* in `eventually_barrier_lt_of_active_descent` the inactive-piece step now takes `0 ≤ t` as an
  explicit hypothesis, uses `ContinuousWithinAt … (Ici 0) t` with
  `Filter.Tendsto.eventually_lt_const` to get `∀ᶠ z in 𝓝[Ici 0] t, …`, then `nhdsWithin_mono`
  transfers it to `𝓝[>] t` because `0 ≤ t` gives `Ioi t ⊆ Ici 0`;
* in `le_of_dini_slope_nonpos_at_level` the `u x < R` branch is the same manoeuvre, the truncation
  uses `ContinuousOn.sup` (there is no `ContinuousOn.max`), and the fencing step gets
  `ContinuousOn` on `Icc 0 T` by `.mono Set.Icc_subset_Ici_self`.

The change propagates through `barrier_le_of_local_descent`,
`minMaxBarrier_le_of_local_descent`, the two `dist_ge_…` wiring lemmas,
`barrier_le_of_toric_descent`, `minMaxBarrier_le_of_toric_descent`,
`coordinate_lower_bounds_of_toric_barrier`, `exists_positive_omegaPoint_of_toric_blueprint`,
`…_of_convex_tiles`, `…_of_selfConsistent_normals`, `…_of_blueprintData`,
`…_of_toric_halfspace`, `…_of_faceRelevantCore` and `…_of_tiled_faceCores`, plus a new
`Network.continuousOn_euclideanStoichState_comp`.  The `forwardInvariant_…` lemmas are unaffected:
an inclusion solution is globally continuous, so they pass `Continuous.continuousOn`.

Note a tempting shortcut that does **not** work: replacing the orbit by `fun t => γ x₀ (max t 0)`
to make it globally continuous.  That curve fails `HasDerivAt` at `t = 0`, because it is constant
to the left while the mass-action field there is generally nonzero, and the trapping theorems need
the derivative at `0` inclusive.

## Bridge 3 is done

`Network.stoichCompatible_of_forward_solution` discharges bridge 3 from `hsol` **alone**.

A note against wasted effort: the first version of this proof reproved the fact from scratch by
testing against the orthogonal complement.  That was unnecessary —
`Network.sub_mem_stoichSubspace_of_solution` already existed in
`CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean` and does exactly this, so bridge 3 is a
three-line corollary.  Search `AsymptoticStability.lean` before proving anything about mass-action
solutions; it also holds `orbit_pos`, `exists_field_lower_bound` and
`ge_mul_exp_of_forward_deriv_ge`.

## Bridge 2 is done

`Network.orbit_pos_forward` in `CRNT/Dynamics/OrbitRegularity.lean` is the unclamped forward-time
version, and the gap-analysis file discharges bridge 2 with it.  The coordinate ceiling it needs
comes from compactness of `K`: `IsCompact.exists_isMaxOn` per species, then the `sup'` over the
finitely many species.

`orbit_pos` (`CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean:162`) could not be used
directly, because its hypotheses are

* `hbound : ∀ x nonneg with x s ≤ B, ∀ s, -(L * x s) ≤ massActionVectorField κ x s` — the
  Gronwall-type lower bound, true because every negative term of the `s`-component carries a factor
  of `x s`;
* `hΓd : ∀ t, HasDerivAt Γ (massActionVectorField κ (clampBox B (Γ t))) t` — the **clamped** field,
  for *all* `t`.

The residual gives the unclamped field for `t ≥ 0` only.  The unclamped forward version now proved
is:

```
theorem orbit_pos_forward (N : Network S) (κ : N.RateConstants) {B : ℝ}
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ B)
    (hΓd : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∀ t : ℝ, 0 ≤ t → (Γ t).Positive
```

The Gronwall input is obtained internally from `Network.exists_field_lower_bound`, so no `L` or
`hbound` appears in the signature.  Dropping the clamp *simplifies* the Gronwall step — no
`clampBox` juggling.  The cost is that continuity is only available on `Set.Ici 0`, so the closed
sets in the first-hitting-time argument are built with `IsClosed.isClosed_le` relative to `Ici 0`,
and the passage to the limit `t → t₁` uses `le_on_closure` instead of a globally closed set.
