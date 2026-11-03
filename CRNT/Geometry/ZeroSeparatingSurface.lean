import CRNT.Dynamics.ThmBGenuine
import CRNT.Dynamics.ZeroSeparating
import CRNT.Geometry.ToricFan

/-!
# The zero-separating-surface construction interface

A *zero-separating surface* is a `C¹` function `g : E → ℝ` whose sublevel set `{g ≤ c}` is
forward-invariant for a toric differential inclusion and is separated from a ball about the
origin, so a genuine flow starting in it stays a fixed distance from extinction. Such a surface
is the geometric heart of the persistence argument in Craciun, _Toric differential inclusions
and a proof of the global attractor conjecture_.

`ThmBGenuine.lean` proves the *consequence*: if a function `g` admits neighborhood-descent of the
field on a band around a sublevel value `c`, and the sublevel set `{g ≤ c}` is separated from a
ball about the origin, then the genuine flow stays in `{g ≤ c}` and a fixed distance from `0`.
The remaining task is to *construct* such a `g` out of a toric differential inclusion, by
induction on dimension. This module packages the surface as a predicate and wires it to
`ThmBGenuine`, proves the one-dimensional base case, and states the induction step
precisely. The simplicial gluing that would discharge the induction step is taken as a hypothesis,
not constructed here.

## What this module formalizes

* `ZeroSeparatingSurfaceExists f x₀`: the **surface-existence predicate.** For a genuine vector
  field `f : E → E` (intended to be a selection of a toric inclusion field) and a start `x₀`,
  there exist `g : E → ℝ`, a derivative field `g'`, and reals `c δ r` such that the full
  hypothesis bundle of `ThmBGenuine.genuine_away_from_origin` holds: `g` is `C¹`, has
  neighborhood descent `g' y (f y) ≤ 0` on the band `{c − δ ≤ g y ≤ c + δ}` (`δ > 0`),
  `g x₀ ≤ c`, and `{g ≤ c}` misses `Metric.ball 0 r` (`r > 0`).

* `ZeroSeparatingSurfaceExists.away_from_origin` — the **wiring lemma.** From the surface
  existence and any genuine curve `γ` with `γ 0 = x₀` solving `ẋ = f (γ t)` on `[0, ∞)`, the
  genuine trajectory keeps a hard distance `r` from the origin for all forward times. A direct
  feed into `genuine_away_from_origin`. `genuineZeroSeparating` repackages it as a
  `GenuineZeroSeparating` bundle.

* `toricSelection_zeroSeparating` — the **toric wrapper.** Same conclusion stated against a fan
  `F` and scale `δfan`, given a witness that the genuine field `f` is a pointwise selection of
  `toricInclusionField F δfan` together with the surface existence for `f`.

* `zeroSeparatingSurfaceExists_one_dim` — the **1-D base case**. When the genuine
  field on `ℝ` is nonnegative near and beyond a far point (`f y ≥ 0` for `y ≥ P₀ − 1`, say via the
  toric inclusion being `⊆ Ici 0` there) the affine surface `g := fun x => P₀ − x` separates: the
  sublevel set `{g ≤ 0} = {x ≥ P₀}` is the far ray, descent is `g' · f = −f ≤ 0`, and the ray
  misses `Metric.ball 0 P₀`. This realizes `ZeroSeparatingSurfaceExists` in dimension one and
  connects to `ZeroSeparating.zeroSeparatingRegion_Ici`.

* `InductionStepHypothesis` — the **induction-step interface**, stated as a precise `Prop`
  shape "a faithful `(n−1)`-D zero-separating surface yields an `n`-D one", with the simplicial
  construction itself taken as a hypothesis, *not* proved.

## What is proved here, and what is taken as a hypothesis

Proved here:

* the surface-existence predicate and its wiring to `genuine_away_from_origin`;
* the 1-D base case realizing the predicate.

Taken as hypotheses, not constructed here — the geometric core of the surface construction:

* **Neighborhood patches.** Cover a neighborhood of `0` in the positive orthant by the
  cones of the fan; on each cone the toric field is the polar cone, giving a constant admissible
  half-space. The separating surface is assembled patch-by-patch.
* **2-D polygonal zero-separating curves.** In the plane, the surface is a polygonal line
  whose edges are subtangent to the field on each patch; the induction base above dimension one.
* **The naive `n`-D surface and its failure in `ℝ⁴`.** The direct generalization of the
  3-D dotted-surface construction is *overdetermined* in `ℝ⁴`: the per-patch subtangency
  constraints exceed the available degrees of freedom. This is the subtlety that forces the
  inductive simplicial approach instead of a closed-form surface.
* **The simplicial induction.** A faithful `(n−1)`-D zero-separating surface on each facet
  of a simplicial subdivision is glued into an `n`-D one. `InductionStepHypothesis` states the
  shape of this step; the gluing, the subdivision combinatorics, and the verification that the
  glued surface retains neighborhood-descent are taken as given.

These rest additionally on the set-valued viability (Nagumo) layer absent from Mathlib,
recorded in `ZeroSeparating.lean`; the genuine-flow wiring here needs only the single-valued
descent lemma, which is why the predicate and base case land cleanly.

Depends on: `CRNT.Dynamics.ThmBGenuine`,
`CRNT.Dynamics.ZeroSeparating`, `CRNT.Geometry.ToricFan`.
-/

namespace CRNT

namespace DifferentialInclusion

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Item 1 — the surface-existence interface and its wiring -/

/-- **Zero-separating-surface existence.** For a genuine vector
field `f : E → E` and a start `x₀`: there is a `C¹` function `g`, a derivative field `g'`, a
sublevel value `c`, a band radius `δ > 0`, and a separation margin `r > 0` such that

* `g` is continuous and `HasFDerivAt g (g' y) y` everywhere (so `g` is `C¹` with field `g'`);
* neighborhood descent holds: `g' y (f y) ≤ 0` whenever `c − δ ≤ g y ≤ c + δ`;
* the start lies in the sublevel set: `g x₀ ≤ c`;
* the sublevel set is separated from the origin: `{g ≤ c} ⊆ (Metric.ball 0 r)ᶜ`.

This is exactly the hypothesis bundle that `genuine_away_from_origin` consumes, so an instance of
this predicate is precisely a separating surface for the field. -/
structure ZeroSeparatingSurfaceExists (f : E → E) (x₀ : E) : Prop where
  /-- The constructed surface and all of its scalar parameters and descent data. -/
  exists_surface :
    ∃ (g : E → ℝ) (g' : E → (E →L[ℝ] ℝ)) (c δ r : ℝ),
      Continuous g ∧
      (∀ y, HasFDerivAt g (g' y) y) ∧
      0 < δ ∧
      (∀ y, c - δ ≤ g y → g y ≤ c + δ → g' y (f y) ≤ 0) ∧
      g x₀ ≤ c ∧
      0 < r ∧
      ({y : E | g y ≤ c} ⊆ (Metric.ball (0 : E) r)ᶜ)

/-- **Wiring lemma.** Given the zero-separating surface for `f` at `x₀`, every genuine
trajectory `γ` continuous on `[0, ∞)`, solving `ẋ = f (γ t)` there, and starting at `γ 0 = x₀`,
keeps a hard distance from the origin: there is `r > 0` with `r ≤ dist (γ t) 0` for all `t ≥ 0`.
The origin is therefore not an `ω`-limit point of `γ`. This feeds the surface directly into
`genuine_away_from_origin`. -/
theorem ZeroSeparatingSurfaceExists.away_from_origin {f : E → E} {x₀ : E}
    (h : ZeroSeparatingSurfaceExists f x₀)
    {γ : ℝ → E} (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hstart : γ 0 = x₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 := by
  obtain ⟨g, g', c, δ, r, hgc, hg, hδ, hdescent, hx₀, hr, hsep⟩ := h.exists_surface
  refine ⟨r, hr, ?_⟩
  refine genuine_away_from_origin hgc hg hγcont hγderiv hδ hdescent ?_ hsep
  rw [hstart]; exact hx₀

/-- **Wiring lemma, bundled form.** The zero-separating surface for `f` at `x₀`, together with a
genuine curve through `x₀`, yields a `GenuineZeroSeparating` bundle for some margin `r > 0`:
forward sublevel invariance along `γ`, the start inside the region, and exclusion of the
`r`-ball about the origin. -/
theorem ZeroSeparatingSurfaceExists.genuineZeroSeparating {f : E → E} {x₀ : E}
    (h : ZeroSeparatingSurfaceExists f x₀)
    {γ : ℝ → E} (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hstart : γ 0 = x₀) :
    ∃ (g : E → ℝ) (c r : ℝ), GenuineZeroSeparating f γ g c r := by
  obtain ⟨g, g', c, δ, r, hgc, hg, hδ, hdescent, hx₀, hr, hsepset⟩ := h.exists_surface
  have h0 : g (γ 0) ≤ c := by rw [hstart]; exact hx₀
  have hsep : Metric.ball (0 : E) r ⊆ {y : E | g y ≤ c}ᶜ := fun x hx hmem => hsepset hmem hx
  exact ⟨g, c, r,
    genuineZeroSeparating_of_descent hgc hg hγcont hγderiv hδ hdescent h0 hr hsep⟩

/-- Craciun v3, §8 Step 2: cylindrically extend a zero-separating surface when the projected
component of the product field is the original lower-dimensional field. Pulling the defining
function back along the first projection preserves its derivative inequality, while the product
norm ensures its sublevel set remains separated from the origin in the larger space. -/
theorem ZeroSeparatingSurfaceExists.product_left
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → E} {x₀ : E} (hsurf : ZeroSeparatingSurfaceExists f x₀)
    (G : E × F → E × F) (hproj : ∀ p, (G p).1 = f p.1) (y₀ : F) :
    ZeroSeparatingSurfaceExists G (x₀, y₀) := by
  obtain ⟨g, g', c, δ, r, hgc, hg, hδ, hdescent, hx₀, hr, hsep⟩ := hsurf.exists_surface
  let gProd : E × F → ℝ := fun p => g p.1
  let gProd' : E × F → (E × F →L[ℝ] ℝ) := fun p =>
    g' p.1 ∘L ContinuousLinearMap.fst ℝ E F
  refine ⟨gProd, gProd', c, δ, r, ?_, ?_, hδ, ?_, ?_, hr, ?_⟩
  · exact hgc.comp continuous_fst
  · intro p
    change HasFDerivAt (fun q : E × F => g q.1)
      (g' p.1 ∘L ContinuousLinearMap.fst ℝ E F) p
    exact (hg p.1).comp p (ContinuousLinearMap.fst ℝ E F).hasFDerivAt
  · intro p hlo hhi
    change g' p.1 ((G p).1) ≤ 0
    rw [hproj p]
    exact hdescent p.1 hlo hhi
  · simpa [gProd] using hx₀
  · intro p hp hball
    have hnorm : ‖p‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    have hnormFst : ‖p.1‖ < r := lt_of_le_of_lt (norm_fst_le p) hnorm
    have hballFst : p.1 ∈ Metric.ball (0 : E) r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hnormFst
    exact (hsep hp) hballFst

end DifferentialInclusion

/-! ## Item 1 (continued) — the toric wrapper

The genuine mass-action flow is a *selection* of the toric differential inclusion
(`toricInclusionField`): its velocity `f x` is an admissible velocity `f x ∈ F_{F,δfan}(log x)`.
A zero-separating surface separates that genuine selection, so the persistence conclusion holds
for the genuine flow whenever a separating surface for `f` exists. -/

namespace DifferentialInclusion

open scoped Topology

variable {S : Type*} [Fintype S]

/-- **Toric persistence via the zero-separating surface.** Let `f` be a genuine vector field on
`EuclideanSpace ℝ S` that is a pointwise selection of the toric inclusion field
`toricInclusionField F δfan` (`f x ∈ toricInclusionField F δfan x` for all `x`), and suppose a
zero-separating surface for `f` at `x₀` exists (`ZeroSeparatingSurfaceExists f x₀`). Then
every genuine trajectory `γ` of `f` through `x₀` keeps a hard positive distance from the origin
for all forward times. The selection hypothesis records that `γ` is also an inclusion solution of
the toric field, the form persistence is stated against in the inclusion layer. -/
theorem toricSelection_zeroSeparating
    (F : Fan (EuclideanSpace ℝ S)) (δfan : ℝ)
    {f : EuclideanSpace ℝ S → EuclideanSpace ℝ S} {x₀ : EuclideanSpace ℝ S}
    (_hsel : ∀ x, f x ∈ toricInclusionField F δfan x)
    (hsurf : ZeroSeparatingSurfaceExists f x₀)
    {γ : ℝ → EuclideanSpace ℝ S} (hγcont : Continuous γ)
    (hγderiv : ∀ t, 0 ≤ t → HasDerivAt γ (f (γ t)) t)
    (hstart : γ 0 = x₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → r ≤ dist (γ t) 0 :=
  hsurf.away_from_origin hγcont hγderiv hstart

end DifferentialInclusion

/-! ## Item 2 — the 1-D base case

In one dimension, near and beyond the far point `P₀` the toric inclusion is exactly `dx/dt ≥ 0`:
the admissible velocities form the nonnegative ray. The genuine field `f` is then a selection
with `f y ≥ 0` on the sublevel band. The affine surface `g := fun x => P₀ − x` has constant
derivative field `g' y = -(ContinuousLinearMap.id …)` evaluated as `g' y v = -v`, so descent is
`g' y (f y) = -(f y) ≤ 0`. The sublevel set `{g ≤ 0} = {x ≥ P₀} = Set.Ici P₀` is the far ray,
which misses `Metric.ball 0 P₀`. This realizes `ZeroSeparatingSurfaceExists`. -/

namespace DifferentialInclusion

/-- The affine surface `x ↦ P₀ − x` on `ℝ`, whose sublevel set `{g ≤ 0}` is the far ray
`Set.Ici P₀`. -/
private def surface1D (P₀ : ℝ) : ℝ → ℝ := fun x => P₀ - x

/-- The constant derivative field of `surface1D`: the continuous linear map `v ↦ -v`. -/
private noncomputable def surface1Dderiv : ℝ → (ℝ →L[ℝ] ℝ) :=
  fun _ => -(ContinuousLinearMap.id ℝ ℝ)

/-- **1-D base case.** A genuine field `f : ℝ → ℝ` that is nonnegative on the far band
(`0 ≤ f y` whenever `P₀ - 1 ≤ P₀ - y`, i.e. on `{y | g y ≤ 1}` for the affine surface) admits a
zero-separating surface at `x₀ = P₀`, for any `0 < P₀`. The surface is `g x = P₀ - x` with band
radius `δ = 1`, sublevel value `c = 0`, and margin `r = P₀`. This is `ZeroSeparatingSurfaceExists`
in dimension one. -/
theorem zeroSeparatingSurfaceExists_one_dim {f : ℝ → ℝ} {P₀ : ℝ} (hP₀ : 0 < P₀)
    (hf : ∀ y, P₀ - y ≤ 1 → 0 ≤ f y) :
    ZeroSeparatingSurfaceExists f P₀ where
  exists_surface := by
    refine ⟨surface1D P₀, surface1Dderiv, 0, 1, P₀, ?_, ?_, one_pos, ?_, ?_, hP₀, ?_⟩
    · exact (continuous_const.sub continuous_id)
    · intro y
      show HasFDerivAt (fun x : ℝ => P₀ - x) (surface1Dderiv y) y
      have h : HasFDerivAt (fun x : ℝ => P₀ - x) (0 - ContinuousLinearMap.id ℝ ℝ) y :=
        (hasFDerivAt_const P₀ y).sub (hasFDerivAt_id y)
      simpa [surface1Dderiv, zero_sub] using h
    · intro y _hlo hhi
      -- descent: g' y (f y) = -(f y) ≤ 0, using 0 ≤ f y on the band `{g ≤ 1}`
      have hband : P₀ - y ≤ 1 := by
        have : surface1D P₀ y ≤ (0 : ℝ) + 1 := hhi
        simpa [surface1D] using this
      have hfnn : 0 ≤ f y := hf y hband
      show surface1Dderiv y (f y) ≤ 0
      simp only [surface1Dderiv, neg_apply, ContinuousLinearMap.id_apply]
      linarith
    · show surface1D P₀ P₀ ≤ 0
      simp [surface1D]
    · -- separation: {g ≤ 0} = {x ≥ P₀} = Set.Ici P₀ ⊆ (ball 0 P₀)ᶜ
      intro x hx
      have hxge : P₀ ≤ x := by
        have : surface1D P₀ x ≤ 0 := hx
        simp only [surface1D] at this
        linarith
      -- `x ≥ P₀` is at least `P₀` from `0`, hence not in the open `P₀`-ball.
      rw [Set.mem_compl_iff, Metric.mem_ball, Real.dist_eq, sub_zero]
      have : P₀ ≤ |x| := le_trans hxge (le_abs_self x)
      linarith

end DifferentialInclusion

/-! ## Item 3 — the induction-step interface

The induction turns a faithful zero-separating surface on the boundary facets of a
simplicial subdivision (the `(n−1)`-D data) into a zero-separating surface on the full `n`-D
neighborhood. Below is the *shape* of that step as a `Prop`: it asserts that surface existence on
each facet-restricted field implies surface existence on the ambient field. The hypothesis
quantifies the facet data abstractly — a finite family of `(n−1)`-D restricted fields and start
points each carrying its own surface — and the conclusion is ambient surface existence. The
content of the step — the simplicial subdivision combinatorics, the polygonal-lines-of-patches
gluing, and the verification that the glued surface retains neighborhood-descent across facet
seams (delicate, since the naive closed form fails in `ℝ⁴`) — is taken as a hypothesis and is
**not** proved here. -/

namespace DifferentialInclusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Induction-step interface.** For an ambient genuine field `f` and start `x₀`, an
induction step is a witness that surface existence for a finite indexed family of facet data
`facetField i` / `facetStart i` (the `(n−1)`-D zero-separating surfaces) yields surface existence
for `f` at `x₀` (the `n`-D surface). This captures the *form* of the simplicial induction; the
simplicial gluing that would discharge it is taken as a hypothesis. -/
def InductionStepHypothesis
    (f : E → E) (x₀ : E) {ι : Type*} [Fintype ι]
    (facetField : ι → (E → E)) (facetStart : ι → E) : Prop :=
  (∀ i, ZeroSeparatingSurfaceExists (facetField i) (facetStart i)) →
    ZeroSeparatingSurfaceExists f x₀

/-- Discharging an `InductionStepHypothesis` against facet surfaces yields the ambient surface:
the trivial unfolding that records how the step is meant to be applied once the simplicial gluing
supplies the implication. -/
theorem InductionStepHypothesis.elim
    {f : E → E} {x₀ : E} {ι : Type*} [Fintype ι]
    {facetField : ι → (E → E)} {facetStart : ι → E}
    (step : InductionStepHypothesis f x₀ facetField facetStart)
    (hfacets : ∀ i, ZeroSeparatingSurfaceExists (facetField i) (facetStart i)) :
    ZeroSeparatingSurfaceExists f x₀ :=
  step hfacets

end DifferentialInclusion

end CRNT
