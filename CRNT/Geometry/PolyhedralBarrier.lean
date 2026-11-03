import CRNT.Dynamics.DifferentialInclusion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Polyhedral barriers with local descent

A *polyhedral barrier* is the maximum of finitely many affine functions,

```
barrier L b x = max i (L i x - b i),   L i : E →L[ℝ] ℝ,  b i : ℝ,
```

and the region it guards is the polyhedron `{x | barrier L b x ≤ R}`.  This module proves that
such a region traps forward trajectories under a **local** descent condition: at a point where
the barrier has reached the level, only the *active* pieces — those attaining the maximum —
need to be nonincreasing along the velocity.

## Why the localisation matters

`CRNT.Geometry.SmoothBarrierGluing` already provides a smooth barrier, the log-sum-exp
`smoothWallList`, and `Network.WeaklyReversible.zeroSeparatingSurfaceExists_toric_activeWallList_of_compact_band`
turns it into a `DifferentialInclusion.ZeroSeparatingSurfaceExists`.  Because a log-sum-exp keeps
*every* wall weakly active everywhere, that route needs the descent inequality for every wall
simultaneously on the whole band, and in the toric setting that means one normal direction
inward for every reaction vector at once.  No such direction exists for a general fan: which
reaction dominates depends on which cone `log x` lies in.

A genuine maximum localises: off the ridges exactly one piece is active, and the region is
trapped as soon as each piece descends *where it is the active one*.  That is precisely the
descent bookkeeping of Craciun, *Toric differential inclusions and a proof of the global
attractor conjecture* (v3), Lemma 9.5 and Lemma 9.7: the outer normal at a point of the
zero-separating hypersurface must lie in the fan cone containing that point, and each flat piece
of the polyhedral surface carries one normal, valid only on its own tile.

## Contents

* `barrier`, `le_barrier`, `exists_active`, `barrier_le_iff`, `continuous_barrier`:
  the barrier and its elementary interface.
* `eventually_barrier_lt_of_active_descent`: the right Dini estimate.  If every active piece has
  nonpositive derivative along the velocity, then for any `r > 0` the barrier satisfies
  `barrier (γ z) < barrier (γ t) + r * (z - t)` for `z` slightly to the right of `t`.  Inactive
  pieces are handled by continuity, active ones by the derivative.
* `barrier_le_of_local_descent`: the trapping theorem.  Fencing the truncation
  `max (barrier ∘ γ) R` between `R` and `R + ε · t` and letting `ε → 0` gives
  `barrier (γ t) ≤ R` for all `t ≥ 0`.
* `forwardInvariant_barrierSublevel`: the same statement in the
  `DifferentialInclusion.ForwardInvariant` interface.
* `dist_pos_of_local_descent`: the wiring lemma.  A guarded region separated from a point keeps
  the trajectory at a positive distance from it — the persistence conclusion.

Everything here is proved; there is no axiom and no `sorry`.

Depends on: `CRNT.Dynamics.DifferentialInclusion`, Mathlib mean-value and lattice topology.
-/

open scoped Topology
open Filter Set

namespace CRNT
namespace PolyhedralBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ### The barrier and its elementary interface -/

/-- The polyhedral barrier `x ↦ max i (L i x - b i)`. -/
noncomputable def barrier (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => L i x - b i

theorem le_barrier (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) (x : E) (i : ι) :
    L i x - b i ≤ barrier L b x :=
  Finset.le_sup' (fun i => L i x - b i) (Finset.mem_univ i)

/-- Some piece attains the barrier: the *active* piece at `x`. -/
theorem exists_active (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) (x : E) :
    ∃ i : ι, L i x - b i = barrier L b x := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) fun i => L i x - b i
  exact ⟨i, hi.symm⟩

theorem barrier_le_iff {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {x : E} {c : ℝ} :
    barrier L b x ≤ c ↔ ∀ i : ι, L i x - b i ≤ c := by
  rw [barrier, Finset.sup'_le_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

theorem barrier_lt_iff {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {x : E} {c : ℝ} :
    barrier L b x < c ↔ ∀ i : ι, L i x - b i < c := by
  rw [barrier, Finset.sup'_lt_iff]
  exact ⟨fun h i => h i (Finset.mem_univ i), fun h i _ => h i⟩

/-- A one-piece barrier is just its affine function. -/
theorem barrier_unique [Unique ι] (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) (x : E) :
    barrier L b x = L default x - b default := by
  refine le_antisymm (barrier_le_iff.mpr ?_) (le_barrier L b x default)
  intro i
  rw [Unique.eq_default i]

theorem continuous_barrier (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) :
    Continuous (barrier L b) := by
  refine Continuous.finset_sup'_apply (f := fun i (x : E) => L i x - b i)
    Finset.univ_nonempty ?_
  intro i _
  exact (L i).continuous.sub continuous_const

/-- The guarded polyhedron is closed. -/
theorem isClosed_sublevel (L : ι → (E →L[ℝ] ℝ)) (b : ι → ℝ) (R : ℝ) :
    IsClosed {x : E | barrier L b x ≤ R} :=
  isClosed_le (continuous_barrier L b) continuous_const

/-! ### An abstract fencing lemma -/

/-- **Fencing a continuous function below a level.**  Suppose `u 0 ≤ R` and, at every nonnegative
time where `u` has reached `R`, the right Dini slope of `u` is nonpositive — stated as: for every
`r > 0`, `u z < u t + r * (z - t)` for all `z` slightly to the right of `t`.  Then `u` never
exceeds `R`.

Nothing is assumed at times where `u` is strictly below `R`.  The truncation `max u R` supplies the
missing estimate there — it is locally constant below the level — and
`image_le_of_liminf_slope_right_le_deriv_boundary` performs the `ε → 0` limit against the fences
`R + ε · t`.  Isolating this step keeps the barrier arguments below purely algebraic. -/
theorem le_of_dini_slope_nonpos_at_level_le {u : ℝ → ℝ} {R : ℝ}
    (hucont : ContinuousOn u (Set.Ici 0)) (hstart : u 0 ≤ R) {T : ℝ} (hT : 0 ≤ T)
    (hdini : ∀ t, 0 ≤ t → t < T → R ≤ u t → ∀ r : ℝ, 0 < r →
      ∀ᶠ z in 𝓝[>] t, u z < u t + r * (z - t)) :
    u T ≤ R := by
  set w : ℝ → ℝ := fun t => max (u t) R with hw
  have hwcont : ContinuousOn w (Set.Ici 0) := ContinuousOn.sup hucont continuousOn_const
  have hw0 : w 0 ≤ R := max_le hstart le_rfl
  have hbound : ∀ x ∈ Ico (0 : ℝ) T, ∀ r : ℝ, (0 : ℝ) < r →
      ∃ᶠ z in 𝓝[>] x, slope w x z < r := by
    intro x hx r hr
    have hx0 : 0 ≤ x := hx.1
    have hpos : ∀ᶠ z in 𝓝[>] x, x < z := eventually_mem_nhdsWithin
    have key : ∀ᶠ z in 𝓝[>] x, w z < w x + r * (z - x) := by
      by_cases hlt : u x < R
      · -- below the level: the truncation is locally constant
        have hsub : Set.Ioi x ⊆ Set.Ici 0 := fun z hz => le_trans hx0 (le_of_lt hz)
        have hcw : ContinuousWithinAt u (Set.Ici 0) x := hucont x (Set.mem_Ici.mpr hx0)
        have hev : ∀ᶠ z in 𝓝[>] x, u z < R :=
          (Filter.Tendsto.eventually_lt_const hlt hcw).filter_mono (nhdsWithin_mono x hsub)
        filter_upwards [hev, hpos] with z hz hzx
        have hwz : w z = R := max_eq_right hz.le
        have hwx : w x = R := max_eq_right hlt.le
        have hrz : 0 < r * (z - x) := mul_pos hr (sub_pos.mpr hzx)
        rw [hwz, hwx]
        linarith
      · -- at or above the level: use the Dini hypothesis
        have hge : R ≤ u x := not_lt.mp hlt
        have hwx : w x = u x := max_eq_left hge
        filter_upwards [hdini x hx0 hx.2 hge r hr, hpos] with z hz hzx
        have hrz : 0 < r * (z - x) := mul_pos hr (sub_pos.mpr hzx)
        have hzR : R < u x + r * (z - x) := by linarith
        rw [hwx]
        exact max_lt hz hzR
    refine (key.and hpos).frequently.mono ?_
    rintro z ⟨hz, hzx⟩
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hzx)]
    linarith
  have hfence := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := w) (a := 0) (b := T) (B := fun _ => R) (B' := fun _ => 0)
    (hwcont.mono Set.Icc_subset_Ici_self) hw0 continuousOn_const
    (fun x _ => hasDerivWithinAt_const x (Ici x) R) hbound
  exact le_trans (le_max_left _ _) (hfence (Set.mem_Icc.mpr ⟨hT, le_rfl⟩))

/-- Global form: the fencing bound at every nonnegative time. -/
theorem le_of_dini_slope_nonpos_at_level {u : ℝ → ℝ} {R : ℝ}
    (hucont : ContinuousOn u (Set.Ici 0)) (hstart : u 0 ≤ R)
    (hdini : ∀ t, 0 ≤ t → R ≤ u t → ∀ r : ℝ, 0 < r →
      ∀ᶠ z in 𝓝[>] t, u z < u t + r * (z - t)) :
    ∀ t, 0 ≤ t → u t ≤ R := fun _T hT =>
  le_of_dini_slope_nonpos_at_level_le hucont hstart hT
    fun t ht _ hge r hr => hdini t ht hge r hr

/-- **Band form of the fencing lemma.**

The Dini bound is required only where `u` lies in the band `[R, R']`, and the conclusion is still
`u ≤ R` everywhere.  This matters for the toric barrier: the descent hypothesis carries side
conditions (coordinate floors, off-face bounds) that are only available *inside* the guarded
region, so a hypothesis quantified over all `u t ≥ R` would have to be established at points the
argument has not yet excluded — circular.  Restricting to a band `R < R'` breaks that: the side
conditions need only hold on `{u ≤ R'}`.

The proof is a two-step bootstrap.  First `u` never reaches `R'`: otherwise take the first such
time `t₁` (the set `{t ≥ 0 | R' ≤ u t}` is closed by `IsClosed.isClosed_le`), note `u < R'` on
`[0, t₁)` so the band hypothesis applies throughout, and the local fencing lemma gives
`u t₁ ≤ R < R'`.  With `u < R'` everywhere the band hypothesis is unconditional, and the global
form finishes. -/
theorem le_of_dini_slope_nonpos_in_band {u : ℝ → ℝ} {R R' : ℝ} (hRR' : R < R')
    (hucont : ContinuousOn u (Set.Ici 0)) (hstart : u 0 ≤ R)
    (hdini : ∀ t, 0 ≤ t → R ≤ u t → u t ≤ R' → ∀ r : ℝ, 0 < r →
      ∀ᶠ z in 𝓝[>] t, u z < u t + r * (z - t)) :
    ∀ t, 0 ≤ t → u t ≤ R := by
  have hnever : ∀ t, 0 ≤ t → u t < R' := by
    intro T hT
    by_contra hcon
    rw [not_lt] at hcon
    set A : Set ℝ := {t ∈ Set.Ici (0 : ℝ) | R' ≤ u t} with hA
    have hAcl : IsClosed A := isClosed_Ici.isClosed_le continuousOn_const hucont
    have hAne : A.Nonempty := ⟨T, hT, hcon⟩
    have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
    set t₁ := sInf A with ht₁def
    have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
    have ht₁0 : 0 ≤ t₁ := ht₁A.1
    have hbefore : ∀ t, 0 ≤ t → t < t₁ → u t < R' := by
      intro t ht htlt
      by_contra hle
      rw [not_lt] at hle
      exact absurd (csInf_le hAbdd ⟨ht, hle⟩) (not_le.mpr htlt)
    have hle : u t₁ ≤ R :=
      le_of_dini_slope_nonpos_at_level_le hucont hstart ht₁0
        fun t ht htlt hge r hr => hdini t ht hge (hbefore t ht htlt).le r hr
    exact absurd (le_trans ht₁A.2 hle) (not_le.mpr hRR')
  exact le_of_dini_slope_nonpos_at_level hucont hstart
    fun t ht hge r hr => hdini t ht hge (hnever t ht).le r hr

/-! ### The right Dini estimate -/

/-- **Right Dini estimate for a polyhedral barrier.**  Along a continuous curve differentiable at
`t`, if every piece active at `γ t` has nonpositive derivative `L i (v) ≤ 0`, then for every
`r > 0` the barrier grows slower than `r` to the right of `t`.

Inactive pieces are strictly below the barrier at `γ t`, so continuity keeps them below it
nearby; active pieces are controlled by their own derivative. -/
theorem eventually_barrier_lt_of_active_descent
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {γ : ℝ → E} {v : E} {t : ℝ}
    (hγcont : ContinuousOn γ (Set.Ici 0)) (ht : 0 ≤ t) (hd : HasDerivAt γ v t)
    (hact : ∀ i : ι, L i (γ t) - b i = barrier L b (γ t) → L i v ≤ 0)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝[>] t, barrier L b (γ z) < barrier L b (γ t) + r * (z - t) := by
  have hpos : ∀ᶠ z in 𝓝[>] t, t < z := eventually_mem_nhdsWithin
  have hpiece : ∀ i : ι, ∀ᶠ z in 𝓝[>] t,
      L i (γ z) - b i < barrier L b (γ t) + r * (z - t) := by
    intro i
    by_cases hi : L i (γ t) - b i = barrier L b (γ t)
    · -- active piece: use its derivative
      have hφ : HasDerivAt (fun z => L i (γ z) - b i) (L i v) t :=
        ((L i).hasFDerivAt.comp_hasDerivAt t hd).sub_const (b i)
      have hslope : Tendsto (slope (fun z => L i (γ z) - b i) t) (𝓝[≠] t) (𝓝 (L i v)) :=
        hasDerivAt_iff_tendsto_slope.mp hφ
      have hsub : 𝓝[>] t ≤ 𝓝[≠] t := nhdsWithin_mono t fun _ hz => ne_of_gt hz
      have hlt : L i v < r := lt_of_le_of_lt (hact i hi) hr
      have hev := (hslope.mono_left hsub).eventually_lt_const hlt
      filter_upwards [hev, hpos] with z hz hzt
      have hzne : z - t ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hzt)
      rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hzt)] at hz
      · rw [hi] at hz
        linarith
    · -- inactive piece: use continuity
      have hstrict : L i (γ t) - b i < barrier L b (γ t) :=
        lt_of_le_of_ne (le_barrier L b (γ t) i) hi
      have hsub : Set.Ioi t ⊆ Set.Ici 0 := fun z hz => le_trans ht (le_of_lt hz)
      have hγcw : ContinuousWithinAt γ (Set.Ici 0) t := hγcont t (Set.mem_Ici.mpr ht)
      have hcw : ContinuousWithinAt (fun z => L i (γ z) - b i) (Set.Ici 0) t :=
        (((L i).continuous.continuousAt).comp_continuousWithinAt hγcw).sub
          continuousWithinAt_const
      have hev : ∀ᶠ z in 𝓝[>] t, L i (γ z) - b i < barrier L b (γ t) :=
        (Filter.Tendsto.eventually_lt_const hstrict hcw).filter_mono (nhdsWithin_mono t hsub)
      filter_upwards [hev, hpos] with z hz hzt
      have : 0 < r * (z - t) := mul_pos hr (sub_pos.mpr hzt)
      linarith
  filter_upwards [eventually_all.mpr hpiece] with z hz
  exact barrier_lt_iff.mpr hz

/-! ### The trapping theorem -/

/-- **A polyhedral barrier with local descent traps the forward trajectory.**

`γ` is a continuous curve with velocity `v t` at every nonnegative time, starting inside the
polyhedron `{barrier ≤ R}`.  The hypothesis `hdesc` is the localised descent condition: at a
time where the barrier has reached `R`, every *active* piece is nonincreasing along the
velocity.  Nothing is assumed about the inactive pieces, and nothing at all is assumed at times
where the barrier is below `R`.

The proof fences the truncation `w t = max (barrier (γ t)) R` between the constant `R` and the
lines `R + ε · t`, using `image_le_of_liminf_slope_right_le_deriv_boundary` with the Dini
estimate above; `ε → 0` is already performed inside that Mathlib lemma. -/
theorem barrier_le_of_local_descent
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {R : ℝ} {γ : ℝ → E} {v : ℝ → E}
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (v t) t)
    (hstart : barrier L b (γ 0) ≤ R)
    (hdesc : ∀ t, 0 ≤ t → R ≤ barrier L b (γ t) → ∀ i : ι,
      L i (γ t) - b i = barrier L b (γ t) → L i (v t) ≤ 0) :
    ∀ t, 0 ≤ t → barrier L b (γ t) ≤ R := by
  refine le_of_dini_slope_nonpos_at_level
    ((continuous_barrier L b).comp_continuousOn hγcont) hstart ?_
  intro t ht hlevel r hr
  exact eventually_barrier_lt_of_active_descent hγcont ht (hγ t ht) (hdesc t ht hlevel) hr

/-- **Band form of the trapping theorem.**  The descent hypothesis is needed only while the barrier
lies in `[R, R']`, so any side conditions it carries need only hold on `{barrier ≤ R'}` — see
`le_of_dini_slope_nonpos_in_band` for why that matters. -/
theorem barrier_le_of_local_descent_in_band
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {R R' : ℝ} (hRR' : R < R') {γ : ℝ → E} {v : ℝ → E}
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (v t) t)
    (hstart : barrier L b (γ 0) ≤ R)
    (hdesc : ∀ t, 0 ≤ t → R ≤ barrier L b (γ t) → barrier L b (γ t) ≤ R' → ∀ i : ι,
      L i (γ t) - b i = barrier L b (γ t) → L i (v t) ≤ 0) :
    ∀ t, 0 ≤ t → barrier L b (γ t) ≤ R := by
  refine le_of_dini_slope_nonpos_in_band hRR'
    ((continuous_barrier L b).comp_continuousOn hγcont) hstart ?_
  intro t ht hlevel hband r hr
  exact eventually_barrier_lt_of_active_descent hγcont ht (hγ t ht)
    (hdesc t ht hlevel hband) hr

/-! ### Repackaging -/

/-- The trapping theorem in the `DifferentialInclusion.ForwardInvariant` interface: the guarded
polyhedron is forward invariant for any field whose admissible velocities make every active
piece nonincreasing at the level. -/
theorem forwardInvariant_barrierSublevel
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {R : ℝ} {F : DifferentialInclusion.Field E}
    (hdesc : ∀ y : E, R ≤ barrier L b y → ∀ i : ι,
      L i y - b i = barrier L b y → ∀ c ∈ F y, L i c ≤ 0) :
    DifferentialInclusion.ForwardInvariant F {x : E | barrier L b x ≤ R} := by
  intro γ hγ h0 t ht
  have hγcont : ContinuousOn γ (Set.Ici 0) := by
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun s => ?_)
    exact (hγ s).1.continuousAt
  refine barrier_le_of_local_descent (v := fun s => deriv γ s) hγcont
    (fun s _ => (hγ s).1) h0 ?_ t ht
  intro s _ hlevel i hi
  exact hdesc (γ s) hlevel i hi (deriv γ s) (hγ s).2

/-- **Descent from a cone condition on the field.**  Suppose each piece `i` comes with a set
`Λ i` of functionals containing its own normal `L i`, and suppose that wherever piece `i` is
active at the level, every admissible velocity is annihilated-or-decreased by *every* functional
of `Λ i`.  Then the guarded polyhedron is forward invariant.

This is the shape the toric differential inclusion supplies: at a point whose log-coordinates
lie in a fan cone `C`, the admissible velocities form (a subcone of) the polar cone of `C`, so
taking `Λ i = C` and `L i ∈ C` gives the descent inequality for free.  Craciun's Lemma 9.5 is
exactly the requirement `L i ∈ C`: the outer normal of the separating hypersurface at a point
must lie in the fan cone containing that point. -/
theorem forwardInvariant_of_cone_descent
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {R : ℝ} {F : DifferentialInclusion.Field E}
    {Λ : ι → Set (E →L[ℝ] ℝ)}
    (hmem : ∀ i : ι, L i ∈ Λ i)
    (hpolar : ∀ y : E, R ≤ barrier L b y → ∀ i : ι,
      L i y - b i = barrier L b y → ∀ c ∈ F y, ∀ M ∈ Λ i, M c ≤ 0) :
    DifferentialInclusion.ForwardInvariant F {x : E | barrier L b x ≤ R} :=
  forwardInvariant_barrierSublevel fun y hy i hi c hc =>
    hpolar y hy i hi c hc (L i) (hmem i)

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {κ : Type*} [Fintype κ] [Nonempty κ]

open scoped RealInnerProductSpace

/-- **Polar-cone form of the descent criterion.**  The normals `n i` are vectors, each lying in
a cone `K i`, and where piece `i` is active the admissible velocities lie in the polar cone of
`K i` (`⟪x, c⟫ ≤ 0` for every `x ∈ K i`).  Then the guarded polyhedron traps the flow.

Note the sign convention: `CRNT.coneDual` is the *dual* cone (`0 ≤ ⟪x, y⟫`), so a field valued in
`coneDual (K i)` satisfies this hypothesis with the normals `-n i`. -/
theorem forwardInvariant_of_polar_descent
    {n : κ → H} {b : κ → ℝ} {R : ℝ} {F : DifferentialInclusion.Field H} {K : κ → Set H}
    (hn : ∀ i : κ, n i ∈ K i)
    (hpolar : ∀ y : H, R ≤ barrier (fun i => innerSL ℝ (n i)) b y → ∀ i : κ,
      ⟪n i, y⟫ - b i = barrier (fun i => innerSL ℝ (n i)) b y →
      ∀ c ∈ F y, ∀ x ∈ K i, ⟪x, c⟫ ≤ 0) :
    DifferentialInclusion.ForwardInvariant F
      {x : H | barrier (fun i => innerSL ℝ (n i)) b x ≤ R} := by
  refine forwardInvariant_barrierSublevel ?_
  intro y hy i hi c hc
  simpa using hpolar y hy i (by simpa using hi) c hc (n i) (hn i)

end InnerProduct

/-- **Wiring lemma.**  If the guarded polyhedron misses the open `r`-ball about a point `p`, a
trajectory that starts inside it stays at distance at least `r` from `p` forever.  With `p = 0`
this is exactly the persistence conclusion consumed by
`CRNT.DifferentialInclusion.ZeroSeparatingSurfaceExists.away_from_origin`. -/
theorem dist_ge_of_local_descent
    {L : ι → (E →L[ℝ] ℝ)} {b : ι → ℝ} {R r : ℝ} {γ : ℝ → E} {v : ℝ → E} {p : E}
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (v t) t)
    (hstart : barrier L b (γ 0) ≤ R)
    (hdesc : ∀ t, 0 ≤ t → R ≤ barrier L b (γ t) → ∀ i : ι,
      L i (γ t) - b i = barrier L b (γ t) → L i (v t) ≤ 0)
    (hsep : {x : E | barrier L b x ≤ R} ⊆ (Metric.ball p r)ᶜ) :
    ∀ t, 0 ≤ t → r ≤ dist (γ t) p := by
  intro t ht
  have hmem : γ t ∈ {x : E | barrier L b x ≤ R} :=
    barrier_le_of_local_descent hγcont hγ hstart hdesc t ht
  have := hsep hmem
  simpa [Metric.mem_ball, not_lt] using this

/-! ### Non-convex barriers: minima of polyhedral barriers

A single `barrier` guards a *convex* polyhedron, and convexity is a real restriction here.  Asking
for one affine piece per fan cone, each with its normal inside its own cone, forces the family of
normals to be the face points of a polytope whose normal fan refines the given fan — and constant
level offsets cannot repair a violation, because the deficit between two competing pieces grows
linearly in `‖x‖`.  For a hyperplane-generated fan the natural candidate is the zonotope
`∑ⱼ [-aⱼ, aⱼ]`, whose normal fan *is* the arrangement fan; but its vertices need not lie in their
own normal cones.  With `a₀ = (1,0), …, a₁₀` at one degree apart and one further normal near
`178°`, the all-positive sign vector is realizable while
`a₁₇₈ · ∑ⱼ σⱼ aⱼ < 0`, so that vertex falls outside its cone.

Craciun's zero-separating hypersurface is *not* convex: it is a radial graph assembled from tiles,
each carrying its own normal, valid only on its own tile.  A minimum of polyhedral barriers
describes exactly such a region — every piecewise-affine function is a min of maxes of affine
functions — and the trapping argument is, if anything, easier: only **one** branch has to descend,
namely a branch attaining the minimum.
-/

section MinMax

variable {ι' : Type*} [Fintype ι'] [Nonempty ι']

/-- A minimum of polyhedral barriers: `x ↦ min k (max i (L k i x - b k i))`.  Its sublevel sets
are finite unions of convex polyhedra, so the guarded region need not be convex. -/
noncomputable def minMaxBarrier (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) (x : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun k => barrier (L k) (b k) x

theorem minMaxBarrier_le (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) (x : E) (k : ι') :
    minMaxBarrier L b x ≤ barrier (L k) (b k) x :=
  Finset.inf'_le (fun k => barrier (L k) (b k) x) (Finset.mem_univ k)

/-- Some branch attains the minimum: the *active branch* at `x`. -/
theorem exists_min_branch (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) (x : E) :
    ∃ k : ι', barrier (L k) (b k) x = minMaxBarrier L b x := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι'))
      fun k => barrier (L k) (b k) x
  exact ⟨k, hk.symm⟩

theorem continuous_minMaxBarrier (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) :
    Continuous (minMaxBarrier L b) := by
  refine Continuous.finset_inf'_apply (f := fun k (x : E) => barrier (L k) (b k) x)
    Finset.univ_nonempty ?_
  intro k _
  exact continuous_barrier (L k) (b k)

theorem isClosed_minMaxSublevel (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) (R : ℝ) :
    IsClosed {x : E | minMaxBarrier L b x ≤ R} :=
  isClosed_le (continuous_minMaxBarrier L b) continuous_const

/-- A one-branch minimum is just that branch's barrier. -/
theorem minMaxBarrier_unique [Unique ι'] (L : ι' → ι → (E →L[ℝ] ℝ)) (b : ι' → ι → ℝ) (x : E) :
    minMaxBarrier L b x = barrier (L default) (b default) x := by
  obtain ⟨k, hk⟩ := exists_min_branch L b x
  rw [Unique.eq_default k] at hk
  exact hk.symm

/-- A min-max barrier is below a level exactly when some branch is. -/
theorem minMaxBarrier_le_iff {L : ι' → ι → (E →L[ℝ] ℝ)} {b : ι' → ι → ℝ} {x : E} {c : ℝ} :
    minMaxBarrier L b x ≤ c ↔ ∃ k : ι', barrier (L k) (b k) x ≤ c := by
  rw [minMaxBarrier, Finset.inf'_le_iff]
  exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, Finset.mem_univ k, h⟩⟩

/-- **A non-convex polyhedral barrier with local descent traps the forward trajectory.**

At a time where the region's boundary level has been reached it is enough that *one* branch
attaining the minimum has all of its active pieces nonincreasing along the velocity.  The other
branches, and the inactive pieces of the chosen branch, are unconstrained.

This is the trapping criterion a tile-by-tile zero-separating hypersurface satisfies: each tile is
one branch, its normal is the active piece there, and the toric differential inclusion puts the
velocity in the polar cone of the fan cone carrying that normal. -/
theorem minMaxBarrier_le_of_local_descent
    {L : ι' → ι → (E →L[ℝ] ℝ)} {b : ι' → ι → ℝ} {R : ℝ} {γ : ℝ → E} {v : ℝ → E}
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (v t) t)
    (hstart : minMaxBarrier L b (γ 0) ≤ R)
    (hdesc : ∀ t, 0 ≤ t → R ≤ minMaxBarrier L b (γ t) → ∃ k : ι',
      barrier (L k) (b k) (γ t) = minMaxBarrier L b (γ t) ∧
      ∀ i : ι, L k i (γ t) - b k i = barrier (L k) (b k) (γ t) → L k i (v t) ≤ 0) :
    ∀ t, 0 ≤ t → minMaxBarrier L b (γ t) ≤ R := by
  refine le_of_dini_slope_nonpos_at_level
    ((continuous_minMaxBarrier L b).comp_continuousOn hγcont) hstart ?_
  intro t ht hlevel r hr
  obtain ⟨k, hk, hact⟩ := hdesc t ht hlevel
  have hbr := eventually_barrier_lt_of_active_descent (L := L k) (b := b k)
    hγcont ht (hγ t ht) hact hr
  filter_upwards [hbr] with z hz
  calc minMaxBarrier L b (γ z) ≤ barrier (L k) (b k) (γ z) := minMaxBarrier_le _ _ _ k
    _ < barrier (L k) (b k) (γ t) + r * (z - t) := hz
    _ = minMaxBarrier L b (γ t) + r * (z - t) := by rw [hk]

/-- The non-convex trapping theorem in the `DifferentialInclusion.ForwardInvariant` interface. -/
theorem forwardInvariant_minMaxSublevel
    {L : ι' → ι → (E →L[ℝ] ℝ)} {b : ι' → ι → ℝ} {R : ℝ} {F : DifferentialInclusion.Field E}
    (hdesc : ∀ y : E, R ≤ minMaxBarrier L b y → ∀ c ∈ F y, ∃ k : ι',
      barrier (L k) (b k) y = minMaxBarrier L b y ∧
      ∀ i : ι, L k i y - b k i = barrier (L k) (b k) y → L k i c ≤ 0) :
    DifferentialInclusion.ForwardInvariant F {x : E | minMaxBarrier L b x ≤ R} := by
  intro γ hγ h0 t ht
  have hγcont : ContinuousOn γ (Set.Ici 0) :=
    Continuous.continuousOn (continuous_iff_continuousAt.2 fun s => (hγ s).1.continuousAt)
  refine minMaxBarrier_le_of_local_descent (v := fun s => deriv γ s) hγcont
    (fun s _ => (hγ s).1) h0 ?_ t ht
  intro s _ hlevel
  exact hdesc (γ s) hlevel (deriv γ s) (hγ s).2

/-- **Wiring lemma, non-convex form.**  A trajectory trapped in a guarded region that misses the
open `r`-ball about `p` stays at distance at least `r` from `p` forever. -/
theorem dist_ge_of_minMax_local_descent
    {L : ι' → ι → (E →L[ℝ] ℝ)} {b : ι' → ι → ℝ} {R r : ℝ} {γ : ℝ → E} {v : ℝ → E} {p : E}
    (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (v t) t)
    (hstart : minMaxBarrier L b (γ 0) ≤ R)
    (hdesc : ∀ t, 0 ≤ t → R ≤ minMaxBarrier L b (γ t) → ∃ k : ι',
      barrier (L k) (b k) (γ t) = minMaxBarrier L b (γ t) ∧
      ∀ i : ι, L k i (γ t) - b k i = barrier (L k) (b k) (γ t) → L k i (v t) ≤ 0)
    (hsep : {x : E | minMaxBarrier L b x ≤ R} ⊆ (Metric.ball p r)ᶜ) :
    ∀ t, 0 ≤ t → r ≤ dist (γ t) p := by
  intro t ht
  have hmem : γ t ∈ {x : E | minMaxBarrier L b x ≤ R} :=
    minMaxBarrier_le_of_local_descent hγcont hγ hstart hdesc t ht
  simpa [Metric.mem_ball, not_lt] using hsep hmem

end MinMax

end PolyhedralBarrier
end CRNT
