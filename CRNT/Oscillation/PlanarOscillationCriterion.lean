import CRNT.Dynamics.CooperativeNetworks
import CRNT.Oscillation.Basic
import CRNT.Oscillation.PlanarPoincareBendixson
import CRNT.Examples.Lotka
import CRNT.Examples.LotkaPeriodic
import CRNT.Oscillation.RankTwoPlanar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A structural criterion for the absence of oscillations in planar mass-action systems

This module formalizes the **no-oscillation half** of the oscillation program: a *general
structural criterion* that rules out periodic orbits for a whole class of planar reaction
networks, rather than for one network at a time.

The classical result is the following.

> **Theorem (planar monotonicity).** Let `F : ℝ² → ℝ²` be a vector field which is
> *quasi-monotone* (Kamke) — `a ≤ b` and `aᵢ = bᵢ` imply `F aᵢ ≤ F bᵢ` — and let `x : ℝ → ℝ²`
> be a nonconstant periodic solution of `ẋ = F(x)`. Then no such solution exists: the
> solution must be constant.

In particular this holds when `F` is *order preserving* (`a ≤ b → F a ≤ F b`), which is the
hypothesis asked for in the field map (leaf D18). The proof is completely analytic — no planar
topology, no Jordan curve theorem, no Poincaré–Bendixson — and it is the reason the
criterion is a *structural* one:

* the orbit is `T`-periodic, so each coordinate is bounded and attains its extremal values;
* let `t₋` be a time of the minimum of the first coordinate and `t₊` a time of the maximum
  of the second coordinate.  Then `x t₋ ≤ x t₊` in the componentwise order, because the
  first coordinate of `x t₋` is minimal and the second coordinate of `x t₊` is maximal;
* the Kamke comparison principle (`CRNT.Monotone.kamke_comparison`) therefore gives
  `x s ≤ x (s + δ)` for all `s`, where `δ = t₊ - t₋`;
* the difference `x (s + δ) - x s` is a non-negative continuous `T`-periodic function with
  vanishing integral over a period, hence it vanishes identically: `δ` is a period of `x`;
* consequently `x t₋ = x t₊`, and the field vanishes at that common point (the first
  coordinate has a minimum there, the second a maximum);
* the constant solution through that point is then the *unique* solution there, again by
  the comparison principle, so `x` is constant.

The planar hypothesis is essential: the step "the minimum of the first coordinate is below
the maximum of the second coordinate" uses exactly two coordinates.

The plane is written as `Concentration (Fin 2) = Fin 2 → ℝ`; the order `≤` on it is the
componentwise order, exactly as `≤` on `ℝ × ℝ` in Mathlib.

## Contents

* `planarBox`, `mem_planarBox`, `sup_mem_planarBox` — the closed box `[lo, hi]` in the plane.
* `BoxedKamkeField` — a planar field which is quasi-monotone and Lipschitz on a box;
  `kamkeOn_box_of_monotone` and `kamkeOn_box_of_orthant` build such a field.
* `periodicSolution_constant_of_boxedKamke` — **the no-oscillation criterion.**
* `periodicSolution_constant_of_monotone` — the same for order-preserving fields, and
  `periodicSolution_constant_of_monotone_locallyLipschitz` for locally Lipschitz ones.
* `Network.boxedKamkeField_massAction_of_cooperative`,
  `Network.positivePeriodicOrbit_constant_of_cooperative`,
  `Network.neverPositivePeriodic_of_cooperative` — **the mass-action application:** a
  cooperative planar mass-action network has no positive periodic orbit.
* `Example` — a concrete cooperative planar network with every hypothesis checked.
* `massAction_contDiff_planar`,
  `omegaSet_contains_periodicTrajectory_of_kernelBundle` — the *conditional*
  Poincaré–Bendixson conclusion, isolating the universal kernel that is still open in the
  repository (see the last section).
* `lotka_stoichRank`, `lotka_hasPositivePeriodicOrbit_of_poincareBendixson` — the same
  reduction for a concrete planar mass-action network which *does* oscillate.
* `not_cooperative_lotka` — the sharpness check: the Lotka network, which does oscillate, is
  not covered by the criterion.

## Auxiliary lemmas

`exists_eq_add_int_mul`, `periodic_eq_int_mul` (reduction of a time to a fundamental
interval), `exists_extremal_times` (global extrema of the two coordinates of a periodic
trajectory), `isLocalMin_of_isGlobalMin`, `isLocalMax_of_isGlobalMax`,
`eq_zero_of_nonneg_of_integral_eq_zero` (a non-negative continuous function with vanishing
integral vanishes).

## What this formalizes of leaf D18

Leaf D18 asks for "general structural criteria for oscillation and chaos".  This file
supplies the structural **no-oscillation** criterion for the planar (two-species) case: a
cooperative planar mass-action network has `NeverPositivePeriodic`, i.e. it has no
`OscillatoryCapacity` whatsoever.  The complementary existence direction (an oscillation
criterion) still requires the universal planar kernel of
`CRNT.Oscillation.PlanarPoincareBendixson`, which is *not* discharged in this repository;
the last section of this file isolates exactly that residual and shows that the
network-specific side of the route (the `C¹` regularity of a mass-action field) is
discharged here.

Depends on: `CRNT.Dynamics.CooperativeNetworks`, `CRNT.Oscillation.Basic`,
`CRNT.Oscillation.PlanarPoincareBendixson`.
-/

namespace CRNT

namespace Oscillation

open Set Filter Topology
open scoped BigOperators NNReal

/-! ## Planar boxes -/

/-- The closed box `[lo, hi]` in the plane: the set of concentration vectors whose two
coordinates lie between `lo` and `hi`.  This is the two-dimensional analogue of
`Set.Icc` for a concentration vector. -/
def planarBox (lo hi : ℝ) : Set (Concentration (Fin 2)) := Set.Icc (fun _ => lo) (fun _ => hi)

@[simp] theorem mem_planarBox {lo hi : ℝ} {x : Concentration (Fin 2)} :
    x ∈ planarBox lo hi ↔ (∀ i : Fin 2, lo ≤ x i ∧ x i ≤ hi) := by
  rw [planarBox, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩ i
    rw [Pi.le_def] at h1 h2
    exact ⟨h1 i, h2 i⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Pi.le_def]; intro i; exact (h i).1
    · rw [Pi.le_def]; intro i; exact (h i).2

/-- A box is closed under the componentwise maximum, which is what the Kamke comparison
principle needs. -/
theorem sup_mem_planarBox {lo hi : ℝ} {a b : Concentration (Fin 2)}
    (ha : a ∈ planarBox lo hi) (hb : b ∈ planarBox lo hi) : a ⊔ b ∈ planarBox lo hi := by
  rw [mem_planarBox] at ha hb ⊢
  intro i
  constructor
  · rw [Pi.sup_apply]
    exact le_trans (ha i).1 (le_max_left (a i) (b i))
  · rw [Pi.sup_apply]
    exact max_le (ha i).2 (hb i).2

/-! ## Quasi-monotone planar fields -/

/-- **A quasi-monotone (Kamke) planar field on a box.**

The field is required to be Lipschitz on the box (the comparison principle needs a
Lipschitz bound) and to satisfy the Kamke condition there: `a ≤ b` and `a i = b i` imply
`F a i ≤ F b i`.  The second hypothesis is the *off-diagonal* monotonicity of a
cooperative system; it is implied by order preservation, which is the hypothesis used in
`periodicSolution_constant_of_monotone`. -/
structure BoxedKamkeField (F : Concentration (Fin 2) → Concentration (Fin 2)) (lo hi : ℝ) :
    Prop where
  /-- The field is Lipschitz on the box. -/
  lipschitz : ∃ L : ℝ≥0, LipschitzOnWith L F (planarBox lo hi)
  /-- The Kamke (quasi-monotonicity) condition on the box. -/
  kamke : Monotone.KamkeOn F (planarBox lo hi)

/-- **Order preservation implies the Kamke condition on any box.** -/
theorem kamkeOn_box_of_monotone {F : Concentration (Fin 2) → Concentration (Fin 2)}
    {lo hi : ℝ} (hmono : Monotone F) : Monotone.KamkeOn F (planarBox lo hi) := by
  intro a _ b _ hab i hi
  exact hmono hab i

/-- **The Kamke condition on the nonnegative orthant restricts to any box inside it.**  This is
the form used for mass-action networks, whose field is known to be quasi-monotone on the
nonnegative orthant (`CRNT.Network.massAction_kamkeOn_of_cooperative`). -/
theorem kamkeOn_box_of_orthant {F : Concentration (Fin 2) → Concentration (Fin 2)}
    (hK : Monotone.KamkeOn F {x | Concentration.Nonnegative x}) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (_hhi : lo ≤ hi) : Monotone.KamkeOn F (planarBox lo hi) := by
  intro a ha b hb hab i hi
  apply hK a ?_ b ?_ hab i hi
  · intro j
    exact le_trans hlo (mem_planarBox.mp ha j).1
  · intro j
    exact le_trans hlo (mem_planarBox.mp hb j).1

/-! ## Elementary time-periodicity tools -/

/-- Every real time is a representative in `[0, T]` plus an integer multiple of `T`. -/
theorem exists_eq_add_int_mul (T : ℝ) (s : ℝ) (hT : 0 < T) :
    ∃ u : ℝ, u ∈ Set.Icc 0 T ∧ ∃ k : ℤ, s = u + (k : ℝ) * T := by
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hcancel : T * (s / T) = s := by field_simp
  set k : ℤ := ⌊s / T⌋ with hk
  have h1 : (k : ℝ) ≤ s / T := by
    rw [hk]; exact_mod_cast Int.floor_le (s / T)
  have h2 : s / T < (k : ℝ) + 1 := by
    rw [hk]; exact_mod_cast Int.lt_floor_add_one (s / T)
  refine ⟨s - (k : ℝ) * T, ⟨?_, ?_⟩, k, ?_⟩
  · have hle : (k : ℝ) * T ≤ s := by
      have h := mul_le_mul_of_nonneg_left h1 hT.le
      rw [hcancel] at h
      simpa [mul_comm] using h
    linarith
  · have hlt : s < (k : ℝ) * T + T := by
      have h := mul_lt_mul_of_pos_left h2 hT
      rw [hcancel] at h
      linarith
    linarith
  · ring

/-- A `T`-periodic function takes the same value at `s` and at `s + k * T`. -/
theorem periodic_eq_int_mul {α : Type*} {f : ℝ → α} {T : ℝ} (hper : Function.Periodic f T)
    (s : ℝ) (k : ℤ) : f (s + (k : ℝ) * T) = f s := by
  have hz : Function.Periodic f ((k : ℤ) • T) := hper.zsmul k
  have heq : ((k : ℤ) • T : ℝ) = (k : ℝ) * T := by
    rw [zsmul_eq_mul]
  have h := hz.funext
  rw [heq] at h
  exact congrFun h s

/-- A global minimum of a real-valued function is a local minimum. -/
theorem isLocalMin_of_isGlobalMin {f : ℝ → ℝ} {a : ℝ} (h : ∀ y, f a ≤ f y) : IsLocalMin f a := by
  have hev : ∀ᶠ y in 𝓝 a, f a ≤ f y :=
    Filter.Eventually.filter_mono le_top (Filter.Eventually.of_forall h)
  exact hev

/-- A global maximum of a real-valued function is a local maximum. -/
theorem isLocalMax_of_isGlobalMax {f : ℝ → ℝ} {a : ℝ} (h : ∀ y, f y ≤ f a) : IsLocalMax f a := by
  have hev : ∀ᶠ y in 𝓝 a, f y ≤ f a :=
    Filter.Eventually.filter_mono le_top (Filter.Eventually.of_forall h)
  exact hev

/-- A continuous non-negative function on `[0, T]` with zero integral vanishes identically. -/
theorem eq_zero_of_nonneg_of_integral_eq_zero {g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hg : Continuous g) (hg0 : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hInt : ∫ s in 0..T, g s = 0) :
    ∀ s ∈ Set.Icc 0 T, g s = 0 := by
  by_contra hne
  obtain ⟨s, hrest⟩ := not_forall.mp hne
  obtain ⟨hsI, hsne⟩ := not_imp.mp hrest
  have hspos : 0 < g s := lt_of_le_of_ne (hg0 s hsI) (Ne.symm hsne)
  have hpos : 0 < ∫ u in 0..T, g u :=
    intervalIntegral.integral_pos hT hg.continuousOn
      (fun u hu => hg0 u ⟨le_of_lt hu.1, hu.2⟩) ⟨s, hsI, hspos⟩
  linarith

/-- **Extremal times of the two coordinates of a periodic trajectory.**

A `T`-periodic continuous trajectory is bounded, so both coordinates attain a minimum and a
maximum; the times are recorded together with the global extremal inequalities. -/
theorem exists_extremal_times (x : ℝ → Concentration (Fin 2))
    {T : ℝ} (hper : Function.Periodic x T) (hcont : Continuous x) (hT : 0 < T) :
    ∃ tmin0 tmax0 tmin1 tmax1 : ℝ,
      (∀ t, x t 0 ≥ x tmin0 0) ∧ (∀ t, x t 0 ≤ x tmax0 0) ∧
      (∀ t, x t 1 ≥ x tmin1 1) ∧ (∀ t, x t 1 ≤ x tmax1 1) := by
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_rfl, hT.le⟩⟩
  have hc0 : Continuous (fun t => x t 0) := (continuous_apply 0).comp hcont
  have hc1 : Continuous (fun t => x t 1) := (continuous_apply 1).comp hcont
  obtain ⟨tmin0, _, hmin0⟩ := hcpt.exists_isMinOn hne (f := fun t => x t 0) hc0.continuousOn
  obtain ⟨tmax0, _, hmax0⟩ := hcpt.exists_isMaxOn hne (f := fun t => x t 0) hc0.continuousOn
  obtain ⟨tmin1, _, hmin1⟩ := hcpt.exists_isMinOn hne (f := fun t => x t 1) hc1.continuousOn
  obtain ⟨tmax1, _, hmax1⟩ := hcpt.exists_isMaxOn hne (f := fun t => x t 1) hc1.continuousOn
  refine ⟨tmin0, tmax0, tmin1, tmax1, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T t hT
    have hval : x t 0 = x u 0 := by
      have h := periodic_eq_int_mul (f := x) hper u k
      rw [← hk] at h
      exact congrFun h 0
    rw [hval]
    exact hmin0 hu
  · intro t
    obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T t hT
    have hval : x t 0 = x u 0 := by
      have h := periodic_eq_int_mul (f := x) hper u k
      rw [← hk] at h
      exact congrFun h 0
    rw [hval]
    exact hmax0 hu
  · intro t
    obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T t hT
    have hval : x t 1 = x u 1 := by
      have h := periodic_eq_int_mul (f := x) hper u k
      rw [← hk] at h
      exact congrFun h 1
    rw [hval]
    exact hmin1 hu
  · intro t
    obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T t hT
    have hval : x t 1 = x u 1 := by
      have h := periodic_eq_int_mul (f := x) hper u k
      rw [← hk] at h
      exact congrFun h 1
    rw [hval]
    exact hmax1 hu

/-! ## The no-oscillation criterion -/

/-- **The planar no-oscillation criterion.**

A planar system whose field is quasi-monotone (Kamke) on a box containing the orbit has **no
nonconstant periodic solution**: every periodic solution is constant.

The hypotheses are

* `F` is Lipschitz on the box (needed by the comparison principle) and satisfies the Kamke
  condition there;
* `x : ℝ → Concentration (Fin 2)` is an exact solution of `ẋ = F(x)` on all of `ℝ`;
* `x` is `T`-periodic with `T > 0`;
* the orbit stays inside the box.

The conclusion is that `x` is a constant trajectory.  In the language of the oscillation
layer this says that a planar mass-action network whose field is quasi-monotone has no
`PositivePeriodicOrbit` at all. -/
theorem periodicSolution_constant_of_boxedKamke
    {F : Concentration (Fin 2) → Concentration (Fin 2)}
    {x : ℝ → Concentration (Fin 2)}
    (hsol : ∀ t, HasDerivAt x (F (x t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic x T)
    {lo hi : ℝ} (horizon : ∀ t, x t ∈ planarBox lo hi)
    (hK : BoxedKamkeField F lo hi) :
    ∃ p : Concentration (Fin 2), ∀ t, x t = p := by
  have hcont : Continuous x := continuous_iff_continuousAt.2 (fun t => (hsol t).continuousAt)
  obtain ⟨tmin, _, _, tmax, hmin, _, _, hmax⟩ := exists_extremal_times x hper hcont hT
  -- The extremal points are ordered: the point of minimal first coordinate lies below the
  -- point of maximal second coordinate in the componentwise order.
  have horder : x tmin ≤ x tmax := by
    refine Pi.le_def.2 fun i => ?_
    by_cases hi : i = 0
    · subst hi
      exact hmin tmax
    · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst hi1
      exact hmax tmin
  -- The two time translates of the orbit solve the same equation.
  have hsolmin : ∀ t, HasDerivAt (fun t => x (t + tmin)) (F (x (t + tmin))) t := by
    intro t
    have h := hsol (t + tmin)
    have hshift : HasDerivAt (fun u : ℝ => u + tmin) 1 t := by
      simpa using (hasDerivAt_id t).add_const tmin
    simpa [Function.comp_def] using h.scomp t hshift
  have hsolmax : ∀ t, HasDerivAt (fun t => x (t + tmax)) (F (x (t + tmax))) t := by
    intro t
    have h := hsol (t + tmax)
    have hshift : HasDerivAt (fun u : ℝ => u + tmax) 1 t := by
      simpa using (hasDerivAt_id t).add_const tmax
    simpa [Function.comp_def] using h.scomp t hshift
  obtain ⟨L, hLip⟩ := hK.lipschitz
  have hkamke : Monotone.KamkeOn F (planarBox lo hi) := by
    intro a ha b hb hab i hi
    exact hK.kamke a ha b hb hab i hi
  have hsup : ∀ a ∈ planarBox lo hi, ∀ b ∈ planarBox lo hi, a ⊔ b ∈ planarBox lo hi :=
    fun a ha b hb => sup_mem_planarBox ha hb
  -- The comparison principle: the orbit through the minimum of the first coordinate stays
  -- below the orbit through the maximum of the second coordinate.
  have hcomp : ∀ t ∈ Set.Icc 0 T, x (t + tmin) ≤ x (t + tmax) :=
    Monotone.kamke_comparison hLip hsup hkamke
      (fun t _ => (hsolmin t).hasDerivWithinAt) (fun t _ => (hsolmax t).hasDerivWithinAt)
      (fun t _ => horizon (t + tmin)) (fun t _ => horizon (t + tmax)) (by simpa using horder)
  -- Hence the orbit is ordered along the shift `δ = tmax - tmin`.
  have hshift_le : ∀ s : ℝ, x s ≤ x (s + (tmax - tmin)) := by
    intro s
    obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T (s - tmin) hT
    have h1 : x s = x (u + tmin) := by
      have h := periodic_eq_int_mul (f := x) hper (u + tmin) k
      have h' : s = (u + tmin) + (k : ℝ) * T := by linarith [hk]
      rw [h']
      exact h
    have h2 : x (s + (tmax - tmin)) = x (u + tmax) := by
      have h := periodic_eq_int_mul (f := x) hper (u + tmax) k
      have h' : s + (tmax - tmin) = (u + tmax) + (k : ℝ) * T := by linarith [hk]
      rw [h']
      exact h
    rw [h1, h2]
    exact hcomp u hu
  -- The shift is actually a period: the difference is non-negative and has vanishing integral.
  have hperiod : ∀ s : ℝ, x (s + (tmax - tmin)) = x s := by
    intro s
    have hcoordeq : ∀ i : Fin 2, x (s + (tmax - tmin)) i = x s i := by
      intro i
      have hg : Continuous (fun u => x (u + (tmax - tmin)) i - x u i) := by
        fun_prop
      have hg0 : ∀ u ∈ Set.Icc 0 T, 0 ≤ x (u + (tmax - tmin)) i - x u i := by
        intro u hu
        have h := hshift_le u
        exact sub_nonneg.mpr (h i)
      have hInt : ∫ u in 0..T, (fun u => x (u + (tmax - tmin)) i - x u i) u = 0 := by
        set f : ℝ → ℝ := fun u => x u i with hf
        have hper_f : Function.Periodic f T := by
          rw [hf]
          exact hper.comp (fun v : Concentration (Fin 2) => v i)
        have h1 : ∫ u in 0..T, f (u + (tmax - tmin)) = ∫ u in 0..T, f u := by
          rw [intervalIntegral.integral_comp_add_right]
          have h := hper_f.intervalIntegral_add_eq (0 + (tmax - tmin)) 0
          convert h using 1 <;> ring_nf
        have heq : (fun u => x (u + (tmax - tmin)) i - x u i)
            = fun u => f (u + (tmax - tmin)) - f u := by
          funext u; simp [hf]
        have hcontf : Continuous f := by
          rw [hf]
          exact (continuous_apply i).comp hcont
        have hcontg : Continuous (fun u => x (u + (tmax - tmin)) i) := by
          fun_prop
        rw [heq, intervalIntegral.integral_sub (hcontg.intervalIntegrable 0 T)
          (hcontf.intervalIntegrable 0 T), h1]
        simp
      have hz := eq_zero_of_nonneg_of_integral_eq_zero hT hg hg0 hInt
      -- extend from the fundamental interval to all times
      obtain ⟨v, hv, m, hm⟩ := exists_eq_add_int_mul T s hT
      have h1 : x s = x v := by
        have h := periodic_eq_int_mul (f := x) hper v m
        have h' : s = v + (m : ℝ) * T := by linarith [hm]
        rw [h']
        exact h
      have h2 : x (s + (tmax - tmin)) = x (v + (tmax - tmin)) := by
        have h := periodic_eq_int_mul (f := x) hper (v + (tmax - tmin)) m
        have h' : s + (tmax - tmin) = (v + (tmax - tmin)) + (m : ℝ) * T := by
          linarith [hm]
        rw [h']
        exact h
      rw [h1, h2]
      exact sub_eq_zero.mp (hz v hv)
    ext i
    exact hcoordeq i
  -- The extremal points coincide, and the field vanishes there.
  have hcoincide : x tmin = x tmax := by
    have h := hperiod tmin
    have h' : tmin + (tmax - tmin) = tmax := by ring
    rw [h'] at h
    exact h.symm
  have hmin' : IsLocalMin (fun t => x t 0) tmin := isLocalMin_of_isGlobalMin fun y => hmin y
  have hmax' : IsLocalMax (fun t => x t 1) tmax := isLocalMax_of_isGlobalMax fun y => hmax y
  have hzero0 : F (x tmin) 0 = 0 :=
    hmin'.hasDerivAt_eq_zero ((hasDerivAt_pi.mp (hsol tmin)) 0)
  have hzero1 : F (x tmax) 1 = 0 :=
    hmax'.hasDerivAt_eq_zero ((hasDerivAt_pi.mp (hsol tmax)) 1)
  have hFzero : F (x tmin) = 0 := by
    funext i
    by_cases hi : i = 0
    · subst hi
      exact hzero0
    · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst hi1
      rw [hcoincide]
      exact hzero1
  -- The constant solution through the extremal point is the only solution there.
  refine ⟨x tmin, ?_⟩
  have hsolc : ∀ t, HasDerivAt (fun _ : ℝ => x tmin) (F (x tmin)) t := by
    intro t
    have h := hasDerivAt_const t (x tmin)
    rw [hFzero]
    exact h
  have hcomp1 : ∀ t ∈ Set.Icc 0 T, x tmin ≤ x (t + tmin) :=
    Monotone.kamke_comparison hLip hsup hkamke
      (fun t _ => (hsolc t).hasDerivWithinAt) (fun t _ => (hsolmin t).hasDerivWithinAt)
      (fun t _ => horizon tmin) (fun t _ => horizon (t + tmin)) (by simp)
  have hcomp2 : ∀ t ∈ Set.Icc 0 T, x (t + tmin) ≤ x tmin :=
    Monotone.kamke_comparison hLip hsup hkamke
      (fun t _ => (hsolmin t).hasDerivWithinAt) (fun t _ => (hsolc t).hasDerivWithinAt)
      (fun t _ => horizon (t + tmin)) (fun t _ => horizon tmin) (by simp)
  intro t
  obtain ⟨u, hu, k, hk⟩ := exists_eq_add_int_mul T (t - tmin) hT
  have h1 : x t = x (u + tmin) := by
    have h := periodic_eq_int_mul (f := x) hper (u + tmin) k
    have h' : t = (u + tmin) + (k : ℝ) * T := by linarith [hk]
    rw [h']
    exact h
  rw [h1]
  exact le_antisymm (hcomp2 u hu) (hcomp1 u hu)

/-- **The no-oscillation criterion for order-preserving planar fields.**

This is the form asked for in the field map: `F` is *monotone* in the componentwise order
(`a ≤ b → F a ≤ F b`), which is stronger than the Kamke condition used by
`periodicSolution_constant_of_boxedKamke`.  No strictness of the monotonicity is needed: a
plain order-preserving planar field has no nonconstant periodic orbit. -/
theorem periodicSolution_constant_of_monotone
    {F : Concentration (Fin 2) → Concentration (Fin 2)} (hmono : Monotone F)
    {x : ℝ → Concentration (Fin 2)} (hsol : ∀ t, HasDerivAt x (F (x t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic x T)
    {lo hi : ℝ} (horizon : ∀ t, x t ∈ planarBox lo hi)
    (hLip : ∃ L : ℝ≥0, LipschitzOnWith L F (planarBox lo hi)) :
    ∃ p : Concentration (Fin 2), ∀ t, x t = p :=
  periodicSolution_constant_of_boxedKamke hsol hT hper horizon
    { lipschitz := hLip
      kamke := fun _ _ _ _ hab i _ => (Pi.le_def.mp (hmono hab)) i }

/-- **The no-oscillation criterion for locally Lipschitz order-preserving planar fields.**

The Lipschitz bound on the box is supplied by the local Lipschitz hypothesis. -/
theorem periodicSolution_constant_of_monotone_locallyLipschitz
    {F : Concentration (Fin 2) → Concentration (Fin 2)} (hmono : Monotone F)
    (hlip : LocallyLipschitz F)
    {x : ℝ → Concentration (Fin 2)} (hsol : ∀ t, HasDerivAt x (F (x t)) t)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic x T)
    {lo hi : ℝ} (horizon : ∀ t, x t ∈ planarBox lo hi) :
    ∃ p : Concentration (Fin 2), ∀ t, x t = p := by
  obtain ⟨L, hL⟩ := hlip.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := planarBox lo hi)
    (isCompact_Icc (a := (fun _ : Fin 2 => lo)) (b := fun _ => hi))
  exact periodicSolution_constant_of_monotone hmono hsol hT hper horizon ⟨L, hL⟩


/-! ## Application to mass-action networks -/

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The mass-action field of a cooperative planar network is quasi-monotone on every box
inside the nonnegative orthant.**

The Kamke condition is `CRNT.Network.massAction_kamkeOn_of_cooperative`; the Lipschitz bound
comes from the `C1` regularity of the mass-action field. -/
theorem boxedKamkeField_massAction_of_cooperative (N : Network (Fin 2)) (κ : N.RateConstants)
    (hcoop : N.IsCooperativeNetwork) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : lo ≤ hi) :
    BoxedKamkeField (N.massActionVectorField κ) lo hi := by
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ :=
      (N.massActionVectorField_contDiff κ (n := 1)).contDiffOn (s := planarBox lo hi)
        |>.exists_lipschitzOnWith (by simp) (convex_Icc _ _) isCompact_Icc
    exact ⟨L, hL⟩
  · exact kamkeOn_box_of_orthant (N.massAction_kamkeOn_of_cooperative κ hcoop) hlo hhi

/-- **A cooperative planar mass-action network has no positive periodic orbit.**

This is the structural no-oscillation criterion of leaf D18 for the planar case: the
conclusion is that the network has no `PositivePeriodicOrbit` for *any* choice of positive
rate constants. -/
theorem positivePeriodicOrbit_constant_of_cooperative
    {N : Network (Fin 2)} {κ : N.RateConstants} (hcoop : N.IsCooperativeNetwork)
    (P : N.PositivePeriodicOrbit κ) :
    ∃ p : Concentration (Fin 2), ∀ t, P.orbit t = p := by
  have hsol : ∀ t, HasDerivAt P.orbit (N.massActionVectorField κ (P.orbit t)) t := by
    intro t
    exact hasDerivAt_pi.mpr fun s => P.solution t s
  have hcont : Continuous P.orbit := continuous_iff_continuousAt.2 (fun t => (hsol t).continuousAt)
  obtain ⟨_, tmax0, _, tmax1, _, hmax0, _, hmax1⟩ :=
    exists_extremal_times P.orbit P.periodic hcont P.period_pos
  set hi : ℝ := max (P.orbit tmax0 0) (P.orbit tmax1 1)
  have hhi0 : 0 ≤ hi := le_max_of_le_left (P.positive tmax0 0).le
  have hhorizon : ∀ t, P.orbit t ∈ planarBox 0 hi := by
    intro t
    rw [mem_planarBox]
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      constructor
      · exact (P.positive t 0).le
      · exact le_trans (hmax0 t) (le_max_left _ _)
    · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi0
      subst hi1
      constructor
      · exact (P.positive t 1).le
      · exact le_trans (hmax1 t) (le_max_right _ _)
  exact periodicSolution_constant_of_boxedKamke hsol P.period_pos P.periodic hhorizon
    (boxedKamkeField_massAction_of_cooperative N κ hcoop (le_refl 0) hhi0)

/-- **Cooperative planar mass-action networks never oscillate.**

`Network.NeverPositivePeriodic` is the negation of `Network.OscillatoryCapacity`: no choice of
positive rate constants gives a positive nonconstant periodic orbit. -/
theorem neverPositivePeriodic_of_cooperative {N : Network (Fin 2)}
    (hcoop : N.IsCooperativeNetwork) : N.NeverPositivePeriodic := by
  intro κ hκ
  obtain ⟨P⟩ := hκ
  obtain ⟨p, hp⟩ := positivePeriodicOrbit_constant_of_cooperative hcoop P
  obtain ⟨t, ht⟩ := P.nonconstant
  rw [hp t, hp 0] at ht
  exact ht rfl

end Network


/-! ## A concrete instance

The network below is the simplest planar mass-action network which is *cooperative* and
*not* trivially so: the conversion `A → B` consumes `A` (so its source must be supported on
`{A}`) and the decay `B → 0` consumes `B`.  Every hypothesis of
`periodicSolution_constant_of_boxedKamke` is checked explicitly below. -/

namespace Example

/-- Two species, indexed by `Fin 2`. -/
abbrev Species : Type := Fin 2

/-- The substrate `A`. -/
abbrev A : Species := 0

/-- The product `B`. -/
abbrev B : Species := 1

/-- Four reactions, indexed by `Fin 4`. -/
abbrev Rxn : Type := Fin 4

/-- `0 → A`: inflow of substrate. -/
abbrev inflowA : Rxn := 0

/-- `0 → B`: inflow of product. -/
abbrev inflowB : Rxn := 1

/-- `A → B`: conversion of substrate into product. -/
abbrev convertAB : Rxn := 2

/-- `B → 0`: decay of product. -/
abbrev decayB : Rxn := 3

/-- The zero complex. -/
def c0 : Complex Species := ![0, 0]

/-- The complex `A`. -/
def cA : Complex Species := ![1, 0]

/-- The complex `B`. -/
def cB : Complex Species := ![0, 1]

/-- The reaction map. -/
def rxn : Rxn → Reaction Species :=
  ![{ source := c0, target := cA },
    { source := c0, target := cB },
    { source := cA, target := cB },
    { source := cB, target := c0 }]

/-- The example network. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- **The network is cooperative.**

The only reactions which decrease a species are `A → B` (which decreases `A` and has source
`A`) and `B → 0` (which decreases `B` and has source `B`); in both cases the source complex
is supported on the consumed species, which is exactly the definition of
`Network.IsCooperativeNetwork`. -/
theorem isCooperative : N.IsCooperativeNetwork := by
  intro r i hi j hj
  have hjval : j.val ≠ i.val := fun h => hj (Fin.ext h)
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [N, rxn, c0, cA, cB, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at hi hj ⊢;
    norm_num at hi

/-- **The first component of the mass-action field.** -/
theorem field_A (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x A = κ.k inflowA - κ.k convertAB * x A := by
  change (∑ r : Fin 4,
    κ.k r * (N.reaction r).source.massActionMonomial x *
      (((N.reaction r).target A : ℝ) - ((N.reaction r).source A : ℝ))) = _
  simp [Complex.massActionMonomial, N, rxn, c0, cA, cB, Fin.sum_univ_four, Fin.prod_univ_two]
  ring

/-- **The second component of the mass-action field.** -/
theorem field_B (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x B = κ.k inflowB + κ.k convertAB * x A - κ.k decayB * x B := by
  change (∑ r : Fin 4,
    κ.k r * (N.reaction r).source.massActionMonomial x *
      (((N.reaction r).target B : ℝ) - ((N.reaction r).source B : ℝ))) = _
  simp [Complex.massActionMonomial, N, rxn, c0, cA, cB, Fin.sum_univ_four, Fin.prod_univ_two]
  ring

/-- **The example network never oscillates.**

Every hypothesis of the no-oscillation criterion is discharged: the network is cooperative
(`isCooperative`), hence its mass-action field is quasi-monotone on the nonnegative orthant
and Lipschitz there (`CRNT.Network.massAction_kamkeOn_of_cooperative` and
`CRNT.Network.massActionVectorField_contDiff`), and a positive periodic orbit would be a
periodic solution of that field, which `periodicSolution_constant_of_boxedKamke` rules out. -/
theorem neverPositivePeriodic : N.NeverPositivePeriodic :=
  Network.neverPositivePeriodic_of_cooperative isCooperative

/-- **The example network has no oscillatory capacity.** -/
theorem not_oscillatoryCapacity : ¬ N.OscillatoryCapacity :=
  (N.neverPositivePeriodic_iff_not_oscillatoryCapacity.mp neverPositivePeriodic)

end Example


/-! ## The oscillation side: the conditional Poincaré--Bendixson route

The *existence* direction of leaf D18 goes through the planar Poincaré--Bendixson theorem.
That theorem is not yet available in this repository: the structure
`CRNT.Planar.PoincareBendixsonKernelBundle` collects three universal inputs, and **none of
them is discharged in the tree**:

* `flowRegularity : CanonicalFlowRegularityTarget` — the strict differentiability of the
  flow with respect to its initial point (the input of the flow-box inverse function
  theorem);
* `jordanSeparation : SimplePlanarLoop.JordanSeparationTarget` — the Jordan curve theorem;
* `straightEdgeLocalSide : StraightEdgeJordanSideTarget` — the local-side theorem for a
  straight boundary edge, together with the oriented triple increment and the finite
  chronological induction.

All three are *universal* statements: they do not mention a reaction network, a rate
constant or a trapping region.  No amount of network-specific work can discharge them —
they are the genuine planar-topology frontier of the repository.  What *can* be discharged,
and is discharged below, is the network-specific side of the route: the `C¹` regularity of
a mass-action field, which is the analytic hypothesis of the omega-limit classification.

The two theorems of this section therefore isolate the residual exactly: the network side
is done, the universal kernel is the only missing input. -/

/-- **The mass-action field of a planar network is `C¹`.**

This is the analytic hypothesis of the planar Poincaré--Bendixson route
(`CRNT.Planar.CanonicalFlowRegularityTarget` and
`CRNT.Planar.PoincareBendixsonOmegaClassificationTarget` both assume `ContDiff ℝ 1 field`),
and it is discharged here for every planar mass-action network. -/
theorem massAction_contDiff_planar (N : Network (Fin 2)) (κ : N.RateConstants) :
    ContDiff ℝ 1 (N.massActionVectorField κ) :=
  N.massActionVectorField_contDiff κ (n := 1)

/-- **Conditional end-to-end Poincaré--Bendixson for planar systems.**

Given the universal kernel bundle, the omega-limit set of a trapped planar orbit contains a
nonconstant periodic orbit.  For a planar mass-action network the `C¹` hypothesis is
`massAction_contDiff_planar`, so this is the complete reduction of the existence direction
of leaf D18 to the universal kernel. -/
theorem omegaSet_contains_periodicTrajectory_of_kernelBundle
    (K : Planar.PoincareBendixsonKernelBundle) {field : Phase2 → Phase2}
    (D : Planar.FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field) :
    ∃ P : PeriodicTrajectory field, P.orbitSet ⊆ D.omegaSet :=
  K.omegaClassification field D hsmooth



/-! ## The oscillation side: a concrete planar mass-action network

The Lotka network is the planar mass-action network which *does* oscillate
(`CRNT.Examples.LotkaPeriodic.oscillatoryCapacity`).  It has stoichiometric rank two, so
the rank-two reduction of `CRNT.Oscillation.RankTwoPlanar` puts it on the planar phase
space, and the end-to-end consumer
`CRNT.Network.hasPositivePeriodicOrbit_of_rankTwo_poincareBendixson` turns the planar
omega-limit classification into a *positive mass-action periodic orbit of the network*.

The following theorem is therefore the exact reduction of the existence direction of leaf
D18 for a concrete planar mass-action network: once the universal kernel bundle is
available, and once a trapping data for the reduced field with an omega-limit set inside
the positive chart region is certified, the Lotka network has a positive periodic orbit. -/

/-- **The stoichiometric rank of the Lotka network is two.** -/
theorem lotka_stoichRank : Examples.Lotka.N.stoichRank = 2 := by
  have h1 : 2 ≤ Examples.Lotka.N.stoichRank := Examples.Lotka.two_le_stoichRank
  have h2 : Examples.Lotka.N.stoichRank ≤ 2 := by
    simpa using Examples.Lotka.N.stoichRank_le_card
  exact le_antisymm h2 h1

/-- **Conditional end-to-end Poincaré--Bendixson for the Lotka network.**

Given the universal planar kernel bundle, a certified trapping data for the reduced
rank-two field of the Lotka network whose omega-limit set lies in the positive chart
region, and the `C¹` regularity of that reduced field, the Lotka network has a positive
periodic orbit. -/
theorem lotka_hasPositivePeriodicOrbit_of_poincareBendixson
    (K : Planar.PoincareBendixsonKernelBundle) (κ : Examples.Lotka.N.RateConstants)
    (x₀ : Concentration Examples.Lotka.Species)
    (D : Planar.FlowTrappingData
      (Examples.Lotka.N.rankTwoReducedField lotka_stoichRank κ x₀))
    (hsmooth : ContDiff ℝ 1
      (Examples.Lotka.N.rankTwoReducedField lotka_stoichRank κ x₀))
    (hpositive : D.omegaSet ⊆ Examples.Lotka.N.rankTwoPositiveRegion lotka_stoichRank x₀) :
    Examples.Lotka.N.HasPositivePeriodicOrbit κ :=
  Examples.Lotka.N.hasPositivePeriodicOrbit_of_rankTwo_poincareBendixson K.omegaClassification
    lotka_stoichRank κ x₀ D hsmooth hpositive

/-! ## Sharpness: the Lotka network is not covered by the criterion

A no-oscillation criterion is only useful if it does not exclude a network which does
oscillate.  The Lotka network `A → 2A`, `A + B → 2B`, `B → 0` is planar and has a positive
periodic orbit for every choice of positive rate constants
(`CRNT.Examples.LotkaPeriodic.oscillatoryCapacity`), and it is *not* cooperative: the
conversion `A + B → 2B` consumes `A` while its source complex also contains `B`. -/

/-- **The Lotka network is not cooperative.** -/
theorem not_cooperative_lotka : ¬ Examples.Lotka.N.IsCooperativeNetwork := by
  intro h
  have h1 : Examples.Lotka.N.reactionVector Examples.Lotka.prey Examples.Lotka.A = -1 := by
    simp [Examples.Lotka.N, Examples.Lotka.rxn, Examples.Lotka.cAB, Examples.Lotka.c2B]
  have h2 : (Examples.Lotka.N.reaction Examples.Lotka.prey).source Examples.Lotka.B = 1 := by
    simp [Examples.Lotka.N, Examples.Lotka.rxn, Examples.Lotka.cAB]
  have h3 : Examples.Lotka.B ≠ Examples.Lotka.A := by decide
  have h4 := h Examples.Lotka.prey Examples.Lotka.A (by rw [h1]; norm_num) Examples.Lotka.B h3
  rw [h2] at h4
  norm_num at h4

end Oscillation
end CRNT
