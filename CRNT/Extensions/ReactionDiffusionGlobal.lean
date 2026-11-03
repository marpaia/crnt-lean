import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Piecewise
import CRNT.Dynamics.FlowConstruction
import CRNT.Extensions.ReactionDiffusion

/-!
# Global existence for the semidiscrete reaction–diffusion system

This module adds **global existence** for the semidiscrete (method of lines) reaction–diffusion
system to the local existence theorem of `CRNT.Extensions.ReactionDiffusion`.

## The mathematical setting

The semidiscrete (method of lines) reading of a reaction–diffusion system is the ODE

```
ẋ = D Δ_h x + f(x),
```

on the finite dimensional space `ι → ℝ`, where `Δ_h` is the (box) Laplacian of the grid and
`f` is the reaction term.  Mathlib contains no PDE theory (no Sobolev spaces, no parabolic
maximal regularity), so the literal nonlinear PDE `∂_t x = D Δ x + f(x)` is out of reach; see
`CRNT.Extensions.ReactionDiffusion` for the semidiscrete backbone (the box Laplacian, the
semidiscrete field `reactionDiffusionField`, its Lipschitz constant, the *local* existence
theorem `exists_reactionDiffusion_solution`, the Jacobian `reactionDiffusionJacobian` and the
Turing connection `turing_connection`).

The classical fact about the ODE `ẋ = f(x)` that is used here is the **continuation
argument**: a *locally Lipschitz* field whose values grow at most *linearly*,
`‖f x‖ ≤ C (1 + ‖x‖)`, cannot blow up in finite time, so the local solution can be continued
past any finite time.  (Standard reference: G. Teschl, *Ordinary Differential Equations:
Dynamical Systems and an Introduction to the Theory of Linear ODEs*, §2.2.)  Mathlib's
`ODE.exists_flow` only covers *bounded* fields, because it glues the interval solutions
without any continuation argument; the present module supplies the missing continuation
machinery.

## What is formalized here

* **The growth bound of the semidiscrete field** (`reactionDiffusionField_growth_le`): the
  semidiscrete field satisfies `‖reactionDiffusionField D f x‖ ≤ C (1 + ‖x‖)`.  This is
  immediate from the Lipschitz estimate of the field, which is already available in
  `CRNT.Extensions.ReactionDiffusion`.
* **The continuation argument** (`exists_global_solution_of_linearGrowth`): a locally
  Lipschitz field on a Banach space with at most linear growth admits a solution of
  `ẋ = f x` through `x₀` on every interval `[0, T]`.  The proof is the classical one, in
  three pieces:
  * `exists_local_step`: one continuation step.  On the ball `closedBall v (1 + ‖v‖)` the
    field is bounded by `C (2 + 2‖v‖)`, and `C (2 + 2‖v‖) * (1/(2C)) = 1 + ‖v‖`; hence
    Mathlib's Picard–Lindelöf theorem (`IsPicardLindelof`) gives a solution on
    `[t, t + 1/(2C)]` through `v` at time `t`.
  * `hasDerivAt_paste`: the pasting of two solutions at a junction.  A solution approaching
    `t₀` from the left and a solution leaving `t₀` to the right agree in value at `t₀`, hence
    also in derivative, so the pasted curve solves the ODE at `t₀`.
  * `exists_solution_extend`: the extension of a solution from `[0, t₀]` to `[0, t₀ + 1/(2C)]`.
  The theorem itself is an induction over the number of steps, the pieces being pasted at the
  junctions.
* **Global existence for the semidiscrete system** (`exists_reactionDiffusion_solution_global`):
  for every `T ≥ 0` there is a solution of the semidiscrete ODE on `[0, T]`.

## What this module does **not** give

* No PDE well-posedness: no weak or strong solutions of the continuous PDE
  `∂_t x = D Δ x + f(x)`, no parabolic theory, no pattern selection.  This module is about
  the *semidiscrete* ODE only.
* No *flow* (`Flow ℝ≥0 (ι → ℝ)`) and no semigroup law for the semidiscrete system: the
  semigroup law requires uniqueness of the solution of the semidiscrete ODE from its initial
  value at the *endpoint* `0` (whereas Mathlib's uniqueness theorems
  `ODE_solution_unique_of_mem_Ioo`, `ODE_solution_unique_of_mem_Icc_right` need the common
  value either at an interior point or together with continuity on the closed interval), and
  the joint continuity required by the `Flow` structure needs the continuous dependence
  estimate for *global* solutions (`ODE.dist_le_of_isIntegralCurve`), i.e. a two-sided
  solution of the semidiscrete ODE.  Both ingredients are missing here.
* The growth bound and the continuation argument are stated for a *decoupled* reaction term
  `f i (w i)`, as in `CRNT.Extensions.ReactionDiffusion`.
-/

set_option maxHeartbeats 800000

namespace CRNT
namespace ReactionDiffusion

open scoped NNReal Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## The continuation argument for ODEs with linear growth -/

/-- **One continuation step.**  A field with at most linear growth is locally Lipschitz, so a
solution of `ẋ = f x` through `v` at time `t` exists on the interval `[t, t + δ]`, where
`δ = 1/(2C)` and `C` is the growth constant. -/
theorem exists_local_step {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) {δ : ℝ} (hδC : δ = 1 / (2 * C))
    (v : E) (t : ℝ) :
    ∃ α : ℝ → E, α t = v ∧
      ∀ s ∈ Set.Icc t (t + δ), HasDerivWithinAt α (f (α s)) (Set.Icc t (t + δ)) s := by
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hδ : 0 < δ := by rw [hδC]; positivity
  have hδ2 : (0:ℝ) ≤ δ := le_of_lt hδ
  have hCpos : (0:ℝ) ≤ C * (2 + 2 * ‖v‖) := by positivity
  have hvpos : (0:ℝ) ≤ 1 + ‖v‖ := by positivity
  have hpl : IsPicardLindelof (fun _ : ℝ => f)
      (⟨t, ⟨le_rfl, by linarith⟩⟩ : Set.Icc t (t + δ)) v
      (Real.toNNReal (1 + ‖v‖)) 0 (Real.toNNReal (C * (2 + 2 * ‖v‖))) K := by
    refine IsPicardLindelof.of_time_independent (hb := ?_) hl.lipschitzOnWith ?_
    · intro x hx
      have hxv : ‖x - v‖ ≤ ((Real.toNNReal (1 + ‖v‖) : ℝ≥0) : ℝ) := by
        have h := (Metric.mem_closedBall.mp hx)
        rw [dist_eq_norm] at h
        exact h
      have hxn : ‖x‖ ≤ ((Real.toNNReal (1 + ‖v‖) : ℝ≥0) : ℝ) + ‖v‖ := by
        calc ‖x‖ = ‖x - v + v‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - v‖ + ‖v‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have h1 : ‖f x‖ ≤ C * (1 + ‖x‖) := hgrow x
      have h2 : 1 + ‖x‖ ≤ 1 + (((Real.toNNReal (1 + ‖v‖) : ℝ≥0) : ℝ) + ‖v‖) := by linarith
      calc ‖f x‖ ≤ C * (1 + ‖x‖) := h1
        _ ≤ C * (1 + (((Real.toNNReal (1 + ‖v‖) : ℝ≥0) : ℝ) + ‖v‖)) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hC)
        _ = ((Real.toNNReal (C * (2 + 2 * ‖v‖)) : ℝ≥0) : ℝ) := by
          rw [Real.coe_toNNReal _ hCpos, Real.coe_toNNReal _ hvpos]
          ring
    · simp only [Real.coe_toNNReal _ hCpos, Real.coe_toNNReal _ hvpos, NNReal.coe_zero,
        sub_zero, add_sub_cancel_left, sub_self]
      rw [max_eq_left (by linarith [hδ2])]
      rw [hδC]
      have heq : C * (2 + 2 * ‖v‖) * (1 / (2 * C)) = 1 + ‖v‖ := by
        field_simp
      linarith
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα0, fun s hs => ?_⟩
  simpa using hα s hs

section Paste

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Pasting two solutions at a junction.**  If `x` solves the ODE up to `t₀` (from the left)
and `α` solves it from `t₀` on, and the two agree at `t₀`, then the pasted function solves the
ODE at `t₀` as well. -/
theorem hasDerivAt_paste {f : E → E} {x α y : ℝ → E} {a t₀ b : ℝ}
    (hat : a ≤ t₀) (htb : t₀ ≤ b) (hat' : a < t₀) (htb' : t₀ < b)
    (hleft : HasDerivWithinAt x (f (x t₀)) (Set.Icc a t₀) t₀)
    (hright : HasDerivWithinAt α (f (α t₀)) (Set.Icc t₀ b) t₀)
    (hmatch : α t₀ = x t₀)
    (hy : ∀ s, y s = if s ≤ t₀ then x s else α s) :
    HasDerivAt y (f (y t₀)) t₀ := by
  have hyl : y =ᶠ[𝓝[Set.Icc a t₀] t₀] x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s ≤ t₀ := by simpa using hs.2
    simp [hy, hst]
  have hleft' : HasDerivWithinAt y (f (x t₀)) (Set.Icc a t₀) t₀ :=
    hleft.congr_of_eventuallyEq hyl (by simp [hy])
  have hyr : y =ᶠ[𝓝[Set.Icc t₀ b] t₀] α := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : t₀ ≤ s := by simpa using hs.1
    by_cases h2 : s ≤ t₀
    · have : s = t₀ := by linarith
      subst this
      simp [hy, hmatch]
    · simp [hy, h2]
  have hright' : HasDerivWithinAt y (f (α t₀)) (Set.Icc t₀ b) t₀ :=
    hright.congr_of_eventuallyEq hyr (by simp [hy, hmatch])
  have hright'' : HasDerivWithinAt y (f (x t₀)) (Set.Icc t₀ b) t₀ := by
    have hfc : f (α t₀) = f (x t₀) := by rw [hmatch]
    rw [hfc] at hright'
    exact hright'
  have hleftF : HasFDerivWithinAt y (ContinuousLinearMap.toSpanSingleton ℝ (f (x t₀)))
      (Set.Icc a t₀) t₀ := hleft'.hasFDerivWithinAt
  have hrightF : HasFDerivWithinAt y (ContinuousLinearMap.toSpanSingleton ℝ (f (x t₀)))
      (Set.Icc t₀ b) t₀ := hright''.hasFDerivWithinAt
  have hunion : HasFDerivWithinAt y (ContinuousLinearMap.toSpanSingleton ℝ (f (x t₀)))
      (Set.Icc a t₀ ∪ Set.Icc t₀ b) t₀ := hleftF.union hrightF
  have hset : Set.Icc a t₀ ∪ Set.Icc t₀ b = Set.Icc a b :=
    Set.Icc_union_Icc_eq_Icc hat htb
  rw [hset] at hunion
  have hnh : Set.Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds hat' htb'
  have hfd : HasFDerivAt y (ContinuousLinearMap.toSpanSingleton ℝ (f (x t₀))) t₀ :=
    hunion.hasFDerivAt hnh
  have hderiv : HasDerivAt y (f (x t₀)) t₀ := by
    simpa using hfd.hasDerivAt
  simpa [hy] using hderiv

end Paste

/-- **Extension of a solution.**  A solution of `ẋ = f x` on `[0, t₀]` extends to a solution
on `[0, t₀ + δ]`, where `δ = 1/(2C)`. -/
theorem exists_solution_extend {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) {δ : ℝ} (hδC : δ = 1 / (2 * C))
    {x₀ : E} {t₀ a : ℝ} (ha0 : 0 ≤ a) (hat : a ≤ t₀) (hat' : a < t₀)
    (x : ℝ → E) (hx0 : x 0 = x₀)
    (hxd : ∀ s ∈ Set.Ioo 0 t₀, HasDerivAt x (f (x s)) s)
    (hxl : HasDerivWithinAt x (f (x t₀)) (Set.Icc a t₀) t₀) :
    ∃ y : ℝ → E, y 0 = x₀ ∧
      (∀ s ∈ Set.Ioo 0 (t₀ + δ), HasDerivAt y (f (y s)) s) ∧
      HasDerivWithinAt y (f (y (t₀ + δ))) (Set.Icc t₀ (t₀ + δ)) (t₀ + δ) := by
  have hδ : 0 < δ := by rw [hδC]; positivity
  obtain ⟨α, hα0, hα⟩ := exists_local_step hl hC hgrow hδC (x t₀) t₀
  set y : ℝ → E := fun s => if s ≤ t₀ then x s else α s with hydef
  have hy : ∀ s, y s = if s ≤ t₀ then x s else α s := by
    intro s; rw [hydef]
  have h0 : 0 ≤ t₀ := ha0.trans hat
  have hy0 : y 0 = x₀ := by simp [hy, h0, hx0]
  have hpaste : HasDerivAt y (f (y t₀)) t₀ := by
    refine hasDerivAt_paste (f := f) (b := t₀ + δ) hat (by linarith) hat' (by linarith) hxl ?_ ?_ hy
    · exact hα t₀ (Set.left_mem_Icc.2 (by linarith))
    · exact hα0
  have hys : ∀ s, s < t₀ → y =ᶠ[𝓝 s] x := by
    intro s hs
    filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
    have hu' : u < t₀ := by simpa using hu
    have hu'' : u ≤ t₀ := hu'.le
    simp [hy, hu'']
  have hys' : ∀ s, t₀ < s → y =ᶠ[𝓝 s] α := by
    intro s hs
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    have hu' : t₀ < u := by simpa using hu
    simp [hy, hu']
  refine ⟨y, hy0, ?_, ?_⟩
  · intro s hs
    have hs0 : 0 < s := hs.1
    have hst : s < t₀ + δ := hs.2
    by_cases hcase : s < t₀
    · have hderiv : HasDerivAt x (f (x s)) s := hxd s ⟨hs0, hcase⟩
      have heq : y =ᶠ[𝓝 s] x := hys s hcase
      have hderiv' : HasDerivAt y (f (x s)) s := hderiv.congr_of_eventuallyEq heq
      have hle : s ≤ t₀ := hcase.le
      simpa [hy, hle] using hderiv'
    · have hcase' : t₀ ≤ s := by linarith
      by_cases hcase2 : s = t₀
      · subst hcase2
        exact hpaste
      · have hlt2 : t₀ < s := lt_of_le_of_ne hcase' (Ne.symm hcase2)
        have hderiv : HasDerivWithinAt α (f (α s)) (Set.Icc t₀ (t₀ + δ)) s :=
          hα s ⟨hcase', hst.le⟩
        have hnh : Set.Icc t₀ (t₀ + δ) ∈ 𝓝 s := Icc_mem_nhds hlt2 hst
        have hderiv' : HasDerivAt α (f (α s)) s := hderiv.hasDerivAt hnh
        have heq : y =ᶠ[𝓝 s] α := hys' s hlt2
        have hderiv'' : HasDerivAt y (f (α s)) s := hderiv'.congr_of_eventuallyEq heq
        have hnot : ¬ s ≤ t₀ := by linarith
        simpa [hy, hnot] using hderiv''
  · have hαd : HasDerivWithinAt α (f (α (t₀ + δ))) (Set.Icc t₀ (t₀ + δ)) (t₀ + δ) :=
      hα (t₀ + δ) (Set.right_mem_Icc.2 (by linarith))
    have heq : y =ᶠ[𝓝[Set.Icc t₀ (t₀ + δ)] (t₀ + δ)] α := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu1 : t₀ ≤ u := by simpa using hu.1
      by_cases h2 : u ≤ t₀
      · have : u = t₀ := by linarith
        subst this
        simp [hy, hα0]
      · simp [hy, h2]
    have hval : y (t₀ + δ) = α (t₀ + δ) := by
      have : ¬ (t₀ + δ ≤ t₀) := by linarith
      simp [hy, this]
    have hres := hαd.congr_of_eventuallyEq heq hval
    rw [← hval] at hres
    exact hres

/-- **Global existence for a Lipschitz field with at most linear growth.**  If `f` is
Lipschitz and `‖f x‖ ≤ C (1 + ‖x‖)`, then for every `T ≥ 0` the initial value problem
`ẋ = f x`, `x 0 = x₀` has a solution on `[0, T]`.  This is the classical continuation
argument (Teschl, *Ordinary Differential Equations: Dynamical Systems and an Introduction to
the Theory of Linear ODEs*, §2.2): the solution is extended step by step, each step
lasting `1/(2C)`, and the pieces are pasted at the junctions. -/
theorem exists_global_solution_of_linearGrowth {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) (x₀ : E)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f (x t)) t := by
  set δ : ℝ := 1 / (2 * C) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hTdiv : 0 ≤ T / δ := div_nonneg hT (le_of_lt hδ)
  have hmain : ∀ n : ℕ, 1 ≤ n → ∃ x : ℝ → E, x 0 = x₀ ∧
      (∀ s ∈ Set.Ioo 0 ((n:ℝ) * δ), HasDerivAt x (f (x s)) s) ∧
      HasDerivWithinAt x (f (x ((n:ℝ) * δ))) (Set.Icc ((n:ℝ) * δ - δ) ((n:ℝ) * δ))
        ((n:ℝ) * δ) := by
    intro n
    induction n with
    | zero =>
      intro h
      omega
    | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst hn0
        have hone : ((0+1:ℕ):ℝ) * δ = δ := by
          simp [Nat.cast_one]
        rw [hone] at *
        obtain ⟨α, hα0, hα⟩ := exists_local_step hl hC hgrow hδdef x₀ 0
        refine ⟨α, hα0, ?_, ?_⟩
        · intro s hs
          have hs0 : 0 < s := hs.1
          have hs1 : s < δ := hs.2
          have hnh : Set.Icc 0 δ ∈ 𝓝 s := Icc_mem_nhds hs0 (by linarith)
          have hαs : HasDerivWithinAt α (f (α s)) (Set.Icc 0 δ) s := by
            simpa [zero_add] using hα s ⟨hs0.le, by linarith⟩
          exact hαs.hasDerivAt hnh
        · have hlast : HasDerivWithinAt α (f (α δ)) (Set.Icc (δ - δ) δ) δ := by
            have hmem : δ ∈ Set.Icc 0 (0 + δ) := ⟨by linarith, by linarith⟩
            have := hα δ hmem
            simpa [zero_add, sub_self] using this
          exact hlast
      · have hn1 : 1 ≤ n := by omega
        have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
        have ha0' : 0 ≤ (n:ℝ) * δ - δ := by
          have hring : (n:ℝ) * δ - δ = ((n:ℝ) - 1) * δ := by ring
          rw [hring]
          exact mul_nonneg (by linarith) (le_of_lt hδ)
        obtain ⟨x, hx0, hxd, hxl⟩ := ih hn1
        obtain ⟨y, hy0, hyd, hyl⟩ := exists_solution_extend (δ := δ) hl hC hgrow hδdef
          (a := (n:ℝ) * δ - δ) ha0' (by linarith) (by linarith)
          x hx0 hxd hxl
        refine ⟨y, hy0, ?_, ?_⟩
        · intro s hs
          have hcast : ((n+1:ℕ):ℝ) * δ = (n:ℝ) * δ + δ := by push_cast; ring
          have hs' : s ∈ Set.Ioo 0 ((n:ℝ) * δ + δ) := by
            rw [hcast] at hs
            exact hs
          apply hyd s hs'
        · have hcast : ((n+1:ℕ):ℝ) * δ = (n:ℝ) * δ + δ := by push_cast; ring
          have hsub : (n:ℝ) * δ + δ - δ = (n:ℝ) * δ := by ring
          simpa only [hcast, hsub] using hyl
  obtain ⟨N, hN1, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ T ≤ (N:ℝ) * δ := by
    refine ⟨Nat.ceil (T / δ) + 1, by omega, ?_⟩
    have h1 : T / δ ≤ (Nat.ceil (T / δ) : ℝ) := Nat.le_ceil (T / δ)
    have h1' : T / δ ≤ ((Nat.ceil (T / δ) + 1 : ℕ) : ℝ) := by
      have hle : (Nat.ceil (T / δ) : ℝ) ≤ ((Nat.ceil (T / δ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_succ _)
      exact h1.trans hle
    have h2 : (T / δ) * δ = T := by field_simp
    calc T = (T / δ) * δ := h2.symm
      _ ≤ ((Nat.ceil (T / δ) + 1 : ℕ) : ℝ) * δ :=
        mul_le_mul_of_nonneg_right h1' (le_of_lt hδ)
  obtain ⟨x, hx0, hxd, hxl⟩ := hmain N hN1
  refine ⟨x, hx0, ?_⟩
  intro t ht
  have ht1 : 0 < t := ht.1
  have ht2 : t < T := ht.2
  have htIcc : t ∈ Set.Ioo 0 ((N:ℝ) * δ) := ⟨by linarith, by linarith⟩
  exact hxd t htIcc

/-! ## The semidiscrete reaction–diffusion field -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The semidiscrete reaction–diffusion field has at most linear growth.**  There is a
constant `C` with `‖reactionDiffusionField D f x‖ ≤ C * (1 + ‖x‖)` for every `x`.  This is the
hypothesis the global existence theorem needs (Mathlib's `ODE.exists_flow` only covers
*bounded* fields). -/
theorem reactionDiffusionField_growth_le
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    [Nonempty ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖reactionDiffusionField D f x‖ ≤ C * (1 + ‖x‖) := by
  have hKreal : 0 ≤ L + diffusionLipschitzConst D := by
    have hconst : 0 ≤ diffusionLipschitzConst D := by
      dsimp [diffusionLipschitzConst, Dsup]
      have hDsup : (0:ℝ) ≤ Finset.sup' Finset.univ (Finset.univ_nonempty)
          (fun i : ι => |D i|) := by
        obtain ⟨i⟩ := (inferInstance : Nonempty ι)
        exact le_trans (abs_nonneg (D i))
          (Finset.le_sup' (fun i => |D i|) (Finset.mem_univ i))
      have hn : (0:ℝ) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by
        have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos)
        nlinarith [hcard1]
      exact mul_nonneg hDsup hn
    have hL0 : 0 ≤ L := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      have h := hf i (0:ℝ) 1
      have hone : |(0:ℝ) - 1| = 1 := by norm_num
      rw [hone] at h
      have h2 : L * 1 = L := by ring
      rw [h2] at h
      exact le_trans (abs_nonneg _) h
    linarith
  set Knn : NNReal := Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)) with hKnn
  have hKnn_eq : Knn = Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)) := rfl
  have hlipF : LipschitzWith Knn (reactionDiffusionField D f) := by
    rw [hKnn_eq]
    exact reactionDiffusionField_lipschitz D f L hf
  have hKnn_coe : (↑Knn : ℝ) = L + diffusionLipschitzConst D := by
    dsimp [Knn]
    rw [max_eq_right hKreal]
    exact Real.coe_toNNReal _ hKreal
  refine ⟨‖reactionDiffusionField D f 0‖ + (L + diffusionLipschitzConst D), ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ ‖reactionDiffusionField D f 0‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ L + diffusionLipschitzConst D := hKreal
    linarith
  · intro x
    have h1 : ‖reactionDiffusionField D f x - reactionDiffusionField D f 0‖
        ≤ (L + diffusionLipschitzConst D) * ‖x‖ := by
      have hdist := hlipF.dist_le_mul x 0
      rw [hKnn_coe] at hdist
      simpa [dist_eq_norm, sub_zero] using hdist
    have h2 : ‖reactionDiffusionField D f x‖
        ≤ ‖reactionDiffusionField D f 0‖ + (L + diffusionLipschitzConst D) * ‖x‖ := by
      have h := norm_add_le (reactionDiffusionField D f x - reactionDiffusionField D f 0)
        (reactionDiffusionField D f 0)
      rw [sub_add_cancel] at h
      have h' : ‖reactionDiffusionField D f x‖
          ≤ (L + diffusionLipschitzConst D) * ‖x‖ + ‖reactionDiffusionField D f 0‖ :=
        h.trans (add_le_add_left h1 _)
      rw [add_comm] at h'
      exact h'
    have h3 : (L + diffusionLipschitzConst D) * ‖x‖
        ≤ (L + diffusionLipschitzConst D) * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hKreal
    calc ‖reactionDiffusionField D f x‖
        ≤ ‖reactionDiffusionField D f 0‖ + (L + diffusionLipschitzConst D) * ‖x‖ := h2
      _ ≤ ‖reactionDiffusionField D f 0‖ + (L + diffusionLipschitzConst D) * (1 + ‖x‖) :=
        add_le_add_right h3 _
      _ ≤ (‖reactionDiffusionField D f 0‖ + (L + diffusionLipschitzConst D)) * (1 + ‖x‖) := by
        have hnonneg : (0:ℝ) ≤ ‖reactionDiffusionField D f 0‖ * ‖x‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith [hnonneg]

/-- **Global existence for the semidiscrete reaction–diffusion system.**  For every `T ≥ 0`
there is a solution of the semidiscrete ODE `ẋ = D Δ_h x + f(x)` on `[0, T]`. -/
theorem exists_reactionDiffusion_solution_global
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    (x₀ : ι → ℝ) [Nonempty ι] (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → (ι → ℝ), γ 0 = x₀ ∧
      ∀ t ∈ Set.Ioo 0 T, HasDerivAt γ (reactionDiffusionField D f (γ t)) t := by
  obtain ⟨C, hC, hgrowth⟩ := reactionDiffusionField_growth_le D f L hL hf
  have hKreal : 0 ≤ L + diffusionLipschitzConst D := by
    have hconst : 0 ≤ diffusionLipschitzConst D := by
      dsimp [diffusionLipschitzConst, Dsup]
      have hDsup : (0:ℝ) ≤ Finset.sup' Finset.univ (Finset.univ_nonempty)
          (fun i : ι => |D i|) := by
        obtain ⟨i⟩ := (inferInstance : Nonempty ι)
        exact le_trans (abs_nonneg (D i))
          (Finset.le_sup' (fun i => |D i|) (Finset.mem_univ i))
      have hn : (0:ℝ) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by
        have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos)
        nlinarith [hcard1]
      exact mul_nonneg hDsup hn
    have hL0 : 0 ≤ L := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      have h := hf i (0:ℝ) 1
      have hone : |(0:ℝ) - 1| = 1 := by norm_num
      rw [hone] at h
      have h2 : L * 1 = L := by ring
      rw [h2] at h
      exact le_trans (abs_nonneg _) h
    linarith
  have hlip : LipschitzWith (Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)))
      (reactionDiffusionField D f) :=
    reactionDiffusionField_lipschitz D f L hf
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_solution_of_linearGrowth
    (E := ι → ℝ) hlip (C := C + 1) (by linarith)
    (fun x => by
      have hx := hgrowth x
      calc ‖reactionDiffusionField D f x‖ ≤ C * (1 + ‖x‖) := hx
        _ ≤ (C + 1) * (1 + ‖x‖) := by
          have hnonneg : (0:ℝ) ≤ 1 * (1 + ‖x‖) := by positivity
          nlinarith [hnonneg]) x₀ T hT
  exact ⟨γ, hγ0, hγ⟩

/-- **A concrete instance.**  The one-site decay system `ẋ = -x` (no diffusion, one species) is a
semidiscrete reaction–diffusion system whose field is globally Lipschitz; hence it admits a
global solution.  This shows that `exists_reactionDiffusion_solution_global` is not vacuous. -/
theorem exists_decay_solution_global (x₀ : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → (Fin 1 → ℝ), γ 0 = (fun _ : Fin 1 => x₀) ∧
      ∀ t ∈ Set.Ioo 0 T, HasDerivAt γ (fun _ : Fin 1 => -(γ t 0)) t := by
  have hf : ∀ (i : Fin 1) x y, |(-x : ℝ) - (-y : ℝ)| ≤ (1:ℝ) * |x - y| := by
    intro i x y
    rw [show (-x : ℝ) - (-y : ℝ) = -(x - y) by ring, abs_neg]
    simp
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_reactionDiffusion_solution_global (ι := Fin 1) (D := fun _ => 0)
      (f := fun _ x => -x) (L := 1) (by norm_num) hf (x₀ := fun _ => x₀) T hT
  have hfield : ∀ t, reactionDiffusionField (fun _ : Fin 1 => 0) (fun _ x => -x) (γ t)
      = fun _ : Fin 1 => -(γ t 0) := by
    intro t
    funext i
    fin_cases i
    simp [reactionDiffusionField, laplacian]
  refine ⟨γ, ?_, ?_⟩
  · simpa using hγ0
  · intro t ht
    have hγt := hγ t ht
    rw [hfield] at hγt
    exact hγt

end ReactionDiffusion
end CRNT

/-! ## Axioms -/

#print axioms CRNT.ReactionDiffusion.exists_local_step
#print axioms CRNT.ReactionDiffusion.hasDerivAt_paste
#print axioms CRNT.ReactionDiffusion.exists_solution_extend
#print axioms CRNT.ReactionDiffusion.exists_global_solution_of_linearGrowth
#print axioms CRNT.ReactionDiffusion.reactionDiffusionField_growth_le
#print axioms CRNT.ReactionDiffusion.exists_reactionDiffusion_solution_global
#print axioms CRNT.ReactionDiffusion.exists_decay_solution_global
