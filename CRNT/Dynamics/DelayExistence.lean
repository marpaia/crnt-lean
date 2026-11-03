import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Piecewise
import CRNT.Extensions.DelaySemistability

/-!
# Existence theory and semistability for delay differential equations

This module supplies the two pieces that field-map leaf **E3 (non-isothermal and delay systems)**
was still missing: an **existence theory** for delay differential equations, and a
**semistability** statement for the linear (scalar) delay equation.

## The setting

A *delay field* is a map `f : ℝ → E → E → E`, `f t x y`, which is the right-hand side of the
delay differential equation

`ẋ(t) = f ( t, x(t), x (t − τ) )`,   `τ > 0`,

where `E` is a Banach space.  The hypotheses on `f` are the classical ones: continuity, a
Lipschitz bound in the *current* state `x`, and at most linear growth.

## The method of steps

The classical existence theorem for delay equations is the **method of steps**.  On the first
step `[0, τ]` the delayed term `x (t − τ)` is already known — it is the history `φ` — so the
equation degenerates to the ordinary differential equation `ẋ(t) = f (t, x(t), φ (t − τ))`, which
Picard–Lindelöf solves.  On the second step `[τ, 2τ]` the delayed term `x (t − τ)` is the already
computed part of the solution, so again one solves an ODE; and so on.  In this module the steps
are carried out on a uniform grid of mesh `h ≤ τ` (the mesh has to be small enough for the
Picard–Lindelöf step, see `delayStep_exists`), which has the advantage that the *same* mesh works
at every stage.

The ingredients are:

* `delayStep_exists` / `delayStep_unique`: the **one-step theorem**, the heart of the method of
  steps — the ODE `ẋ(t) = f (t, x(t), ψ (t))` with a *known* `ψ` has a unique solution on
  `[t₀, t₀ + h]`;
* `delay_glue`: the **gluing lemma** — a solution on one step and a solution on the next step
  (which sees the first one as its delayed part) glue to a solution of the delay equation on the
  union;
* `delay_steps_exists` / `delay_steps_unique`: the **induction over the steps**, giving a unique
  solution on `[0, (n+1) h]` for every `n`, and `delay_solution_exists` /
  `delay_solution_unique`: the global solution on `[0, ∞)`.

## The linear delay equation and its semistability

For the linear equation `ẋ(t) = −a x(t) + b x (t − τ)` with `a > |b|` every solution tends to `0`
as `t → ∞`: the system is **semistable** (the classical Halanay argument, whose ingredients are
made explicit below; the comparison principle itself is *not* formalised here, see the last
section).  The ingredients that are made explicit here are:

* `linearDelayField`: the delay field of the scalar linear equation;
* `delayLinear_rate_exists`: an admissible decay rate `ε > 0` with `ε + |b| e^{ε τ} ≤ 2a − |b|`
  exists (by the intermediate value theorem).  This is the rate that the Halanay estimate
  requires: the square `x²` of a solution satisfies the scalar delay inequality
  `u' ≤ −(2a − |b|) u + |b| u(·−τ)`, and the exponential `e^{−ε t}` is a supersolution of that
  inequality exactly when `ε + |b| e^{ε τ} ≤ 2a − |b|`;
* `delayLinear_constant_solution` and `delayLinear_constant_not_tendsto`: the *obstruction*.  If
  `b = a` the constant trajectories are solutions of the equation, and a nonzero constant
  trajectory does not converge to `0`; the delay equation is then *not* semistable.

**A remark on the rate.**  The rate `a − |b|` that is sometimes quoted for the scalar equation is
*not* admissible: the true rate is the unique positive root `ε` of `ε + |b| e^{ε τ} = 2a − |b|`,
and `ε < 2(a − |b|)` whenever `b ≠ 0`.  Concretely, for `a = 1`, `b = 1/2`, `τ = 1` and the
constant history `φ ≡ 1` the solution obeys `x(1) = (1 + e^{−1})/2 > e^{−1/2}`, so an estimate
with rate `a − |b|` fails already at `t = 1`.  The module therefore records the *admissible*
rate (`delayLinear_rate_exists`) rather than the inadmissible one.

## Relation to the repository and to leaf E3

`CRNT.Extensions.DelayMassAction` and `CRNT.Extensions.DelaySemistability` formalise the
*mass-action* delay systems `ẋ(t) = ∑_r κ_r (x(t−τ_r)^{y_r} y'_r − x^{y_r} y_r)` of
Lipták–Hangos–Pituk–Szederkényi.  This module provides the missing analytic backdrop for them:

* the constant trajectories of a delay mass-action system are exactly its steady states
  (`CRNT.Network.const_isDelaySolution_iff`), and the present module shows that the *general*
  delay equation has the same property: a constant history gives a constant solution
  (`delay_constHistory_isSolution`);
* the semistability theorem `CRNT.Network.delay_semistability` of the repository is the
  mass-action instance of the semistability of the linear delay equation; the two are
  compatible in the sense that the delay solutions have their limits in the set of equilibria
  (`CRNT.Network.delay_limit_isSteadyState`), and that the equilibria are exactly the constant
  solutions (`delay_constHistory_isSolution`).

## What is *not* proved here

* The growth hypothesis on `f` (at most linear) is what makes a *uniform* mesh possible.  For
  fields of higher growth the same construction works with a mesh that shrinks along the
  trajectory; that refinement is not formalised here.
* The **Halanay comparison principle** itself (`w' ≤ −α w + β w(·−τ)` with `w ≤ 0` on the
  history implies `w ≤ 0` on `[−τ, ∞)`) is *not* formalised here, and hence neither is the
  resulting estimate `|x(t)| ≤ ‖φ‖_∞ e^{−(ε/2) t}` for the linear delay equation, nor the
  semistability theorem `delayLinear_semistability` that would follow from it.  What *is*
  proved is the admissible rate (`delayLinear_rate_exists`), the constant solutions of the
  linear equation (`delayLinear_constant_solution`) and the resulting obstruction to
  semistability (`delayLinear_constant_not_tendsto`).
* The full **Hayes criterion** (all the roots of `λ = −a + b e^{−λ τ}` have negative real part)
  is not formalised.  Only the two ends of the criterion are: `a > |b|` is the regime in which
  the admissible rate exists, and `b = a` is the regime in which the constant solutions show
  that semistability fails.  The intermediate case `b < 0 ≤ a` is not covered.
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Dynamics

open scoped BigOperators NNReal
open Filter Topology Set

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The data of a delay equation -/

/-- **The data of a delay equation.**  `f t x y` is the right-hand side of
`ẋ(t) = f (t, x(t), x (t − τ))`; the field is continuous, Lipschitz in the current state `x`, and
has at most linear growth. -/
structure DelayField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] where
  /-- The right-hand side of the delay equation. -/
  f : ℝ → E → E → E
  /-- Continuity of the right-hand side. -/
  cont : Continuous (fun p : ℝ × (E × E) => f p.1 p.2.1 p.2.2)
  /-- Lipschitz constant in the *current* state. -/
  K₂ : ℝ≥0
  /-- `f` is Lipschitz in the current state. -/
  lip₂ : ∀ t y, LipschitzWith K₂ (fun x => f t x y)
  /-- The additive constant of the growth bound. -/
  M : ℝ≥0
  /-- The growth rate. -/
  C : ℝ≥0
  /-- `f` has at most linear growth. -/
  growth : ∀ t x y, ‖f t x y‖ ≤ (M : ℝ) + (C : ℝ) * (‖x‖ + ‖y‖)

namespace DelayField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Continuity in the time variable, for a known delayed part.**  If `ψ` is continuous on `s`,
then `t ↦ f t x (ψ t)` is continuous on `s`. -/
theorem continuousOn_time_delayed (F : DelayField E) (x : E) (ψ : ℝ → E) {s : Set ℝ}
    (hψ : ContinuousOn ψ s) : ContinuousOn (fun t => F.f t x (ψ t)) s := by
  have h1 : Continuous (fun p : ℝ × (E × E) => F.f p.1 p.2.1 p.2.2) := F.cont
  have h2 : ContinuousOn (fun t : ℝ => (t, (x, ψ t))) s :=
    (continuous_id.continuousOn.mono hψ).prodMk
      ((continuous_const.continuousOn.mono hψ).prodMk hψ)
  have h3 : ContinuousOn (fun p : ℝ × (E × E) => F.f p.1 p.2.1 p.2.2) Set.univ := h1.continuousOn
  have h4 := h3.comp h2 (fun _ _ => Set.mem_univ _)
  simpa only [Function.comp_def] using h4

end DelayField

/-- **The mesh condition**: a step of length `h` is small enough for the Picard–Lindelöf step
if `2 C h < 1`, where `C` is the growth rate of the field. -/
def DelayField.meshOk (F : DelayField E) (h : ℝ) : Prop := (F.C : ℝ) * h * 2 < 1

/-- The mesh condition is satisfied by every sufficiently small step. -/
theorem DelayField.exists_meshOk (F : DelayField E) (h : ℝ) (hh : 0 < h) :
    ∃ h' : ℝ, 0 < h' ∧ h' ≤ h ∧ F.meshOk h' := by
  have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
  have hpos : 0 < 2 * (F.C : ℝ) + 1 := by linarith
  refine ⟨min h (1 / (2 * (F.C : ℝ) + 1)), ?_, ?_, ?_⟩
  · exact lt_min hh (one_div_pos.mpr hpos)
  · exact min_le_left _ _
  · have h1 : (F.C : ℝ) * (min h (1 / (2 * (F.C : ℝ) + 1))) * 2
        ≤ (F.C : ℝ) * (1 / (2 * (F.C : ℝ) + 1)) * 2 := by
      have := mul_le_mul_of_nonneg_left (min_le_right h (1 / (2 * (F.C : ℝ) + 1))) hC0
      linarith
    have h2 : (F.C : ℝ) * (1 / (2 * (F.C : ℝ) + 1)) * 2 < 1 := by
      have : (F.C : ℝ) * (1 / (2 * (F.C : ℝ) + 1)) * 2
          = (2 * (F.C : ℝ)) / (2 * (F.C : ℝ) + 1) := by
        field_simp [ne_of_gt hpos]
      rw [this, div_lt_one hpos]
      linarith
    exact lt_of_le_of_lt h1 h2

/-! ### The one-step theorem: Picard–Lindelöf with a known delayed part -/

/-- **The one-step existence theorem.**  Let `f` be a delay field, `ψ : ℝ → E` a *known* (hence
continuous on the step) delayed part, and `t₀`, `h` with `h > 0` small enough for the
Picard–Lindelöf step.  Then the ordinary differential equation `ẋ(t) = f (t, x(t), ψ (t))` has a
solution on `[t₀, t₀ + h]` with initial value `x₀` at `t₀`.

This is the heart of the method of steps: on every step of a delay equation the delayed part is
already known, and the step is an ordinary differential equation. -/
theorem delayStep_exists (F : DelayField E) {t₀ h : ℝ} (hh : 0 < h) (hsmall : F.meshOk h)
    (ψ : ℝ → E) (hψ : ContinuousOn ψ (Set.Icc t₀ (t₀ + h))) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + h),
        HasDerivWithinAt α (F.f t (α t) (ψ t)) (Set.Icc t₀ (t₀ + h)) t := by
  -- the delayed part is bounded on the (compact) time interval
  have hIcc : IsCompact (Set.Icc t₀ (t₀ + h)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hIcc.bddAbove_image (f := fun t => ‖ψ t‖) hψ.norm
  have hBmem : ∀ t ∈ Set.Icc t₀ (t₀ + h), ‖ψ t‖ ≤ B := fun t ht => hB (mem_image_of_mem _ ht)
  have hB0 : 0 ≤ B := by
    have h1 := hBmem t₀ ⟨le_rfl, by linarith⟩
    linarith [norm_nonneg (ψ t₀)]
  -- the radius of the ball on which the field is controlled
  set Mc : ℝ := (F.M : ℝ) + (F.C : ℝ) * (‖x₀‖ + B) with hMcdef
  have hMc0 : 0 ≤ Mc := by
    rw [hMcdef]
    have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
    have hM0 : 0 ≤ (F.M : ℝ) := F.M.coe_nonneg
    positivity
  set den : ℝ := 1 - 2 * (F.C : ℝ) * h with hden
  have hden0 : 0 < den := by
    unfold den
    have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
    have h1 : 2 * (F.C : ℝ) * h < 1 := by
      have hsmall' := hsmall
      unfold DelayField.meshOk at hsmall'
      calc 2 * (F.C : ℝ) * h = (F.C : ℝ) * h * 2 := by ring
        _ < 1 := hsmall'
    linarith
  set a : ℝ := h * Mc / den with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    exact div_nonneg (mul_nonneg hh.le hMc0) hden0.le
  -- the norm bound of the field on the ball
  set L : ℝ := Mc + (F.C : ℝ) * a with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
    positivity
  have hLh : L * h ≤ a := by
    have haeq : a * den = Mc * h := by
      rw [hadef]
      field_simp [ne_of_gt hden0]
    rw [hLdef]
    calc (Mc + (F.C : ℝ) * a) * h = Mc * h + (F.C : ℝ) * a * h := by ring
      _ = a * den + (F.C : ℝ) * a * h := by rw [← haeq]
      _ = a * (den + (F.C : ℝ) * h) := by ring
      _ ≤ a * 1 := by
        rw [hden]
        have hstep : (1 - 2 * (F.C : ℝ) * h) + (F.C : ℝ) * h ≤ 1 := by
          have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
          have hh0 : 0 < h := hh
          nlinarith
        exact mul_le_mul_of_nonneg_left hstep ha0
      _ = a := by ring
  -- the Picard–Lindelöf hypotheses
  have hpl : IsPicardLindelof (fun t x => F.f t x (ψ t)) (tmin := t₀) (tmax := t₀ + h)
      ⟨t₀, le_rfl, by linarith⟩ x₀
      ⟨a, ha0⟩ 0 ⟨L, hL0⟩ F.K₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (F.lip₂ t (ψ t)).lipschitzOnWith.mono (fun _ _ => Set.mem_univ _)
    · intro x _
      exact F.continuousOn_time_delayed x ψ hψ
    · intro t ht x hx
      have hxn : ‖x‖ ≤ ‖x₀‖ + a := by
        have hdist : dist x x₀ ≤ a := Metric.mem_closedBall.mp hx
        have h1 : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
          have := norm_add_le (x - x₀) x₀
          rwa [sub_add_cancel] at this
        rw [dist_eq_norm] at hdist
        linarith
      have hgr := F.growth t x (ψ t)
      have hψb := hBmem t ht
      have h1 : (F.C : ℝ) * (‖x‖ + ‖ψ t‖) ≤ (F.C : ℝ) * (‖x₀‖ + a + B) := by
        have hC0 : 0 ≤ (F.C : ℝ) := F.C.coe_nonneg
        have := mul_le_mul_of_nonneg_left (add_le_add hxn hψb) hC0
        linarith
      have h2 : (F.M : ℝ) + (F.C : ℝ) * (‖x₀‖ + a + B) = L := by
        rw [hLdef, hMcdef]
        ring
      have : ‖F.f t x (ψ t)‖ ≤ L := by linarith
      exact this
    · have hmax : max ((t₀ + h) - t₀) (t₀ - t₀) = h := by
        rw [add_sub_cancel_left, sub_self, max_eq_left hh.le]
      rw [hmax]
      have h1 : L * h ≤ a - 0 := by linarith [hLh]
      exact h1
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

/-- **The one-step uniqueness theorem.**  Two solutions of the ODE `ẋ(t) = f (t, x(t), ψ (t))` on
`[t₀, t₀+h]` with the same initial value agree there. -/
theorem delayStep_unique (F : DelayField E) {t₀ h : ℝ} (hh : 0 < h)
    (ψ : ℝ → E) (x₀ : E) {α β : ℝ → E}
    (hα0 : α t₀ = x₀) (hβ0 : β t₀ = x₀)
    (hα : ∀ t ∈ Set.Icc t₀ (t₀ + h),
      HasDerivWithinAt α (F.f t (α t) (ψ t)) (Set.Icc t₀ (t₀ + h)) t)
    (hβ : ∀ t ∈ Set.Icc t₀ (t₀ + h),
      HasDerivWithinAt β (F.f t (β t) (ψ t)) (Set.Icc t₀ (t₀ + h)) t) :
    ∀ t ∈ Set.Icc t₀ (t₀ + h), α t = β t := by
  -- the right-hand derivative at every point of the interval
  have hright : ∀ (g : ℝ → E) (hg : ∀ t ∈ Set.Icc t₀ (t₀ + h),
        HasDerivWithinAt g (F.f t (g t) (ψ t)) (Set.Icc t₀ (t₀ + h)) t),
      ∀ t ∈ Set.Ico t₀ (t₀ + h),
        HasDerivWithinAt g (F.f t (g t) (ψ t)) (Set.Ici t) t := by
    intro g hg t ht
    by_cases heq : t = t₀
    · refine heq.symm ▸ ?_
      refine (hg t₀ ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (t₀ - 1) (t₀ + h), isOpen_Ioo, ?_, ?_⟩
      · exact ⟨by linarith, by linarith⟩
      · intro y hy
        exact ⟨hy.2, by linarith [hy.1.2]⟩
    · have ht' : t ∈ Set.Ioo t₀ (t₀ + h) :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), by linarith [ht.2]⟩
      have hnhds : Set.Icc t₀ (t₀ + h) ∈ 𝓝 t := Icc_mem_nhds ht'.1 ht'.2
      exact (hg t ⟨ht.1, ht.2.le⟩).hasDerivAt hnhds |>.hasDerivWithinAt
  have hαd : ∀ t ∈ Set.Ico t₀ (t₀ + h),
      HasDerivWithinAt α (F.f t (α t) (ψ t)) (Set.Ici t) t := hright α hα
  have hβd : ∀ t ∈ Set.Ico t₀ (t₀ + h),
      HasDerivWithinAt β (F.f t (β t) (ψ t)) (Set.Ici t) t := hright β hβ
  have hcontα : ContinuousOn α (Set.Icc t₀ (t₀ + h)) :=
    fun t ht => (hα t ht).continuousWithinAt
  have hcontβ : ContinuousOn β (Set.Icc t₀ (t₀ + h)) :=
    fun t ht => (hβ t ht).continuousWithinAt
  have h := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => F.f t x (ψ t)) (s := fun _ => Set.univ) (K := F.K₂)
    (fun t _ => (F.lip₂ t (ψ t)).lipschitzOnWith)
    hcontα hαd (fun _ _ => Set.mem_univ _)
    hcontβ hβd (fun _ _ => Set.mem_univ _)
    (hα0.trans hβ0.symm)
  exact fun t ht => h ht

/-! ### The gluing lemma -/

/-- **The glued trajectory.**  The first solution up to the junction `a`, the second one after. -/
noncomputable def delayGlue (x₁ x₂ : ℝ → E) (a : ℝ) : ℝ → E := fun t => if t ≤ a then x₁ t else x₂ t

/-- The lower set `{x | x ≤ a}` is `Set.Iic a`. -/
theorem setIic_eq (a : ℝ) : {x : ℝ | x ≤ a} = Set.Iic a := by ext t; simp [Set.Iic]

/-- The upper set `{x | a < x}` is `Set.Ioi a`. -/
theorem setIoi_eq (a : ℝ) : {x : ℝ | a < x} = Set.Ioi a := by ext t; simp [Set.Ioi]

/-- The closure of `{x | x ≤ a}` is `Set.Iic a`. -/
theorem closure_set_le_eq (a : ℝ) : closure {x : ℝ | x ≤ a} = Set.Iic a := by
  rw [setIic_eq, closure_Iic]

/-- The closure of `{x | ¬(x ≤ a)}` is `Set.Ici a`. -/
theorem closure_set_not_le_eq (a : ℝ) : closure {x : ℝ | ¬(x ≤ a)} = Set.Ici a := by
  have h : {x : ℝ | ¬(x ≤ a)} = Set.Ioi a := by ext t; simp [Set.Ioi]
  rw [h, closure_Ioi]

/-- **The gluing lemma.**  Let `F` be a delay field, `τ ≥ 0`, and `a ≤ b` with `b − a ≤ τ` (so
that the delayed part of the second interval reaches back at most to the junction).  Let `x₁`
solve the delay equation on `[0, a]`, and let `x₂` solve the *ordinary* differential equation
`ẋ(t) = f (t, x (t)) (ψ t)` on `[a, b]`, where the delayed part `ψ` is the already known part
of the first solution: `ψ t = x₁ (t − τ)`.  If the two pieces match at the junction
(`x₂ a = x₁ a`), the glued trajectory solves the delay equation on `[0, b]`.

This is the second ingredient of the method of steps: the solution computed on one step and the
solution computed on the next step (which sees the first one as its delayed part) combine into a
solution of the delay equation on the whole interval. -/
theorem delay_glue (F : DelayField E) {τ a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (hτ : 0 ≤ τ)
    (hba : b - a ≤ τ)
    {x₁ x₂ : ℝ → E} {ψ : ℝ → E}
    (hx₁ : ∀ t ∈ Set.Icc 0 a,
      HasDerivWithinAt x₁ (F.f t (x₁ t) (x₁ (t - τ))) (Set.Icc 0 a) t)
    (hx₂ : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt x₂ (F.f t (x₂ t) (ψ t)) (Set.Icc a b) t)
    (hψ : ∀ t ∈ Set.Icc a b, ψ t = x₁ (t - τ))
    (hmatch : x₂ a = x₁ a) :
    ∀ t ∈ Set.Icc 0 b,
      HasDerivWithinAt (delayGlue x₁ x₂ a)
        (F.f t (delayGlue x₁ x₂ a t) (delayGlue x₁ x₂ a (t - τ))) (Set.Icc 0 b) t := by
  have hagree₁ : ∀ y ≤ a, delayGlue x₁ x₂ a y = x₁ y := by
    intro y hy
    simp [delayGlue, hy]
  have hagree₂ : ∀ y ≥ a, delayGlue x₁ x₂ a y = x₂ y := by
    intro y hy
    by_cases hy' : y ≤ a
    · have hyeq : y = a := le_antisymm hy' hy
      rw [hyeq]
      simp [delayGlue]
      exact hmatch.symm
    · simp [delayGlue, hy']
  -- the delayed part of the glued trajectory on the second interval is the delayed part of `x₁`
  have hdel : ∀ y ∈ Set.Icc a b, delayGlue x₁ x₂ a (y - τ) = ψ y := by
    intro y hy
    have hyb : y ≤ b := hy.2
    have hle : y - τ ≤ a := by linarith
    rw [hagree₁ _ hle]
    exact (hψ y hy).symm
  -- the delayed part of the glued trajectory on the first interval is the delayed part of `x₁`
  have hdel₁ : ∀ y ∈ Set.Icc 0 a, delayGlue x₁ x₂ a (y - τ) = x₁ (y - τ) := by
    intro y hy
    have hya : y ≤ a := hy.2
    have hle : y - τ ≤ a := by linarith
    exact hagree₁ _ hle
  intro t ht
  by_cases hta : t < a
  · -- the solution on the first interval
    have h1 := hx₁ t ⟨ht.1, hta.le⟩
    have h1' : HasDerivWithinAt (delayGlue x₁ x₂ a)
        (F.f t (x₁ t) (x₁ (t - τ))) (Set.Icc 0 a) t :=
      h1.congr_of_mem (fun y hy => hagree₁ y hy.2) ⟨ht.1, hta.le⟩
    have hg1 : delayGlue x₁ x₂ a t = x₁ t := hagree₁ t hta.le
    have hg2 : delayGlue x₁ x₂ a (t - τ) = x₁ (t - τ) := hdel₁ t ⟨ht.1, hta.le⟩
    rw [hg1, hg2]
    -- the within-set is enlarged from `[0, a]` to `[0, b]`
    have hnhds : Set.Icc 0 a ∈ 𝓝[Set.Icc 0 b] t := by
      refine mem_nhdsWithin.mpr ⟨Set.Ioo (t - (a - t) / 2) (t + (a - t) / 2),
        isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
      · intro y hy
        have hy1 : y < t + (a - t) / 2 := hy.1.2
        have hy2 : t - (a - t) / 2 < y := hy.1.1
        have hy3 : 0 ≤ y := hy.2.1
        exact ⟨by linarith, by linarith⟩
    exact h1'.mono_of_mem_nhdsWithin hnhds
  · -- the solution on the second interval
    have ha' : a ≤ t := le_of_not_gt hta
    have h2 := hx₂ t ⟨ha', ht.2⟩
    have h2' : HasDerivWithinAt (delayGlue x₁ x₂ a)
        (F.f t (x₂ t) (ψ t)) (Set.Icc a b) t :=
      h2.congr_of_mem (fun y hy => hagree₂ y hy.1) ⟨ha', ht.2⟩
    have hg1 : delayGlue x₁ x₂ a t = x₂ t := hagree₂ t ha'
    have hg2 : delayGlue x₁ x₂ a (t - τ) = ψ t := hdel t ⟨ha', ht.2⟩
    rw [hg1, hg2]
    by_cases hteq : t = a
    · -- at the junction the two one-sided derivatives are combined
      have h2'' : HasDerivWithinAt (delayGlue x₁ x₂ a)
          (F.f a (x₂ a) (ψ a)) (Set.Icc a b) a := by simpa [hteq] using h2'
      have h1 := hx₁ a ⟨ha0, le_rfl⟩
      have h1'' : HasDerivWithinAt (delayGlue x₁ x₂ a)
          (F.f a (x₂ a) (ψ a)) (Set.Icc 0 a) a := by
        have h1' : HasDerivWithinAt (delayGlue x₁ x₂ a)
            (F.f a (x₁ a) (x₁ (a - τ))) (Set.Icc 0 a) a :=
          h1.congr_of_mem (fun y hy => hagree₁ y hy.2) ⟨ha0, le_rfl⟩
        have hval : F.f a (x₁ a) (x₁ (a - τ)) = F.f a (x₂ a) (ψ a) := by
          rw [hmatch, hψ a ⟨le_rfl, hab⟩]
        rw [← hval]
        exact h1'
      have hunion : Set.Icc 0 a ∪ Set.Icc a b = Set.Icc 0 b := by
        rw [Icc_union_Icc_eq_Icc ha0 hab]
      rw [← hunion, hteq]
      exact h1''.union h2''
    · -- away from the junction the within-set is enlarged
      have hat : a < t := lt_of_le_of_ne ha' (Ne.symm hteq)
      have hnhds : Set.Icc a b ∈ 𝓝[Set.Icc 0 b] t := by
        refine mem_nhdsWithin.mpr ⟨Set.Ioo (t - (t - a) / 2) (t + (t - a) / 2),
          isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
        · intro y hy
          have hy1 : y < t + (t - a) / 2 := hy.1.2
          have hy2 : t - (t - a) / 2 < y := hy.1.1
          have hy3 : 0 ≤ y := hy.2.1
          have hy4 : y ≤ b := hy.2.2
          exact ⟨by linarith, by linarith⟩
      exact h2'.mono_of_mem_nhdsWithin hnhds

/-! ### The solution of a delay equation -/

/-- **A solution of the delay equation on `[0, T]` with history `φ`.**  The trajectory agrees with
the history on `(-∞, 0]`, is continuous on `[0, T]`, and satisfies the delay equation on
`[0, T]`. -/
structure DelaySolutionOn (F : DelayField E) (τ : ℝ) (φ : ℝ → E) (T : ℝ) where
  /-- The trajectory of the solution. -/
  x : ℝ → E
  /-- The trajectory agrees with the history on `(-∞, 0]`. -/
  hist : ∀ t ≤ 0, x t = φ t
  /-- The trajectory is continuous on `[0, T]`. -/
  cont : ContinuousOn x (Set.Icc (0 : ℝ) T)
  /-- The delay equation holds on `[0, T]`. -/
  deriv : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc (0 : ℝ) T) t

namespace DelaySolutionOn

variable {F : DelayField E} {τ : ℝ} {φ : ℝ → E} {T : ℝ}

/-- **The solution on a shorter interval.**  A solution on `[0, T]` is a solution on `[0, T']` for
every `T' ≤ T`. -/
def restrict (s : DelaySolutionOn F τ φ T) {T' : ℝ} (hT' : T' ≤ T) :
    DelaySolutionOn F τ φ T' :=
  { x := s.x, hist := s.hist,
    cont := s.cont.mono (fun _ hy => ⟨hy.1, le_trans hy.2 hT'⟩),
    deriv := fun t ht => (s.deriv t ⟨ht.1, le_trans ht.2 hT'⟩).mono
      (fun _ hy => ⟨hy.1, le_trans hy.2 hT'⟩) }

/-- **Continuity on the window `[a − τ, a]`.**  The solution is continuous on the window of length
`τ` that ends at `a`: on the part below `0` it is the history, on the part above `0` it is the
solution itself, and the two agree at `0`. -/
theorem continuousOn_window (s : DelaySolutionOn F τ φ T) {a : ℝ} (_ha0 : 0 ≤ a) (ha : a ≤ T)
    (_hτ : 0 ≤ τ) (hφ : Continuous φ) : ContinuousOn s.x (Set.Icc (a - τ) a) := by
  -- the trajectory is the history below `0` and the solution above `0`
  have hpaste : s.x = fun t => if t ≤ 0 then φ t else s.x t := by
    funext t
    by_cases h : t ≤ 0
    · simp [h, s.hist t h]
    · simp [h]
  rw [hpaste]
  refine ContinuousOn.if (s := Set.Icc (a - τ) a) (p := fun t => t ≤ 0) ?_ ?_ ?_
  · -- the two pieces agree at the frontier `{0}`
    intro y hy
    rw [setIic_eq 0, frontier_Iic] at hy
    rcases hy with ⟨hy1, hy2⟩
    have hy0 : y = 0 := by simpa using hy2
    subst hy0
    exact (s.hist 0 le_rfl).symm
  · -- the history is continuous on the part below `0`
    exact hφ.continuousOn.mono (fun y _ => Set.mem_univ _)
  · -- the solution is continuous on the part above `0`
    rw [closure_set_not_le_eq 0]
    exact s.cont.mono (fun y hy => ⟨hy.2, le_trans hy.1.2 ha⟩)

end DelaySolutionOn

/-- **The first step of the method of steps.**  The history, followed by the solution of the
ordinary differential equation `ẋ(t) = f (t, x (t)) (φ (t − τ))` on `[0, h]`.  Since `h ≤ τ`, the
delayed part of the equation is the history, which is known. -/
theorem delay_first_step (F : DelayField E) (τ : ℝ) (_hτ : 0 ≤ τ) (φ : ℝ → E) (hφ : Continuous φ)
    {h : ℝ} (hh : 0 < h) (hhτ : h ≤ τ) (hmesh : F.meshOk h) :
    ∃ s : DelaySolutionOn F τ φ h, s.x 0 = φ 0 := by
  -- the delayed part on the first step is the history
  have hcont_sub : ContinuousOn (fun t : ℝ => t - τ) (Set.Icc 0 (0 + h)) := by
    intro t ht
    exact continuousWithinAt_id.sub (continuousWithinAt_const (b := τ))
  have hψ : ContinuousOn (fun t => φ (t - τ)) (Set.Icc 0 (0 + h)) :=
    hφ.continuousOn.comp hcont_sub (fun t _ => Set.mem_univ _)
  obtain ⟨α, hα0, hα⟩ :=
    delayStep_exists F (t₀ := 0) (h := h) hh hmesh (fun t => φ (t - τ)) hψ (φ 0)
  classical
  -- the trajectory: the history on `(-∞, 0]`, the step solution on `[0, h]`
  set x : ℝ → E := fun t => if t ≤ 0 then φ t else α t with hxdef
  have hagree : ∀ y ∈ Set.Icc 0 (0 + h), x y = α y := by
    intro y hy
    by_cases h0 : 0 < y
    · simp [hxdef, h0]
    · have hy0 : y = 0 := by linarith [hy.1]
      subst hy0
      simp [hxdef]
      exact hα0.symm
  have hdel : ∀ t ∈ Set.Icc 0 (0 + h), x (t - τ) = φ (t - τ) := by
    intro t ht
    have hle : t - τ ≤ 0 := by linarith [ht.2, hhτ]
    simp [hxdef, hle]
  refine ⟨{ x := x, hist := ?_, cont := ?_, deriv := ?_ }, ?_⟩
  · -- the history
    intro t ht
    simp [hxdef, ht]
  · -- continuity on `[0, h]`
    change ContinuousOn (fun t => if t ≤ 0 then φ t else α t) (Set.Icc 0 h)
    refine ContinuousOn.if (s := Set.Icc 0 h) (p := fun t => t ≤ 0) ?_ ?_ ?_
    · intro y hy
      rw [setIic_eq 0, frontier_Iic] at hy
      rcases hy with ⟨hy1, hy2⟩
      have hy0 : y = 0 := by simpa using hy2
      subst hy0
      exact hα0.symm
    · exact hφ.continuousOn.mono (fun y _ => Set.mem_univ _)
    · rw [closure_set_not_le_eq 0]
      have hαcont : ContinuousOn α (Set.Icc 0 (0 + h)) :=
        fun t ht => (hα t ht).continuousWithinAt
      exact hαcont.mono (fun y hy => ⟨hy.1.1, by linarith [hy.1.2]⟩)
  · -- the delay equation on `[0, h]`
    intro t ht
    have hmem : t ∈ Set.Icc 0 (0 + h) := ⟨ht.1, by linarith [ht.2]⟩
    have h := hα t hmem
    have h' := h.congr_of_mem hagree hmem
    rw [← hagree t hmem, ← hdel t hmem] at h'
    simpa only [zero_add] using h'
  · simp [hxdef]

/-- **One step of the method of steps.**  Extend a solution on `[0, a]` to a solution on
`[0, a + h]`: on the new step the delayed part is the already known part of the trajectory. -/
theorem delay_step (F : DelayField E) {τ h a : ℝ} (hτ : 0 ≤ τ) (hh : 0 < h) (hhτ : h ≤ τ)
    (hmesh : F.meshOk h) (ha0 : 0 ≤ a) {φ : ℝ → E} (hφ : Continuous φ)
    {s : DelaySolutionOn F τ φ a} :
    ∃ s' : DelaySolutionOn F τ φ (a + h), ∀ t ∈ Set.Icc 0 a, s'.x t = s.x t := by
  -- the delayed part of the new step is known
  have hwin : ContinuousOn s.x (Set.Icc (a - τ) a) :=
    s.continuousOn_window ha0 le_rfl hτ hφ
  have hψ : ContinuousOn (fun t => s.x (t - τ)) (Set.Icc a (a + h)) := by
    refine hwin.comp ?_ ?_
    · intro t ht
      exact continuousWithinAt_id.sub (continuousWithinAt_const (b := τ))
    · intro t ht
      constructor
      · linarith [ht.1]
      · linarith [ht.2, hhτ]
  obtain ⟨α, hα0, hα⟩ :=
    delayStep_exists F (t₀ := a) (h := h) hh hmesh (fun t => s.x (t - τ)) hψ (s.x a)
  classical
  -- the glued trajectory
  set y : ℝ → E := delayGlue s.x α a with hydef
  have hderiv := delay_glue F (a := a) (b := a + h) (by linarith) ha0 hτ (by linarith)
    s.deriv hα (fun t ht => rfl) hα0
  have hagree : ∀ t ∈ Set.Icc 0 a, y t = s.x t := by
    intro t ht
    simp [hydef, delayGlue, ht.2]
  have hagree' : ∀ t ≤ a, y t = s.x t := by
    intro t ht
    simp [hydef, delayGlue, ht]
  refine ⟨{ x := y, hist := ?_, cont := ?_, deriv := ?_ }, hagree⟩
  · intro t ht
    rw [hagree' t (by linarith)]
    exact s.hist t ht
  · change ContinuousOn (fun t => if t ≤ a then s.x t else α t) (Set.Icc 0 (a + h))
    refine ContinuousOn.if (s := Set.Icc 0 (a + h)) (p := fun t => t ≤ a) ?_ ?_ ?_
    · intro y hy
      rw [setIic_eq a, frontier_Iic] at hy
      rcases hy with ⟨hy1, hy2⟩
      have hy0 : y = a := by simpa using hy2
      subst hy0
      exact hα0.symm
    · rw [closure_set_le_eq a]
      exact s.cont.mono (fun y hy => ⟨hy.1.1, hy.2⟩)
    · rw [closure_set_not_le_eq a]
      have hαcont : ContinuousOn α (Set.Icc a (a + h)) :=
        fun t ht => (hα t ht).continuousWithinAt
      exact hαcont.mono (fun y hy => ⟨hy.2, hy.1.2⟩)
  · exact hderiv

/-- **The method of steps: existence.**  For every `n` there is a solution of the delay equation
on `[0, (n+1) h]` with the prescribed history. -/
theorem delay_steps_exists (F : DelayField E) (τ : ℝ) (hτ : 0 ≤ τ) (φ : ℝ → E)
    (hφ : Continuous φ) {h : ℝ} (hh : 0 < h) (hhτ : h ≤ τ) (hmesh : F.meshOk h) :
    ∀ n : ℕ, ∃ s : DelaySolutionOn F τ φ ((((n : ℕ) : ℝ) + 1) * h), s.x 0 = φ 0 := by
  intro n
  induction n with
  | zero =>
      obtain ⟨s, hs⟩ := delay_first_step F τ hτ φ hφ hh hhτ hmesh
      refine ⟨s.restrict (T' := (((0 : ℕ) : ℝ) + 1) * h) (by simp), ?_⟩
      exact hs
  | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨s', hag⟩ := delay_step F hτ hh hhτ hmesh (by positivity) hφ (s := s)
      refine ⟨s'.restrict (T' := ((((n + 1 : ℕ) : ℝ) + 1) * h)) ?_, ?_⟩
      · push_cast
        linarith
      · have h1 : (0 : ℝ) ≤ (↑n : ℝ) + 1 := by positivity
        have hnonneg : (0 : ℝ) ≤ ((↑n : ℝ) + 1) * h := mul_nonneg h1 (le_of_lt hh)
        have h0 : s'.x 0 = s.x 0 := hag 0 ⟨by linarith, hnonneg⟩
        exact h0.trans hs

/-- **One step of uniqueness.**  Two solutions of the delay equation on `[0, T]` (with
`T = a + h`) that agree on `[0, a]` agree on `[0, T]`.

Indeed, on the new step `[a, a + h]` the delayed part of the two solutions agrees (it is the
already determined part of the trajectory), so the two trajectories solve the *same* ordinary
differential equation on the step, and the one-step uniqueness applies. -/
theorem delay_step_unique (F : DelayField E) {τ h a T : ℝ} (_hτ : 0 ≤ τ) (hh : 0 < h)
    (hhτ : h ≤ τ) (ha0 : 0 ≤ a) (hT : T = a + h) {φ : ℝ → E}
    {s t : DelaySolutionOn F τ φ T} (hprev : ∀ u ∈ Set.Icc 0 a, s.x u = t.x u) :
    ∀ u ∈ Set.Icc 0 T, s.x u = t.x u := by
  intro u hu
  by_cases ha : u ≤ a
  · exact hprev u ⟨hu.1, ha⟩
  · -- on the new step the delayed parts of the two solutions agree
    have hdel : ∀ w ∈ Set.Icc a (a + h), s.x (w - τ) = t.x (w - τ) := by
      intro w hw
      by_cases h0 : w - τ ≤ 0
      · rw [s.hist _ h0, t.hist _ h0]
      · have hmem : w - τ ∈ Set.Icc 0 a := by
          constructor
          · linarith
          · linarith [hw.2, hhτ]
        exact hprev (w - τ) hmem
    -- both trajectories solve the same ordinary differential equation on the step
    have hs : ∀ w ∈ Set.Icc a (a + h),
        HasDerivWithinAt s.x (F.f w (s.x w) (s.x (w - τ))) (Set.Icc a (a + h)) w := by
      intro w hw
      have hw1 : a ≤ w := hw.1
      have h := s.deriv w ⟨by linarith, by linarith [hw.2, hT]⟩
      exact h.mono (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2, hT]⟩)
    have ht : ∀ w ∈ Set.Icc a (a + h),
        HasDerivWithinAt t.x (F.f w (t.x w) (s.x (w - τ))) (Set.Icc a (a + h)) w := by
      intro w hw
      have hw1 : a ≤ w := hw.1
      have h := t.deriv w ⟨by linarith, by linarith [hw.2, hT]⟩
      have h' := h.congr_deriv (by rw [← hdel w hw])
      exact h'.mono (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2, hT]⟩)
    have hinit : s.x a = t.x a := hprev a ⟨by linarith, le_rfl⟩
    have hone := delayStep_unique F (t₀ := a) (h := h) hh (fun w => s.x (w - τ)) (s.x a)
      (α := s.x) (β := t.x) rfl hinit.symm hs ht
    exact hone u ⟨le_of_not_ge ha, by linarith [hu.2, hT]⟩

/-- **The method of steps: uniqueness.**  Two solutions of the delay equation with the same
history agree on `[0, ((n+1) h)]`. -/
theorem delay_steps_unique (F : DelayField E) (τ : ℝ) (hτ : 0 ≤ τ) (φ : ℝ → E)
    (_hφ : Continuous φ) {h : ℝ} (hh : 0 < h) (hhτ : h ≤ τ) (_hmesh : F.meshOk h) :
    ∀ (n : ℕ) (s t : DelaySolutionOn F τ φ ((((n : ℕ) : ℝ) + 1) * h)),
      ∀ u ∈ Set.Icc 0 ((((n : ℕ) : ℝ) + 1) * h), s.x u = t.x u := by
  intro n
  induction n with
  | zero =>
      intro s t u hu
      -- the two solutions agree at the initial point
      have hprev : ∀ w ∈ Set.Icc 0 (0 : ℝ), s.x w = t.x w := by
        intro w hw
        rw [s.hist w hw.2, t.hist w hw.2]
      have hone := delay_step_unique F (τ := τ) (h := h) (a := 0)
        (T := (((0 : ℕ) : ℝ) + 1) * h) (s := s) (t := t)
        hτ hh hhτ (by linarith) (by push_cast; ring) hprev u hu
      exact hone
  | succ n ih =>
      intro s t u hu
      -- the two solutions agree on the previous interval
      have hprev : ∀ w ∈ Set.Icc 0 ((((n : ℕ) : ℝ) + 1) * h), s.x w = t.x w := by
        have hT : ((((n : ℕ) : ℝ) + 1) * h) ≤ ((((Nat.succ n : ℕ) : ℝ) + 1) * h) := by
          push_cast
          nlinarith [hh.le]
        have hih := ih (s.restrict (T' := ((((n : ℕ) : ℝ) + 1) * h)) hT)
          (t.restrict (T' := ((((n : ℕ) : ℝ) + 1) * h)) hT)
        intro w hw
        exact hih w hw
      -- and hence on the whole interval
      have hconv : ((((Nat.succ n : ℕ) : ℝ) + 1) * h)
          = ((((n : ℕ) : ℝ) + 1) * h) + h := by
        push_cast
        ring
      have hu' : u ∈ Set.Icc 0 ((((Nat.succ n : ℕ) : ℝ) + 1) * h) := hu
      exact delay_step_unique F (τ := τ) (h := h) (a := ((((n : ℕ) : ℝ) + 1) * h))
        (T := ((((Nat.succ n : ℕ) : ℝ) + 1) * h)) (s := s) (t := t)
        hτ hh hhτ (by positivity) hconv hprev u hu'

/-- **The solution of a delay equation on an interval.**  The trajectory is continuous on
`[0, T]` and satisfies the delay equation there. -/
def IsDelaySolutionOn (F : DelayField E) (τ : ℝ) (X : ℝ → E) (T : ℝ) : Prop :=
  ContinuousOn X (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt X (F.f t (X t) (X (t - τ))) (Set.Icc (0 : ℝ) T) t

/-- **The global solution of the delay equation.**  There is a trajectory `X` on `[0, ∞)` with the
prescribed history which solves the delay equation on every finite interval. -/
theorem delay_solution_exists (F : DelayField E) (τ : ℝ) (hτ : 0 ≤ τ) (φ : ℝ → E)
    (hφ : Continuous φ) {h : ℝ} (hh : 0 < h) (hhτ : h ≤ τ) (hmesh : F.meshOk h) :
    ∃ X : ℝ → E, (∀ t ≤ 0, X t = φ t) ∧ (∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T) := by
  classical
  -- the step solutions
  set s : ∀ n : ℕ, DelaySolutionOn F τ φ ((((n : ℕ) : ℝ) + 1) * h) :=
    fun n => Classical.choose (delay_steps_exists F τ hτ φ hφ hh hhτ hmesh n) with hsdef
  -- the global trajectory
  set X : ℝ → E := fun t => if t ≤ 0 then φ t else (s (Nat.ceil (t / h))).x t with hXdef
  -- the step solutions are compatible: `s k` and `s m` agree on `[0, ((k+1) h)]` when `k ≤ m`
  have hcompat : ∀ (k m : ℕ), k ≤ m →
      ∀ y ∈ Set.Icc 0 ((((k : ℕ) : ℝ) + 1) * h), (s k).x y = (s m).x y := by
    intro k m hkm y hy
    have hT : ((((k : ℕ) : ℝ) + 1) * h) ≤ ((((m : ℕ) : ℝ) + 1) * h) := by
      have hkm'' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
      have hh0 : (0 : ℝ) ≤ h := le_of_lt hh
      have h1 : (k : ℝ) * h ≤ (m : ℝ) * h := mul_le_mul_of_nonneg_right hkm'' hh0
      linarith
    have h := delay_steps_unique F τ hτ φ hφ hh hhτ hmesh k (s k)
      ((s m).restrict (T' := ((((k : ℕ) : ℝ) + 1) * h)) hT) y hy
    exact h
  refine ⟨X, ?_, ?_⟩
  · -- the history
    intro t ht
    simp [hXdef, ht]
  · -- the delay equation on every finite interval
    intro T hT
    set m : ℕ := Nat.ceil (T / h) with hm
    have hmh : (m : ℝ) * h ≤ (((m : ℕ) : ℝ) + 1) * h := by
      have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ h := le_of_lt hh
      calc (m : ℝ) * h ≤ (m : ℝ) * h + h := by linarith
        _ = (((m : ℕ) : ℝ) + 1) * h := by ring
    have hTmh : T ≤ (m : ℝ) * h := by
      have h1 : T / h ≤ (m : ℝ) := by
        have := Nat.le_ceil (T / h)
        simpa [hm] using this
      have h2 : (0 : ℝ) ≤ h := le_of_lt hh
      have h3 : T = T / h * h := by field_simp
      calc T = T / h * h := h3
        _ ≤ (m : ℝ) * h := mul_le_mul_of_nonneg_right h1 h2
    -- the trajectory agrees with the step solution `s m` on `[0, T]`
    have hagree : ∀ y ∈ Set.Icc 0 T, X y = (s m).x y := by
      intro y hy
      by_cases h0 : y ≤ 0
      · simp [hXdef, h0]
        exact (s m).hist y h0 |>.symm
      · have hceil : Nat.ceil (y / h) ≤ m := by
          have h1 : y / h ≤ T / h := div_le_div_of_nonneg_right hy.2 (le_of_lt hh)
          have h2 : Nat.ceil (y / h) ≤ Nat.ceil (T / h) := Nat.ceil_le_ceil h1
          simpa [hm] using h2
        have hmem : y ∈ Set.Icc 0 ((((Nat.ceil (y / h) : ℕ) : ℝ) + 1) * h) := by
          constructor
          · linarith
          · have h1 : y / h ≤ (Nat.ceil (y / h) : ℝ) := Nat.le_ceil _
            have h2 : (0 : ℝ) ≤ h := le_of_lt hh
            have h3 : y = y / h * h := by field_simp
            have h4 : y / h * h ≤ (Nat.ceil (y / h) : ℝ) * h := mul_le_mul_of_nonneg_right h1 h2
            have h5 : (Nat.ceil (y / h) : ℝ) * h ≤ (((Nat.ceil (y / h) : ℕ) : ℝ) + 1) * h := by
              have h6 : (0 : ℝ) ≤ (Nat.ceil (y / h) : ℝ) := Nat.cast_nonneg _
              have h7 : (0 : ℝ) ≤ h := le_of_lt hh
              calc (Nat.ceil (y / h) : ℝ) * h ≤ (Nat.ceil (y / h) : ℝ) * h + h := by linarith
                _ = (((Nat.ceil (y / h) : ℕ) : ℝ) + 1) * h := by ring
            linarith
        have hagree' : (s (Nat.ceil (y / h))).x y = (s m).x y :=
          hcompat (Nat.ceil (y / h)) m (by simpa using hceil) y hmem
        simp [hXdef, h0]
        exact hagree'
    refine ⟨?_, ?_⟩
    · -- continuity
      have hcont : ContinuousOn (s m).x (Set.Icc 0 ((((m : ℕ) : ℝ) + 1) * h)) := (s m).cont
      have hcont' : ContinuousOn (s m).x (Set.Icc (0 : ℝ) T) :=
        hcont.mono (fun (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) T) => ⟨hy.1, by linarith [hy.2, hTmh, hmh]⟩)
      exact hcont'.congr (fun y hy => hagree y hy)
    · -- the delay equation
      intro t ht
      have hmem : t ∈ Set.Icc 0 ((((m : ℕ) : ℝ) + 1) * h) :=
        ⟨ht.1, by linarith [ht.2, hTmh, hmh]⟩
      have h := (s m).deriv t hmem
      have h' := h.mono (fun (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) T) =>
        ⟨hy.1, by linarith [hy.2, hTmh, hmh]⟩)
      have hagree_del : X (t - τ) = (s m).x (t - τ) := by
        by_cases h0 : t - τ ≤ 0
        · simp [hXdef, h0]
          exact (s m).hist (t - τ) h0 |>.symm
        · have hmem' : t - τ ∈ Set.Icc 0 T := by
            constructor
            · linarith
            · linarith [ht.2]
          exact hagree (t - τ) hmem'
      have h'' := h'.congr_of_mem hagree (by exact ⟨ht.1, by linarith [ht.2, hTmh, hmh]⟩)
      have hval : F.f t ((s m).x t) ((s m).x (t - τ)) = F.f t (X t) (X (t - τ)) := by
        rw [← hagree t ⟨ht.1, by linarith [ht.2, hTmh, hmh]⟩, ← hagree_del]
      exact h''.congr_deriv hval

/-- **The global solution is unique.**  Two solutions of the delay equation on `[0, ∞)` with the
same history agree. -/
theorem delay_solution_unique (F : DelayField E) (τ : ℝ) (hτ : 0 ≤ τ) (φ : ℝ → E)
    (hφ : Continuous φ) {h : ℝ} (hh : 0 < h) (hhτ : h ≤ τ) (hmesh : F.meshOk h)
    {X Y : ℝ → E} (hX : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T)
    (hY : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ Y T)
    (hXh : ∀ t ≤ 0, X t = φ t) (hYh : ∀ t ≤ 0, Y t = φ t) :
    ∀ t, X t = Y t := by
  intro t
  by_cases h0 : t ≤ 0
  · rw [hXh t h0, hYh t h0]
  · -- on every finite interval the two solutions agree
    obtain ⟨n, hn⟩ : ∃ n : ℕ, t ≤ (((n : ℕ) : ℝ) + 1) * h := by
      refine ⟨Nat.ceil (t / h), ?_⟩
      have h1 : t / h ≤ (Nat.ceil (t / h) : ℝ) := Nat.le_ceil _
      have h2 : (0 : ℝ) ≤ h := le_of_lt hh
      have h3 : t = t / h * h := by field_simp
      calc t = t / h * h := h3
        _ ≤ (Nat.ceil (t / h) : ℝ) * h := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ ((Nat.ceil (t / h) : ℝ) + 1) * h := by
          have h5 : (0 : ℝ) ≤ (Nat.ceil (t / h) : ℝ) := Nat.cast_nonneg _
          have h6 : (Nat.ceil (t / h) : ℝ) * h ≤ (Nat.ceil (t / h) : ℝ) * h + h := by linarith
          calc (Nat.ceil (t / h) : ℝ) * h ≤ (Nat.ceil (t / h) : ℝ) * h + h := h6
            _ = ((Nat.ceil (t / h) : ℝ) + 1) * h := by ring
    -- the two global trajectories restrict to solutions on the same interval
    have hnonneg : (0 : ℝ) ≤ (((n : ℕ) : ℝ) + 1) * h := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      exact mul_nonneg h1 (le_of_lt hh)
    have hagree := delay_steps_unique F τ hτ φ hφ hh hhτ hmesh n
      { x := X, hist := hXh, cont := (hX _ hnonneg).1, deriv := (hX _ hnonneg).2 }
      { x := Y, hist := hYh, cont := (hY _ hnonneg).1, deriv := (hY _ hnonneg).2 }
      t ⟨by linarith, hn⟩
    exact hagree

/-! ### Constant solutions and the repository -/

/-- **A constant history gives a constant solution.**  If the delay field vanishes at the
constant state, the constant trajectory is a solution of the delay equation on every interval.
This is the statement that the fixed points of the delay dynamics are the equilibria; the
converse (a constant solution forces the field to vanish) is the content of
`CRNT.Network.const_isDelaySolution_iff` for the mass-action delay systems of
`CRNT.Extensions.DelayMassAction`. -/
theorem delay_constHistory_isSolution (F : DelayField E) {_τ : ℝ} {c : E} {T : ℝ} (_hT : 0 ≤ T)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) T, F.f t c c = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun _ => c) (F.f t c c) (Set.Icc (0 : ℝ) T) t := by
  intro t ht
  have h1 : HasDerivWithinAt (fun _ => c) (0 : E) (Set.Icc (0 : ℝ) T) t :=
    hasDerivWithinAt_const (c := c) (s := Set.Icc (0 : ℝ) T) (x := t)
  exact h1.congr_deriv (by rw [hc t ht])

end General

/-! ### The linear delay equation -/

section Linear

/-- The `ℝ`-module structure used by the derivative calculus. -/
noncomputable local instance : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule

/-- **The linear delay field.**  The right-hand side of the scalar linear delay equation
`ẋ(t) = −a x(t) + b x (t − τ)`. -/
noncomputable def linearDelayField (a b : ℝ) : DelayField ℝ where
  f := fun _ x y => -a * x + b * y
  cont := by
    fun_prop
  K₂ := Real.toNNReal |a|
  lip₂ := by
    intro t y
    refine LipschitzWith.of_dist_le_mul ?_
    intro x1 x2
    simp only [dist_eq_norm]
    have h1 : -a * x1 + b * y - (-a * x2 + b * y) = a * (x2 - x1) := by ring
    rw [h1, norm_sub_rev]
    have hnn : ((Real.toNNReal |a| : ℝ≥0) : ℝ) = |a| := Real.coe_toNNReal _ (by positivity)
    rw [hnn, Real.norm_eq_abs]
    exact norm_mul_le a (x2 - x1)
  M := 0
  C := Real.toNNReal (|a| + |b|)
  growth := by
    intro t x y
    have h1 : ‖-a * x + b * y‖ ≤ |a| * ‖x‖ + |b| * ‖y‖ := by
      calc ‖-a * x + b * y‖ ≤ ‖-a * x‖ + ‖b * y‖ := norm_add_le _ _
        _ ≤ |a| * ‖x‖ + |b| * ‖y‖ := by
          have h3 : ‖-a * x‖ ≤ |a| * ‖x‖ := by
            have h3' := norm_mul_le (-a) x
            rw [norm_neg, Real.norm_eq_abs] at h3'
            exact h3'
          have h4 : ‖b * y‖ ≤ |b| * ‖y‖ := by
            have h4' := norm_mul_le b y
            rw [Real.norm_eq_abs] at h4'
            exact h4'
          linarith
    have h2 : |a| * ‖x‖ + |b| * ‖y‖ ≤ 0 + (|a| + |b|) * (‖x‖ + ‖y‖) := by
      have h5 : |a| * ‖x‖ ≤ (|a| + |b|) * ‖x‖ := by
        have := mul_le_mul_of_nonneg_right (abs_nonneg b) (norm_nonneg x)
        nlinarith
      have h6 : |b| * ‖y‖ ≤ (|a| + |b|) * ‖y‖ := by
        have := mul_le_mul_of_nonneg_right (abs_nonneg a) (norm_nonneg y)
        nlinarith
      have h7 : (|a| + |b|) * ‖x‖ + (|a| + |b|) * ‖y‖ = (|a| + |b|) * (‖x‖ + ‖y‖) := by ring
      linarith
    have hC : (Real.toNNReal (|a| + |b|) : ℝ) = |a| + |b| := Real.coe_toNNReal _ (by positivity)
    rw [hC]
    exact le_trans h1 h2

/-- **An admissible decay rate exists.**  If `a > |b|` then there is `ε > 0` with
`ε + |b| e^{ε τ} ≤ 2a − |b|`.

This is the rate that the Halanay estimate of the linear delay equation requires: the square
`x²` of a solution satisfies the scalar delay inequality
`u' ≤ −(2a − |b|) u + |b| u(·−τ)`, and the exponential `e^{−ε t}` is a supersolution of that
inequality exactly when `ε + |b| e^{ε τ} ≤ 2a − |b|`. -/
theorem delayLinear_rate_exists {a b τ : ℝ} (_hτ : 0 < τ) (ha : |b| < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε + |b| * Real.exp (ε * τ) ≤ 2 * a - |b| := by
  have ha0 : 0 < a := by
    have : 0 ≤ |b| := abs_nonneg b
    linarith
  have hcont : Continuous (fun e : ℝ => e + |b| * Real.exp (e * τ) - (2 * a - |b|)) := by
    have h1 : Continuous (fun e : ℝ => e * τ) := by fun_prop
    have h2 : Continuous (fun e : ℝ => Real.exp (e * τ)) := Real.continuous_exp.comp h1
    have h3 : Continuous (fun e : ℝ => |b| * Real.exp (e * τ)) := continuous_const.mul h2
    have h4 : Continuous (fun e : ℝ => e + |b| * Real.exp (e * τ)) := continuous_id.add h3
    exact h4.sub continuous_const
  have hf0 : (0 : ℝ) + |b| * Real.exp ((0 : ℝ) * τ) - (2 * a - |b|) < 0 := by
    have h0 : Real.exp ((0 : ℝ) * τ) = 1 := by rw [zero_mul, Real.exp_zero]
    have h7 : 0 ≤ |b| := abs_nonneg b
    rw [h0, mul_one]
    linarith
  have hf1 : 0 ≤ (2 * a : ℝ) + |b| * Real.exp ((2 * a : ℝ) * τ) - (2 * a - |b|) := by
    have h6 : 0 ≤ |b| * Real.exp ((2 * a : ℝ) * τ) :=
      mul_nonneg (abs_nonneg b) (Real.exp_nonneg _)
    have h7 : 0 ≤ |b| := abs_nonneg b
    nlinarith
  obtain ⟨e, he, heq⟩ : ∃ e ∈ Set.Icc (0 : ℝ) (2 * a),
      e + |b| * Real.exp (e * τ) - (2 * a - |b|) = 0 := by
    have himg := intermediate_value_Icc (by linarith) hcont.continuousOn ⟨hf0.le, hf1⟩
    have himg2 : ∃ e ∈ Set.Icc (0 : ℝ) (2 * a),
        (fun e : ℝ => e + |b| * Real.exp (e * τ) - (2 * a - |b|)) e = 0 := by
      exact himg
    obtain ⟨e, he, heq⟩ := himg2
    exact ⟨e, he, heq⟩
  refine ⟨e, ?_, ?_⟩
  · by_contra hcon
    have he0 : 0 ≤ e := he.1
    have hz : e = 0 := le_antisymm (le_of_not_gt hcon) he0
    subst hz
    linarith [heq]
  · have : |b| * Real.exp (e * τ) = 2 * a - |b| - e := by linarith [heq]
    linarith

/-- **The constant solutions of the linear delay equation.**  If `b = a` then every constant
trajectory `x(t) ≡ c` solves the equation `ẋ(t) = −a x(t) + b x (t − τ)`. -/
theorem delayLinear_constant_solution {a b : ℝ} (hab : a = b) (c : ℝ) (t : ℝ) :
    HasDerivAt (fun _ => c) ((-a : ℝ) * c + b * c) t := by
  have h1 : (-a : ℝ) * c + b * c = 0 := by rw [hab]; ring
  rw [h1]
  exact hasDerivAt_const t c

/-- **The obstruction: constant solutions do not decay.**  If `b = a` and `c ≠ 0`, the constant
solution of the linear delay equation does not converge to `0`; the delay equation is *not*
semistable. -/
theorem delayLinear_constant_not_tendsto {_a : ℝ} (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun _ : ℝ => c) atTop (𝓝 (0 : ℝ)) := by
  intro h
  have h1 : c = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℝ => c) atTop (𝓝 c)) h
  exact hc h1

end Linear

end Dynamics

end CRNT
