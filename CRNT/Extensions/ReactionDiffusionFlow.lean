import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Piecewise
import CRNT.Dynamics.FlowConstruction
import CRNT.Extensions.ReactionDiffusionGlobal

/-!
# The flow and the semigroup law for the semidiscrete reaction–diffusion system

This module closes the gap left open by `CRNT.Extensions.ReactionDiffusionGlobal`: it supplies
the **two-sided solution** of the semidiscrete (method of lines) reaction–diffusion ODE, its
**uniqueness**, the **semigroup law** and the **flow** of the system.

## The mathematical setting

The semidiscrete (method of lines) reading of a reaction–diffusion system is the ODE

```
ẋ = D Δ_h x + f(x),
```

on the finite dimensional space `ι → ℝ`, where `Δ_h` is the (box) Laplacian of the grid and `f`
is the reaction term.  Mathlib contains no PDE theory (no Sobolev spaces, no parabolic maximal
regularity), so the literal nonlinear PDE `∂_t x = D Δ x + f(x)` is out of reach; see
`CRNT.Extensions.ReactionDiffusion` for the semidiscrete backbone (the box Laplacian, the
semidiscrete field `reactionDiffusionField`, its Lipschitz constant, the *local* existence
theorem `exists_reactionDiffusion_solution`, the Jacobian `reactionDiffusionJacobian` and the
Turing connection `turing_connection`).

The classical facts about the ODE `ẋ = f(x)` used here are the classical facts about an
autonomous ODE with a *locally Lipschitz* field:

* the **continuation argument** (Teschl, *Ordinary Differential Equations: Dynamical Systems and
  an Introduction to the Theory of Linear ODEs*, §2.2): a field whose values grow at most
  *linearly* cannot blow up in finite time, so the local solution can be continued past any
  finite time.  This is formalized in `CRNT.Extensions.ReactionDiffusionGlobal`
  (`exists_global_solution_of_linearGrowth`), which is a *one-sided* (`t ≥ 0`) statement.
* the **uniqueness of the solution** of the initial value problem (Mathlib's
  `ODE_solution_unique_of_mem_Ioo`, applied at the *interior* point `0`), and hence
* the **semigroup law** `ϕ (t + s) x = ϕ t (ϕ s x)` of the flow, and
* the **continuous dependence** estimate `ODE.dist_le_of_trajectories_ODE`, which yields the
  joint continuity in `(x, t)` required by the structure `Flow`.

## What is formalized here

* **The continuation machinery** (`exists_solution_extend_agree`, `exists_global_forward_solution`).
  `exists_solution_extend_agree` strengthens `CRNT.ReactionDiffusion.exists_solution_extend` by
  recording the *pasting* of the extended solution with the original one on `[0, t₀]`; this
  agreement is what makes the global solution obtained by iterating the extension well defined.
  `exists_global_forward_solution` iterates the extension and glues the pieces by uniqueness at
  the interior point `0`.
* **The two-sided solution** (`exists_global_twoSided_solution_of_linearGrowth`, and its
  semidiscrete instance `exists_global_twoSided_solution`).  The backward piece is obtained by
  applying the forward construction to the *negated* field `g x = -f x` and reflecting the
  result: if `w` solves `ẇ = g w`, then `t ↦ w (-t)` solves `ẋ = f x` on the negative half axis.
  The two pieces are pasted at `0` with `CRNT.ReactionDiffusion.hasDerivAt_paste`, which yields
  a solution of the ODE on **all** of `ℝ`.
* **Uniqueness** (`global_solution_unique`): two global solutions with the same initial value
  coincide (Mathlib's `ODE_solution_unique_univ`).
* **The semigroup law** (`global_solution_semigroup`): for a global solution `γ` and a global
  solution `η` through `γ s`, one has `η t = γ (s + t)`: the shifted solution `t ↦ γ (s + t)`
  is again a solution of the initial value problem with the initial value `γ s`, so it agrees
  with `η` by uniqueness.
* **The flow** (`exists_reactionDiffusion_flow`): there is a `Flow ℝ≥0 (ι → ℝ)` of the
  semidiscrete field whose orbits are the global solutions; the joint continuity is obtained
  from the continuous dependence estimate `ODE.dist_le_of_isIntegralCurve`.

## What this module does **not** give

* No PDE well-posedness: no weak or strong solutions of the continuous PDE
  `∂_t x = D Δ x + f(x)`, no parabolic theory, no pattern selection.  This module is about the
  *semidiscrete* ODE only.
* The flow is a *forward* semiflow `Flow ℝ≥0 (ι → ℝ)`; the backward flow is not formalized
  (although the two-sided solution of this module would give one).
* The growth bound and the continuation argument are stated for a *decoupled* reaction term
  `f i (w i)`, as in `CRNT.Extensions.ReactionDiffusion`.
-/

set_option maxHeartbeats 800000

namespace CRNT
namespace ReactionDiffusion

open scoped NNReal Topology
open Filter

/-! ## The continuation argument with the pasting made explicit -/

/-- **The negated field is as Lipschitz as the field.** -/
theorem lipschitzWith_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E}
    {K : ℝ≥0} (hl : LipschitzWith K f) :
    LipschitzWith K (fun x : E => -f x) := by
  refine LipschitzWith.of_dist_le_mul (K := K) fun x y => ?_
  have h := hl.dist_le_mul x y
  have h2 : dist (-f x) (-f y) = dist (f x) (f y) := by
    rw [dist_eq_norm, dist_eq_norm]
    have hq : (-f x) - (-f y) = -(f x - f y) := by module
    rw [hq, norm_neg]
  rw [h2]
  exact h

/-- **Reflection of a derivative.**  If `g` has derivative `c` at `s`, then `t ↦ g (-t)` has
derivative `-c` at `-s`. -/
theorem hasDerivAt_neg_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    {c : E} {s : ℝ} (h : HasDerivAt g c s) :
    HasDerivAt (fun t : ℝ => g (-t)) (-c) (-s) := by
  have h1 := HasDerivAt.scomp_of_eq (-s) h (hasDerivAt_neg' (-s)) (by ring)
  simpa [Function.comp_def] using h1

section Extend

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Extension of a solution, with the pasting made explicit.**  A solution of `ẋ = f x` on
`[0, t₀]` extends to a solution on `[0, t₀ + δ]`, where `δ = 1/(2C)`; the extension agrees
with the original solution on `[0, t₀]`.

This strengthens `CRNT.ReactionDiffusion.exists_solution_extend`: the agreement is what makes
the *global* solution obtained by iterating the extension well defined. -/
theorem exists_solution_extend_agree {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) {δ : ℝ} (hδC : δ = 1 / (2 * C))
    {x₀ : E} {t₀ a : ℝ} (ha0 : 0 ≤ a) (hat : a ≤ t₀) (hat' : a < t₀)
    (x : ℝ → E) (hx0 : x 0 = x₀)
    (hxd : ∀ s ∈ Set.Ioo 0 t₀, HasDerivAt x (f (x s)) s)
    (hxl : HasDerivWithinAt x (f (x t₀)) (Set.Icc a t₀) t₀) :
    ∃ y : ℝ → E, y 0 = x₀ ∧
      (∀ s, s ≤ t₀ → y s = x s) ∧
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
  refine ⟨y, hy0, ?_, ?_, ?_⟩
  · intro s hs
    simp [hy, hs]
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

end Extend

/-! ## The global forward solution -/

section Forward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The global forward solution.**  Let `f` be Lipschitz with at most linear growth, and let
`x₀sol` be a local solution of `ẋ = f x` through `x₀` on the open interval `(-ε, ε)`.  Then
there is a function `xplus : ℝ → E` with `xplus 0 = x₀` which solves `ẋ = f x` on `(-ε, ∞)`; it
agrees with `x₀sol` on `(-ε, t₀]`.

This is the classical continuation argument: the solution is extended step by step, each step
lasting `δ = 1/(2C)`, the pieces being pasted at the junctions.  The pieces are glued together
by uniqueness of the solution of the initial value problem, the common point being the interior
point `0`. -/
theorem exists_global_forward_solution {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) {δ : ℝ} (hδC : δ = 1 / (2 * C))
    {x₀ : E} {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : 0 < t₀) (ht₀ε : t₀ < ε)
    (x₀sol : ℝ → E) (hx₀sol0 : x₀sol 0 = x₀)
    (hx₀sold : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x₀sol (f (x₀sol t)) t) :
    ∃ xplus : ℝ → E, xplus 0 = x₀ ∧
      (∀ t, -ε < t → HasDerivAt xplus (f (xplus t)) t) ∧
      (∀ t, -ε < t → t ≤ t₀ → xplus t = x₀sol t) := by
  have hδ : 0 < δ := by rw [hδC]; positivity
  -- the left end of the window of the `n`-th piece
  set an : ℕ → ℝ := fun n => max 0 (t₀ + (((n : ℤ) - 1 : ℝ)) * δ) with han
  have han0 : ∀ n, 0 ≤ an n := fun n => le_max_left _ _
  have hancast : ∀ n : ℕ, (((n : ℤ) - 1 : ℝ)) = (n:ℝ) - 1 := by
    intro n; push_cast; ring
  have hanlt : ∀ n, an n < t₀ + (n:ℝ) * δ := by
    intro n
    have h1 : (((n : ℤ) - 1 : ℝ)) < (n:ℝ) := by rw [hancast]; linarith
    have h2 : (((n : ℤ) - 1 : ℝ)) * δ < (n:ℝ) * δ := mul_lt_mul_of_pos_right h1 hδ
    have h3 : t₀ + (((n : ℤ) - 1 : ℝ)) * δ < t₀ + (n:ℝ) * δ := add_lt_add_right h2 t₀
    have han' : an n = max 0 (t₀ + (((n : ℤ) - 1 : ℝ)) * δ) := congrFun han n
    have hpos : (0:ℝ) < t₀ + (n:ℝ) * δ := by positivity
    rw [han']
    exact max_lt hpos h3
  have han1 : ∀ n : ℕ, an (n+1) = t₀ + (n:ℝ) * δ := by
    intro n
    have hpos : (0:ℝ) < t₀ + (n:ℝ) * δ := by positivity
    have hcast : (((n+1 : ℕ) : ℤ) - 1 : ℝ) = (n:ℝ) := by push_cast; ring
    have han' : an (n+1) = max 0 (t₀ + (((n+1 : ℕ) : ℤ) - 1 : ℝ) * δ) := congrFun han _
    rw [han', hcast, max_eq_right hpos.le]
  -- the chain of continued solutions
  have hchain : ∀ n : ℕ, ∃ x : ℝ → E,
      x 0 = x₀ ∧
      (∀ s ∈ Set.Ioo 0 (t₀ + (n:ℝ) * δ), HasDerivAt x (f (x s)) s) ∧
      (∀ s ≤ t₀, x s = x₀sol s) ∧
      HasDerivWithinAt x (f (x (t₀ + (n:ℝ) * δ))) (Set.Icc (an n) (t₀ + (n:ℝ) * δ))
        (t₀ + (n:ℝ) * δ) := by
    intro n
    induction n with
    | zero =>
      have hzero : t₀ + ((0:ℕ) : ℝ) * δ = t₀ := by simp
      refine ⟨x₀sol, hx₀sol0, ?_, ?_, ?_⟩
      · intro s hs
        rw [hzero] at hs
        have h1 : -ε < s := by linarith [hε, hs.1]
        have h2 : s < ε := lt_of_lt_of_le hs.2 (le_of_lt ht₀ε)
        exact hx₀sold s ⟨h1, h2⟩
      · intro s hs; rfl
      · have hd := hx₀sold t₀ ⟨lt_of_lt_of_le (by linarith [hε]) (le_of_lt ht₀), ht₀ε⟩
        simpa only [hzero] using hd.hasDerivWithinAt
    | succ n ih =>
      obtain ⟨x, hx0, hxd, hxsa, hxse⟩ := ih
      obtain ⟨y, hy0, hyagree, hyd, hyend⟩ := exists_solution_extend_agree hl hC hgrow hδC
        (a := an n) (han0 n) (by linarith [hanlt n]) (by linarith [hanlt n]) x hx0 hxd hxse
      have hcast : t₀ + ((n+1:ℕ):ℝ) * δ = t₀ + (n:ℝ) * δ + δ := by push_cast; ring
      refine ⟨y, hy0, ?_, ?_, ?_⟩
      · intro s hs
        rw [hcast] at hs
        exact hyd s hs
      · intro s hs
        exact (hyagree s (le_trans hs (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n)
          (le_of_lt hδ))))).trans (hxsa s hs)
      · rw [hcast, han1 n]
        exact hyend
  choose xs hxs0 hxsd hxsa hxsend using hchain
  -- the chain members agree on the overlaps, by uniqueness at the interior point `0`
  have huniq : ∀ (m n : ℕ) (s : ℝ), -ε < s → s < t₀ + ((min m n : ℕ) : ℝ) * δ →
      xs m s = xs n s := by
    intro m n s hs hsn
    have hIoo : s ∈ Set.Ioo (-ε) (t₀ + ((min m n : ℕ) : ℝ) * δ) := ⟨hs, hsn⟩
    have hb : (0:ℝ) ∈ Set.Ioo (-ε) (t₀ + ((min m n : ℕ) : ℝ) * δ) :=
      ⟨by linarith [hε], by positivity⟩
    have hsol : ∀ (k : ℕ), min m n ≤ k →
        ∀ t ∈ Set.Ioo (-ε) (t₀ + ((min m n : ℕ) : ℝ) * δ),
          HasDerivAt (xs k) (f (xs k t)) t := by
      intro k hk t ht
      by_cases ht0 : t ≤ 0
      · have heq : (xs k) t = x₀sol t := hxsa k t (le_trans ht0 (le_of_lt ht₀))
        rw [heq]
        have hd := hx₀sold t ⟨ht.1, lt_of_le_of_lt ht0 hε⟩
        have hcong : x₀sol =ᶠ[𝓝 t] (xs k) :=
          Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨ht.1, lt_of_le_of_lt ht0 ht₀⟩)
            (fun u hu => (hxsa k u hu.2.le).symm)
        exact hd.congr_of_eventuallyEq hcong.symm
      · have hle : t₀ + ((min m n : ℕ) : ℝ) * δ ≤ t₀ + (k:ℝ) * δ := by
          have h1 : ((min m n : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
          have h2 : ((min m n : ℕ) : ℝ) * δ ≤ (k:ℝ) * δ :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hδ)
          exact add_le_add_right h2 t₀
        have htk : t ∈ Set.Ioo 0 (t₀ + (k:ℝ) * δ) :=
          ⟨lt_of_not_ge ht0, lt_of_lt_of_le ht.2 hle⟩
        exact hxsd k t htk
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ => f) (s := fun _ => Set.univ)
      (fun _ _ => hl.lipschitzOnWith) hb
      (fun t ht => ⟨hsol m (min_le_left _ _) t ht, Set.mem_univ _⟩)
      (fun t ht => ⟨hsol n (min_le_right _ _) t ht, Set.mem_univ _⟩) (by rw [hxs0 m, hxs0 n]) hIoo
  -- the index of the chain member to be used at time `t`
  have hex : ∀ t : ℝ, ∃ n : ℕ, t < t₀ + (n:ℝ) * δ := by
    intro t
    refine ⟨Nat.ceil ((t - t₀) / δ) + 1, ?_⟩
    have h1 : (t - t₀) / δ ≤ (Nat.ceil ((t - t₀) / δ) : ℝ) := Nat.le_ceil _
    have h2 : t - t₀ ≤ (Nat.ceil ((t - t₀) / δ) : ℝ) * δ :=
      (div_le_iff₀ hδ).1 h1
    have hcast : ((Nat.ceil ((t - t₀) / δ) + 1 : ℕ) : ℝ) = (Nat.ceil ((t - t₀) / δ) : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    linarith
  set xplus : ℝ → E := fun t => xs (Nat.find (hex t)) t with hxplus
  refine ⟨xplus, ?_, ?_, ?_⟩
  · rw [hxplus]; exact hxs0 (Nat.find (hex 0))
  · intro t ht
    have hspec : t < t₀ + ((Nat.find (hex t) : ℕ) : ℝ) * δ := Nat.find_spec (hex t)
    have hcong : xplus =ᶠ[𝓝 t] (fun s => xs (Nat.find (hex t)) s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨ht, hspec⟩] with s hs
      have hle : Nat.find (hex s) ≤ Nat.find (hex t) := Nat.find_min' (hex s) hs.2
      have hspec' : s < t₀ + ((Nat.find (hex s) : ℕ) : ℝ) * δ := Nat.find_spec (hex s)
      have hmin : min (Nat.find (hex s)) (Nat.find (hex t)) = Nat.find (hex s) := min_eq_left hle
      have hagree := huniq (Nat.find (hex s)) (Nat.find (hex t)) s hs.1
        (by rw [hmin]; exact hspec')
      rw [hxplus]
      exact hagree
    have hderiv : HasDerivAt (xs (Nat.find (hex t))) (f (xs (Nat.find (hex t)) t)) t := by
      by_cases ht0 : t ≤ 0
      · have heq : (xs (Nat.find (hex t))) t = x₀sol t :=
          hxsa (Nat.find (hex t)) t (le_trans ht0 (le_of_lt ht₀))
        rw [heq]
        have hd := hx₀sold t ⟨ht, lt_of_le_of_lt ht0 hε⟩
        have hcong2 : x₀sol =ᶠ[𝓝 t] (xs (Nat.find (hex t))) :=
          Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ⟨ht, lt_of_le_of_lt ht0 ht₀⟩)
            (fun u hu => (hxsa (Nat.find (hex t)) u hu.2.le).symm)
        exact hd.congr_of_eventuallyEq hcong2.symm
      · have htk : t ∈ Set.Ioo 0 (t₀ + ((Nat.find (hex t) : ℕ) : ℝ) * δ) :=
          ⟨lt_of_not_ge ht0, hspec⟩
        exact hxsd (Nat.find (hex t)) t htk
    have hderiv' := hderiv.congr_of_eventuallyEq hcong
    have hval : xplus t = xs (Nat.find (hex t)) t := by rw [hxplus]
    rw [← hval] at hderiv'
    exact hderiv'
  · intro t ht ht0
    rw [hxplus]
    exact hxsa (Nat.find (hex t)) t ht0

end Forward

/-! ## The two-sided solution -/

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **A global two-sided solution.**  Let `f` be a Lipschitz field with at most linear growth and
let `x₀sol` be a local solution of `ẋ = f x` through `x₀` on `(-ε, ε)`.  Then there is a function
`γ : ℝ → E` with `γ 0 = x₀` which solves `ẋ = f x` on all of `ℝ`.

The backward piece is obtained by applying the forward continuation to the *negated* field
`g x = -f x` and reflecting the result: if `w` solves `ẇ = g w` then `t ↦ w (-t)` solves
`ẋ = f x` on the negative half axis.  The two pieces are pasted at `0` with
`CRNT.ReactionDiffusion.hasDerivAt_paste`. -/
theorem exists_global_twoSided_solution_of_linearGrowth {f : E → E} {K : ℝ≥0}
    (hl : LipschitzWith K f)
    {C : ℝ} (hC : 0 < C) (hgrow : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)) {δ : ℝ} (hδC : δ = 1 / (2 * C))
    {x₀ : E} {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : 0 < t₀) (ht₀ε : t₀ < ε)
    (x₀sol : ℝ → E) (hx₀sol0 : x₀sol 0 = x₀)
    (hx₀sold : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt x₀sol (f (x₀sol t)) t) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  have hδ : 0 < δ := by rw [hδC]; positivity
  set g : E → E := fun x => -f x with hg
  have hgl : LipschitzWith K g := lipschitzWith_neg hl
  have hggrow : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) := by
    intro x
    have h := hgrow x
    rw [hg]
    simpa using h
  -- the local solution of the negated field is the reflection of the local solution
  set w₀sol : ℝ → E := fun t => x₀sol (-t) with hw₀
  have hw₀0 : w₀sol 0 = x₀ := by simp [hw₀, hx₀sol0]
  have hw₀d : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt w₀sol (g (w₀sol t)) t := by
    intro t ht
    have h1 : -t ∈ Set.Ioo (-ε) ε := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h2 := hx₀sold (-t) h1
    have h3 := hasDerivAt_neg_comp h2
    have h4 : -(f (x₀sol (-t))) = g (w₀sol t) := by
      rw [hg, hw₀]
    rw [h4] at h3
    simpa only [hw₀, neg_neg] using h3
  -- the forward pieces
  obtain ⟨xplus, hxplus0, hxplusd, hxplusa⟩ :=
    exists_global_forward_solution (f := f) hl hC hgrow hδC hε ht₀ ht₀ε x₀sol hx₀sol0 hx₀sold
  obtain ⟨wplus, hwplus0, hwplusd, hwplusa⟩ :=
    exists_global_forward_solution (f := g) hgl hC hggrow hδC hε ht₀ ht₀ε w₀sol hw₀0 hw₀d
  -- the backward piece is the reflection of the forward solution of the negated field
  set xminus : ℝ → E := fun t => wplus (-t) with hxminus
  have hxminus0 : xminus 0 = x₀ := by simp [hxminus, hwplus0]
  have hxminusd : ∀ t < 0, HasDerivAt xminus (f (xminus t)) t := by
    intro t ht
    have h1 : -ε < -t := by linarith
    have h2 := hwplusd (-t) h1
    have h3 := hasDerivAt_neg_comp h2
    have h4 : -(g (wplus (-t))) = f (xminus t) := by
      simp only [hg, hxminus]
      exact neg_neg _
    rw [h4] at h3
    simpa only [hxminus, neg_neg] using h3
  have hxminus0d : HasDerivAt xminus (f (xminus 0)) 0 := by
    have h1 := hwplusd 0 (by linarith [hε])
    have h2 := hasDerivAt_neg_comp h1
    have h3 : -(g (wplus 0)) = f (xminus 0) := by
      simp only [hg, hxminus, neg_zero]
      exact neg_neg _
    rw [h3] at h2
    simpa only [hxminus, neg_neg, neg_zero] using h2
  have hxplus0d : HasDerivAt xplus (f (xplus 0)) 0 := hxplusd 0 (by linarith [hε])
  -- paste the two pieces at `0`
  set γ : ℝ → E := fun t => if t ≤ 0 then xminus t else xplus t with hγ
  have hγ0 : γ 0 = x₀ := by simp [hγ, hxminus0]
  have hpaste : HasDerivAt γ (f (γ 0)) 0 := by
    refine hasDerivAt_paste (f := f) (x := xminus) (α := xplus) (a := -δ) (b := δ)
      (by linarith) (by linarith) (by linarith) (by linarith)
      hxminus0d.hasDerivWithinAt hxplus0d.hasDerivWithinAt ?_ ?_
    · rw [hxplus0, hxminus0]
    · intro s
      rw [hγ]
  refine ⟨γ, hγ0, ?_⟩
  intro t
  by_cases ht0 : t ≤ 0
  · by_cases hteq : t = 0
    · subst hteq
      exact hpaste
    · have hlt : t < 0 := lt_of_le_of_ne ht0 hteq
      have hderiv := hxminusd t hlt
      have hcong : γ =ᶠ[𝓝 t] xminus := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
        have hu' : u < 0 := Set.mem_Iio.mp hu
        simp [hγ, hu'.le]
      have hderiv' := hderiv.congr_of_eventuallyEq hcong
      have hval : γ t = xminus t := by simp [hγ, ht0]
      rw [← hval] at hderiv'
      exact hderiv'
  · have hderiv := hxplusd t (by linarith [hε])
    have hcong : γ =ᶠ[𝓝 t] xplus := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo 0 (t + 1) from
          ⟨lt_of_not_ge ht0, by linarith⟩)] with u hu
      have hu' : 0 < u := hu.1
      simp [hγ, not_le_of_gt hu']
    have hderiv' := hderiv.congr_of_eventuallyEq hcong
    have hval : γ t = xplus t := by simp [hγ, ht0]
    rw [← hval] at hderiv'
    exact hderiv'

end TwoSided

/-! ## Uniqueness and the semigroup law -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness of the global solution.**  Two global solutions of `ẋ = f x` with the same
initial value coincide. -/
theorem global_solution_unique {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t) (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t)
    (h0 : γ₁ 0 = γ₂ 0) : γ₁ = γ₂ := by
  exact ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => Set.univ)
    (fun _ => hl.lipschitzOnWith) (fun t => ⟨h₁ t, Set.mem_univ _⟩) (fun t => ⟨h₂ t, Set.mem_univ _⟩)
    h0

end Uniqueness

section Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The semigroup law.**  Let `γ` be a global solution of `ẋ = f x` and let `η` be a global
solution through the point `γ s`.  Then `η t = γ (s + t)` for all `t`.

Indeed, the shifted solution `t ↦ γ (s + t)` is again a solution of the initial value problem
with the initial value `γ s`, so by uniqueness it agrees with `η`. -/
theorem global_solution_semigroup {f : E → E} {K : ℝ≥0} (hl : LipschitzWith K f)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (f (γ t)) t)
    {s : ℝ} {η : ℝ → E} (hη : ∀ t, HasDerivAt η (f (η t)) t) (hη0 : η 0 = γ s) :
    ∀ t, η t = γ (s + t) := by
  have hshift : ∀ t : ℝ, HasDerivAt (fun u => γ (u + s)) (f (γ (t + s))) t := by
    intro t
    have hg : HasDerivAt (fun u : ℝ => u + s) 1 t := by
      simpa using (hasDerivAt_id t).add_const s
    simpa [Function.comp_def] using (hγ (t + s)).scomp t hg
  have heq : (fun u => γ (u + s)) = η := global_solution_unique hl hshift hη (by
    rw [zero_add]; exact hη0.symm)
  intro t
  have h1 := congrFun heq t
  rw [← add_comm s t] at h1
  exact h1.symm

end Semigroup

/-! ## The semidiscrete reaction–diffusion system -/

section Semidiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A global two-sided solution of the semidiscrete reaction–diffusion ODE.**  For every
initial value `x₀` there is a solution `γ : ℝ → (ι → ℝ)` of `ẋ = D Δ_h x + f(x)` on the whole
real line, with `γ 0 = x₀`.

In particular, restricting `γ` to `(-T, T)` gives a solution on `(-T, T)` for every `T > 0`. -/
theorem exists_global_twoSided_solution
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    (x₀ : ι → ℝ) [Nonempty ι] :
    ∃ γ : ℝ → (ι → ℝ), γ 0 = x₀ ∧
      ∀ t, HasDerivAt γ (reactionDiffusionField D f (γ t)) t := by
  obtain ⟨C, hC, hgrowth⟩ := reactionDiffusionField_growth_le D f L hL hf
  have hlip : LipschitzWith (Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)))
      (reactionDiffusionField D f) :=
    reactionDiffusionField_lipschitz D f L hf
  obtain ⟨ε, hε, γ₀, hγ₀0, hγ₀d⟩ := exists_reactionDiffusion_solution D f L hL hf x₀
  obtain ⟨γ, hγ0, hγd⟩ :=
    exists_global_twoSided_solution_of_linearGrowth (E := ι → ℝ) hlip (C := C + 1)
      (by linarith)
      (fun x => by
        have hx := hgrowth x
        calc ‖reactionDiffusionField D f x‖ ≤ C * (1 + ‖x‖) := hx
          _ ≤ (C + 1) * (1 + ‖x‖) := by
            have hnonneg : (0:ℝ) ≤ 1 * (1 + ‖x‖) := by positivity
            nlinarith [hnonneg])
      (δ := 1 / (2 * (C + 1))) (by rfl) (ε := ε) (t₀ := ε / 2)
      (by linarith) (by linarith) (by linarith) γ₀ hγ₀0 hγ₀d
  exact ⟨γ, hγ0, hγd⟩

/-- **The flow of the semidiscrete reaction–diffusion system.**  There is a forward flow
`Flow ℝ≥0 (ι → ℝ)` of the semidiscrete field, whose orbits are the global (two-sided) solutions
of the semidiscrete ODE; the semigroup law `ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x)` holds. -/
theorem exists_reactionDiffusion_flow
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    [Nonempty ι] :
    ∃ (ϕ : Flow ℝ≥0 (ι → ℝ)) (γ : (ι → ℝ) → ℝ → (ι → ℝ)),
      (∀ x, γ x 0 = x) ∧ (∀ x t, HasDerivAt (γ x) (reactionDiffusionField D f (γ x t)) t) ∧
      (∀ x (t : ℝ≥0), ϕ t x = γ x (t : ℝ)) := by
  set K : ℝ≥0 := Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)) with hK
  have hlip : LipschitzWith K (reactionDiffusionField D f) := by
    rw [hK]
    exact reactionDiffusionField_lipschitz D f L hf
  choose γ hγ0 hγd using fun x => exists_global_twoSided_solution D f L hL hf x
  have hγc : ∀ x, Continuous (γ x) :=
    fun x => continuous_iff_continuousAt.2 fun t => (hγd x t).continuousAt
  -- the semigroup law
  have hsemi : ∀ (x : ι → ℝ) (a b : ℝ), γ x (a + b) = γ (γ x b) a := by
    intro x a b
    have h := global_solution_semigroup hlip (hγd x) (hγd (γ x b)) (hγ0 (γ x b))
    have h2 := h a
    have h3 : γ x (b + a) = γ (γ x b) a := h2.symm
    rw [add_comm b a] at h3
    exact h3
  -- joint continuity, from the continuous dependence estimate
  have hcont : Continuous (Function.uncurry fun (t : ℝ≥0) (x : ι → ℝ) => γ x (t : ℝ)) := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    obtain ⟨t₀, x₀⟩ := p
    have he : Continuous fun p : ℝ≥0 × (ι → ℝ) => Real.exp (K * (p.1 : ℝ)) :=
      Real.continuous_exp.comp (continuous_const.mul (NNReal.continuous_coe.comp continuous_fst))
    have h1 : Tendsto (fun p : ℝ≥0 × (ι → ℝ) => dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by
      have hcd : Continuous fun p : ℝ≥0 × (ι → ℝ) => dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) :=
        (continuous_snd.dist continuous_const).mul he
      exact hcd.tendsto' (t₀, x₀) 0 (by simp)
    have h2 : Tendsto (fun p : ℝ≥0 × (ι → ℝ) => dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by
      have hcd : Continuous fun p : ℝ≥0 × (ι → ℝ) => dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) :=
        ((hγc x₀).comp (NNReal.continuous_coe.comp continuous_fst)).dist continuous_const
      exact hcd.tendsto' (t₀, x₀) 0 (by simp)
    have hbound : Tendsto (fun p : ℝ≥0 × (ι → ℝ) =>
        dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)))
        (𝓝 (t₀, x₀)) (𝓝 0) := by simpa using h1.add h2
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) hbound
    calc dist (γ p.2 (p.1 : ℝ)) (γ x₀ (t₀ : ℝ))
        ≤ dist (γ p.2 (p.1 : ℝ)) (γ x₀ (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) :=
          dist_triangle _ _ _
      _ ≤ dist p.2 x₀ * Real.exp (K * (p.1 : ℝ)) + dist (γ x₀ (p.1 : ℝ)) (γ x₀ (t₀ : ℝ)) := by
          gcongr
          have hd := ODE.dist_le_of_isIntegralCurve hlip (hγd p.2) (hγd x₀) (p.1).coe_nonneg
          rwa [hγ0 p.2, hγ0 x₀] at hd
  let ϕ : Flow ℝ≥0 (ι → ℝ) :=
    { toFun := fun t x => γ x (t : ℝ)
      cont' := hcont
      map_zero' := fun x => hγ0 x
      map_add' := fun t₁ t₂ x => by
        have hc : ((t₁ + t₂ : ℝ≥0) : ℝ) = (t₁ : ℝ) + (t₂ : ℝ) := NNReal.coe_add t₁ t₂
        simp only [hc]
        exact hsemi x (t₁ : ℝ) (t₂ : ℝ) }
  exact ⟨ϕ, γ, hγ0, hγd, fun _ _ => rfl⟩

/-- **A two-sided solution on `(-T, T)`.**  For every `T > 0` there is a solution of the
semidiscrete ODE on `(-T, T)` through `x₀`; it is the restriction of a global two-sided
solution. -/
theorem exists_twoSided_solution_on_Ioo
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    (x₀ : ι → ℝ) [Nonempty ι] (T : ℝ) (hT : 0 < T) :
    ∃ γ : ℝ → (ι → ℝ), γ 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-T) T, HasDerivAt γ (reactionDiffusionField D f (γ t)) t := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_twoSided_solution D f L hL hf x₀
  have hmem : (0:ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, by linarith⟩
  exact ⟨γ, hγ0, fun t _ => hγ t⟩

/-- **The semigroup law of the flow.**  `ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x)`: the flow of the
semidiscrete field is a semigroup. -/
theorem exists_reactionDiffusion_flow_semigroup
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    [Nonempty ι] :
    ∃ (ϕ : Flow ℝ≥0 (ι → ℝ)), ∀ (t₁ t₂ : ℝ≥0) (x : ι → ℝ), ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) := by
  obtain ⟨ϕ, _, _, _, _⟩ := exists_reactionDiffusion_flow D f L hL hf
  exact ⟨ϕ, fun t₁ t₂ x => ϕ.map_add' t₁ t₂ x⟩

/-- **A concrete instance.**  The one-site decay system `ẋ = -x` (no diffusion, one species) is a
semidiscrete reaction–diffusion system; it admits a global two-sided solution.  This shows that
the statements above are not vacuous. -/
theorem exists_decay_twoSided_solution (x₀ : ℝ) :
    ∃ γ : ℝ → (Fin 1 → ℝ), γ 0 = (fun _ : Fin 1 => x₀) ∧
      ∀ t, HasDerivAt γ (fun _ : Fin 1 => -(γ t 0)) t := by
  have hf : ∀ (i : Fin 1) x y, |(-x : ℝ) - (-y : ℝ)| ≤ (1:ℝ) * |x - y| := by
    intro i x y
    rw [show (-x : ℝ) - (-y : ℝ) = -(x - y) by ring, abs_neg]
    simp
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_global_twoSided_solution (ι := Fin 1) (D := fun _ => 0) (f := fun _ x => -x)
      (L := 1) (by norm_num) hf (x₀ := fun _ => x₀)
  have hfield : ∀ t, reactionDiffusionField (fun _ : Fin 1 => 0) (fun _ x => -x) (γ t)
      = fun _ : Fin 1 => -(γ t 0) := by
    intro t
    funext i
    fin_cases i
    simp [reactionDiffusionField, laplacian]
  refine ⟨γ, ?_, ?_⟩
  · simpa using hγ0
  · intro t
    have hγt := hγ t
    rw [hfield] at hγt
    exact hγt

end Semidiscrete

end ReactionDiffusion
end CRNT

/-! ## Axioms -/

#print axioms CRNT.ReactionDiffusion.exists_solution_extend_agree
#print axioms CRNT.ReactionDiffusion.exists_global_forward_solution
#print axioms CRNT.ReactionDiffusion.exists_global_twoSided_solution_of_linearGrowth
#print axioms CRNT.ReactionDiffusion.global_solution_unique
#print axioms CRNT.ReactionDiffusion.global_solution_semigroup
#print axioms CRNT.ReactionDiffusion.exists_global_twoSided_solution
#print axioms CRNT.ReactionDiffusion.exists_reactionDiffusion_flow
#print axioms CRNT.ReactionDiffusion.exists_twoSided_solution_on_Ioo
#print axioms CRNT.ReactionDiffusion.exists_reactionDiffusion_flow_semigroup
#print axioms CRNT.ReactionDiffusion.exists_decay_twoSided_solution
