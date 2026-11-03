import CRNT.Dynamics.FlowSmoothDependence
import CRNT.Analysis.LinearODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The fundamental matrix of the mass-action flow

This module supplies the **fundamental-matrix step** of the smooth-dependence theorem for the
mass-action flow: the variational equation of the flow along the orbit of a point has a
solution, and that solution is the derivative of the flow in its initial point.

## The classical theorem

For an autonomous ODE `x' = f(x)` with `f` locally Lipschitz, the flow `x0 |-> Phi x0 t` depends
continuously on the initial point; if `f` is `C1`, the dependence is differentiable, and the
derivative is given by the **fundamental matrix** `V t` of the *variational equation*

`V' = Df (Phi x0 t) . V`,   `V 0 = id`,

so that `d/dt_x (Phi x0 t) = V t`.  This is the classical smooth-dependence theorem of ODEs
(E. Coddington and O. Levinson, *Theory of Ordinary Differential Equations*, Ch. I, Sec. 5;
W. Hale, *Ordinary Differential Equations*, Ch. 3, Sec. 8).  It is one of the two universal
inputs of the Poincare-Bendixson route to the existence of periodic orbits in the plane: the
other is the Jordan separation theorem.

## What the repository already had

* `CRNT/Dynamics/FlowSmoothDependence.lean` records the *target* as data:
  `Network.MassActionFlowSmoothDependenceTarget`, and decomposes it into
  `Network.UniformModulusTarget`, `Network.FundamentalMatrixTarget` (the step discharged here)
  and `Network.DerivativeAssemblyTarget`.
* `CRNT/Dynamics/VariationalEquation.lean` proves the analytic core of the differentiable
  dependence, the Gronwall variational estimate

  ```
  theorem ODE.norm_flow_variational_error_le {f : E -> E} {x y W : R -> E} {v : E} {h K rho T : R}
      (hK : 0 <= K) (hrho : 0 <= rho)
      (hx : forall t in Ico 0 T, HasDerivAt x (f (x t)) t)
      (hy : forall t in Ico 0 T, HasDerivAt y (f (y t)) t)
      (hW : forall t in Ico 0 T, HasDerivAt W ((fderiv R f (x t)) (W t)) t)
      (hxc : ContinuousOn x (Icc 0 T)) (hyc : ContinuousOn y (Icc 0 T))
      (hWc : ContinuousOn W (Icc 0 T))
      (hDfK : forall t in Ico 0 T, ||fderiv R f (x t)|| <= K)
      (hmod : forall t in Ico 0 T,
        ||f (y t) - f (x t) - (fderiv R f (x t)) (y t - x t)|| <= rho * ||y t - x t||)
      (hsep : forall t in Ico 0 T, ||y t - x t|| <= |h| * ||v|| * Real.exp (K * t))
      (h0 : (y 0 - x 0) - h . W 0 = 0) :
      forall t in Icc 0 T,
        ||(y t - x t) - h . W t|| <= gronwallBound 0 K (rho * (|h| * ||v|| * Real.exp (K * T))) t
  ```

  i.e. the flow separation `y t - x t` differs from its linear prediction `h . W t` by a
  quantity that is `O (rho |h|)`, where `rho` is a modulus of continuity of `Df` along the
  joining segment.
* `CRNT/Dynamics/FlowConstruction.lean` builds the flow of a *bounded* Lipschitz field
  (`ODE.exists_flow`), and `CRNT/Analysis/LinearODE.lean` solves linear ODEs on a compact
  interval (`CRNT.exists_linear_ode_Icc`).

## What this module proves

The mass-action field is `C^oo` (`N.massActionVectorField_contDiff`), hence its flow is
differentiable in the initial point, and the derivative is the fundamental matrix.  The
mathematical content is the solution of the *variational equation*, a linear ODE on the
Banach space of continuous linear maps of the concentration space into itself:

* `exists_global_solution` -- the general fact that a linear ODE `phi' = B t phi` with `B`
  continuous has a global solution `phi` with `phi 0 = x0` and `HasDerivAt phi (B t (phi t)) t`
  for all `t`.  The proof chains the solutions of `CRNT.exists_linear_ode_Icc` on adjacent
  intervals, gluing them with a new gluing lemma for `HasDerivWithinAt`; the two time
  directions are joined at `0` by mirroring the equation.
* `exists_variationalFundamental` -- the **fundamental matrix of the mass-action flow**: for
  every flow family `F` of the mass-action field there is `V` with `V x 0 = id` and

  ```
  forall x t, HasDerivAt (fun tau => V x tau) (N.massActionJacobianCLM k (F.flow x t) .L V x t) t
  ```

  i.e. `V x` solves the variational equation `V' = J (Phi x t) .L V` along the orbit of `x`,
  with `V x 0 = id`.
* `variationalFundamental_exists` -- the pointwise form `d/dt (V x t v) = J (Phi x t) (V x t v)`,
  which is exactly the data of the repository's structure `Network.VariationalFundamental`.
* `fundamentalMatrixTarget` -- the repository's second decomposition step
  (`Network.FundamentalMatrixTarget`) is discharged: every flow family of the mass-action field
  has a fundamental matrix.

## What is *not* claimed

The Frechet-differentiability of the flow in the initial point (`HasFDerivAt (fun y => F.flow y t)
(V x t) x`) and the joint continuity of `(x, t) |-> F.flow x t` are **not** proved here; they are
the third step (`Network.DerivativeAssemblyTarget`) of the decomposition in
`CRNT/Dynamics/FlowSmoothDependence.lean`, and they require the uniform modulus of continuity of
the Jacobian along the joining segment, which the repository still has to provide.  Moreover the
**Jordan separation theorem** -- the second universal input of the Poincare-Bendixson theorem --
is out of the reach of Mathlib and remains an open target of the repository.  No
Poincare-Bendixson conclusion is claimed in this module.
-/

open Set Filter
open scoped Topology

namespace CRNT
namespace Dynamics

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Glue two solutions of a linear ODE on adjacent intervals. -/
theorem linear_ode_glue_general (B : ℝ → E →L[ℝ] E) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {φ β : ℝ → E}
    (hφ : ∀ s ∈ Icc a b, HasDerivWithinAt φ (B s (φ s)) (Icc a b) s)
    (hβ : ∀ s ∈ Icc b c, HasDerivWithinAt β (B s (β s)) (Icc b c) s)
    (heq : β b = φ b) :
    ∀ s ∈ Icc a c, HasDerivWithinAt (fun s => if s ≤ b then φ s else β s)
      (B s (if s ≤ b then φ s else β s)) (Icc a c) s := by
  set γ : ℝ → E := fun s => if s ≤ b then φ s else β s with hγ
  have hγφ : ∀ s ∈ Icc a b, γ s = φ s := fun s hs => ite_eq_left hs.2
  have hγβ : ∀ s ∈ Icc b c, γ s = β s := by
    intro s hs
    by_cases h : s ≤ b
    · have : s = b := le_antisymm h hs.1
      simp only [hγ, ite_eq_left h]; rw [this, heq]
    · exact ite_eq_right h
  have hunion : Icc a b ∪ Icc b c = Icc a c := Icc_union_Icc_eq_Icc hab hbc
  intro s hs
  rcases lt_trichotomy s b with hlt | heq' | hgt
  · have hsφ : s ∈ Icc a b := ⟨hs.1, hlt.le⟩
    have h1 := (hφ s hsφ).congr_of_mem hγφ hsφ
    rw [show (if s ≤ b then φ s else β s) = φ s from hγφ s hsφ]
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [← hunion]
    refine mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, hlt, fun y hy => ?_⟩
    rcases hy.2 with h | h
    · exact h
    · exact absurd hy.1 (not_lt.mpr h.1)
  · subst heq'
    have h1 := (hφ s ⟨hab, le_rfl⟩).congr_of_mem hγφ ⟨hab, le_rfl⟩
    have h2 := (hβ s ⟨le_rfl, hbc⟩).congr_of_mem hγβ ⟨le_rfl, hbc⟩
    rw [heq] at h2
    rw [ite_eq_left le_rfl, ← hunion]
    exact h1.union h2
  · have hsβ : s ∈ Icc b c := ⟨hgt.le, hs.2⟩
    have h1 := (hβ s hsβ).congr_of_mem hγβ hsβ
    rw [show (if s ≤ b then φ s else β s) = β s from hγβ s hsβ]
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [← hunion]
    refine mem_nhdsWithin.mpr ⟨Ioi b, isOpen_Ioi, hgt, fun y hy => ?_⟩
    rcases hy.2 with h | h
    · exact absurd hy.1 (not_lt.mpr h.2)
    · exact h

/-- Existence of a solution of the linear ODE `φ' = B φ` on `[a, b]` with `φ a = x₀`. -/
theorem exists_linear_ode_Icc' (B : ℝ → E →L[ℝ] E) {a b : ℝ} (hab : a ≤ b)
    (hB : ContinuousOn B (Icc a b)) (x₀ : E) :
    ∃ φ : ℝ → E, φ a = x₀ ∧ ∀ s ∈ Icc a b, HasDerivWithinAt φ (B s (φ s)) (Icc a b) s := by
  have hcont : ContinuousOn (fun t : ℝ => t + a) (Icc 0 (b - a)) := by
    have h1 : ContinuousOn (fun t : ℝ => t + a) (Icc 0 (b - a)) :=
      (continuousOn_id : ContinuousOn id (Icc 0 (b - a))).add
        (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => a) (Icc 0 (b - a)))
    exact h1
  have hB' : ContinuousOn (fun t => B (t + a)) (Icc 0 (b - a)) := by
    exact hB.comp hcont (by
      intro t ht
      simp only [mem_Icc] at ht ⊢
      constructor <;> linarith)
  obtain ⟨ψ, hψ0, hψ⟩ :=
    exists_linear_ode_Icc (fun t => B (t + a)) (by linarith [hab]) hB' x₀
  refine ⟨fun t => ψ (t - a), ?_, ?_⟩
  · show ψ (a - a) = x₀
    rw [sub_self, hψ0]
  · intro s hs
    simp only [mem_Icc] at hs
    have hmem : s - a ∈ Icc 0 (b - a) := by constructor <;> linarith
    have hderiv := hψ (s - a) hmem
    have hneg : HasDerivWithinAt (fun t : ℝ => t - a) 1 (Icc a b) s := by
      have h1 : HasDerivAt (fun t : ℝ => t - a) 1 s := by
        have hx := (hasDerivAt_id s).sub (hasDerivAt_const s a)
        have heq : (id - fun _ : ℝ => a) = (fun t : ℝ => t - a) := by
          funext t; simp
        rw [heq] at hx
        simpa using hx
      exact h1.hasDerivWithinAt
    have hmaps : MapsTo (fun t : ℝ => t - a) (Icc a b) (Icc 0 (b - a)) := by
      intro t ht
      simp only [mem_Icc] at ht ⊢
      constructor <;> linarith
    have h := hderiv.scomp (x := s) hneg hmaps
    simpa [Function.comp_def, smul_eq_mul, add_sub_cancel] using h

/-- **A compatible chain of solutions of a linear ODE on `[0, n]`.** -/
theorem exists_linear_ode_chain (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃ A : ℕ → (ℝ → E),
      (∀ n : ℕ, A n 0 = x₀) ∧
      (∀ (n : ℕ) (s : ℝ), s ∈ Icc 0 (Nat.succ n : ℝ) → HasDerivWithinAt (A n) (B s (A n s))
          (Icc 0 (Nat.succ n : ℝ)) s) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc 0 (Nat.succ n : ℝ) → A (Nat.succ n) t = A n t) := by
  classical
  obtain ⟨A0, hA00, hA0⟩ :=
    exists_linear_ode_Icc' B (a := 0) (b := 1) (by norm_num) hB.continuousOn x₀
  -- the pieces of the chain
  have hpiece : ∀ (n : ℕ) (φ : ℝ → E), ∃ χ : ℝ → E,
      χ (Nat.succ n) = φ (Nat.succ n) ∧
      (∀ (s : ℝ), s ∈ Icc (Nat.succ n : ℝ) (Nat.succ (Nat.succ n) : ℝ) →
        HasDerivWithinAt χ (B s (χ s)) (Icc (Nat.succ n : ℝ) (Nat.succ (Nat.succ n) : ℝ)) s) := by
    intro n φ
    obtain ⟨χ, hχ0, hχ⟩ := exists_linear_ode_Icc' B (a := Nat.succ n) (b := Nat.succ (Nat.succ n))
      (by norm_num) hB.continuousOn (φ (Nat.succ n))
    exact ⟨χ, hχ0, hχ⟩
  set pieces : ℕ → (ℝ → E) :=
    Nat.rec (motive := fun _ => ℝ → E) A0 (fun n φ => Classical.choose (hpiece n φ)) with hpieces
  -- the accumulated solutions
  set acc : ℕ → (ℝ → E) :=
    Nat.rec (motive := fun _ => ℝ → E) (pieces 0)
      (fun (n : ℕ) (a : ℝ → E) => fun (t : ℝ) => if t ≤ (Nat.succ n : ℝ) then a t else pieces (Nat.succ n) t)
      with hacc
  have hpieces_zero : pieces 0 = A0 := by
    rw [hpieces]; rfl
  have hpieces_succ (n : ℕ) : pieces (Nat.succ n) = Classical.choose (hpiece n (pieces n)) := by
    rw [hpieces]
  have hacc_zero : acc 0 = pieces 0 := by
    rw [hacc]; rfl
  have hacc_succ (n : ℕ) :
      acc (Nat.succ n) = fun t => if t ≤ (Nat.succ n : ℝ) then acc n t else pieces (Nat.succ n) t := by
    rw [hacc]
  have hacc_pieces : ∀ n : ℕ, acc n (Nat.succ n) = pieces n (Nat.succ n) := by
    intro n
    induction n with
    | zero =>
        rw [hacc_zero]
    | succ n ih =>
        rw [hacc_succ]
        simp
  -- the accumulated solutions satisfy the ODE on `[0, n+1]`
  have hmain : ∀ n : ℕ, (acc n 0 = x₀) ∧
      (∀ (s : ℝ), s ∈ Icc 0 (Nat.succ n : ℝ) → HasDerivWithinAt (acc n) (B s (acc n s))
          (Icc 0 (Nat.succ n : ℝ)) s) ∧
      (∀ (t : ℝ), t ∈ Icc 0 (Nat.succ n : ℝ) → acc (Nat.succ n) t = acc n t) := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · rw [hacc_zero, hpieces_zero]; exact hA00
        · rw [hacc_zero, hpieces_zero]; simpa using hA0
        · intro t ht
          rw [hacc_succ]
          simp only [ite_eq_left ht.2]
    | succ n ih =>
        obtain ⟨h0, hder, heq⟩ := ih
        refine ⟨?_, ?_, ?_⟩
        · rw [hacc_succ]
          have hpos : (0 : ℝ) ≤ (Nat.succ n : ℝ) := Nat.cast_nonneg _
          simp only [ite_eq_left hpos]
          exact h0
        · intro s hs
          have hφd : ∀ (u : ℝ), u ∈ Icc 0 (Nat.succ n : ℝ) → HasDerivWithinAt (acc n) (B u (acc n u))
              (Icc 0 (Nat.succ n : ℝ)) u :=
            hder
          have hχd : ∀ (u : ℝ), u ∈ Icc (Nat.succ n : ℝ) (Nat.succ (Nat.succ n) : ℝ) →
              HasDerivWithinAt (pieces (Nat.succ n)) (B u (pieces (Nat.succ n) u))
                (Icc (Nat.succ n : ℝ) (Nat.succ (Nat.succ n) : ℝ)) u := by
            rw [hpieces_succ]
            exact (Classical.choose_spec (hpiece n (pieces n))).2
          have hχ0 : pieces (Nat.succ n) (Nat.succ n) = acc n (Nat.succ n) := by
            rw [hpieces_succ]
            rw [(Classical.choose_spec (hpiece n (pieces n))).1]
            exact (hacc_pieces n).symm
          have hglue := linear_ode_glue_general B
            (by have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg (α := ℝ) n; linarith)
            (by have h1 : (Nat.succ n : ℝ) ≤ (Nat.succ (Nat.succ n) : ℝ) :=
                Nat.cast_le.2 (Nat.le_succ (Nat.succ n)); exact h1) hφd hχd hχ0
          rw [hacc_succ]
          exact hglue s hs
        · intro t ht
          rw [hacc_succ]
          simp only [ite_eq_left ht.2]
  refine ⟨acc, ?_, ?_, ?_⟩
  · intro n
    exact (hmain n).1
  · intro n s hs
    exact (hmain n).2.1 s hs
  · intro n t ht
    exact (hmain n).2.2 t ht


/-- The cast of a successor into `ℝ`. -/
theorem cast_natSucc (m : ℕ) : (Nat.succ m : ℝ) = (m : ℝ) + 1 := by
  simp [Nat.succ_eq_add_one, Nat.cast_succ]

/-- **The global forward solution of a linear ODE with continuous coefficients.** -/
theorem exists_global_forward (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃ (Φ : ℝ → E) (A : ℕ → (ℝ → E)),
      Φ 0 = x₀ ∧ (∀ t > 0, HasDerivAt Φ (B t (Φ t)) t) ∧
      (∀ s ∈ Icc 0 1, Φ s = A 0 s) ∧
      (∀ s ∈ Icc 0 1, HasDerivWithinAt (A 0) (B s ((A 0) s)) (Icc 0 1) s) := by
  obtain ⟨A, hA0, hAd, hAeq⟩ := exists_linear_ode_chain B hB x₀
  -- the chain is consistent: `A n` and `A m` agree on `[0, m+1]` when `m ≤ n`
  have htrans : ∀ (n m : ℕ), m ≤ n → ∀ t : ℝ, t ∈ Icc 0 (Nat.succ m : ℝ) → A n t = A m t := by
    intro n
    induction n with
    | zero =>
        intro m hm t ht
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        rfl
    | succ n ih =>
        intro m hm t ht
        by_cases heq : m = Nat.succ n
        · subst heq
          rfl
        · have hmn : m ≤ n := by omega
          have ht' : t ∈ Icc 0 (Nat.succ n : ℝ) := by
            refine ⟨ht.1, ?_⟩
            have h2 : (Nat.succ m : ℝ) ≤ (Nat.succ n : ℝ) := by
              rw [cast_natSucc, cast_natSucc]
              simpa using (Nat.succ_le_succ hmn)
            exact le_trans ht.2 h2
          rw [hAeq n t ht']
          exact ih m hmn t ht
  -- the global forward solution
  set Φ : ℝ → E := fun t => if t ≤ 0 then x₀ else A (Nat.floor t) t with hΦ
  have hΦ_zero : Φ 0 = x₀ := by
    rw [hΦ]; simp
  have hΦ_eq : ∀ (n : ℕ) (t : ℝ), t ∈ Icc 0 (Nat.succ n : ℝ) → t > 0 → Φ t = A n t := by
    intro n t ht ht0
    rw [hΦ]
    simp only [ite_eq_right (not_le.mpr ht0)]
    have hfl : (Nat.floor t : ℝ) ≤ t := Nat.floor_le (R := ℝ) (a := t) (by linarith [ht.1])
    have hfl_le : (Nat.floor t : ℝ) ≤ (Nat.succ n : ℝ) := le_trans hfl ht.2
    have hfl_nat : Nat.floor t ≤ Nat.succ n := by
      have h := Nat.floor_mono (show t ≤ (Nat.succ n : ℝ) from ht.2)
      rw [Nat.floor_natCast] at h
      simpa using h
    by_cases hcase : Nat.floor t ≤ n
    · have hmem : t ∈ Icc 0 (Nat.succ (Nat.floor t) : ℝ) := by
        refine ⟨ht.1, ?_⟩
        rw [cast_natSucc]
        exact (Nat.lt_floor_add_one t).le
      have hA := htrans n (Nat.floor t) hcase t hmem
      exact hA.symm
    · have hfl' : Nat.floor t = Nat.succ n := by omega
      rw [hfl']
      exact hAeq n t ht
  refine ⟨Φ, A, hΦ_zero, ?_, ?_, ?_⟩
  · intro t ht
    set n := Nat.floor t with hn
    have htmem : t ∈ Icc 0 (Nat.succ n : ℝ) := by
      refine ⟨ht.le, ?_⟩
      rw [cast_natSucc, hn]
      exact (Nat.lt_floor_add_one t).le
    have hderiv := hAd n t htmem
    have hcongr : ∀ s ∈ Icc 0 (Nat.succ n : ℝ), Φ s = A n s := by
      intro s hs
      by_cases hs0 : s > 0
      · exact hΦ_eq n s hs hs0
      · have hsz : s = 0 := le_antisymm (le_of_not_gt hs0) hs.1
        subst hsz
        simp [hΦ, hA0 n]
    have hwithin := hderiv.congr_of_mem hcongr htmem
    have hval : A n t = Φ t := (hΦ_eq n t htmem ht).symm
    rw [hval] at hwithin
    refine hwithin.hasDerivAt (Icc_mem_nhds_iff.2 ⟨ht, ?_⟩)
    rw [cast_natSucc, hn]
    exact Nat.lt_floor_add_one t
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      simp [hΦ, hA0 0]
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      rw [hΦ]
      simp only [ite_eq_right (not_le.mpr hspos)]
      by_cases hfl : Nat.floor s = 0
      · rw [hfl]
      · have hfl' : Nat.floor s = 1 := by
          have hfl_le : Nat.floor s ≤ 1 := by
            have := Nat.floor_mono (show s ≤ (1 : ℝ) from hs.2)
            simpa [Nat.floor_natCast] using this
          omega
        rw [hfl']
        have hs1 : s = 1 := by
          have hfl_le : (Nat.floor s : ℝ) ≤ s := Nat.floor_le (R := ℝ) (a := s) (by linarith [hs.1])
          rw [hfl'] at hfl_le
          have h1 : (1 : ℝ) ≤ s := by simpa using hfl_le
          linarith [hs.2]
        subst hs1
        have hmem : (1 : ℝ) ∈ Icc 0 (Nat.succ 0 : ℝ) := by
          refine ⟨by simp, ?_⟩
          rw [cast_natSucc]; simp
        rw [hAeq 0 1 hmem]
  · intro s hs
    have hs' : s ∈ Icc 0 (Nat.succ 0 : ℝ) := by simpa using hs
    simpa using hAd 0 s hs'


/-- **The global solution of a linear ODE with continuous coefficients.** -/
theorem exists_global_solution (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃ Φ : ℝ → E, Φ 0 = x₀ ∧ ∀ t, HasDerivAt Φ (B t (Φ t)) t := by
  obtain ⟨Φf, A, hΦf0, hΦfder, hΦfA, hA0deriv⟩ := exists_global_forward B hB x₀
  -- the time-reversed coefficient
  set negId : E →L[ℝ] E := (-1) • (ContinuousLinearMap.id ℝ E) with hnegId
  have hnegId (v : E) : negId v = -v := by
    simp [negId]
  set C : ℝ → E →L[ℝ] E := fun s => B (-s) ∘L negId with hC
  have hC_cont : Continuous C := by
    have h1 : Continuous (fun s : ℝ => B (-s)) := hB.comp continuous_neg
    rw [hC]
    exact h1.clm_comp_const negId
  have hCval : ∀ t v, C t v = -(B (-t) v) := by
    intro t v
    rw [hC, ContinuousLinearMap.comp_apply, hnegId]
    simp [map_neg]
  obtain ⟨Ψ, D, hΨ0, hΨder, hΨD, hD0deriv⟩ := exists_global_forward C hC_cont x₀
  -- the global solution
  set Φ : ℝ → E := fun t => if t ≤ 0 then Ψ (-t) else Φf t with hΦ
  have hΦ_zero : Φ 0 = x₀ := by
    rw [hΦ]; simp [hΨ0]
  refine ⟨Φ, hΦ_zero, ?_⟩
  intro t
  by_cases ht0 : t = 0
  · subst ht0
    -- the backward piece on `[-1, 0]`
    have hback : ∀ s ∈ Icc (-1) 0,
        HasDerivWithinAt (fun u => D 0 (-u)) (B s ((fun u => D 0 (-u)) s)) (Icc (-1) 0) s := by
      intro s hs
      have hmem : -s ∈ Icc 0 1 := by
        rw [mem_Icc]; constructor <;> linarith [hs.1, hs.2]
      have hderiv := hD0deriv (-s) hmem
      have hneg : HasDerivWithinAt (fun u : ℝ => -u) (-1) (Icc (-1) 0) s :=
        (hasDerivAt_neg s).hasDerivWithinAt
      have hmaps : MapsTo (fun u : ℝ => -u) (Icc (-1) 0) (Icc 0 1) := by
        intro u hu
        rw [mem_Icc] at hu ⊢
        constructor <;> linarith
      have h := hderiv.scomp (x := s) hneg hmaps
      simp only [hCval, smul_neg, neg_smul, neg_neg, one_smul] at h
      simpa [Function.comp_def] using h
    -- glue the backward and the forward piece at `0`
    have hD0zero : D 0 0 = x₀ := by
      have h1 := hΨD 0 (by norm_num)
      rw [hΨ0] at h1
      exact h1.symm
    have hglue := linear_ode_glue_general B (by norm_num) (by norm_num) hback hA0deriv (by
      have h1 : A 0 0 = x₀ := by
        have h2 := hΦfA 0 (by norm_num)
        rw [hΦf0] at h2
        exact h2.symm
      rw [h1, neg_zero, hD0zero])
    have hγderiv : ∀ s ∈ Icc (-1) 1,
        HasDerivWithinAt (fun s => if s ≤ 0 then (fun u => D 0 (-u)) s else (A 0) s)
          (B s (if s ≤ 0 then (fun u => D 0 (-u)) s else (A 0) s)) (Icc (-1) 1) s := by
      intro s hs
      simpa using hglue s hs
    -- the global solution agrees with the glued function near `0`
    have hcong : ∀ s ∈ Icc (-1) 1,
        Φ s = (if s ≤ 0 then (fun u => D 0 (-u)) s else (A 0) s) := by
      intro s hs
      by_cases hs0 : s ≤ 0
      · rw [ite_eq_left hs0]
        by_cases hz : s = 0
        · subst hz
          rw [hΦ]
          simp only [ite_eq_left le_rfl]
          rw [neg_zero, hD0zero]
          exact hΨ0
        · have hmem : -s ∈ Icc 0 1 := by
            rw [mem_Icc]; constructor <;> linarith [hs.1, hs.2]
          have hD := hΨD (-s) hmem
          rw [hΦ]
          simp only [ite_eq_left hs0]
          rw [hD]
      · rw [ite_eq_right hs0]
        have hmem : s ∈ Icc 0 1 := by
          rw [mem_Icc] at hs ⊢
          constructor <;> linarith
        have hA := hΦfA s hmem
        rw [hΦ]
        simp only [ite_eq_right hs0]
        rw [hA]
    have hwithin := (hγderiv 0 (by norm_num)).congr_of_mem hcong (by norm_num)
    have hval : (if (0 : ℝ) ≤ 0 then (fun u => D 0 (-u)) 0 else (A 0) 0) = Φ 0 :=
      (hcong 0 (by norm_num)).symm
    rw [hval] at hwithin
    refine hwithin.hasDerivAt (Icc_mem_nhds_iff.2 ⟨by norm_num, by norm_num⟩)
  · by_cases htneg : t < 0
    · -- the backward direction
      have hΨder' : HasDerivAt Ψ (C (-t) (Ψ (-t))) (-t) := hΨder (-t) (by linarith)
      have hneg : HasDerivAt (fun u : ℝ => -u) (-1) t := hasDerivAt_neg t
      have hcomp := hΨder'.scomp t hneg
      simp only [hCval, smul_neg, neg_smul, neg_neg, one_smul] at hcomp
      have hcong : ∀ s ∈ Icc (t - 1) 0, Φ s = (fun u => Ψ (-u)) s := by
        intro s hs
        rw [hΦ]
        simp only [ite_eq_left hs.2]
      have hwithin := hcomp.hasDerivWithinAt.congr_of_mem hcong (by
        rw [mem_Icc]; constructor <;> linarith)
      have hval' : Ψ (-t) = Φ t := by
        rw [hΦ]; simp [htneg.le]
      rw [hval'] at hwithin
      refine hwithin.hasDerivAt (Icc_mem_nhds_iff.2 ⟨?_, ?_⟩)
      · linarith
      · exact htneg
    · -- the forward direction
      have htpos : 0 < t := by
        have h1 : 0 ≤ t := by linarith
        by_contra hcon
        have h2 : t ≤ 0 := le_of_not_gt hcon
        exact ht0 (le_antisymm h2 h1)
      have hΦfder' : HasDerivAt Φf (B t (Φf t)) t := hΦfder t htpos
      have hcong : ∀ s ∈ Icc 0 (t + 1), Φ s = Φf s := by
        intro s hs
        show (if s ≤ 0 then Ψ (-s) else Φf s) = Φf s
        by_cases hs0 : s = 0
        · subst hs0
          simp [hΨ0, hΦf0]
        · rw [ite_eq_right (not_le.mpr (lt_of_le_of_ne hs.1 (Ne.symm hs0)))]
      have hwithin := hΦfder'.hasDerivWithinAt.congr_of_mem hcong (by
        rw [mem_Icc]; constructor <;> linarith)
      have hval' : Φf t = Φ t := by
        rw [hΦ]; simp [not_le.mpr htpos]
      rw [hval'] at hwithin
      refine hwithin.hasDerivAt (Icc_mem_nhds_iff.2 ⟨?_, ?_⟩)
      · exact htpos
      · linarith


/-! ## The coefficient of the variational equation -/

section Comp

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

/-- **Left composition by a fixed continuous linear map.** For `g : C →L[ℝ] C`, the map
`w ↦ g ∘L w` is a continuous linear map of the Banach space `C →L[ℝ] C` into itself: it is the
second component of the continuous bilinear map `compL` of composition. -/
noncomputable def leftComp (g : C →L[ℝ] C) : (C →L[ℝ] C) →L[ℝ] (C →L[ℝ] C) :=
  ContinuousLinearMap.compL ℝ C C C g

omit [CompleteSpace C] in
@[simp] theorem leftComp_apply (g : C →L[ℝ] C) (w : C →L[ℝ] C) : leftComp g w = g ∘L w := by
  rw [leftComp, ContinuousLinearMap.compL_apply]

omit [CompleteSpace C] in
/-- Left composition by a continuous family of operators is continuous. -/
theorem continuous_leftComp {g : ℝ → C →L[ℝ] C} (hg : Continuous g) :
    Continuous (fun t => leftComp (g t)) := by
  exact (ContinuousLinearMap.compL ℝ C C C).continuous.comp hg


omit [CompleteSpace C] in
/-- **Evaluation at a fixed vector**, as a continuous linear map of the space of continuous
linear maps into the underlying space. -/
theorem evalAt_lipschitz (v : C) :
    LipschitzWith (Real.toNNReal ‖v‖) (fun w : C →L[ℝ] C => w v) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro w₁ w₂
  calc dist (w₁ v) (w₂ v) = ‖w₁ v - w₂ v‖ := dist_eq_norm (w₁ v) (w₂ v)
    _ = ‖(w₁ - w₂) v‖ := by simp
    _ ≤ ‖w₁ - w₂‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = dist w₁ w₂ * ‖v‖ := by rw [dist_eq_norm]
    _ = ↑(Real.toNNReal ‖v‖) * dist w₁ w₂ := by
        rw [show (↑(Real.toNNReal ‖v‖) : ℝ) = ‖v‖ by simp, mul_comm]

/-- **Evaluation at a fixed vector**, as a continuous linear map of the space of continuous
linear maps into the underlying space. -/
noncomputable def evalAt (v : C) : (C →L[ℝ] C) →L[ℝ] C :=
  ContinuousLinearMap.mk
    { toFun := fun w : C →L[ℝ] C => w v
      map_add' := by
        intro w₁ w₂
        simp
      map_smul' := by
        intro c w
        simp }
    (evalAt_lipschitz v).continuous

omit [CompleteSpace C] in
@[simp] theorem evalAt_apply (v : C) (w : C →L[ℝ] C) : evalAt v w = w v := rfl

end Comp
end Linear

/-! ## The mass-action flow -/

open scoped Topology

section MassAction

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The orbits of the flow family are continuous. -/
theorem flowFamily_continuous (F : Network.MassActionFlowFamily N κ) (x : Concentration S) :
    Continuous (F.flow x) := by
  exact continuous_iff_continuousAt.2 fun t => (F.flow_solution x t).continuousAt

/-- **The variational equation of the mass-action flow has a solution.**  The linear equation
`V' = J(x(t)) ∘L V` with `V 0 = id` has a (continuous, operator-norm differentiable) solution on
the whole time line. -/
theorem exists_variationalFundamental (N : Network S) (κ : N.RateConstants)
    (F : Network.MassActionFlowFamily N κ) :
    ∃ V : Concentration S → ℝ → (Concentration S →L[ℝ] Concentration S),
      (∀ x, V x 0 = ContinuousLinearMap.id ℝ (Concentration S)) ∧
      (∀ x t, HasDerivAt (fun τ => V x τ)
        (N.massActionJacobianCLM κ (F.flow x t) ∘L V x t) t) := by
  have hJ : ∀ x : Concentration S,
      Continuous (fun t => N.massActionJacobianCLM κ (F.flow x t)) := by
    intro x
    exact (N.massActionJacobianCLM_continuous κ).comp (flowFamily_continuous F x)
  choose V hV0 hVder using fun x : Concentration S =>
    exists_global_solution (fun t => leftComp (N.massActionJacobianCLM κ (F.flow x t)))
      (continuous_leftComp (hJ x)) (ContinuousLinearMap.id ℝ (Concentration S))
  refine ⟨V, ?_, ?_⟩
  · intro x
    exact hV0 x
  · intro x t
    have h := hVder x t
    have hval : (fun s => leftComp (N.massActionJacobianCLM κ (F.flow x s))) t (V x t)
        = N.massActionJacobianCLM κ (F.flow x t) ∘L V x t := leftComp_apply _ _
    rw [hval] at h
    exact h


/-- **The fundamental matrix of the variational equation exists.**  The pointwise form of the
variational equation, `d/dt (V x t v) = J (Φ x t) (V x t v)`, holds for every `v`. -/
theorem variationalFundamental_exists (N : Network S) (κ : N.RateConstants)
    (F : Network.MassActionFlowFamily N κ) : Nonempty (N.VariationalFundamental κ F) := by
  obtain ⟨V, hV0, hVder⟩ := exists_variationalFundamental N κ F
  refine ⟨{ fundamental := V
            fundamental_zero := hV0
            fundamental_solution := ?_ }⟩
  intro x t v
  have h := hVder x t
  have hc : HasDerivAt (fun _ : ℝ => evalAt v) 0 t := hasDerivAt_const t (evalAt v)
  have h2 := hc.clm_apply h
  simp only [evalAt_apply] at h2
  simpa using h2

/-- **The fundamental-matrix target of `CRNT.Dynamics.FlowSmoothDependence` is discharged:**
every flow family of the mass-action field has a fundamental matrix. -/
theorem fundamentalMatrixTarget (N : Network S) (κ : N.RateConstants) :
    N.FundamentalMatrixTarget κ := by
  intro F
  exact variationalFundamental_exists N κ F

end MassAction

#print axioms CRNT.Dynamics.exists_variationalFundamental
#print axioms CRNT.Dynamics.variationalFundamental_exists
#print axioms CRNT.Dynamics.fundamentalMatrixTarget
#print axioms CRNT.Dynamics.exists_global_solution
