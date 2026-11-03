import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import CRNT.Dynamics.QSSA

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace


/-!
# Boundary-layer exponential attraction for a contracting fast subsystem

This module supplies the fast-side (boundary-layer) half of the singular-perturbation picture
that `CRNT.Dynamics.QSSA` leaves as a hypothesis. For an autonomous field whose unique fast
equilibrium is one-sidedly contracting, an integral curve decays to that equilibrium at an
explicit exponential rate, and the slaving defect `εf` consumed by the compact-time QSSA
estimate becomes a *derived* quantity rather than a postulated one. It is CRN-free and written
in the `ODE` namespace shared with `CRNT.Dynamics.QSSA` and `CRNT.Dynamics.FlowConstruction`.

**One-sided contraction.** Over a real inner product space, `ODE.OneSidedContractionAt f zstar lam`
asserts `⟪f z - f zstar, z - zstar⟫_ℝ ≤ -lam * ‖z - zstar‖ ^ 2` at the point `z`, and
`ODE.OneSidedContraction f zstar lam` quantifies this over all `z`. This is the monotonicity /
dissipativity condition characterising a contracting fast fibre; for a linear field `f z = A z`
it is `⟪A (z - zstar), z - zstar⟫ ≤ -lam ‖z - zstar‖²`, i.e. `A` has its symmetric part bounded
above by `-lam`.

**Exponential-attraction estimate** (`ODE.norm_sub_le_exp_neg_mul`). If `z` is an integral curve
of `f` (`∀ t, HasDerivAt z (f (z t)) t`), `f zstar = 0`, `f` is one-sided contracting at rate
`lam ≥ 0`, then `‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t)` for every `t ≥ 0`. The proof
runs the Lyapunov function `V t = ‖z t - zstar‖²`: `V' t ≤ -2 lam · V t`, so `t ↦ V t · exp(2 lam t)`
is antitone, giving `V t ≤ V 0 · exp(-2 lam t)`, and a square root finishes it.

**Layer collapse** (`ODE.norm_sub_tendsto_zero`). With `0 < lam` the envelope `‖z 0 - zstar‖·exp(-lam t)`
tends to `0`, so `‖z t - zstar‖ → 0`: the boundary layer collapses onto the fast equilibrium.

**Fast subsystem** (`ODE.FastSubsystem`). The bundle of a fast field, its equilibrium, and a
positive contraction rate, with `FastSubsystem.attraction_bound` re-exporting the estimate.

**Derived QSSA defect** (`ODE.qssaDefect_of_fastSubsystem`). For a full field `full = fast + slow`
of a fast subsystem, the constant reduced curve sitting at the fast equilibrium has slaving defect
exactly the slow-drift magnitude `‖full zstar‖ = ‖full zstar - fast zstar‖` at the equilibrium.
Hence any bound `εf` on this slow drift yields `ODE.QssaDefect full (fun _ => zstar) (fun _ => 0)
a b εf`, which a Michaelis–Menten reduction can compose with `ODE.qssa_error_tendsto_zero`. When the
slow drift is `O(ε)` the defect is `O(ε)` and vanishes as `ε → 0`.

**Out of scope.** Full Tikhonov–Fenichel theory is unavailable: there is no normally-hyperbolic
invariant-manifold construction, so the fast equilibrium is a flat fibre `z = zstar` rather than a
slow-variable-dependent `h(y)`; there is no infinite-horizon shadowing, so the slow side stays
compact-time; and there is no parametrised uniform-in-`ε` attraction family, so the `ε → 0` limit
is taken on the already-derived bound.

Depends on: Mathlib.Analysis.ODE.Gronwall,
Mathlib.Analysis.InnerProductSpace.Calculus, Mathlib.Analysis.Calculus.MeanValue,
Mathlib.Analysis.SpecialFunctions.Exp, CRNT.Dynamics.QSSA.
-/

open Filter Set
open scoped Topology RealInnerProductSpace

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One-sided contraction of `f` toward `zstar` at rate `lam`, evaluated at the point `z`:
`⟪f z - f zstar, z - zstar⟫_ℝ ≤ -lam * ‖z - zstar‖ ^ 2`. -/
def OneSidedContractionAt (f : E → E) (zstar : E) (lam : ℝ) (z : E) : Prop :=
  ⟪f z - f zstar, z - zstar⟫ ≤ -lam * ‖z - zstar‖ ^ 2

/-- One-sided (dissipative) contraction of `f` toward `zstar` at rate `lam`, holding everywhere.
This is the boundary-layer hypothesis: the fast field pulls inward at a uniform rate `lam`. -/
def OneSidedContraction (f : E → E) (zstar : E) (lam : ℝ) : Prop :=
  ∀ z, OneSidedContractionAt f zstar lam z

/-- **Exponential-attraction (boundary-layer) estimate.** Let `z` be an integral curve of an
autonomous field `f`, let `zstar` be a stationary point (`f zstar = 0`), and suppose `f` is
one-sided contracting toward `zstar` at rate `lam ≥ 0`. Then the curve approaches `zstar`
exponentially: `‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t)` for all `t ≥ 0`. -/
theorem norm_sub_le_exp_neg_mul {f : E → E} {z : ℝ → E} {zstar : E} {lam : ℝ}
    (hz : ∀ t, HasDerivAt z (f (z t)) t) (hstat : f zstar = 0)
    (hcon : OneSidedContraction f zstar lam) (_hlam : 0 ≤ lam) :
    ∀ t, 0 ≤ t → ‖z t - zstar‖ ≤ ‖z 0 - zstar‖ * Real.exp (-lam * t) := by
  -- The error `e t = z t - zstar` has derivative `f (z t)` (the constant `zstar` drops out).
  set e : ℝ → E := fun t => z t - zstar with he
  have hed : ∀ t, HasDerivAt e (f (z t)) t := by
    intro t
    simpa [he] using (hz t).sub_const zstar
  -- Lyapunov function `V t = ⟪e t, e t⟫ = ‖e t‖²` and its derivative.
  set V : ℝ → ℝ := fun t => ⟪e t, e t⟫ with hV
  have hVd : ∀ t, HasDerivAt V (2 * ⟪f (z t), e t⟫) t := by
    intro t
    have h := (hed t).inner ℝ (hed t)
    have hsym : ⟪e t, f (z t)⟫ + ⟪f (z t), e t⟫ = 2 * ⟪f (z t), e t⟫ := by
      rw [real_inner_comm (e t) (f (z t))]; ring
    simpa [hV, hsym] using h
  -- Contraction bound: `V' t ≤ -2 lam · V t`.
  have hVbound : ∀ t, 2 * ⟪f (z t), e t⟫ ≤ -(2 * lam) * V t := by
    intro t
    have hc : ⟪f (z t) - f zstar, z t - zstar⟫ ≤ -lam * ‖z t - zstar‖ ^ 2 := hcon (z t)
    rw [hstat, sub_zero] at hc
    have hVe : V t = ‖e t‖ ^ 2 := by simp only [hV]; rw [real_inner_self_eq_norm_sq]
    have : ⟪f (z t), e t⟫ ≤ -lam * V t := by
      rw [hVe]; simpa [he] using hc
    nlinarith [this]
  -- The companion `W t = V t * exp(2 lam t)` has nonpositive derivative.
  set W : ℝ → ℝ := fun t => V t * Real.exp (2 * lam * t) with hW
  have hWd : ∀ t, HasDerivAt W
      ((2 * ⟪f (z t), e t⟫ + (2 * lam) * V t) * Real.exp (2 * lam * t)) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => 2 * lam * s) (2 * lam) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * lam)
    have hexp : HasDerivAt (fun s => Real.exp (2 * lam * s))
        (Real.exp (2 * lam * t) * (2 * lam)) t := hlin.exp
    have h := (hVd t).mul hexp
    have heq : (2 * ⟪f (z t), e t⟫ + (2 * lam) * V t) * Real.exp (2 * lam * t)
        = 2 * ⟪f (z t), e t⟫ * Real.exp (2 * lam * t)
          + V t * (Real.exp (2 * lam * t) * (2 * lam)) := by ring
    rw [heq]
    exact h
  have hWnonpos : ∀ t, (2 * ⟪f (z t), e t⟫ + (2 * lam) * V t) * Real.exp (2 * lam * t) ≤ 0 := by
    intro t
    have hb := hVbound t
    have hle : 2 * ⟪f (z t), e t⟫ + (2 * lam) * V t ≤ 0 := by nlinarith [hb]
    exact mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  -- Therefore `W` is antitone: `W t ≤ W 0` for `t ≥ 0`.
  intro t ht
  have hWmono : W t ≤ W 0 := by
    have hWcont : ContinuousOn W (Icc 0 t) :=
      (continuous_iff_continuousAt.2 fun s => (hWd s).continuousAt).continuousOn
    have key := image_le_of_deriv_right_le_deriv_boundary (f := W)
      (f' := fun s => (2 * ⟪f (z s), e s⟫ + (2 * lam) * V s) * Real.exp (2 * lam * s))
      (a := 0) (b := t) hWcont
      (fun s _ => (hWd s).hasDerivWithinAt)
      (B := fun _ => W 0) (B' := fun _ => 0) (le_refl _)
      (continuousOn_const)
      (fun s _ => (hasDerivWithinAt_const s _ (W 0)))
      (fun s _ => hWnonpos s)
    exact key (right_mem_Icc.2 ht)
  -- Unpack `W t ≤ W 0` into `V t ≤ V 0 * exp(-2 lam t)`.
  have hVexp : V t ≤ V 0 * Real.exp (-(2 * lam) * t) := by
    have h0 : W 0 = V 0 := by simp [hW]
    have hWt : V t * Real.exp (2 * lam * t) ≤ V 0 := by
      simpa [hW, h0] using hWmono
    have hpos : 0 < Real.exp (2 * lam * t) := Real.exp_pos _
    have hexpinv : Real.exp (-(2 * lam) * t) = (Real.exp (2 * lam * t))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hexpinv, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [hWt]
  -- Take square roots. `‖e t‖ = √(V t)` and `√(V 0 · exp(-2λt)) = ‖e 0‖ · exp(-λt)`.
  have hVt_nonneg : 0 ≤ V t := real_inner_self_nonneg
  have hsqrtVt : Real.sqrt (V t) = ‖e t‖ := by
    simp only [hV]; rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsqrtV0 : Real.sqrt (V 0) = ‖e 0‖ := by
    simp only [hV]; rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hstep : ‖e t‖ ≤ Real.sqrt (V 0 * Real.exp (-(2 * lam) * t)) := by
    rw [← hsqrtVt]; exact Real.sqrt_le_sqrt hVexp
  have hV0_nonneg : 0 ≤ V 0 := real_inner_self_nonneg
  have hsqrtexp : Real.sqrt (Real.exp (-(2 * lam) * t)) = Real.exp (-lam * t) := by
    rw [show -(2 * lam) * t = (-lam * t) * 2 by ring, ← Real.exp_half ((-lam * t) * 2)]
    congr 1; ring
  have hsqrtRHS : Real.sqrt (V 0 * Real.exp (-(2 * lam) * t)) = ‖e 0‖ * Real.exp (-lam * t) := by
    rw [Real.sqrt_mul hV0_nonneg, hsqrtV0, hsqrtexp]
  rw [hsqrtRHS] at hstep
  simpa [he] using hstep

/-- **Layer collapse.** With a strictly positive contraction rate `lam`, the boundary-layer
trajectory converges to the fast equilibrium: `‖z t - zstar‖ → 0` as `t → ∞`. -/
theorem norm_sub_tendsto_zero {f : E → E} {z : ℝ → E} {zstar : E} {lam : ℝ}
    (hz : ∀ t, HasDerivAt z (f (z t)) t) (hstat : f zstar = 0)
    (hcon : OneSidedContraction f zstar lam) (hlam : 0 < lam) :
    Tendsto (fun t => ‖z t - zstar‖) atTop (𝓝 0) := by
  have hbound := norm_sub_le_exp_neg_mul hz hstat hcon hlam.le
  -- The envelope `‖z 0 - zstar‖ * exp(-lam t) → 0`.
  have henv : Tendsto (fun t : ℝ => ‖z 0 - zstar‖ * Real.exp (-lam * t)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (𝓝 0) := by
      have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
        Tendsto.const_mul_atTop hlam (tendsto_id (α := ℝ))
      have hcomp : Tendsto (fun t : ℝ => -lam * t) atTop atBot := by
        have h := tendsto_neg_atTop_atBot.comp hmul
        have hfun : (Neg.neg ∘ fun t : ℝ => lam * t) = fun t : ℝ => -lam * t := by
          funext s; simp [Function.comp, neg_mul]
        rwa [hfun] at h
      exact Real.tendsto_exp_atBot.comp hcomp
    simpa using hexp.const_mul (‖z 0 - zstar‖)
  -- Squeeze `0 ≤ ‖z t - zstar‖ ≤ envelope` eventually (for `t ≥ 0`).
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ henv
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hbound t ht

/-- A contracting fast subsystem: an autonomous fast field with a one-sidedly contracting
stationary equilibrium and a strictly positive contraction rate. This is the boundary-layer
data the QSSA bridge consumes; it stands in for the (absent) normally-hyperbolic slow-manifold
geometry by fixing the equilibrium to a flat fibre `z = equil`. -/
structure FastSubsystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The fast vector field `ż = fast z`. -/
  fast : E → E
  /-- The fast equilibrium (the flat fibre of the slow manifold). -/
  equil : E
  /-- The contraction rate. -/
  rate : ℝ
  /-- The contraction rate is strictly positive. -/
  rate_pos : 0 < rate
  /-- The equilibrium is stationary for the fast field. -/
  equil_stat : fast equil = 0
  /-- The fast field is one-sided contracting toward the equilibrium at `rate`. -/
  contraction : OneSidedContraction fast equil rate

/-- The exponential-attraction estimate for a `FastSubsystem`: any integral curve of the fast
field decays to the equilibrium at the bundled rate. -/
theorem FastSubsystem.attraction_bound (S : FastSubsystem E) {z : ℝ → E}
    (hz : ∀ t, HasDerivAt z (S.fast (z t)) t) :
    ∀ t, 0 ≤ t → ‖z t - S.equil‖ ≤ ‖z 0 - S.equil‖ * Real.exp (-S.rate * t) :=
  norm_sub_le_exp_neg_mul hz S.equil_stat S.contraction S.rate_pos.le

/-- The boundary layer of a `FastSubsystem` collapses onto the equilibrium. -/
theorem FastSubsystem.tendsto_equil (S : FastSubsystem E) {z : ℝ → E}
    (hz : ∀ t, HasDerivAt z (S.fast (z t)) t) :
    Tendsto (fun t => ‖z t - S.equil‖) atTop (𝓝 0) :=
  norm_sub_tendsto_zero hz S.equil_stat S.contraction S.rate_pos

/-- **Derived QSSA slaving defect.** Consider a full field `full` whose fast part is the fast
field of `S` and whose slow part is `slow := fun z => full z - S.fast z`. The reduced trajectory
that sits at the fast equilibrium (`γᵣ = fun _ => S.equil`, `γᵣ' = fun _ => 0`) has slaving defect
against the full field equal to the slow-drift magnitude `‖full S.equil‖` at the equilibrium.
Hence any bound `εf` on that slow drift produces `ODE.QssaDefect full (fun _ => S.equil)
(fun _ => 0) a b εf` — the defect is *derived* from the geometry, not postulated. When the slow
drift is `O(ε)` the defect is `O(ε)` and tends to `0` as `ε → 0`. -/
theorem qssaDefect_of_fastSubsystem (S : FastSubsystem E) (full : E → E)
    {a b εf : ℝ} (hslow : ‖full S.equil‖ ≤ εf) :
    QssaDefect full (fun _ => S.equil) (fun _ => 0) a b εf := by
  intro t _
  -- `dist 0 (full S.equil) = ‖full S.equil‖`, and `full S.equil = full S.equil - S.fast S.equil`.
  have : dist (0 : E) (full S.equil) = ‖full S.equil‖ := by
    rw [dist_eq_norm, zero_sub, norm_neg]
  rw [this]
  exact hslow

end ODE
