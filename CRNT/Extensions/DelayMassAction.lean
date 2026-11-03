import CRNT.Equilibria.SteadyState
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Stoich.Subspace
import CRNT.Dynamics.CooperativeNetworks
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Delay mass-action systems

In a delay mass-action system each reaction `r : y_r → y'_r` consumes its reactants at time `t`
and releases its products after a delay `τ_r ≥ 0`:

`ẋ(t) = ∑_r κ_r ( x(t − τ_r)^{y_r} y'_r − x(t)^{y_r} y_r )`.

Following Lipták, Hangos, Pituk and Szederkényi (*Semistability of complex balanced kinetic systems
with arbitrary time delays*, Systems Control Lett. 114 (2018)), two structural facts carry over from
the undelayed theory:

* `CRNT.Network.const_isDelaySolution_iff`: the constant solutions are exactly the mass-action
  steady states;
* `CRNT.Network.delayConservedQuantity_const`: every linear conservation law `w ⊥ S` of the
  network yields a conserved functional of the solution segment,
  `w·x(t) + ∑_r κ_r (w·y_r) ∫_{t−τ_r}^{t} x(u)^{y_r} du`,
  which replaces the affine compatibility classes of the undelayed system.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The right-hand side of the delay system at time `t` along a trajectory `x`. -/
noncomputable def delayField (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (x : ℝ → Concentration S) (t : ℝ) : S → ℝ :=
  fun s => ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
      ((N.reaction r).target s : ℝ) -
    (N.reaction r).source.massActionMonomial (x t) * ((N.reaction r).source s : ℝ))

/-- **Delayed mass-action is inward at every coordinate boundary.** For arbitrary
reaction-specific delays, if all delayed concentrations are nonnegative and the current
concentration vanishes at species `i`, then the `i`-th component of the delay field is
nonnegative. No restriction on reaction source support is needed: each current-consumption term
for `i` vanishes at the boundary, while delayed production is nonnegative. -/
theorem delayField_coord_nonneg_of_current_zero (N : Network S) (κ : RateConstants N)
    (τ : N.R → ℝ) (x : ℝ → Concentration S) (t : ℝ) (i : S)
    (hzero : x t i = 0)
    (hdelayed : ∀ r s, 0 ≤ x (t - τ r) s) :
    0 ≤ N.delayField κ τ x t i := by
  unfold delayField
  refine Finset.sum_nonneg fun r _ => ?_
  have hcons : (N.reaction r).source.massActionMonomial (x t) *
      ((N.reaction r).source i : ℝ) = 0 := by
    by_cases hi : (N.reaction r).source i = 0
    · simp [hi]
    · have hmon : (N.reaction r).source.massActionMonomial (x t) = 0 := by
        show (∏ s, (x t) s ^ (N.reaction r).source s) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hzero, zero_pow hi])
      rw [hmon]
      simp
  have hprod : 0 ≤ (N.reaction r).source.massActionMonomial (x (t - τ r)) :=
    Complex.massActionMonomial_nonneg (fun s => hdelayed r s) (N.reaction r).source
  change 0 ≤ κ.k r *
    ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
        ((N.reaction r).target i : ℝ) -
      (N.reaction r).source.massActionMonomial (x t) *
        ((N.reaction r).source i : ℝ))
  rw [hcons, sub_zero]
  exact mul_nonneg (κ.positive r).le
    (mul_nonneg hprod (Nat.cast_nonneg _))

/-- Every reaction source contains at most one distinct species. -/
def HasSingleSpeciesSources (N : Network S) : Prop :=
  ∀ r i j, (N.reaction r).source i ≠ 0 → (N.reaction r).source j ≠ 0 → i = j

/-- **Delayed production is order preserving while current consumption is coordinatewise.**

If each reaction source contains at most one species, then whenever two trajectories are ordered
at every delayed evaluation, have nonnegative lower delayed states, and agree in coordinate `i` at
the current time, the `i`-th coordinate of the delayed mass-action field is ordered as well.
This is a field-level comparison lemma; it does not assert a trajectory comparison theorem for
delay systems. -/
theorem delayField_coord_mono_of_singleSpeciesSources (N : Network S) (κ : RateConstants N)
    (τ : N.R → ℝ) (hsrc : N.HasSingleSpeciesSources)
    {x y : ℝ → Concentration S} (t : ℝ) (i : S)
    (hdel : ∀ r, x (t - τ r) ≤ y (t - τ r))
    (hdelNonneg : ∀ r s, 0 ≤ x (t - τ r) s)
    (hcurEq : x t i = y t i) :
    N.delayField κ τ x t i ≤ N.delayField κ τ y t i := by
  classical
  rw [delayField, delayField]
  refine Finset.sum_le_sum fun r _ => ?_
  let src := (N.reaction r).source
  let tgt := (N.reaction r).target
  have hmono : src.massActionMonomial (x (t - τ r)) ≤
      src.massActionMonomial (y (t - τ r)) :=
    massActionMonomial_mono (fun s => hdelNonneg r s) (hdel r)
  have hcurMono : src.massActionMonomial (x t) * (src i : ℝ) =
      src.massActionMonomial (y t) * (src i : ℝ) := by
    by_cases hi : src i = 0
    · simp [hi]
    · have hsupp : ∀ j, j ≠ i → src j = 0 := by
        intro j hji
        by_contra hj
        exact hji (hsrc r i j hi (Nat.ne_of_gt (Nat.pos_of_ne_zero hj))).symm
      rw [massActionMonomial_eq_of_support hsupp hcurEq]
  have hrelease : κ.k r *
      (src.massActionMonomial (x (t - τ r)) * (tgt i : ℝ)) ≤
      κ.k r * (src.massActionMonomial (y (t - τ r)) * (tgt i : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmono (Nat.cast_nonneg _)) (κ.positive r).le
  change κ.k r *
      (src.massActionMonomial (x (t - τ r)) * (tgt i : ℝ) -
        src.massActionMonomial (x t) * (src i : ℝ)) ≤
    κ.k r * (src.massActionMonomial (y (t - τ r)) * (tgt i : ℝ) -
        src.massActionMonomial (y t) * (src i : ℝ))
  rw [hcurMono]
  nlinarith [hrelease]

/-- `x` solves the delay system. -/
def IsDelaySolution (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (x : ℝ → Concentration S) : Prop :=
  ∀ t, HasDerivAt x (N.delayField κ τ x t) t

/-- Along a constant trajectory the delay field is the mass-action field. -/
theorem delayField_const (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (c : Concentration S) (t : ℝ) :
    N.delayField κ τ (fun _ => c) t = N.massActionVectorField κ c := by
  funext s
  rw [massActionVectorField_apply]
  simp only [delayField, massActionRate, reactionVector_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **Constant solutions are the steady states.** -/
theorem const_isDelaySolution_iff (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (c : Concentration S) :
    N.IsDelaySolution κ τ (fun _ => c) ↔ N.IsMassActionSteadyState κ c := by
  constructor
  · intro h s
    have hd := (h 0).unique (hasDerivAt_const 0 c)
    rw [delayField_const] at hd
    exact congrFun hd s
  · intro h t
    rw [delayField_const]
    have : N.massActionVectorField κ c = 0 := funext h
    rw [this]
    exact hasDerivAt_const t c

/-- The delayed conserved functional attached to a linear conservation law `w`. -/
noncomputable def delayConservedQuantity (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (w : S → ℝ) (x : ℝ → Concentration S) (t : ℝ) : ℝ :=
  ∑ s, w s * x t s + ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
    ∫ u in (t - τ r)..t, (N.reaction r).source.massActionMonomial (x u)

/-- **Delayed conservation laws.** For a continuous solution of the delay system and a
conservation law `w ⊥ S`, the delayed functional is constant in time. -/
theorem delayConservedQuantity_const (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    {w : S → ℝ} (hw : w ∈ orthSum N.stoichSubspace) {x : ℝ → Concentration S}
    (hx : N.IsDelaySolution κ τ x) (t₁ t₂ : ℝ) :
    N.delayConservedQuantity κ τ w x t₁ = N.delayConservedQuantity κ τ w x t₂ := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  -- the monomials along the solution are continuous
  have hmc : ∀ r, Continuous fun u => (N.reaction r).source.massActionMonomial (x u) := by
    intro r
    unfold Complex.massActionMonomial
    exact continuous_finsetProd _ fun s _ =>
      ((continuous_apply s).comp hxc).pow _
  set m : N.R → ℝ → ℝ := fun r u => (N.reaction r).source.massActionMonomial (x u)
  -- derivative of each delay integral
  have hint : ∀ r t, HasDerivAt (fun t => ∫ u in (t - τ r)..t, m r u) (m r t - m r (t - τ r)) t := by
    intro r t
    have hG := fun t => ((hmc r).integral_hasStrictDerivAt 0 t).hasDerivAt
    have hsplit : (fun t => ∫ u in (t - τ r)..t, m r u) =
        fun t => (∫ u in (0 : ℝ)..t, m r u) - ∫ u in (0 : ℝ)..(t - τ r), m r u := by
      funext t
      rw [intervalIntegral.integral_interval_sub_left
        ((hmc r).intervalIntegrable _ _) ((hmc r).intervalIntegrable _ _)]
    rw [hsplit]
    have h2 : HasDerivAt (fun t => ∫ u in (0 : ℝ)..(t - τ r), m r u) (m r (t - τ r)) t := by
      exact HasDerivAt.comp_sub_const t (τ r) (hG (t - τ r))
    exact (hG t).sub h2
  -- the total derivative vanishes
  have hderiv : ∀ t, HasDerivAt (N.delayConservedQuantity κ τ w x) 0 t := by
    intro t
    have hcoord : ∀ s, HasDerivAt (fun t => x t s) (N.delayField κ τ x t s) t :=
      fun s => (hasDerivAt_pi.mp (hx t)) s
    have h1 : HasDerivAt (fun t => ∑ s, w s * x t s) (∑ s, w s * N.delayField κ τ x t s) t :=
      HasDerivAt.fun_sum fun s _ => (hcoord s).const_mul (w s)
    have h2 : HasDerivAt (fun t => ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
        ∫ u in (t - τ r)..t, m r u)
        (∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) * (m r t - m r (t - τ r))) t :=
      HasDerivAt.fun_sum fun r _ => (hint r t).const_mul _
    have hfun : N.delayConservedQuantity κ τ w x = fun t => (∑ s, w s * x t s) +
        ∑ r, κ.k r * (∑ s, w s * ((N.reaction r).source s : ℝ)) *
          ∫ u in (t - τ r)..t, m r u := rfl
    rw [hfun]
    refine (h1.fun_add h2).congr_deriv ?_
    -- algebra: the sum collapses to `∑_r κ_r m_r(t-τ_r) (w · v_r) = 0`
    have hperp : ∀ r, ∑ s, w s * N.reactionVector r s = 0 := fun r =>
      (mem_orthSum.mp hw) _ (N.reactionVector_mem_stoichSubspace r)
    have e1 : ∑ s, w s * N.delayField κ τ x t s =
        ∑ r, ∑ s, w s * (κ.k r * (m r (t - τ r) * ((N.reaction r).target s : ℝ) -
          m r t * ((N.reaction r).source s : ℝ))) := by
      simp only [delayField, Finset.mul_sum]
      exact Finset.sum_comm
    rw [e1, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hp := hperp r
    simp only [reactionVector_apply] at hp
    have : ∑ s, w s * (κ.k r * (m r (t - τ r) * ((N.reaction r).target s : ℝ) -
        m r t * ((N.reaction r).source s : ℝ))) =
        κ.k r * m r (t - τ r) * ∑ s, w s * (((N.reaction r).target s : ℝ) -
          ((N.reaction r).source s : ℝ)) +
        κ.k r * (m r (t - τ r) - m r t) * ∑ s, w s * ((N.reaction r).source s : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    rw [this, hp]
    simp only [m]
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) t₁ t₂

end Network

end CRNT
