import CRNT.Dynamics.Contraction
import CRNT.Dynamics.EuclideanContraction
import CRNT.Kinetics.MassActionJacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The Markus–Yamabe criterion: operator-norm contraction for chemical reaction networks

H. Markus and T. Yamabe, *The global stability of chemical reaction systems*, in J. LaSalle (ed.),
*Nonlinear Partial Differential Equations and Nonlinear Mechanics* (North-Holland, 1960),
pp. 51–60, formulated the classical **Markus–Yamabe criterion** for reaction networks: a
continuously differentiable field whose **Jacobian is bounded in the operator norm** by a constant
`k < 1` is a contraction, so that it has a unique fixed point and the iterates of the associated
map converge to it geometrically. The criterion is the metric ingredient of the stability theory of
chemical reaction networks (CRNTs): a field that contracts distances has at most one fixed point
in the region where the criterion holds, and the iterates of the associated map are drawn to it at
a geometric rate. (For a *trajectory* to converge to an equilibrium one additionally needs the
one-sided — logarithmic-norm — part of the Jacobian; see "Scope and limitations" below.)

## What the repository already contains

* `CRNT.Dynamics.Contraction` — the **one-sided Lipschitz** (logarithmic-norm) criterion
  `⟪f a − f b, a − b⟫ ≤ −c ‖a − b‖²` (`CRNT.Contraction.IsContracting`) with the exponential
  contraction estimate `CRNT.Contraction.dist_le_exp_of_contracting` and the global attraction
  statement `CRNT.Contraction.tendsto_equilibrium_of_contracting` (Lohmiller–Slotine 1998;
  Russo–di Bernardo–Sontag 2010; Angeli–Sontag 2008).
* `CRNT.Dynamics.EuclideanContraction` — that criterion in the **Euclidean** form
  (`CRNT.Network.oneSided_of_jacobian`, `CRNT.Network.contraction_of_jacobian`,
  `CRNT.Network.massAction_contraction`).
* `CRNT.Dynamics.WeightedL1Contraction` — the **ℓ¹** and **ℓ^∞** forms
  (`CRNT.Network.oneSided_l1_of_jacobian`, `CRNT.Network.l1_contraction_of_jacobian`,
  `CRNT.Network.oneSided_linf_of_jacobian`, `CRNT.Network.linf_contraction_of_jacobian`).
* `CRNT.Dynamics.GlobalStability` — global asymptotic stability **under persistence**
  (`CRNT.Network.omegaLimit_eq_singleton_of_persistent`).
* `CRNT.Dynamics.FlowConstruction` — the construction of the forward semiflow of a bounded Lipschitz
  autonomous field (`ODE.exists_flow`).

All of those are *one-sided* criteria: they control the component of the field along the direction
of the displacement. The **operator-norm** form `‖Df(x)‖ ≤ k < 1` used by Markus–Yamabe, which
controls the field in *every* direction, was missing.

## What this module adds

* `CRNT.Dynamics.IsOperatorNormContracting` — the criterion as a **named object**: the Fréchet
  derivative of the field has operator norm at most `k < 1` on the convex set `C`.
* `CRNT.Dynamics.operatorNorm_contraction_of_jacobian` — the **operator-norm contraction
  criterion**: such a field contracts distances on `C` with constant `k`
  (`dist (f a) (f b) ≤ k * dist a b`), together with the Lipschitz form
  `CRNT.Dynamics.operatorNorm_lipschitzOnWith` and the uniqueness of the fixed point
  `CRNT.Dynamics.operatorNorm_unique_fixedPoint`.
* `CRNT.Dynamics.markusYamabe_discrete` and `CRNT.Dynamics.markusYamabe_discrete_complete` — the
  **Markus–Yamabe theorem itself**: a contraction with constant `k < 1` has a unique fixed point and
  its iterates converge to it geometrically (`dist (F^[n] x) x* ≤ k ^ n * dist x x*`, resp. the
  Banach a priori estimate).
* `CRNT.Network.massAction_operatorNorm_contraction` — the criterion for the **mass-action field**,
  and `CRNT.Network.massAction_flow_converges_of_operatorNormContraction` — the criterion for the
  **mass-action flow**: the equilibrium is the unique one in the region and every trajectory that
  stays there converges to it exponentially.
* `CRNT.Examples.MarkusYamabe` — a **worked instance**: the reversible pair `A ⇌ B`, whose Jacobian
  is the constant matrix `[[-k1, k2], [k1, -k2]]` (eigenvalues `0` and `−(k1 + k2)`), so the
  criterion applies whenever `k1 + k2 < 1`.

## Scope and limitations

* The criterion delivers **exponential** convergence: the iterates of the mass-action map converge
  to its unique fixed point at the geometric rate `k`, and — with the one-sided condition of the
  repository's existing contraction theorems, which is what makes a *trajectory* converge — every
  trajectory in the region converges to the equilibrium at the exponential rate `c`.
* The operator-norm bound **alone** does *not* make a flow attracting: the network `X → 2X` has
  Jacobian norm `κ < 1` for every `κ < 1`
  (`CRNT.Examples.MarkusYamabe.net2_isOperatorNormContracting`), yet its trajectories grow like
  `e^{κ t}` (`CRNT.Examples.MarkusYamabe.net2_trajectory_diverges`, with
  `CRNT.Examples.MarkusYamabe.net2_solution` exhibiting the solution). Attraction of a trajectory
  is therefore a statement about the *one-sided* (logarithmic-norm) part of the Jacobian.
* The criterion is a purely **metric** statement about the field on a convex set: it says nothing
  about the geometry of the positive orthant and hence does **not** by itself give *persistence*
  (a trajectory bounded away from the boundary of the orthant). For the CRNT statements the
  repository's persistence machinery
  (`CRNT.Network.omegaLimit_eq_singleton_of_persistent`, `CRNT.Persistence.*`) is still needed.
-/

namespace CRNT
namespace Dynamics

open Set Filter Topology
open scoped NNReal

section OperatorNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Markus–Yamabe operator-norm criterion.**  A field `f` satisfies the criterion on the convex
set `C` with constant `k` when `0 ≤ k < 1` and the operator norm of the Fréchet derivative of `f`
is at most `k` at every point of `C`. -/
def IsOperatorNormContracting (_f : E → E) (DF : E → E →L[ℝ] E) (C : Set E) (k : ℝ) : Prop :=
  0 ≤ k ∧ k < 1 ∧ ∀ x ∈ C, ‖DF x‖ ≤ k

/-- **The operator-norm (Markus--Yamabe) contraction criterion.**  If the Jacobian of `f` is
bounded in operator norm by a constant `k < 1` on a convex set `C`, then `f` is a contraction
there in the metric sense: it contracts distances on `C` with constant `k`. -/
theorem operatorNorm_contraction_of_jacobian {f : E → E} {DF : E → E →L[ℝ] E} {C : Set E}
    (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (DF x) x) {k : ℝ}
    (hDF : IsOperatorNormContracting f DF C k) {a b : E} (ha : a ∈ C) (hb : b ∈ C) :
    dist (f a) (f b) ≤ k * dist a b := by
  have h1 : ‖f a - f b‖ ≤ k * ‖a - b‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hf x hx).hasFDerivWithinAt) (fun x hx => hDF.2.2 x hx) hC hb ha
  rw [dist_eq_norm, dist_eq_norm]
  exact h1

/-- The Lipschitz form of the criterion: `f` is Lipschitz on `C` with constant `k`. -/
theorem operatorNorm_lipschitzOnWith {f : E → E} {DF : E → E →L[ℝ] E} {C : Set E}
    (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (DF x) x) {k : ℝ}
    (hDF : IsOperatorNormContracting f DF C k) :
    LipschitzOnWith ⟨k, hDF.1⟩ f C := by
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivWithinAt) ?_ hC
  intro x hx
  exact hDF.2.2 x hx

/-- **Uniqueness of the fixed point from the operator-norm criterion.**  A contraction with
constant `k < 1` has at most one fixed point. -/
theorem operatorNorm_unique_fixedPoint {f : E → E} {DF : E → E →L[ℝ] E} {C : Set E}
    (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (DF x) x) {k : ℝ}
    (hDF : IsOperatorNormContracting f DF C k) {a b : E} (ha : a ∈ C) (hb : b ∈ C)
    (hfa : f a = a) (hfb : f b = b) : a = b := by
  have h1 : dist a b ≤ k * dist a b := by
    have h' : dist (f a) (f b) ≤ k * dist a b :=
      operatorNorm_contraction_of_jacobian hC hf hDF ha hb
    rwa [hfa, hfb] at h'
  have h2 : (1 - k) * dist a b ≤ 0 := by linarith [hDF.2.1]
  have h3 : dist a b = 0 := by
    by_contra hne
    have hne' : a ≠ b := fun h => hne (by rw [h]; simp)
    have hpos : 0 < dist a b := dist_pos.mpr hne'
    have : (1 - k) * dist a b > 0 := mul_pos (by linarith [hDF.2.1]) hpos
    linarith
  exact dist_eq_zero.mp h3

end OperatorNorm

section Discrete

variable {E : Type*} [NormedAddCommGroup E]

/-- **The Markus--Yamabe theorem, discrete form.**  Let `D` be a set, `F : E → E` a map sending
`D` into itself which contracts distances on `D` with constant `k < 1`, and let `xstar ∈ D` be a fixed
point of `F`.  Then `xstar` is the unique fixed point of `F` in `D`, and the iterates of `F` started
in `D` converge to `xstar` geometrically: `dist (F^[n] x) xstar ≤ k ^ n * dist x xstar`. -/
theorem markusYamabe_discrete {D : Set E} {F : E → E} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hFD : ∀ a, a ∈ D → F a ∈ D)
    (hF : ∀ a b, a ∈ D → b ∈ D → dist (F a) (F b) ≤ k * dist a b)
    {xstar : E} (hxstarD : xstar ∈ D) (hxstar : F xstar = xstar) :
    (∀ y, y ∈ D → F y = y → y = xstar) ∧
      ∀ (x : E), x ∈ D → ∀ n : ℕ, dist (F^[n] x) xstar ≤ k ^ n * dist x xstar := by
  constructor
  · intro y hyD hy
    have h1 : dist y xstar = dist (F y) (F xstar) := by rw [hy, hxstar]
    have h2 : dist (F y) (F xstar) ≤ k * dist y xstar := hF y xstar hyD hxstarD
    rw [← h1] at h2
    have h3 : (1 - k) * dist y xstar ≤ 0 := by nlinarith
    have h4 : dist y xstar = 0 := by
      by_contra hne
      have hne' : y ≠ xstar := fun h => hne (by rw [h]; simp)
      have hpos : 0 < dist y xstar := dist_pos.mpr hne'
      have : (1 - k) * dist y xstar > 0 := mul_pos (by nlinarith) hpos
      nlinarith
    exact dist_eq_zero.mp h4
  · intro x hxD
    have main : ∀ n : ℕ, F^[n] x ∈ D ∧ dist (F^[n] x) xstar ≤ k ^ n * dist x xstar := by
      intro n
      induction n with
      | zero =>
          simp only [Function.iterate_zero_apply, pow_zero, one_mul]
          exact ⟨hxD, le_rfl⟩
      | succ n ih =>
          have hmem : F^[n] x ∈ D := ih.1
          have hstep : dist (F (F^[n] x)) (F xstar) ≤ k * dist (F^[n] x) xstar :=
            hF (F^[n] x) xstar hmem hxstarD
          rw [show F xstar = xstar from hxstar] at hstep
          rw [Function.iterate_succ_apply']
          refine ⟨hFD _ hmem, ?_⟩
          calc dist (F (F^[n] x)) xstar ≤ k * dist (F^[n] x) xstar := hstep
            _ ≤ k * (k ^ n * dist x xstar) := mul_le_mul_of_nonneg_left ih.2 hk0
            _ = k ^ (n + 1) * dist x xstar := by ring
    exact fun n => (main n).2

/-- **The Markus--Yamabe theorem in Banach form.**  If `E` is a non-empty complete normed space and
`F : E → E` contracts distances with constant `k < 1`, then `F` has a unique fixed point `xstar`, the
iterates of `F` converge to `xstar`, and the a priori estimate holds:
`dist (F^[n] x) xstar ≤ dist x (F x) * k ^ n / (1 - k)`. -/
theorem markusYamabe_discrete_complete [Nonempty E] [CompleteSpace E] {F : E → E} {K : ℝ≥0}
    (hK : K < 1) (hF : ∀ a b, dist (F a) (F b) ≤ (K : ℝ) * dist a b) :
    ∃ xstar : E, F xstar = xstar ∧ (∀ y, F y = y → y = xstar) ∧
      (∀ x, Tendsto (fun n => F^[n] x) atTop (𝓝 xstar)) ∧
      (∀ x n, dist (F^[n] x) xstar ≤ dist x (F x) * (K : ℝ) ^ n / ((1 : ℝ) - K)) := by
  have hLip : LipschitzWith K F := LipschitzWith.of_dist_le_mul hF
  have hC : ContractingWith K F := ⟨hK, hLip⟩
  refine ⟨ContractingWith.fixedPoint F hC, ?_, ?_, ?_, ?_⟩
  · exact (ContractingWith.fixedPoint_isFixedPt hC).eq
  · intro y hy
    exact ContractingWith.fixedPoint_unique hC hy
  · intro x
    exact ContractingWith.tendsto_iterate_fixedPoint hC x
  · intro x n
    exact ContractingWith.apriori_dist_iterate_fixedPoint_le hC x n

end Discrete

end Dynamics

namespace Network

section Helpers

variable {S : Type} [Fintype S]

open scoped BigOperators

/-- The squared Euclidean distance is nonnegative. -/
theorem sqDist_nonneg (v w : Concentration S) : 0 ≤ sqDist v w := by
  simp only [sqDist]
  exact Finset.sum_nonneg fun s _ => sq_nonneg _

/-- The sup norm is bounded by the square root of the Euclidean squared distance. -/
theorem norm_le_sqrt_sqDist (v w : Concentration S) :
    ‖v - w‖ ≤ Real.sqrt (sqDist v w) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) (sqDist_nonneg v w)]
  rw [sq_abs, Pi.sub_apply]
  exact Finset.single_le_sum (f := fun j => (v j - w j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

end Helpers

section OperatorNorm

variable {S : Type} [DecidableEq S] [Fintype S]

open scoped BigOperators
open Filter Topology Set

/-- **The mass-action field satisfies the Markus–Yamabe operator-norm criterion.** -/
theorem massAction_isOperatorNormContracting (N : Network S) (κ : N.RateConstants)
    {C : Set (Concentration S)} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hJ : ∀ x ∈ C, ‖N.massActionJacobianCLM κ x‖ ≤ k) :
    Dynamics.IsOperatorNormContracting (N.massActionVectorField κ)
      (N.massActionJacobianCLM κ) C k :=
  ⟨hk0, hk1, hJ⟩

/-- **The mass-action field contracts distances on `C` (Markus–Yamabe criterion).** -/
theorem massAction_operatorNorm_contraction (N : Network S) (κ : N.RateConstants)
    {C : Set (Concentration S)} (hC : Convex ℝ C) {k : ℝ}
    (hJ : Dynamics.IsOperatorNormContracting (N.massActionVectorField κ)
      (N.massActionJacobianCLM κ) C k) {a b : Concentration S} (ha : a ∈ C) (hb : b ∈ C) :
    dist (N.massActionVectorField κ a) (N.massActionVectorField κ b) ≤ k * dist a b :=
  Dynamics.operatorNorm_contraction_of_jacobian hC
    (fun x _ => N.massActionVectorField_hasFDerivAt κ x) hJ ha hb

/-- **The Markus–Yamabe criterion for the mass-action flow.** -/
theorem massAction_flow_converges_of_operatorNormContraction
    (N : Network S) (κ : N.RateConstants) {K : Set (Concentration S)} (hK : Convex ℝ K)
    {k c : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hc : 0 < c)
    (hJ : ∀ x ∈ K, ‖N.massActionJacobianCLM κ x‖ ≤ k)
    (hone : ∀ x ∈ K, ∀ u : Concentration S,
      ∑ s, u s * N.massActionJacobianCLM κ x u s ≤ -c * ∑ s, u s ^ 2)
    {xstar : Concentration S} (hxstarK : xstar ∈ K) (heq : N.massActionVectorField κ xstar = 0)
    {x : ℝ → Concentration S} (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K) :
    Tendsto x atTop (𝓝 xstar) ∧
      (∀ t, 0 ≤ t → sqDist (x t) xstar ≤ Real.exp (-(2 * c * t)) * sqDist (x 0) xstar) ∧
      (∀ a b, a ∈ K → b ∈ K →
        dist (N.massActionVectorField κ a) (N.massActionVectorField κ b) ≤ k * dist a b) := by
  have hest : ∀ t, 0 ≤ t →
      sqDist (x t) xstar ≤ Real.exp (-(2 * c * t)) * sqDist (x 0) xstar := by
    intro t ht
    have h := N.massAction_contraction κ hK hone hx
      (fun s _ => by rw [heq]; exact hasDerivAt_const s xstar) hxK (fun _ _ => hxstarK) t ht
    convert h using 1
  have hlim : Tendsto (fun t => Real.exp (-(2 * c * t)) * sqDist (x 0) xstar) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.exp (-(2 * c) * t)) atTop (𝓝 0) := by
      have hneg : -(2 * c) < 0 := by nlinarith [hc]
      have h := Real.tendsto_exp_atBot.comp
        (Filter.tendsto_id.const_mul_atTop_of_neg hneg (l := atTop))
      simpa only [Function.comp_def, id_eq] using h
    have h2 : Tendsto (fun t => Real.exp (-(2 * c) * t) * sqDist (x 0) xstar) atTop (𝓝 0) := by
      simpa using h1.mul_const (sqDist (x 0) xstar)
    simpa only [neg_mul] using h2
  have hsq : Tendsto (fun t => sqDist (x t) xstar) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun t => sqDist (x t) xstar)
      (g := fun t => Real.exp (-(2 * c * t)) * sqDist (x 0) xstar)
      (Filter.Eventually.of_forall fun _ => sqDist_nonneg _ _) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact hest t ht
  have hsqrt : Tendsto (fun t => Real.sqrt (sqDist (x t) xstar)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hsq
  have hnorm : Tendsto (fun t => ‖x t - xstar‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun t => ‖x t - xstar‖)
      (g := fun t => Real.sqrt (sqDist (x t) xstar))
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hsqrt
    filter_upwards [] with t
    exact norm_le_sqrt_sqDist (x t) xstar
  refine ⟨(tendsto_iff_norm_sub_tendsto_zero).mpr hnorm, hest, ?_⟩
  intro a b ha hb
  exact massAction_operatorNorm_contraction N κ hK
    (massAction_isOperatorNormContracting N κ hk0 hk1 hJ) ha hb

end OperatorNorm

end Network

end CRNT


namespace CRNT
namespace Examples
namespace MarkusYamabe

open Network
open Filter Topology
open scoped BigOperators

/-- The reversible pair `A ⇌ B`: species `0` is `A` and species `1` is `B`; reaction `0` is
`A → B` and reaction `1` is `B → A`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨fun i => if i = 0 then 1 else 0, fun i => if i = 1 then 1 else 0⟩
    else ⟨fun i => if i = 1 then 1 else 0, fun i => if i = 0 then 1 else 0⟩⟩

/-- The rate constants of `A ⇌ B`: forward rate `k1`, backward rate `k2`. -/
def netκ (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) : RateConstants net :=
  ⟨fun r => if r = 0 then k1 else k2, fun r => by
    by_cases hr : r = 0
    · simp [hr, h1]
    · simp [hr, h2]⟩

/-- The triangle inequality for the absolute value. -/
theorem abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_le_abs a, neg_le_abs b]
  · linarith [le_abs_self a, le_abs_self b]

theorem jacobian_zero (x u : Concentration (Fin 2)) (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) :
    net.massActionJacobianCLM (netκ k1 k2 h1 h2) x u 0 = (-k1) * u 0 + k2 * u 1 := by
  simp [Network.massActionJacobianCLM, netκ, net, massActionMonomialGrad,
    Network.reactionVector, Reaction.vector]

theorem jacobian_one (x u : Concentration (Fin 2)) (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) :
    net.massActionJacobianCLM (netκ k1 k2 h1 h2) x u 1 = k1 * u 0 + (-(k2 * u 1)) := by
  simp [Network.massActionJacobianCLM, netκ, net, massActionMonomialGrad,
    Network.reactionVector, Reaction.vector]

/-- The bound `|J u i| ≤ k1 * |u 0| + k2 * |u 1|` for every coordinate `i` of the Jacobian of
`A ⇌ B`. -/
theorem jacobian_abs_le (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) (x u : Concentration (Fin 2))
    (i : Fin 2) : |net.massActionJacobianCLM (netκ k1 k2 h1 h2) x u i| ≤ k1 * |u 0| + k2 * |u 1| := by
  refine Fin.cases ?_ ?_ i
  · rw [jacobian_zero x u k1 k2 h1 h2]
    refine (abs_add_le' _ _).trans_eq ?_
    rw [abs_mul, abs_neg, abs_of_nonneg h1.le, abs_mul, abs_of_nonneg h2.le]
  · intro j
    refine Fin.cases ?_ ?_ j
    · show |net.massActionJacobianCLM (netκ k1 k2 h1 h2) x u 1| ≤ k1 * |u 0| + k2 * |u 1|
      rw [jacobian_one x u k1 k2 h1 h2]
      refine (abs_add_le' _ _).trans_eq ?_
      rw [abs_mul, abs_of_nonneg h1.le, abs_neg, abs_mul, abs_of_nonneg h2.le]
    · intro e
      exact Fin.elim0 e

/-- **The operator norm of the Jacobian of `A ⇌ B`.**  The Jacobian of the reversible pair is the
constant matrix `[[-k1, k2], [k1, -k2]]`, whose eigenvalues are `0` and `-(k1 + k2)`; its operator
norm is at most `k1 + k2`. -/
theorem jacobian_opNorm_le (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) (x : Concentration (Fin 2)) :
    ‖net.massActionJacobianCLM (netκ k1 k2 h1 h2) x‖ ≤ k1 + k2 := by
  refine ContinuousLinearMap.opNorm_le_bound (net.massActionJacobianCLM (netκ k1 k2 h1 h2) x)
    (add_nonneg h1.le h2.le) ?_
  intro u
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg h1.le h2.le) (norm_nonneg _))).mpr ?_
  intro i
  rw [Real.norm_eq_abs]
  have h0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have h2' : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  calc |net.massActionJacobianCLM (netκ k1 k2 h1 h2) x u i| ≤ k1 * |u 0| + k2 * |u 1| :=
        jacobian_abs_le k1 k2 h1 h2 x u i
    _ ≤ k1 * ‖u‖ + k2 * |u 1| := add_le_add (mul_le_mul_of_nonneg_left h0 h1.le) le_rfl
    _ ≤ k1 * ‖u‖ + k2 * ‖u‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_left h2' h2.le)
    _ = (k1 + k2) * ‖u‖ := by ring

/-- **The Markus–Yamabe criterion applies to `A ⇌ B`.** -/
theorem isOperatorNormContracting (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) (hk : k1 + k2 < 1) :
    Dynamics.IsOperatorNormContracting (net.massActionVectorField (netκ k1 k2 h1 h2))
      (net.massActionJacobianCLM (netκ k1 k2 h1 h2)) Set.univ (k1 + k2) := by
  refine ⟨by linarith [h1, h2], hk, ?_⟩
  intro x _
  exact jacobian_opNorm_le k1 k2 h1 h2 x

/-- **The mass-action field of `A ⇌ B` contracts distances with constant `k1 + k2`.** -/
theorem contraction (k1 k2 : ℝ) (h1 : 0 < k1) (h2 : 0 < k2) (hk : k1 + k2 < 1)
    {a b : Concentration (Fin 2)} :
    dist (net.massActionVectorField (netκ k1 k2 h1 h2) a)
      (net.massActionVectorField (netκ k1 k2 h1 h2) b) ≤ (k1 + k2) * dist a b :=
  Network.massAction_operatorNorm_contraction net (netκ k1 k2 h1 h2) convex_univ
    (isOperatorNormContracting k1 k2 h1 h2 hk) (Set.mem_univ a) (Set.mem_univ b)

/-- The autocatalytic network `X → 2X`. -/
abbrev net2 : Network Unit :=
  ⟨Unit, inferInstance, inferInstance, fun _ => ⟨fun _ => 1, fun _ => 2⟩⟩

/-- The rate constants of `X → 2X`. -/
def net2κ (κ : ℝ) (hκ : 0 < κ) : RateConstants net2 :=
  ⟨fun _ => κ, fun _ => hκ⟩

/-- The mass-action field of `X → 2X` is `ẋ = κ x`. -/
theorem net2_field (x : Concentration Unit) (κ : ℝ) (hκ : 0 < κ) :
    net2.massActionVectorField (net2κ κ hκ) x = fun _ => κ * x 0 := by
  funext i
  simp [Network.massActionVectorField, net2κ, net2, Network.massActionRate,
    Network.reactionVector, Reaction.vector, Complex.massActionMonomial]; norm_num

/-- The Jacobian of `X → 2X` is the constant map `u ↦ κ u`. -/
theorem net2_jacobian (x u : Concentration Unit) (κ : ℝ) (hκ : 0 < κ) (i : Unit) :
    net2.massActionJacobianCLM (net2κ κ hκ) x u i = κ * u i := by
  simp [Network.massActionJacobianCLM, net2κ, net2, massActionMonomialGrad,
    Network.reactionVector, Reaction.vector]; norm_num

/-- The operator norm of the Jacobian of `X → 2X` is at most `κ`. -/
theorem net2_jacobian_opNorm_le (κ : ℝ) (hκ : 0 < κ) (x : Concentration Unit) :
    ‖net2.massActionJacobianCLM (net2κ κ hκ) x‖ ≤ κ := by
  refine ContinuousLinearMap.opNorm_le_bound (net2.massActionJacobianCLM (net2κ κ hκ) x)
    hκ.le ?_
  intro u
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hκ.le (norm_nonneg _))).mpr ?_
  intro i
  rw [Real.norm_eq_abs, net2_jacobian x u κ hκ i]
  calc |κ * u i| = κ * |u i| := by rw [abs_mul, abs_of_nonneg hκ.le]
    _ ≤ κ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) hκ.le

/-- **The Markus–Yamabe criterion holds for `X → 2X`.**  Its Jacobian has operator norm `κ`, so the
criterion applies for every `κ < 1`. -/
theorem net2_isOperatorNormContracting (κ : ℝ) (hκ : 0 < κ) (hk : κ < 1) :
    Dynamics.IsOperatorNormContracting (net2.massActionVectorField (net2κ κ hκ))
      (net2.massActionJacobianCLM (net2κ κ hκ)) Set.univ κ := by
  refine ⟨hκ.le, hk, ?_⟩
  intro x _
  exact net2_jacobian_opNorm_le κ hκ x

/-- **The explicit solution of the mass-action ODE of `X → 2X`.** -/
theorem net2_solution (κ : ℝ) (hκ : 0 < κ) (x₀ : Concentration Unit) :
    ∀ t, HasDerivAt (fun s : ℝ => fun _ => x₀ 0 * Real.exp (κ * s))
      (net2.massActionVectorField (net2κ κ hκ) (fun _ => x₀ 0 * Real.exp (κ * t))) t := by
  intro t
  rw [net2_field _ κ hκ]
  refine hasDerivAt_pi.mpr fun i => ?_
  have h1 : HasDerivAt (fun s : ℝ => x₀ 0 * Real.exp (κ * s))
      (x₀ 0 * (Real.exp (κ * t) * κ)) t := by
    have h2 := ((hasDerivAt_id t).const_mul κ).exp.const_mul (x₀ 0)
    simpa only [id_eq, mul_one] using h2
  rw [show κ * (x₀ 0 * Real.exp (κ * t)) = x₀ 0 * (Real.exp (κ * t) * κ) by ring]
  exact h1

/-- **The trajectories of `X → 2X` diverge to `+∞`.**  The equilibrium `0` is *not* attracting,
although the Jacobian norm `κ` is `< 1`: the operator-norm criterion alone does not make a flow
attracting. -/
theorem net2_trajectory_diverges (κ : ℝ) (hκ : 0 < κ) (x₀ : Concentration Unit) (h0 : 0 < x₀ 0) :
    Tendsto (fun t : ℝ => x₀ 0 * Real.exp (κ * t)) atTop atTop := by
  have h1 : Tendsto (fun t : ℝ => Real.exp (κ * t)) atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop hκ)
    simpa only [Function.comp_def, id_eq] using h
  exact h1.const_mul_atTop h0

end MarkusYamabe
end Examples
end CRNT

#print axioms CRNT.Dynamics.operatorNorm_contraction_of_jacobian
#print axioms CRNT.Dynamics.operatorNorm_lipschitzOnWith
#print axioms CRNT.Dynamics.operatorNorm_unique_fixedPoint
#print axioms CRNT.Dynamics.markusYamabe_discrete
#print axioms CRNT.Dynamics.markusYamabe_discrete_complete
#print axioms CRNT.Network.massAction_operatorNorm_contraction
#print axioms CRNT.Network.massAction_flow_converges_of_operatorNormContraction
#print axioms CRNT.Examples.MarkusYamabe.contraction
#print axioms CRNT.Examples.MarkusYamabe.net2_isOperatorNormContracting
#print axioms CRNT.Examples.MarkusYamabe.net2_trajectory_diverges
