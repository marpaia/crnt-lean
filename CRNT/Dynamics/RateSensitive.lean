import CRNT.Kinetics.MassAction
import CRNT.Kinetics.MassActionJacobian
import CRNT.Dynamics.EuclideanContraction
import CRNT.Dynamics.Gronwall
import CRNT.Examples.ReversiblePair

/-!
# Rate-sensitive persistence: exponentially converging rate constants

## The theory

Classical chemical reaction network theory fixes the rate constants once and for all.  The
*rate-sensitive* theory asks what happens when the rates themselves move in time.  Anderson,
Ramaswamy, Serafini and Soni (*Exponential Dichotomy and Persistence*, SIAM J. Appl. Math. 56
(1997), 653–673) and Ramaswamy (*On the Persistence of Dynamical Systems*, PhD thesis, 1996)
studied systems `ẋ = f(x, t)` whose kinetic parameters vary with `t` and converge, as
`t → ∞`, to a limiting set of parameters.  The central question is whether the persistence
results for the *static* system survive a perturbation of the rates that dies out in time.

This is the right generalisation of the static theory for three reasons.

* The kinetics of a real CRN are never exactly constant: temperature, `pH`, catalyst loading and
  feed concentration all drift.  A persistence theorem that is not robust under such drift is
  of limited use.
* The dynamical system becomes *non-autonomous*, so the classical machinery (LaSalle, ω-limit
  sets, relative entropy) has to be replaced by something that compares the time-dependent flow
  with the limiting one.  The right notion is the **exponential dichotomy**: the state space
  splits into a stable and an unstable subspace for the time-dependent linearisation, and the
  persistence question becomes a question about the distance between the time-dependent orbit
  and the stable manifold of the limiting equilibrium.
* The quantitative question is the interesting one.  If the rates converge to their limit only
  *algebraically*, the perturbation may accumulate and destroy persistence; if they converge
  *exponentially* — `‖κ t − κ ∞‖ ≤ C e^{−γ t}` — the perturbation is integrable, its total
  effect is bounded, and the persistence of the limiting system is inherited.

## What this repository already provides

* **The tempered-rate floor** (`CRNT.Persistence.VariableRateFloor`): the *Extended Persistence
  Conjecture* for trajectories whose rate constants merely stay in a compact interval
  `[ε, 1/ε]` (`weaklyReversible_forward_floor_varK`,
  `weaklyReversible_conservative_confined_varK`).  That is a *uniform* statement, with no
  limiting behaviour: it survives arbitrary time-dependence, but says nothing about the
  asymptotics.
* **Spectral splitting** (`CRNT.Dynamics.SpectralSplitting`, `CRNT.Dynamics.SpectralSplittingReal`):
  the linear skeleton `V = E_s ⊕ E_c ⊕ E_u` of the *static* Jacobian, by the sign of `Re λ`.
* **Contraction** (`CRNT.Dynamics.Contraction`, `CRNT.Dynamics.EuclideanContraction`): the
  one-sided Lipschitz / logarithmic-norm criterion, its exponential contraction estimate, and the
  convergence of a contracting flow to its equilibrium.
* **Scalar Grönwall with a rate** (`CRNT.ExponentialDecay.le_mul_exp_of_deriv_le`,
  `CRNT.Dynamics.Gronwall`): the exponential comparison principle.

## What this module adds

This module is the *rate-sensitive layer*: it connects a rate hypothesis to a persistence
statement.

* `RateConvergesExponentially` — the definition: the rate constants `κ t` converge to the
  limiting rate constants `κ ∞` exponentially fast, `|κ t r − κ ∞ r| ≤ C e^{−γ t}`.
* `massActionVectorField_sub_le_of_expConvergence` — the **uniform drift estimate**: the
  mass-action field is *affine* in the rate constants, so the drift of the field caused by the
  moving rates is bounded by `C e^{−γ t}` times a constant that depends only on the network and
  on a bound for the concentrations.  This is the quantitative content of "the time-dependent
  flow is the limiting flow plus a perturbation of size `O(e^{−γ t})`".
* `rateSensitive_sqDist_le` and `rateSensitive_convergence` — the **rate-sensitive persistence
  theorem**: if the limiting field is strictly contracting with rate `c` on a set containing the
  equilibrium (the local-divergence criterion), then every trajectory of the time-dependent
  system that stays in that set converges to the equilibrium, at an exponential rate.  The
  proof is the classical one: the perturbation is *integrated* rather than merely estimated, its
  accumulated effect is bounded by the constant `rateSensitiveBuffer`, and the contraction of
  the limiting flow then forces the orbit onto the equilibrium.
* `rateSensitive_convergence_of_jacobian` — the same statement with the hypothesis expressed
  through the **stable Jacobian** (negative logarithmic norm of the Jacobian of the limiting
  field), which is how the criterion is usually stated.
* `CRNT.Dynamics.ReversiblePairInstance` — a **worked instance**: for the reversible pair
  `A ⇌ B` with rates converging exponentially to the detailed-balanced values, every
  trajectory converges to the equilibrium of the limiting system in its own stoichiometric class.

## What is *not* formalized

The **full exponential-dichotomy theory is not formalized here**.  In particular this module does
*not*

* split the state space of the *time-dependent* system into a stable and an unstable subspace,
* construct the (time-dependent) dichotomy projections, nor
* prove the dichotomy estimates for a non-autonomous linearisation, nor
* treat the persistence question in terms of the distance to a time-dependent stable manifold.

What is claimed instead is the following, weaker but complete statement: *under an exponential
convergence of the rate constants, and a strictly contracting limiting field on a set containing
the equilibrium, every admissible trajectory of the time-dependent system converges to that
equilibrium, with an explicit exponential rate.*  The contraction hypothesis is the local
counterpart of the dichotomy hypothesis (it says that the limiting Jacobian has no unstable
direction on the set in question), and the exponential convergence of the rates plays exactly the
role of the "integrable perturbation" in the dichotomy theory.  The gap between the two
statements is precisely the passage from a local, linear, spectral description to a global,
non-autonomous, dynamical one.

Nothing here is an axiom or a `sorry`.
-/

open BigOperators Filter Topology Set
open CRNT.Network

namespace CRNT
namespace Dynamics

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Multiplying a finite sum by a constant. -/
private theorem sum_mul_const {ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (∑ i, a * f i) = a * (∑ i, f i) := by
  rw [Finset.mul_sum (Finset.univ : Finset ι) f a]

/-- **Exponential convergence of the rate constants.**  The rate constants `κ t` converge to a
limit `κ ∞` exponentially fast, with rate `γ`: `‖κ t − κ ∞‖ ≤ C e^{−γ t}`. -/
def RateConvergesExponentially (N : Network S) (κ : ℝ → N.RateConstants)
    (κlim : N.RateConstants) (γ C : ℝ) : Prop :=
  0 < γ ∧ 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ r, |(κ t).k r - κlim.k r| ≤ C * Real.exp (-γ * t)

/-- The total stoichiometric coefficient of the source complex of a reaction. -/
def reactionDegree (N : Network S) (r : N.R) : ℕ :=
  ∑ s, (N.reaction r).source s

/-- A uniform bound on how much the mass-action field can change when the rate constants
change by at most `B^degree` on the box `{x | ∀ s, |x s| ≤ B}`. -/
def rateLipschitzBound (N : Network S) (B : ℝ) : ℝ :=
  ∑ r : N.R, B ^ (reactionDegree N r) * (∑ s, |N.reactionVector r s|)

/-- **The mass-action monomial is bounded on a box.**  On the box `{x | ∀ s, |x s| ≤ B}` the
source monomial of a reaction is bounded by `B` raised to the total stoichiometric degree of the
source complex. -/
theorem massActionMonomial_abs_le (N : Network S) {B : ℝ} {x : Concentration S}
    (hxB : ∀ s, |x s| ≤ B) (r : N.R) :
    |(N.reaction r).source.massActionMonomial x| ≤ B ^ (reactionDegree N r) := by
  have h1 : |(N.reaction r).source.massActionMonomial x|
      = ∏ s, |x s| ^ (N.reaction r).source s := by
    rw [Complex.massActionMonomial, Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro s _
    rw [abs_pow]
  have h2 : (∏ s, |x s| ^ (N.reaction r).source s) ≤ ∏ s, B ^ (N.reaction r).source s := by
    refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg (abs_nonneg _) _) ?_
    intro s _
    exact pow_le_pow_left₀ (abs_nonneg _) (hxB s) _
  have h3 : (∏ s, B ^ (N.reaction r).source s) = B ^ (∑ s, (N.reaction r).source s) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  calc |(N.reaction r).source.massActionMonomial x|
      = ∏ s, |x s| ^ (N.reaction r).source s := h1
    _ ≤ ∏ s, B ^ (N.reaction r).source s := h2
    _ = B ^ (∑ s, (N.reaction r).source s) := h3

/-- **The drift of the mass-action field is uniform under exponentially converging rates.**  If
the rate constants converge to `κ ∞` exponentially fast, then for `t` large the field at `x` is
within `C e^{−γ t}` of the field at `κ ∞`, uniformly on the box `{x | ∀ s, |x s| ≤ B}`. -/
theorem massActionVectorField_sub_le_of_expConvergence (N : Network S)
    (κ : ℝ → N.RateConstants) (κlim : N.RateConstants) {γ C : ℝ}
    (hκ : RateConvergesExponentially N κ κlim γ C) {B : ℝ} (hB : 1 ≤ B)
    {x : Concentration S} (hxB : ∀ s, |x s| ≤ B) :
    ∀ t, 0 ≤ t → ∀ s : S,
      |N.massActionVectorField (κ t) x s - N.massActionVectorField κlim x s|
        ≤ C * (rateLipschitzBound N B) * Real.exp (-γ * t) := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  intro t ht s
  have hfield : N.massActionVectorField (κ t) x s - N.massActionVectorField κlim x s
      = ∑ r : N.R, (((κ t).k r - κlim.k r) * (N.reaction r).source.massActionMonomial x)
          * N.reactionVector r s := by
    rw [massActionVectorField_apply, massActionVectorField_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simp only [massActionRate]
    ring
  have hmono : ∀ r : N.R,
      |(N.reaction r).source.massActionMonomial x| ≤ B ^ (reactionDegree N r) :=
    fun r => massActionMonomial_abs_le N hxB r
  have hCe : 0 ≤ C * Real.exp (-γ * t) := mul_nonneg hκ.2.1 (Real.exp_pos _).le
  calc |N.massActionVectorField (κ t) x s - N.massActionVectorField κlim x s|
      = |∑ r : N.R, (((κ t).k r - κlim.k r) * (N.reaction r).source.massActionMonomial x)
          * N.reactionVector r s| := by rw [hfield]
    _ ≤ ∑ r : N.R, |(((κ t).k r - κlim.k r) * (N.reaction r).source.massActionMonomial x)
          * N.reactionVector r s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : N.R, (C * Real.exp (-γ * t)) * B ^ (reactionDegree N r)
          * |N.reactionVector r s| := by
      refine Finset.sum_le_sum fun r _ => ?_
      have h1 := hκ.2.2 t ht r
      have h2 := hmono r
      have h4 : 0 ≤ B ^ (reactionDegree N r) := pow_nonneg hB0 _
      have h2' : |(N.reaction r).source.massActionMonomial x| * |N.reactionVector r s|
          ≤ B ^ (reactionDegree N r) * |N.reactionVector r s| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      calc |((κ t).k r - κlim.k r) * (N.reaction r).source.massActionMonomial x
            * N.reactionVector r s|
          = |(κ t).k r - κlim.k r|
              * (|(N.reaction r).source.massActionMonomial x| * |N.reactionVector r s|) := by
            rw [abs_mul, abs_mul]; ring
        _ ≤ (C * Real.exp (-γ * t))
              * (B ^ (reactionDegree N r) * |N.reactionVector r s|) := by
            exact mul_le_mul h1 h2'
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCe
        _ = (C * Real.exp (-γ * t)) * B ^ (reactionDegree N r)
              * |N.reactionVector r s| := by ring
    _ ≤ C * (rateLipschitzBound N B) * Real.exp (-γ * t) := by
      have h5 : ∀ r : N.R, |N.reactionVector r s| ≤ ∑ u, |N.reactionVector r u| := by
        intro r
        exact Finset.single_le_sum (fun u _ => abs_nonneg (N.reactionVector r u))
          (Finset.mem_univ s)
      calc (∑ r : N.R, (C * Real.exp (-γ * t)) * B ^ (reactionDegree N r)
            * |N.reactionVector r s|)
          ≤ ∑ r : N.R, (C * Real.exp (-γ * t)) * B ^ (reactionDegree N r)
            * (∑ u, |N.reactionVector r u|) := by
              refine Finset.sum_le_sum fun r _ => ?_
              exact mul_le_mul_of_nonneg_left (h5 r) (mul_nonneg hCe (pow_nonneg hB0 _))
        _ = C * Real.exp (-γ * t)
            * (∑ r : N.R, B ^ (reactionDegree N r) * (∑ u, |N.reactionVector r u|)) := by
              rw [Finset.mul_sum (Finset.univ : Finset N.R)
                (fun r => B ^ (reactionDegree N r) * (∑ u, |N.reactionVector r u|))
                (C * Real.exp (-γ * t))]
              apply Finset.sum_congr rfl
              intro r _
              ring
        _ = C * (rateLipschitzBound N B) * Real.exp (-γ * t) := by
              simp only [rateLipschitzBound]
              ring

/-! ### The divergence criterion -/

/-- **The local divergence criterion.**  On the set `K` the mass-action field of the limiting
rate constants `κ` has a *strictly negative* one-sided Lipschitz constant: the quadratic form
`⟨u, J u⟩` of its Jacobian, evaluated in the direction `u = a - b`, is bounded above by
`-c ‖u‖²`.  This is the logarithmic-norm (local-divergence) criterion of Anderson–Ramaswamy–
Serafini–Soni for the stability of the limiting equilibrium. -/
def OneSidedLipschitz (N : Network S) (κ : N.RateConstants) (K : Set (Concentration S))
    (c : ℝ) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K,
    ∑ s, (a s - b s) * (N.massActionVectorField κ a s - N.massActionVectorField κ b s)
      ≤ -c * ∑ s, (a s - b s) ^ 2

/-- **The stable-Jacobian criterion.**  The Jacobian of the mass-action field of the limiting
rate constants `κ` has a uniformly negative logarithmic norm on `K`: for every `x ∈ K` and every
direction `u`, `⟨u, J x u⟩ ≤ -c ‖u‖²`.  On a convex `K` this implies `OneSidedLipschitz`. -/
def HasNegativeLogNorm (N : Network S) (κ : N.RateConstants) (K : Set (Concentration S))
    (c : ℝ) : Prop :=
  ∀ x ∈ K, ∀ u : Concentration S,
    ∑ s, u s * N.massActionJacobianCLM κ x u s ≤ -c * ∑ s, u s ^ 2

/-- The quadratic bound on the drift of the mass-action field under exponentially converging
rates: the sum of the squares of the coordinate-wise drift is at most `M2 e^{-2 γ t}`. -/
def rateDriftBound (N : Network S) (C B : ℝ) : ℝ :=
  (Fintype.card S : ℝ) * (C * (rateLipschitzBound N B)) ^ 2

/-- **The accumulated effect of the exponentially decaying perturbation.**  In the rate-sensitive
estimate the perturbation of the limiting field is *integrated*, not merely estimated: an
exponentially decaying forcing term has finite total mass, and the accumulated (discounted)
effect of a perturbation of size `M2 e^{-2 γ t}` on a contracting system with rate `c` is bounded
by `rateSensitiveBuffer M2 c γ`, independently of the length of the time window. -/
noncomputable def rateSensitiveBuffer (M2 c γ : ℝ) : ℝ :=
  M2 / (c * (c - min c (2 * γ) / 2))

/-- **The quantitative rate-sensitive estimate.**  Let the rate constants `κ t` converge to
`κ lim` exponentially fast, let `x lim` be an equilibrium of the limiting mass-action field, and
suppose that the limiting field is *strictly contracting* with rate `c > 0` on a set `K`
containing `x lim` (the local-divergence criterion).  Then every trajectory of the
time-dependent system that stays in `K` and in a bounded box converges to `x lim` exponentially:

`‖x t − x lim‖² ≤ (‖x 0 − x lim‖² + μ) e^{−δ t}`,  `δ = min(c, 2 γ)/2 > 0`.

The rate `δ` is the smaller of the contraction rate `c` and the decay rate `2 γ` of the
*quadratic* drift of the field (up to a factor `2`): the perturbation `f_{κ t} − f_{κ lim}` has
size `O(e^{−γ t})`, so its accumulated, discounted effect on the energy of the trajectory is
controlled by `e^{−2 γ t}`.

Here `μ = rateSensitiveBuffer …` bounds the *accumulated* effect of the exponentially decaying
perturbation `f_{κ t} − f_{κ lim}`.  This is the Anderson–Ramaswamy–Serafini–Soni argument
(*Exponential Dichotomy and Persistence*, SIAM J. Appl. Math. 56 (1997)): the time-dependent flow
is the sum of the limiting flow and a perturbation of size `O(e^{−γ t})`; the perturbation is
integrated, so its accumulated effect stays bounded, and the contraction of the limiting flow
then forces the trajectory onto the equilibrium. -/
theorem rateSensitive_sqDist_le (N : Network S) (κ : ℝ → N.RateConstants)
    (κlim : N.RateConstants) {γ C : ℝ} (hκ : RateConvergesExponentially N κ κlim γ C)
    {xlim : Concentration S} (hxeq : N.massActionVectorField κlim xlim = 0)
    {c : ℝ} (hc : 0 < c)
    {K : Set (Concentration S)} (hxlimK : xlim ∈ K)
    (hLip : OneSidedLipschitz N κlim K c)
    {B : ℝ} (hB : 1 ≤ B)
    {x : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField (κ t) (x t)) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K)
    (hxb : ∀ t, 0 ≤ t → ∀ s, |x t s| ≤ B) :
    ∀ t, 0 ≤ t → sqDist (x t) xlim
      ≤ (sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ)
          * Real.exp (-(min c (2 * γ) / 2) * t) := by
  intro t ht
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- the constants
  have hγ : 0 < γ := hκ.1
  have hC0 : 0 ≤ C := hκ.2.1
  set M2 : ℝ := rateDriftBound N C B with hM2def
  have hM2nn : 0 ≤ M2 := by
    dsimp [M2, rateDriftBound]
    positivity
  set δ : ℝ := min c (2 * γ) / 2 with hδdef
  have hδlt : δ < c := by
    have h1 : min c (2 * γ) ≤ c := min_le_left _ _
    have h2 : min c (2 * γ) / 2 ≤ c / 2 := by linarith
    rw [hδdef]
    linarith
  have hδle : δ ≤ 2 * γ := by
    have h1 : min c (2 * γ) ≤ 2 * γ := min_le_right _ _
    have h2 : min c (2 * γ) / 2 ≤ (2 * γ) / 2 := by linarith
    rw [hδdef]
    have h3 : (2 * γ) / 2 ≤ 2 * γ := by linarith
    linarith
  -- the drift of the field under the exponentially converging rates
  have hdrift : ∀ τ, 0 ≤ τ → ∀ s,
      |N.massActionVectorField (κ τ) (x τ) s - N.massActionVectorField κlim (x τ) s|
        ≤ C * (rateLipschitzBound N B) * Real.exp (-γ * τ) := by
    intro τ hτ s
    exact massActionVectorField_sub_le_of_expConvergence N κ κlim hκ hB
      (fun s => hxb τ hτ s) τ hτ s
  have hsq : ∀ τ, 0 ≤ τ →
      (∑ s, (N.massActionVectorField (κ τ) (x τ) s
          - N.massActionVectorField κlim (x τ) s) ^ 2)
        ≤ M2 * Real.exp (-2 * γ * τ) := by
    intro τ hτ
    have h1 : ∀ s,
        |N.massActionVectorField (κ τ) (x τ) s - N.massActionVectorField κlim (x τ) s|
          ≤ C * (rateLipschitzBound N B) * Real.exp (-γ * τ) := hdrift τ hτ
    have hexp2 : Real.exp (-2 * γ * τ) = (Real.exp (-γ * τ)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc (∑ s, (N.massActionVectorField (κ τ) (x τ) s
          - N.massActionVectorField κlim (x τ) s) ^ 2)
        = ∑ s, |N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s| ^ 2 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [sq_abs]
        _ ≤ ∑ s, (C * (rateLipschitzBound N B) * Real.exp (-γ * τ)) ^ 2 := by
          refine Finset.sum_le_sum fun s _ => ?_
          have hsq' := mul_self_le_mul_self (abs_nonneg _) (h1 s)
          nlinarith [hsq']
        _ = M2 * Real.exp (-2 * γ * τ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hexp2]
          dsimp [M2, rateDriftBound]
          ring
  -- the Lyapunov function
  set V : ℝ → ℝ := fun τ => sqDist (x τ) xlim with hVdef
  have hVd : ∀ τ, 0 ≤ τ → HasDerivAt V
      (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s)) τ := by
    intro τ hτ
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset S)) fun s _ =>
      ((((hasDerivAt_pi.mp (hx τ hτ)) s).sub (hasDerivAt_const τ (xlim s))).pow 2)
    convert hsum using 1
    · funext τ; simp [V, sqDist]
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp
  -- the elementary estimate `2 c |u| |v| ≤ c² |u|² + |v|²`
  have hper : ∀ u v : ℝ, 2 * c * (|u| * |v|) ≤ c ^ 2 * |u| ^ 2 + |v| ^ 2 := by
    intro u v
    have hsq' : 0 ≤ (c * |u| - |v|) ^ 2 := sq_nonneg _
    nlinarith [hsq']
  -- the derivative of the Lyapunov function
  have hVbound : ∀ τ, 0 ≤ τ →
      c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
        ≤ -c ^ 2 * V τ
          + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2) := by
    intro τ hτ
    have hmain : ∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s
        ≤ -c * ∑ s, (x τ s - xlim s) ^ 2 := by
      have h := hLip (x τ) (hxK τ hτ) xlim hxlimK
      calc (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
          = ∑ s, (x τ s - xlim s) * (N.massActionVectorField κlim (x τ) s
              - N.massActionVectorField κlim xlim s) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            have hz : N.massActionVectorField κlim xlim s = 0 := congrFun hxeq s
            rw [hz]
            ring
        _ ≤ -c * ∑ s, (x τ s - xlim s) ^ 2 := h
    have habs : ∑ s, (x τ s - xlim s)
          * (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s)
        ≤ ∑ s, |x τ s - xlim s|
          * |N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s| := by
      refine Finset.sum_le_sum fun s _ => ?_
      calc (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s)
          ≤ |(x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s)| := le_abs_self _
        _ = |x τ s - xlim s|
            * |N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s| := by rw [abs_mul]
    have hB : (∑ s, |x τ s - xlim s| ^ 2) = ∑ s, (x τ s - xlim s) ^ 2 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sq_abs]
    have hC : (∑ s, |N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s| ^ 2)
          = ∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sq_abs]
    have hcont : 2 * c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
        ≤ -2 * c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2) := by
      calc 2 * c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
          = 2 * (c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)) := by
            ring
        _ ≤ 2 * (c * (-c * (∑ s, (x τ s - xlim s) ^ 2))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmain (by positivity)) (by norm_num)
        _ = -2 * c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2) := by ring
    have hpert : 2 * c * (∑ s, (x τ s - xlim s)
          * (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s))
        ≤ c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2)
          + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s) ^ 2) := by
      calc 2 * c * (∑ s, (x τ s - xlim s)
            * (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s))
          ≤ 2 * c * (∑ s, |x τ s - xlim s|
            * |N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s|) := by
            exact mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2 * c)
        _ = ∑ s, 2 * c * (|x τ s - xlim s|
            * |N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s|) := by
            rw [sum_mul_const]
        _ ≤ ∑ s, (c ^ 2 * |x τ s - xlim s| ^ 2
            + |N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s| ^ 2) := by
            refine Finset.sum_le_sum fun s _ => ?_
            exact hper _ _
        _ = (∑ s, c ^ 2 * |x τ s - xlim s| ^ 2)
            + (∑ s, |N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s| ^ 2) := by
            rw [Finset.sum_add_distrib]
        _ = c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2)
            + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2) := by
            rw [sum_mul_const, hB, hC]
    have hsplit : 2 * c * (∑ s, (x τ s - xlim s)
          * (N.massActionVectorField (κ τ) (x τ) s))
        = 2 * c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
          + 2 * c * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
            - N.massActionVectorField κlim (x τ) s)) := by
      calc 2 * c * (∑ s, (x τ s - xlim s)
            * (N.massActionVectorField (κ τ) (x τ) s))
          = ∑ s, 2 * c * ((x τ s - xlim s)
              * (N.massActionVectorField (κ τ) (x τ) s)) := by
            rw [sum_mul_const]
        _ = ∑ s, (2 * c * ((x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
            + 2 * c * ((x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s))) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ = (∑ s, 2 * c * ((x τ s - xlim s) * N.massActionVectorField κlim (x τ) s))
            + (∑ s, 2 * c * ((x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s))) := by
            rw [Finset.sum_add_distrib]
        _ = 2 * c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
            + 2 * c * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s)) := by
            rw [sum_mul_const, sum_mul_const]
    calc c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
        = 2 * c * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s)) := by
          have h1 : (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
              = 2 * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s)) := by
            calc (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
                = ∑ s, 2 * ((x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s)) := by
                  refine Finset.sum_congr rfl fun s _ => ?_
                  ring
              _ = 2 * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s)) := by
                  rw [← Finset.mul_sum (Finset.univ : Finset S)
                    (fun r : S => (x τ r - xlim r) * (N.massActionVectorField (κ τ) (x τ) r)) 2]
          rw [h1]
          ring
        _ = 2 * c * (∑ s, (x τ s - xlim s) * N.massActionVectorField κlim (x τ) s)
            + 2 * c * (∑ s, (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s)) := hsplit
        _ ≤ -2 * c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2)
            + (c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2)
              + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
                - N.massActionVectorField κlim (x τ) s) ^ 2)) := by
          exact add_le_add hcont hpert
        _ = -c ^ 2 * (∑ s, (x τ s - xlim s) ^ 2)
            + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2) := by ring
        _ = -c ^ 2 * V τ
            + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2) := by
          simp only [V, sqDist]
  -- the auxiliary function absorbing the accumulated effect of the perturbation
  set σ : ℝ := -M2 / (c - δ) with hσdef
  have hσkey : σ * (δ - c) = M2 := by
    have hne : c - δ ≠ 0 := by
      rw [hδdef]
      have h1 : min c (2 * γ) ≤ c := min_le_left _ _
      linarith
    rw [hσdef]
    field_simp
    ring
  have hσnn : σ ≤ 0 := by
    rw [hσdef]
    have h1 : 0 < c - δ := by
      rw [hδdef]
      have h2 : min c (2 * γ) ≤ c := min_le_left _ _
      linarith
    have h2 : 0 ≤ M2 := hM2nn
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h2) h1.le
  set W : ℝ → ℝ := fun τ => c * V τ + σ * Real.exp (-δ * τ) with hWdef
  have hWd : ∀ τ, 0 ≤ τ → HasDerivAt W
      (c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
        + σ * Real.exp (-δ * τ) * (-δ)) τ := by
    intro τ hτ
    have hV := hVd τ hτ
    have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-δ * τ))
        (Real.exp (-δ * τ) * (-δ)) τ := by
      simpa using ((hasDerivAt_id τ).const_mul (-δ)).exp
    have hσ := hexp.const_mul σ
    have hcv := hV.const_mul c
    have hsum := hcv.add hσ
    convert hsum using 1
    all_goals ring
  have hWbound : ∀ τ, 0 ≤ τ →
      (c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
        + σ * Real.exp (-δ * τ) * (-δ)) ≤ (-c) * W τ := by
    intro τ hτ
    have h1 := hVbound τ hτ
    have hsqτ := hsq τ hτ
    have hexp1 : Real.exp (-2 * γ * τ) ≤ Real.exp (-δ * τ) := by
      apply Real.exp_le_exp.mpr
      have hmul : -2 * γ * τ ≤ -δ * τ := by
        have h3 := mul_le_mul_of_nonneg_right hδle hτ
        linarith
      exact hmul
    have hY : (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2)
        ≤ M2 * Real.exp (-δ * τ) := by
      calc (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2)
          ≤ M2 * Real.exp (-2 * γ * τ) := hsqτ
        _ ≤ M2 * Real.exp (-δ * τ) := mul_le_mul_of_nonneg_left hexp1 hM2nn
    have hM2key : M2 = -(c - δ) * σ := by
      rw [← hσkey]
      ring
    calc (c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
          + σ * Real.exp (-δ * τ) * (-δ))
        ≤ ((-c ^ 2 * V τ
            + (∑ s, (N.massActionVectorField (κ τ) (x τ) s
              - N.massActionVectorField κlim (x τ) s) ^ 2))
          + σ * Real.exp (-δ * τ) * (-δ)) := by
          exact add_le_add_left h1 (σ * Real.exp (-δ * τ) * (-δ))
        _ ≤ ((-c ^ 2 * V τ + M2 * Real.exp (-δ * τ))
          + σ * Real.exp (-δ * τ) * (-δ)) := by
          exact add_le_add_left (add_le_add_right hY (-c ^ 2 * V τ))
            (σ * Real.exp (-δ * τ) * (-δ))
        _ = -c * (c * V τ + σ * Real.exp (-δ * τ)) := by
          rw [hM2key]
          ring
        _ = -c * W τ := by simp only [W]
  -- Grönwall
  have hgron := gronwall_exp_comparison_of_ge (f := W)
    (f' := fun τ => c * (∑ s, 2 * (x τ s - xlim s) * (N.massActionVectorField (κ τ) (x τ) s))
        + σ * Real.exp (-δ * τ) * (-δ))
    (c := -c) (t₀ := 0)
    (fun τ hτ => hWd τ hτ) (fun τ hτ => hWbound τ hτ) t ht
  have hexpneg : Real.exp ((-c) * (t - 0)) = Real.exp (-c * t) := by
    rw [sub_zero, neg_mul]
  rw [hexpneg] at hgron
  -- the final assembly
  have hV0nn : 0 ≤ V 0 := by simp only [V, sqDist]; positivity
  have hδct : Real.exp (-c * t) ≤ Real.exp (-δ * t) := by
    apply Real.exp_le_exp.mpr
    have h3 := mul_le_mul_of_nonneg_right hδlt.le ht
    linarith
  have hW0 : W 0 = c * V 0 + σ := by
    simp [W]
  have hmain2 : c * V t + σ * Real.exp (-δ * t) ≤ (c * V 0 + σ) * Real.exp (-c * t) := by
    calc c * V t + σ * Real.exp (-δ * t) = W t := by simp only [W]
      _ ≤ Real.exp (-c * t) * W 0 := hgron
      _ = (c * V 0 + σ) * Real.exp (-c * t) := by rw [hW0]; ring
  have hstep : c * V t ≤ (c * V 0 + σ) * Real.exp (-c * t)
      + (-σ) * Real.exp (-δ * t) := by
    have hsub := sub_le_sub_right hmain2 (σ * Real.exp (-δ * t))
    convert hsub using 1 <;> ring
  have hμkey : -σ = c * rateSensitiveBuffer M2 c γ := by
    have hDne : c - δ ≠ 0 := by
      rw [hδdef]
      have h1 : min c (2 * γ) ≤ c := min_le_left _ _
      linarith
    calc -σ = M2 / (c - δ) := by rw [hσdef]; ring
      _ = c * (M2 / (c * (c - δ))) := by
          field_simp
      _ = c * rateSensitiveBuffer M2 c γ := by
          rw [rateSensitiveBuffer, hδdef]
  have hfinal : c * V t ≤ (c * V 0 + c * rateSensitiveBuffer M2 c γ) * Real.exp (-δ * t) := by
    calc c * V t
        ≤ (c * V 0 + σ) * Real.exp (-c * t) + (-σ) * Real.exp (-δ * t) := hstep
      _ = (c * V 0 * Real.exp (-c * t) + σ * Real.exp (-c * t))
          + (-σ) * Real.exp (-δ * t) := by ring
      _ ≤ (c * V 0 * Real.exp (-δ * t) + 0)
          + (-σ) * Real.exp (-δ * t) := by
        have h1 : c * V 0 * Real.exp (-c * t) ≤ c * V 0 * Real.exp (-δ * t) :=
          mul_le_mul_of_nonneg_left hδct (mul_nonneg hc.le hV0nn)
        have h2 : σ * Real.exp (-c * t) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hσnn (Real.exp_nonneg _)
        exact add_le_add_left (add_le_add h1 h2) ((-σ) * Real.exp (-δ * t))
      _ = (c * V 0 + c * rateSensitiveBuffer M2 c γ) * Real.exp (-δ * t) := by
        rw [hμkey]
        ring
  calc sqDist (x t) xlim
      = c * V t / c := by
        simp only [V, sqDist]
        field_simp
    _ ≤ (c * V 0 + c * rateSensitiveBuffer M2 c γ) * Real.exp (-δ * t) / c := by
      exact div_le_div_of_nonneg_right hfinal hc.le
    _ = (V 0 + rateSensitiveBuffer M2 c γ) * Real.exp (-δ * t) := by
      field_simp
    _ = (sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ)
          * Real.exp (-(min c (2 * γ) / 2) * t) := by
      simp only [V, sqDist, hM2def, hδdef]

/-! ### Convergence to the equilibrium -/

/-- **Rate-sensitive convergence.**  Let the rate constants `κ t` converge to `κ lim` exponentially
fast, let `x lim` be an equilibrium of the limiting mass-action field, and suppose that the
limiting field is strictly contracting with rate `c > 0` on a set `K` containing `x lim` (the
local-divergence criterion).  Then every trajectory of the time-dependent system that stays in `K`
and in a bounded box converges to `x lim`. -/
theorem rateSensitive_convergence (N : Network S) (κ : ℝ → N.RateConstants)
    (κlim : N.RateConstants) {γ C : ℝ} (hκ : RateConvergesExponentially N κ κlim γ C)
    {xlim : Concentration S} (hxeq : N.massActionVectorField κlim xlim = 0)
    {c : ℝ} (hc : 0 < c)
    {K : Set (Concentration S)} (hxlimK : xlim ∈ K)
    (hLip : OneSidedLipschitz N κlim K c)
    {B : ℝ} (hB : 1 ≤ B)
    {x : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField (κ t) (x t)) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K)
    (hxb : ∀ t, 0 ≤ t → ∀ s, |x t s| ≤ B) :
    Tendsto x atTop (𝓝 xlim) := by
  have hsq := rateSensitive_sqDist_le N κ κlim hκ hxeq hc hxlimK hLip hB hx hxK hxb
  have hγ : 0 < γ := hκ.1
  have hδpos : 0 < min c (2 * γ) / 2 := by
    have h1 : 0 < min c (2 * γ) := lt_min hc (by linarith)
    linarith
  have hK : 0 ≤ sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ := by
    have h1 : 0 ≤ sqDist (x 0) xlim := by
      simp only [sqDist]
      positivity
    have h2 : 0 ≤ rateSensitiveBuffer (rateDriftBound N C B) c γ := by
      have hM : 0 ≤ rateDriftBound N C B := by
        dsimp [rateDriftBound]
        positivity
      have hcδ : 0 < c - min c (2 * γ) / 2 := by
        have h3 : min c (2 * γ) ≤ c := min_le_left _ _
        linarith
      unfold rateSensitiveBuffer
      exact div_nonneg hM (mul_pos hc hcδ).le
    linarith
  have hexp : Tendsto (fun t => Real.exp (-(min c (2 * γ) / 2) * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hδpos) (l := atTop))
    simpa [Function.comp_def] using h
  have hmul : Tendsto (fun t => (sqDist (x 0) xlim
      + rateSensitiveBuffer (rateDriftBound N C B) c γ)
      * Real.exp (-(min c (2 * γ) / 2) * t)) atTop (𝓝 0) := by
    have hmul0 := hexp.mul_const
      (sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ)
    have heq : (fun t => Real.exp (-(min c (2 * γ) / 2) * t)
        * (sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ))
        = fun t => (sqDist (x 0) xlim + rateSensitiveBuffer (rateDriftBound N C B) c γ)
          * Real.exp (-(min c (2 * γ) / 2) * t) := by
      funext t
      ring
    rw [heq] at hmul0
    simpa using hmul0
  have hlim : Tendsto (fun t => sqDist (x t) xlim) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => ?_) ?_ hmul
    · simp only [sqDist]
      positivity
    · filter_upwards [eventually_ge_atTop 0] with t ht
      exact hsq t ht
  have hcoord : ∀ s : S, Tendsto (fun t => x t s) atTop (𝓝 (xlim s)) := by
    intro s
    have hsqcoord : ∀ᶠ t in atTop, (x t s - xlim s) ^ 2 ≤ sqDist (x t) xlim := by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact Finset.single_le_sum (f := fun r => (x t r - xlim r) ^ 2)
        (fun r _ => sq_nonneg _) (Finset.mem_univ s)
    have h1 : Tendsto (fun t => (x t s - xlim s) ^ 2) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) hsqcoord hlim
    have h2 : Tendsto (fun t => |x t s - xlim s|) atTop (𝓝 0) := by
      have heq : (fun t => |x t s - xlim s|) = fun t => Real.sqrt ((x t s - xlim s) ^ 2) := by
        funext t; rw [Real.sqrt_sq_eq_abs]
      rw [heq]
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h1
    have h3 : Tendsto (fun t => ‖x t s - xlim s‖) atTop (𝓝 0) := by
      simpa using h2
    exact (tendsto_iff_norm_sub_tendsto_zero).2 h3
  exact tendsto_pi_nhds.mpr hcoord

/-- **The rate-sensitive theorem in the stable-Jacobian form.**  The local-divergence criterion
can be expressed through the Jacobian of the limiting field: if the logarithmic norm of the
Jacobian is uniformly negative on the convex set `K`, then the limiting field is strictly
contracting there, and the rate-sensitive convergence theorem applies. -/
theorem rateSensitive_convergence_of_jacobian (N : Network S) (κ : ℝ → N.RateConstants)
    (κlim : N.RateConstants) {γ C : ℝ} (hκ : RateConvergesExponentially N κ κlim γ C)
    {xlim : Concentration S} (hxeq : N.massActionVectorField κlim xlim = 0)
    {c : ℝ} (hc : 0 < c)
    {K : Set (Concentration S)} (hxlimK : xlim ∈ K)
    (hC : Convex ℝ K)
    (hJ : HasNegativeLogNorm N κlim K c)
    {B : ℝ} (hB : 1 ≤ B)
    {x : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField (κ t) (x t)) t)
    (hxK : ∀ t, 0 ≤ t → x t ∈ K)
    (hxb : ∀ t, 0 ≤ t → ∀ s, |x t s| ≤ B) :
    Tendsto x atTop (𝓝 xlim) := by
  have hLip : OneSidedLipschitz N κlim K c := by
    intro a ha b hb
    have h := oneSided_of_jacobian hC (fun x _ => N.massActionVectorField_hasFDerivAt κlim x)
      hJ ha hb
    simpa [sqDist] using h
  exact rateSensitive_convergence N κ κlim hκ hxeq hc hxlimK hLip hB hx hxK hxb

/-! ## The worked instance: the reversible pair `A ⇌ B` -/

namespace ReversiblePairInstance

open CRNT.Examples.ReversiblePair
open Species

/-- **The explicit form of the mass-action field of the reversible pair `A ⇌ B`.**  With forward
rate constant `κ fwd` and backward rate constant `κ bwd`, the field is
`ẋ_A = −κ fwd x_A + κ bwd x_B` and `ẋ_B = κ fwd x_A − κ bwd x_B`. -/
theorem massActionVectorField_reversiblePair (κ : N.RateConstants) (x : Concentration Species)
    (s : Species) :
    N.massActionVectorField κ x s
      = match s with
        | .A => -(κ.k Rxn.fwd) * x .A + (κ.k Rxn.bwd) * x .B
        | .B => (κ.k Rxn.fwd) * x .A - (κ.k Rxn.bwd) * x .B := by
  cases s
  · rw [Network.massActionVectorField_apply]
    have huniv : (Finset.univ : Finset Rxn) = {Rxn.fwd, Rxn.bwd} := by decide
    rw [show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r .A)
          = ∑ r : Rxn, N.massActionRate κ r x * N.reactionVector r .A from rfl, huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Network.massActionRate, Complex.massActionMonomial, prod_univ_species, N, rxn, cA, cB,
      Network.reactionVector, Reaction.vector]
  · rw [Network.massActionVectorField_apply]
    have huniv : (Finset.univ : Finset Rxn) = {Rxn.fwd, Rxn.bwd} := by decide
    rw [show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r .B)
          = ∑ r : Rxn, N.massActionRate κ r x * N.reactionVector r .B from rfl, huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Network.massActionRate, Complex.massActionMonomial, prod_univ_species, N, rxn, cA, cB,
      Network.reactionVector, Reaction.vector]
    ring

/-- The equilibrium of the reversible pair `A ⇌ B` with forward rate constant `k₀`, backward rate
constant `k₁`, in the stoichiometric class of total concentration `T`.  It is the
detailed-balanced point `x_A = k₁ T/(k₀+k₁)`, `x_B = k₀ T/(k₀+k₁)`. -/
noncomputable def reversiblePairEquilibrium (k₀ k₁ T : ℝ) : Concentration Species :=
  fun s => match s with
    | .A => k₁ * T / (k₀ + k₁)
    | .B => k₀ * T / (k₀ + k₁)

/-- The equilibrium of the reversible pair is a steady state of the limiting mass-action field. -/
theorem reversiblePairEquilibrium_isSteadyState {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (T : ℝ) :
    N.massActionVectorField (rates h₀ h₁) (reversiblePairEquilibrium k₀ k₁ T) = 0 := by
  have hsum : k₀ + k₁ ≠ 0 := by
    have : 0 < k₀ + k₁ := by linarith
    exact ne_of_gt this
  funext s
  cases s
  · rw [massActionVectorField_reversiblePair]
    simp [reversiblePairEquilibrium, rates]
    field_simp
    ring
  · rw [massActionVectorField_reversiblePair]
    simp [reversiblePairEquilibrium, rates]
    field_simp
    ring

/-- The total concentration of the reversible pair is conserved by the mass-action dynamics, for
arbitrary (time-dependent) rate constants. -/
theorem reversiblePair_total_conserved (κ : ℝ → N.RateConstants) {x : ℝ → Concentration Species}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField (κ t) (x t)) t) :
    ∀ t, 0 ≤ t → x t .A + x t .B = x 0 .A + x 0 .B := by
  intro t ht
  have hzero : ∀ κ : N.RateConstants, ∀ y : Concentration Species,
      N.massActionVectorField κ y .A + N.massActionVectorField κ y .B = 0 := by
    intro κ y
    rw [massActionVectorField_reversiblePair κ y .A, massActionVectorField_reversiblePair κ y .B]
    ring
  set g : ℝ → ℝ := fun s => x s .A + x s .B with hg
  have hgd : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt g 0 (Set.Icc 0 t) s := by
    intro s hs
    have hA : HasDerivAt (fun y : ℝ => x y .A)
        (N.massActionVectorField (κ s) (x s) .A) s := hasDerivAt_pi.mp (hx s hs.1) .A
    have hB : HasDerivAt (fun y : ℝ => x y .B)
        (N.massActionVectorField (κ s) (x s) .B) s := hasDerivAt_pi.mp (hx s hs.1) .B
    have h3 : HasDerivAt (fun y : ℝ => x y .A + x y .B)
        (N.massActionVectorField (κ s) (x s) .A + N.massActionVectorField (κ s) (x s) .B) s :=
      hA.add hB
    have h2 : HasDerivAt g
        (N.massActionVectorField (κ s) (x s) .A + N.massActionVectorField (κ s) (x s) .B) s := by
      simpa only [hg] using h3
    rw [hzero] at h2
    exact h2.hasDerivWithinAt
  have hconst : g t = g 0 := by
    have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
      (fun s hs => hgd s hs) (fun s _ => by simp) (convex_Icc 0 t) ⟨le_refl 0, ht⟩ ⟨ht, le_refl t⟩
    simp only [zero_mul] at hle
    have h0 : ‖g t - g 0‖ = 0 := le_antisymm hle (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at h0
  simpa only [hg] using hconst

/-- The limiting mass-action field of the reversible pair is contracting with rate `k₀ + k₁` on
each stoichiometric class (the affine line `x_A + x_B = T`).  This is the elementary
counterpart of the logarithmic-norm criterion: the reaction vectors of the pair are opposite, so
the quadratic form of the field is `−(k₀+k₁)` times the squared distance on the class. -/
theorem reversiblePair_oneSided {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) (T : ℝ) :
    OneSidedLipschitz N (rates h₀ h₁) {y : Concentration Species | y .A + y .B = T}
      (k₀ + k₁) := by
  intro a ha b hb
  have hΔ : a .A - b .A = -(a .B - b .B) := by
    have h1 : a .A + a .B = T := by
      simpa only [Set.mem_ofPred_eq] using ha
    have h2 : b .A + b .B = T := by
      simpa only [Set.mem_ofPred_eq] using hb
    linarith
  have hunivS : (Finset.univ : Finset Species) = {Species.A, Species.B} := by decide
  rw [hunivS, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hdiffA : N.massActionVectorField (rates h₀ h₁) a .A
      - N.massActionVectorField (rates h₀ h₁) b .A
      = -(k₀ * (a .A - b .A)) + k₁ * (a .B - b .B) := by
    rw [massActionVectorField_reversiblePair, massActionVectorField_reversiblePair]
    simp only [rates]
    ring
  have hdiffB : N.massActionVectorField (rates h₀ h₁) a .B
      - N.massActionVectorField (rates h₀ h₁) b .B
      = k₀ * (a .A - b .A) - k₁ * (a .B - b .B) := by
    rw [massActionVectorField_reversiblePair, massActionVectorField_reversiblePair]
    simp only [rates]
    ring
  rw [hdiffA, hdiffB]
  rw [hΔ]
  nlinarith

/-- **A worked instance.**  For the reversible pair `A ⇌ B` with rates converging exponentially to
the detailed-balanced values, every trajectory converges to the equilibrium of the limiting system
in its own stoichiometric class.  The conservation of the total concentration `x_A + x_B` is the
only extra ingredient: the limiting field contracts with rate `k₀ + k₁` on each such class,
because the reaction vectors of the pair are opposite. -/
theorem reversiblePair_rateSensitive_convergence {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (κ : ℝ → N.RateConstants) {γ C : ℝ}
    (hκ : RateConvergesExponentially N κ (rates h₀ h₁) γ C)
    {T : ℝ} {x : ℝ → Concentration Species}
    (hx0 : x 0 .A + x 0 .B = T)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField (κ t) (x t)) t)
    {B : ℝ} (hB : 1 ≤ B) (hxb : ∀ t, 0 ≤ t → ∀ s, |x t s| ≤ B) :
    Tendsto x atTop (𝓝 (reversiblePairEquilibrium k₀ k₁ T)) := by
  -- the total concentration is conserved
  have hcons := reversiblePair_total_conserved κ hx
  set K : Set (Concentration Species) := {y | y .A + y .B = T} with hK
  -- the equilibrium lies in the class
  have hxlimK : reversiblePairEquilibrium k₀ k₁ T ∈ K := by
    simp only [hK, Set.mem_ofPred_eq, reversiblePairEquilibrium]
    have hsum : k₀ + k₁ ≠ 0 := by
      have : 0 < k₀ + k₁ := by linarith
      exact ne_of_gt this
    field_simp
    ring
  -- the trajectory stays in the class
  have hxK : ∀ t, 0 ≤ t → x t ∈ K := by
    intro t ht
    simp only [hK, Set.mem_ofPred_eq]
    rw [hcons t ht]
    exact hx0
  -- the equilibrium is a steady state of the limiting field
  have hxeq : N.massActionVectorField (rates h₀ h₁) (reversiblePairEquilibrium k₀ k₁ T) = 0 :=
    reversiblePairEquilibrium_isSteadyState h₀ h₁ T
  -- the limiting field contracts on the class
  have hLip : OneSidedLipschitz N (rates h₀ h₁) K (k₀ + k₁) := by
    rw [hK]
    exact reversiblePair_oneSided h₀ h₁ T
  -- the rate-sensitive theorem
  exact rateSensitive_convergence N κ (rates h₀ h₁) hκ hxeq (by linarith) hxlimK hLip hB hx hxK hxb

end ReversiblePairInstance

end Dynamics
end CRNT

/-! ### Axiom audit (informational) -/

#print axioms CRNT.Dynamics.RateConvergesExponentially
#print axioms CRNT.Dynamics.massActionVectorField_sub_le_of_expConvergence
#print axioms CRNT.Dynamics.OneSidedLipschitz
#print axioms CRNT.Dynamics.HasNegativeLogNorm
#print axioms CRNT.Dynamics.rateSensitiveBuffer
#print axioms CRNT.Dynamics.rateSensitive_sqDist_le
#print axioms CRNT.Dynamics.rateSensitive_convergence
#print axioms CRNT.Dynamics.rateSensitive_convergence_of_jacobian
#print axioms CRNT.Dynamics.ReversiblePairInstance.massActionVectorField_reversiblePair
#print axioms CRNT.Dynamics.ReversiblePairInstance.reversiblePairEquilibrium_isSteadyState
#print axioms CRNT.Dynamics.ReversiblePairInstance.reversiblePair_total_conserved
#print axioms CRNT.Dynamics.ReversiblePairInstance.reversiblePair_oneSided
#print axioms CRNT.Dynamics.ReversiblePairInstance.reversiblePair_rateSensitive_convergence
