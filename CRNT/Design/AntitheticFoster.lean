import CRNT.Design.AntitheticErgodic
import CRNT.Design.AntitheticMeanOutput
import CRNT.Stochastic.EndotacticTierPositiveRecurrence

/-!
# The Foster–Lyapunov certificate for the antithetic closed loop

This module supplies the **Foster–Lyapunov certificate** of the antithetic integral feedback
controller, in a form general enough for the *piecewise quadratic* Lyapunov function of the
repository, and the ergodicity consequence of that certificate.  It closes, for the network of
the repository, the *certificate* part of the item left open in leaf **C3** ("antithetic integral
feedback") of `docs/field-map.md`:

> "What remains: the identification of the repository's specific `lyap` with this shape matrix,
> and the certificate for the antithetic network itself (whose unimolecular part is not
> Hurwitz)."

The identification has been made in `CRNT.Design.AntitheticInstance`
(`lyap_eq_generalPlant_quadratic`); **this** module supplies the certificate.

## 1. The controller and its molecular realization

The antithetic integral controller of Briat, Gupta and Khammash (*Antithetic integral feedback
ensures robust perfect adaptation in noisy biomolecular networks*, Cell Systems 2 (2016); *Robustness
analysis of a class of antithetic integral controllers*, Automatica (2019)) pairs a **reference**
reaction with a **sensing** reaction acting on the plant with opposite signs: the *charge*
`q = z₁ − z₂` (the integral of the control error) is the difference of the two.  In the molecular
realization of the repository (`CRNT.Antithetic.closedLoop`) the anti-correlation is realized by
an **annihilation** `Z₁ + Z₂ → ∅` between the actuated species `Z₁` and the sensing species `Z₂`,
while the reference reaction `∅ → Z₁` feeds `Z₁` without bound.  On the species `0 = Z₁`,
`1 = Z₂`, `2 = X` the five reactions are

```text
0 : ∅ → Z₁        (reference,   rate μ)
1 : Z₁ + Z₂ → ∅   (annihilation, rate η)
2 : Z₁ → Z₁ + X   (actuation,   rate k)
3 : X → ∅         (degradation,  rate γ)
4 : X → X + Z₂    (sensing,     rate θ)
```

## 2. What the repository already contains

* the **charge certificate** `CRNT.Antithetic.certificate` (`q = e_{Z₁} − e_{Z₂}` is a maxRPA
  charge) and the **setpoint theorems** `closedLoop_deterministic_setpoint` (every positive steady
  state has `x_X = μ/θ`) and `closedLoop_stochastic_setpoint` (every stationary law with finite
  first output moment has `E_π[X] = μ/θ`);
* the **piecewise quadratic** Lyapunov function
  `CRNT.AntitheticErgodic.lyap κ n = φ κ (n 0) (n 1) + c_b x² − c_c x q + c_d z₁ z₂` with
  `q = z₁ − z₂` and `φ κ z₁ z₂ = c_A q²` on the region `z₂ ≤ z₁`, `c_B q²` off it
  (`c_A = 32kθ + 9γ²`, `c_B = 4γ²`, `c_b = 32θ²`, `c_c = 16γθ`, `c_d = 2γ²`), together with its
  **exact drift** `drift_lyap` and the **drift bound** `drift_lyap_le`
  `Q lyap ≤ −fLyap + cK` with the norm-like function `fLyap`;
* the **modified (continuous) function** `CRNT.AntitheticMeanOutput.wLyap` (equal to `lyap` on
  the region `z₂ ≤ z₁` and to `c_b x² + c_d z₁²` above it), its exponential drift bound
  `drift_wLyap_le`, the uniform second moment `output_sq_moment_le`, and the convergence of the
  mean output `closedLoop_mean_output_tendsto`;
* the **irreducibility** of the closed loop on `ℕ³` (`CRNT.AntitheticErgodic.irreducible`);
* the network-level **ergodicity theorem** `CRNT.AntitheticErgodic.closedLoop_ergodic`: a unique
  stationary law charging every count, convergence of the law of the chain to it in total
  variation from every count, the moment bound `∑' π fLyap ≤ cK`, and the stationary mean output
  `μ/θ`.

## 3. What this module adds

1. `CRNT.Stochastic.FosterLyapunovCertificate`: a **general** Foster certificate, for an
   *arbitrary* — in particular, a nonlinear — Lyapunov function `V`: `V ≥ 0` with finite sublevel
   sets, `f ≥ 0` with finite sublevel sets, `K ≥ 0`, and the drift condition
   `N.observableGenerator κ V ≤ −f + K`.  The repository's
   `CRNT.Network.LinearFosterLyapunovCertificate` only covers a *linear* `V` (a positive
   weight); the piecewise quadratic function needs the general form.  With it,
   `CRNT.Stochastic.FosterLyapunovCertificate.ergodic` is the Foster–Lyapunov ergodic theorem,
   and `CRNT.Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift` is the
   geometric (Meyn–Tweedie `V`-uniform) ergodicity theorem.
2. `CRNT.Antithetic.closedLoop_fosterCertificate`: **the certificate for the antithetic network**
   — the piecewise quadratic `lyap` with the norm-like `fLyap` and the constant `cK`.
3. `CRNT.Antithetic.closedLoop_ergodic_of_fosterCertificate`: the ergodicity theorem *re-derived
   from the certificate* (rather than from the bespoke proof of `AntitheticErgodic`): the unique
   stationary law charging every count, the convergence in total variation, the moment bound
   `∑' π fLyap ≤ cK`, and the stationary mean output `μ/θ`.
4. `CRNT.Antithetic.closedLoop_exponentialDriftCertificate_wLyap`: the modified function `wLyap`
   carries an **exponential** drift certificate `Q wLyap ≤ −c wLyap + K` (`c > 0`).
5. `CRNT.Antithetic.wLyap_sublevel_infinite` and `wLyap_no_fosterCertificate`: the sublevel sets
   of `wLyap` are infinite (on the region `z₁ < z₂` the function does not depend on `z₂` at
   all), so `wLyap` — although it is the *better* (continuous) Lyapunov function — cannot carry a
   Foster certificate of the form of item 1; the certificate is carried by the piecewise quadratic
   `lyap`.
6. `CRNT.Antithetic.lyap_no_exponential_drift`: **the obstruction to geometric ergodicity** for
   the piecewise quadratic function: on the line `z₁ = 0` the function `lyap` grows *quadratically*
   in `z₂` while its drift grows only *linearly*, so `Q lyap + c lyap` is unbounded above for every
   `c > 0`; the drift condition `Q lyap ≤ −c lyap + K` fails for every `c > 0` and `K`.  Together
   with item 5 this shows that the closed loop cannot be made geometrically ergodic by the
   repository's two Lyapunov functions, and that the general theorem of item 1
   (`geometric_ergodic_of_exponential_drift`) is the right general statement.
7. `CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift`: that general theorem
   *instantiated at the antithetic closed loop* — the Foster certificate of item 2 provides the
   stochasticity of the minimal transition function, and an exponential drift of any Lyapunov
   function `W` with finite sublevel sets then gives geometric ergodicity.  (No such `W` is known
   for this network; see section 5.)

## 4. Why the *general-plant quadratic* route cannot be used instead

The general-plant route of `CRNT.Design.GeneralPlantDrift` certifies the closed loop with a
*quadratic* Lyapunov function built from the Lyapunov equation `2 xᵀ P A x ⪯ −‖x‖²` of the
**unimolecular** part of the network.  For the antithetic closed loop this is *provably
impossible*: the `Z₂` direction lies in the kernel of the first-order drift matrix `A` (the
annihilation is the only consumer of `Z₂`, and it is bimolecular, so it does not enter `A`), while
the reference reaction `∅ → Z₁` feeds `Z₁` at the constant rate `μ > 0` and the affine drift of the
counts has no equilibrium; the Lyapunov equation then reads `0 ≤ −1` at the `Z₂` direction
(`CRNT.Design.AntitheticInstance.antitheticInstance_no_quadratic_certificate`,
`firstOrderDriftMatrix_z2_kernel`).  The two ingredients of the general-plant route which *do*
hold for this network — the annihilation sign condition and the identification of `lyap` with the
general-plant quadratic form — are in `CRNT.Design.AntitheticInstance`; the Foster certificate has
to be built for the *piecewise* function directly, as in this module.

## 5. What remains open

* The geometric ergodicity of the antithetic closed loop is **not** established: it would require
  a Lyapunov function with finite sublevel sets and an exponential drift, and the two functions of
  the repository are excluded by `lyap_no_exponential_drift` and `wLyap_sublevel_infinite`.  A
  function of the third kind (a Lyapunov function growing like `z₂` in the region `z₁ < z₂`, whose
  drift is dominated by the annihilation term `−η c_d z₁ z₂²`) is the natural candidate; it is not
  built here.
* The Foster certificate is stated for the *network* level generator
  `CRNT.Network.observableGenerator`; the identification with the jump-system drift used by the
  stochastic machinery is the existing `CRNT.Network.observableGenerator_eq_jumpSystem_drift`
  (`CRNT.Stochastic.EndotacticTierPositiveRecurrence`; for `Network (Fin m)` the same identity is
  `CRNT.Design.GeneralPlantDrift.jumpSystem_drift_observableGenerator`).

Depends on: `CRNT.Design.AntitheticErgodic`, `CRNT.Design.AntitheticMeanOutput`,
`CRNT.Stochastic.EndotacticTierPositiveRecurrence`.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT

namespace Stochastic

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A Foster–Lyapunov certificate for an arbitrary Lyapunov function.**  A nonnegative
Lyapunov function `V` with finite sublevel sets, whose drift is bounded by `−f + K` for a
nonnegative `f` with finite sublevel sets.  This is the repository's
`CRNT.Network.LinearFosterLyapunovCertificate` generalised to a *nonlinear* `V` — the form a
piecewise quadratic Lyapunov function needs. -/
structure FosterLyapunovCertificate (N : Network S) (κ : N.RateConstants)
    (V : (S → ℕ) → ℝ) (f : (S → ℕ) → ℝ) (K : ℝ) : Prop where
  /-- `V` is nonnegative. -/
  hV : ∀ n, 0 ≤ V n
  /-- `V` has finite sublevel sets. -/
  hfin : ∀ R : ℝ, {n | V n ≤ R}.Finite
  /-- `f` is nonnegative. -/
  hf : ∀ n, 0 ≤ f n
  /-- `f` has finite sublevel sets. -/
  hffin : ∀ R : ℝ, {n | f n ≤ R}.Finite
  /-- `K` is nonnegative. -/
  hK : 0 ≤ K
  /-- **The Foster drift condition** `QV ≤ −f + K`. -/
  hdrift : ∀ n, N.observableGenerator κ V n ≤ -f n + K

/-- **An exponential drift certificate.**  A nonnegative `V` with an exponential drift
`QV ≤ −c V + K` for some `c > 0` and `K ≥ 0`: the hypothesis of geometric ergodicity. -/
structure ExponentialDriftCertificate (N : Network S) (κ : N.RateConstants)
    (V : (S → ℕ) → ℝ) (c K : ℝ) : Prop where
  /-- `V` is nonnegative. -/
  hV : ∀ n, 0 ≤ V n
  /-- The rate `c` is positive. -/
  hc : 0 < c
  /-- The constant `K` is nonnegative. -/
  hK : 0 ≤ K
  /-- **The exponential drift condition** `QV ≤ −c V + K`. -/
  hdrift : ∀ n, N.observableGenerator κ V n ≤ -c * V n + K

namespace FosterLyapunovCertificate

variable {N : Network S} {κ : N.RateConstants} {V f : (S → ℕ) → ℝ} {K : ℝ}

/-- The drift bound in the jump-system form. -/
theorem drift_le (C : FosterLyapunovCertificate N κ V f K) (n : S → ℕ) :
    (N.jumpSystem κ).drift V n ≤ -f n + K := by
  rw [← Network.observableGenerator_eq_jumpSystem_drift]
  exact C.hdrift n

/-- **Non-explosion.**  The minimal transition function of the network is stochastic: the
certificate gives `QV ≤ K`, and `V` has finite sublevel sets. -/
theorem hasSum_Pmin_one (C : FosterLyapunovCertificate N κ V f K) {t : ℝ} (ht : 0 ≤ t)
    (n : S → ℕ) : HasSum (fun b => (N.jumpSystem κ).Pmin t n b) 1 := by
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine V C.hV C.hfin (c := 0) (d := K)
    (by exact le_rfl) C.hK (fun a => ?_) ht n
  have h := C.drift_le a
  have hf := C.hf a
  linarith

/-- **Ergodicity from a Foster certificate.**  On an irreducible countable state space, the
certificate yields a unique invariant probability charging every state, and convergence of the
law of the chain to it in total variation from every state. -/
theorem ergodic (C : FosterLyapunovCertificate N κ V f K)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * (N.jumpSystem κ).Pmin s c b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a, Tendsto (fun t => ∑' b, |(N.jumpSystem κ).Pmin t a b - π b|) atTop (𝓝 0)) ∧
      ∀ μ : (S → ℕ) → ℝ, (∀ b, 0 ≤ μ b) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' c, μ c * (N.jumpSystem κ).Pmin s c b = μ b) → μ = π := by
  obtain ⟨π, hπ0, hπ1, hinv, hπE, hpos, hconv, huniq⟩ :=
    (N.jumpSystem κ).foster_lyapunov_ergodic V f C.hV C.hf C.hffin C.hK
      (C.drift_le) (fun t ht c => C.hasSum_Pmin_one ht c) (E := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => hirr a b) (Set.mem_univ (fun _ => 0))
  exact ⟨π, hπ0, hπ1, hinv, fun b => hpos b (Set.mem_univ b),
    fun a => hconv a (Set.mem_univ a), fun μ hμ0 hμ1 hμinv => huniq μ hμ0
    (fun b hb => absurd (Set.mem_univ b) hb) hμ1 hμinv⟩

/-- **Geometric ergodicity from a Foster certificate and an exponential drift.**  A Foster
certificate makes the minimal transition function stochastic; together with a *second*
Lyapunov function `W` with finite sublevel sets and an exponential drift `QW ≤ −c W + K`
(`c > 0`), the chain is geometrically ergodic (Meyn–Tweedie `V`-uniform ergodicity). -/
theorem geometric_ergodic_of_exponential_drift
    (C : FosterLyapunovCertificate N κ V f K) {W : (S → ℕ) → ℝ} {c K' : ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWfin : ∀ R : ℝ, {n | W n ≤ R}.Finite) (hc : 0 < c) (hK' : 0 ≤ K')
    (hdrift : ∀ n, N.observableGenerator κ W n ≤ -c * W n + K')
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * W b) ≤ C₀ * (1 + W a) * ρ ^ ⌊t⌋₊ := by
  have hdrift' : ∀ n, (N.jumpSystem κ).drift W n ≤ -c * W n + K' := by
    intro n
    rw [← Network.observableGenerator_eq_jumpSystem_drift]
    exact hdrift n
  obtain ⟨π, hπ0, hπ1, hinv, hβ, hρ0, hρ1, hC₀⟩ :=
    (N.jumpSystem κ).geometric_ergodic W hW0 hWfin hc hK' hdrift'
      (fun t ht c => C.hasSum_Pmin_one ht c) hirr
  exact ⟨π, hπ0, hπ1, hinv, hβ, hρ0, hρ1, hC₀⟩

end FosterLyapunovCertificate

end Stochastic

namespace Antithetic

open Network

variable (κ : closedLoop.RateConstants)

/-- **The antithetic closed loop admits a Foster–Lyapunov certificate with the piecewise
quadratic Lyapunov function.**  The drift of `lyap` is bounded by `−fLyap + cK`
(`drift_lyap_le`), `fLyap` is nonnegative with finite sublevel sets (`fLyap_nonneg`,
`fLyap_finite`), and `lyap` is nonnegative with finite sublevel sets (`lyap_nonneg`,
`lyap_finite`). -/
theorem closedLoop_fosterCertificate (κ : closedLoop.RateConstants) :
    Stochastic.FosterLyapunovCertificate closedLoop κ (lyap κ) (fLyap κ) (cK κ) := by
  refine ⟨lyap_nonneg κ, lyap_finite κ, fLyap_nonneg κ, fLyap_finite κ, cK_nonneg κ, ?_⟩
  intro n
  rw [Network.observableGenerator_eq_jumpSystem_drift]
  exact drift_lyap_le κ n

/-- **Ergodicity of the antithetic closed loop, from the Foster certificate.**  This re-derives
`CRNT.AntitheticErgodic.closedLoop_ergodic` from the *certificate* `closedLoop_fosterCertificate`
rather than from the bespoke proof of that file: the certificate delivers the stationary law, the
convergence in total variation, the uniqueness, the moment bound `∑' π fLyap ≤ cK`, and — through
the stationarity identity of the charge observable — the stationary mean output `μ / θ`. -/
theorem closedLoop_ergodic_of_fosterCertificate (κ : closedLoop.RateConstants) :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ n, 0 < π n) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' n, π n * closedLoop.transition κ t n m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |closedLoop.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      (∀ ν : (Fin 3 → ℕ) → ℝ, (∀ n, 0 ≤ ν n) → HasSum ν 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' n, ν n * closedLoop.transition κ t n m = ν m) → ν = π) ∧
      ∑' n, π n * fLyap κ n ≤ cK κ ∧
      ∑' n, π n * (n 2 : ℝ) = κ.k rRef / κ.k rSense := by
  obtain ⟨π, hπ0, hπ1, hinv, hpos, hconv, huniq⟩ :=
    Stochastic.FosterLyapunovCertificate.ergodic (closedLoop_fosterCertificate κ) (irreducible κ)
  obtain ⟨hfs, hfle⟩ := (closedLoop.jumpSystem κ).tsum_invariant_mul_le (lyap κ) (fLyap κ)
    (lyap_nonneg κ) (fLyap_nonneg κ) (cK_nonneg κ) (drift_lyap_le κ) hπ0 hπ1 hinv
  -- the stationary law satisfies the master equation
  have hε := cε_pos κ
  have hraw : Summable fun n => π n * (1 + fRaw n) := by
    have h : Summable fun n => π n * fRaw n :=
      (hfs.div_const (cε κ)).congr fun n => by rw [fLyap_eq]; field_simp
    exact (hπ1.summable.add h).congr fun n => by ring
  set Ctot := μ κ + η κ + kk κ + γ κ + θ κ with hCtot
  have hexit0 : ∀ n, 0 ≤ closedLoop.exitRate κ n := fun n =>
    Finset.sum_nonneg fun r _ => closedLoop.stochasticMassActionRate_nonneg κ n r
  have hexit : Summable fun n => π n * closedLoop.exitRate κ n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hexit0 n))
      (fun n => by
        calc π n * closedLoop.exitRate κ n ≤ π n * (Ctot * (1 + fRaw n)) :=
              mul_le_mul_of_nonneg_left (exitRate_le κ n) (hπ0 n)
          _ = Ctot * (π n * (1 + fRaw n)) := by ring) (hraw.mul_left Ctot)
  have hst := closedLoop.isCMEStationary_of_invariant κ hπ0 hπ1.summable hinv hexit
  have hs0 : ∀ r, Summable fun n => π n * closedLoop.stochasticMassActionRate κ n r := fun r =>
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hπ0 n) (closedLoop.stochasticMassActionRate_nonneg κ n r))
      (fun n => mul_le_mul_of_nonneg_left (rate_le_exitRate κ n r) (hπ0 n)) hexit
  have hs1 : ∀ r, Summable fun n =>
      π n * closedLoop.stochasticMassActionRate κ n r * linearObservable charge n := fun r =>
    Summable.of_norm_bounded (hraw.mul_left Ctot) fun n => by
      rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hπ0 n)]
      calc π n * |closedLoop.stochasticMassActionRate κ n r * linearObservable charge n|
          ≤ π n * (Ctot * (1 + fRaw n)) :=
            mul_le_mul_of_nonneg_left (rate_mul_charge_le κ n r) (hπ0 n)
        _ = Ctot * (π n * (1 + fRaw n)) := by ring
  have hstat := closedLoop.tsum_mul_observableGenerator_linear_eq_zero κ hst charge hs0 hs1
  have hout : Summable fun n => π n * (n 2 : ℝ) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (Nat.cast_nonneg _))
      (fun n => by
        refine mul_le_mul_of_nonneg_left ?_ (hπ0 n)
        have h1 := cast_le_sq (n 2)
        have h2 : (n 2 : ℝ) ^ 2 ≤ fRaw n := by
          unfold fRaw
          have := abs_nonneg ((n 0 : ℝ) - n 1)
          have := sq_nonneg (max ((n 0 : ℝ) - n 1) 0)
          have : 0 ≤ (n 2 : ℝ) * |(n 0 : ℝ) - n 1| := by positivity
          have := annih_nonneg (n 0) (n 1)
          linarith
        linarith) hraw
  have hset := closedLoop_stochastic_setpoint κ π hπ1.summable hπ1.tsum_eq hout hstat
  refine ⟨π, hpos, hπ1, fun t ht m => hinv t ht m, fun n => hconv n, ?_, hfle, hset⟩
  intro ν hν0 hν1 hνinv
  exact huniq ν hν0 hν1 hνinv

/-- **The sublevel sets of the modified Lyapunov function `wLyap` are infinite.**  On the region
`z₁ < z₂` the function `wLyap` does not depend on `z₂` at all, so the counts `(0, m, 0)`,
`m ≥ 1`, all have `wLyap = 0`. -/
theorem wLyap_sublevel_infinite (κ : closedLoop.RateConstants) {R : ℝ} (hR : 0 ≤ R) :
    ({n | wLyap κ n ≤ R}).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => mk3 0 (m + 1) 0) ?_ ?_
  · intro a b hab
    have h1 := congrFun hab (1 : Fin 3)
    simp [mk3] at h1
    omega
  · intro m
    show wLyap κ (mk3 0 (m + 1) 0) ≤ R
    simp [wLyap, mk3]
    linarith

/-- **The modified Lyapunov function `wLyap` admits no Foster certificate.**  Its sublevel sets
are infinite (`wLyap_sublevel_infinite`), so the finite-sublevel hypothesis of
`FosterLyapunovCertificate` fails for it; the certificate of the closed loop is carried by the
piecewise quadratic `lyap` (`closedLoop_fosterCertificate`). -/
theorem wLyap_no_fosterCertificate (κ : closedLoop.RateConstants) :
    ¬ ∃ (f : (Fin 3 → ℕ) → ℝ) (K : ℝ),
      Stochastic.FosterLyapunovCertificate closedLoop κ (wLyap κ) f K := by
  rintro ⟨f, K, hC⟩
  have h := hC.hfin 0
  exact (wLyap_sublevel_infinite κ (show (0 : ℝ) ≤ 0 by norm_num)) h

/-- **The modified Lyapunov function `wLyap` admits an exponential drift certificate.**  The
function `wLyap` is the *continuous* modification of `lyap` (it agrees with `lyap` on the region
`z₂ ≤ z₁` and with `c_b x² + c_d z₁²` above it), and it has an exponential drift
`Q wLyap ≤ −c wLyap + K` (`drift_wLyap_le`).  Together with the Foster certificate
`closedLoop_fosterCertificate` this is the hypothesis of
`Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift`; what is missing is
the finite-sublevel hypothesis for `wLyap` (`wLyap_sublevel_infinite`). -/
theorem closedLoop_exponentialDriftCertificate_wLyap (κ : closedLoop.RateConstants) :
    ∃ c K : ℝ, Stochastic.ExponentialDriftCertificate closedLoop κ (wLyap κ) c K := by
  obtain ⟨c, K, hc, hK, hdrift⟩ := drift_wLyap_le κ
  refine ⟨c, K, ⟨wLyap_nonneg κ, hc, hK, ?_⟩⟩
  intro n
  rw [Network.observableGenerator_eq_jumpSystem_drift]
  exact hdrift n

set_option maxHeartbeats 1000000 in
/-- **The piecewise quadratic `lyap` has no exponential drift.**  On the line `z₁ = 0` the function
`lyap` grows *quadratically* in `z₂` while its drift grows only *linearly*, so `Q lyap + c lyap` is
unbounded above for every `c > 0`: the drift condition `Q lyap ≤ −c lyap + K` fails for every
`c > 0` and `K`.  This is the precise obstruction to geometric ergodicity for the piecewise
quadratic Lyapunov function, and it is why the geometric ergodicity of the antithetic closed loop
is *not* delivered by the certificate of this module. -/
theorem lyap_no_exponential_drift (κ : closedLoop.RateConstants) (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∃ n : Fin 3 → ℕ, closedLoop.observableGenerator κ (lyap κ) n > -c * lyap κ n + K := by
  obtain ⟨hμ, hη, hk, hγ, hθ⟩ := params_pos κ
  have hB : 0 < cB κ := by unfold cB; positivity
  have hcc : 0 < cc κ := by unfold cc; positivity
  have hcb : 0 < cb κ := by unfold cb; positivity
  have hcd : 0 < cd κ := by unfold cd; positivity
  have hcB : 0 < c * cB κ := mul_pos hc hB
  -- the value of `lyap` at the count `(0, m, 1)`
  have hval (m : ℕ) (hm : 2 ≤ m) :
      lyap κ (mk3 0 m 1) = cB κ * (m : ℝ) ^ 2 + cb κ + cc κ * (m : ℝ) := by
    have hn0 : (mk3 0 m 1 : Fin 3 → ℕ) 0 = 0 := by simp [mk3]
    have hn1 : (mk3 0 m 1 : Fin 3 → ℕ) 1 = m := by simp [mk3]
    have hn2 : (mk3 0 m 1 : Fin 3 → ℕ) 2 = 1 := by simp [mk3]
    have hphi : phi κ 0 m = cB κ * ((0 : ℝ) - (m : ℝ)) ^ 2 := by
      unfold phi
      have hnot : ¬ (m ≤ 0) := by omega
      rw [ite_eq_right hnot]
      simp
    rw [lyap, hn0, hn1, hn2, hphi]
    push_cast
    ring
  -- the drift of `lyap` at the count `(0, m, 1)`
  have hdrift (m : ℕ) (hm : 2 ≤ m) :
      closedLoop.observableGenerator κ (lyap κ) (mk3 0 m 1) =
        μ κ * (cB κ * (1 - 2 * (m : ℝ)) - cc κ + cd κ * (m : ℝ)) +
          γ κ * (cb κ * (1 - 2 * 1) + cc κ * (0 - (m : ℝ))) +
          θ κ * (cB κ * (1 + 2 * (m : ℝ)) + cc κ) := by
    have hn0 : (mk3 0 m 1 : Fin 3 → ℕ) 0 = 0 := by simp [mk3]
    have hn1 : (mk3 0 m 1 : Fin 3 → ℕ) 1 = m := by simp [mk3]
    have hn2 : (mk3 0 m 1 : Fin 3 → ℕ) 2 = 1 := by simp [mk3]
    have hphi1 : phi κ 1 m = cB κ * ((1 : ℝ) - (m : ℝ)) ^ 2 := by
      unfold phi
      have hnot : ¬ (m ≤ 1) := by omega
      rw [ite_eq_right hnot]
      simp
    have hphi0 : phi κ 0 m = cB κ * ((0 : ℝ) - (m : ℝ)) ^ 2 := by
      unfold phi
      have hnot : ¬ (m ≤ 0) := by omega
      rw [ite_eq_right hnot]
      simp
    have hphi2 : phi κ 0 (m + 1) = cB κ * ((0 : ℝ) - ((m + 1 : ℕ) : ℝ)) ^ 2 := by
      unfold phi
      have hnot : ¬ (m + 1 ≤ 0) := by omega
      rw [ite_eq_right hnot]
      simp
    rw [Network.observableGenerator_eq_jumpSystem_drift, drift_lyap, hn0, hn1, hn2,
      hphi1, hphi0, hphi2]
    push_cast
    ring
  -- the coefficients of the resulting quadratic polynomial in `m`
  set A : ℝ := -2 * μ κ * cB κ + μ κ * cd κ - γ κ * cc κ + 2 * θ κ * cB κ + c * cc κ with hA
  set B : ℝ := μ κ * cB κ - μ κ * cc κ - γ κ * cb κ + θ κ * cB κ + θ κ * cc κ + c * cb κ with hB
  have hid (m : ℕ) (hm : 2 ≤ m) :
      closedLoop.observableGenerator κ (lyap κ) (mk3 0 m 1) + c * lyap κ (mk3 0 m 1)
        = c * cB κ * (m : ℝ) ^ 2 + A * (m : ℝ) + B := by
    rw [hval m hm, hdrift m hm]
    simp only [hA, hB]
    ring
  -- a large count
  obtain ⟨m1, hm1⟩ := exists_nat_gt (2 * |A| / (c * cB κ))
  obtain ⟨m2, hm2⟩ := exists_nat_gt (2 * (|K| + |B|) / (c * cB κ))
  set m := max m1 (max m2 2) with hmdef
  have hle1 : m1 ≤ m := Nat.le_max_left _ _
  have hle2 : max m2 2 ≤ m := Nat.le_max_right _ _
  have hle3 : m2 ≤ max m2 2 := Nat.le_max_left _ _
  have h2m : 2 ≤ m := le_trans (Nat.le_max_right m2 2) hle2
  have hmle1 : (m1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle1
  have hmle2 : (m2 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_trans hle3 hle2)
  have hmA : 2 * |A| < c * cB κ * (m : ℝ) := by
    have h1 : 2 * |A| / (c * cB κ) < (m1 : ℝ) := by exact_mod_cast hm1
    have h4 : 2 * |A| < c * cB κ * (m1 : ℝ) := by
      rw [div_lt_iff₀ (by positivity)] at h1
      nlinarith
    nlinarith
  have hmB : 2 * (|K| + |B|) < c * cB κ * (m : ℝ) := by
    have h1 : 2 * (|K| + |B|) / (c * cB κ) < (m2 : ℝ) := by exact_mod_cast hm2
    have h4 : 2 * (|K| + |B|) < c * cB κ * (m2 : ℝ) := by
      rw [div_lt_iff₀ (by positivity)] at h1
      nlinarith
    nlinarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1' : 1 ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hKm' : (|K| + |B|) * (m : ℝ) < c * cB κ * (m : ℝ) ^ 2 / 2 := by
    have hKm : |K| + |B| < c * cB κ * (m : ℝ) / 2 := by nlinarith [hmB]
    have he : (c * cB κ * (m : ℝ) / 2) * (m : ℝ) = c * cB κ * (m : ℝ) ^ 2 / 2 := by ring
    nlinarith
  refine ⟨mk3 0 m 1, ?_⟩
  have h1 := hid m h2m
  have h2 : c * cB κ * (m : ℝ) ^ 2 + A * (m : ℝ) + B
      ≥ c * cB κ * (m : ℝ) ^ 2 - |A| * (m : ℝ) - |B| := by
    have hAm : -|A| * (m : ℝ) ≤ A * (m : ℝ) := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs A) hm0
      linarith
    have hB' : -|B| ≤ B := neg_abs_le B
    linarith
  have h3 : c * cB κ * (m : ℝ) ^ 2 - |A| * (m : ℝ) - |B|
      > c * cB κ * (m : ℝ) ^ 2 / 2 - |B| := by
    have hAm : |A| * (m : ℝ) < c * cB κ * (m : ℝ) ^ 2 / 2 := by
      nlinarith [hmA]
    nlinarith
  have h4 : c * cB κ * (m : ℝ) ^ 2 / 2 - |B| > K := by
    have h2 : K + |B| ≤ |K| + |B| := by
      have := le_abs_self K
      linarith
    have h3' : |K| + |B| ≤ (|K| + |B|) * (m : ℝ) := by
      have hnonneg : 0 ≤ |K| + |B| := by positivity
      nlinarith
    nlinarith [hKm', h3']
  have h6 : c * cB κ * (m : ℝ) ^ 2 + A * (m : ℝ) + B > K := by linarith [h2, h3, h4]
  have h5 : closedLoop.observableGenerator κ (lyap κ) (mk3 0 m 1)
      + c * lyap κ (mk3 0 m 1) > K := by linarith [h1, h6]
  linarith

/-- **Geometric ergodicity of the antithetic closed loop, conditional on an exponential
drift.**  If the closed loop admits a Lyapunov function `W` with finite sublevel sets and an
exponential drift `QW ≤ −c W + K` (`c > 0`), then the Foster certificate of this module makes the
minimal transition function stochastic and the chain is geometrically ergodic: there are a
stationary law `π`, `β > 0`, `ρ < 1` and `C₀` with
`∑' b, |P(t)(a, b) − π b| (1 + β W b) ≤ C₀ (1 + W a) ρ ^ ⌊t⌋₊`.  The two Lyapunov functions of the
repository do not supply such a `W` (`lyap_no_exponential_drift`, `wLyap_sublevel_infinite`), so
this is the *general* statement rather than an instance. -/
theorem closedLoop_geometric_ergodic_of_exponential_drift
    (κ : closedLoop.RateConstants) {W : (Fin 3 → ℕ) → ℝ} {c K : ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWfin : ∀ R : ℝ, {n | W n ≤ R}.Finite) (hc : 0 < c) (hK : 0 ≤ K)
    (hdrift : ∀ n, closedLoop.observableGenerator κ W n ≤ -c * W n + K) :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (closedLoop.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(closedLoop.jumpSystem κ).Pmin t a b - π b| * (1 + β * W b)
          ≤ C₀ * (1 + W a) * ρ ^ ⌊t⌋₊ :=
  Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift
    (closedLoop_fosterCertificate κ) hW0 hWfin hc hK hdrift (irreducible κ)

/-- **Instance with unit rates.**  With all rate constants equal to `1` the antithetic closed loop
has a Foster certificate with the piecewise quadratic Lyapunov function. -/
theorem unitRates_fosterCertificate :
    Stochastic.FosterLyapunovCertificate closedLoop unitRates (lyap unitRates) (fLyap unitRates)
      (cK unitRates) :=
  closedLoop_fosterCertificate unitRates

end Antithetic
end CRNT

#print axioms CRNT.Stochastic.FosterLyapunovCertificate.drift_le
#print axioms CRNT.Stochastic.FosterLyapunovCertificate.hasSum_Pmin_one
#print axioms CRNT.Stochastic.FosterLyapunovCertificate.ergodic
#print axioms CRNT.Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift
#print axioms CRNT.Antithetic.closedLoop_fosterCertificate
#print axioms CRNT.Antithetic.closedLoop_ergodic_of_fosterCertificate
#print axioms CRNT.Antithetic.wLyap_sublevel_infinite
#print axioms CRNT.Antithetic.wLyap_no_fosterCertificate
#print axioms CRNT.Antithetic.closedLoop_exponentialDriftCertificate_wLyap
#print axioms CRNT.Antithetic.lyap_no_exponential_drift
#print axioms CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift
#print axioms CRNT.Antithetic.unitRates_fosterCertificate
