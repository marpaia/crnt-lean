import CRNT.Design.MolecularControllerDrift
import CRNT.Design.Antithetic
import CRNT.Design.AntitheticErgodic
import CRNT.Design.AntitheticMeanOutput
import Mathlib.Tactic

/-!
# The explicit antithetic certificate for the repository's own network

This module discharges, for the *specific* network of the repository, the certificate which was
the remaining item of leaf **C3** ("antithetic integral feedback") of the field map
(`docs/field-map.md`): the **annihilation sign condition** on the shape matrix of the
general-plant framework, and the **identification** of the repository's Lyapunov function with
the general-plant quadratic form.  With these two, the cubic term of the drift of the closed loop
is controlled by the sign structure of the shape matrix, exactly as in the general theorem of
`CRNT.Design.MolecularControllerDrift`.

## 1. The antithetic integral feedback controller

The antithetic integral controller of Briat, Gupta and Khammash (*Antithetic integral feedback
ensures robust perfect adaptation in noisy biomolecular networks*, Cell Systems 2 (2016); and
*Robustness analysis of a class of antithetic integral controllers*, Automatica 2020) pairs a
**reference** reaction with a **sensing** reaction: the two act on the plant with opposite signs,
and the *charge* `q` (the integral of the control error) is the difference of the two.  In the
molecular realizations of the controller the anti-correlation is realized by an **annihilation**
`Z₁ + Z₂ → ∅` between the actuated species `Z₁` and the sensing species `Z₂`, and the reference
reaction `∅ → Z₁` feeds `Z₁` without bound.  The two features are exactly the two halves of the
general-plant argument of `CRNT.Design.MolecularControllerDrift`: the annihilation is the source
of the *cubic* term of the drift, and the sign structure of the shape matrix (the `z₁ z₂`
cross-term of the Lyapunov function) is what makes that term non-positive.

## 2. The general-plant framework of the repository

`CRNT.Design.GeneralPlant` and `CRNT.Design.MolecularControllerDrift` provide the following
machinery, for an arbitrary plant and an arbitrary number of species.

* The **shape matrix** `P` of a quadratic Lyapunov function `V n = (n − n*)ᵀ P (n − n*)`
  (`GeneralPlant.quadObservable`, `GeneralPlant.countDeviation`, `GeneralPlant.quadForm`).
* The **exact drift identity**
  `Q V (n) = 2 ⟨n − n*, P (∑_r λ_r(n) Δ_r)⟩ + ∑_r λ_r(n) ⟨Δ_r, P Δ_r⟩`
  (`GeneralPlant.observableGenerator_quadObservable`), whose second term is the *cubic remainder*
  of a bimolecular reaction (`GeneralPlant.cubic_remainder_le`), and the fact that the cubic term
  **cannot** be absorbed into a quadratic drift bound (`GeneralPlant.cubic_not_absorbable`).
* The **annihilation sign condition**
  `P s s + P t s = P s t + P t t = c₀ > 0`, `P k s + P k t = 0` (`k ∉ {s, t}`)
  (`GeneralPlant.AnnihilationSignCondition`), under which the annihilation's contribution to the
  drift is non-positive (`GeneralPlant.annihilation_drift_le_zero`), the quadratic Foster
  condition is restored (`GeneralPlant.fosterDrift_of_sign_controlled`) and the closed loop is
  ergodic (`GeneralPlant.ergodic_of_sign_controlled`).
* The **general-plant shape matrix** of the antithetic controller
  `P (a c e p) = [[a, c − a, e], [c − a, a, −e], [e, −e, p]]`
  (`GeneralPlant.AntitheticInstance.generalMatrix`), whose quadratic form is
  `a (z₁ − z₂)² + 2 c z₁ z₂ + 2 e x (z₁ − z₂) + p x²`: the `a`-part is the charge part, the
  `c`-part the `z₁ z₂` cross-term, the `e`-part the coupling of the charge with the output, and
  the `p`-part the output part.

## 3. The network of the repository

`CRNT.Antithetic.closedLoop` is the antithetic controller closed around a production–degradation
plant.  On the species `0 = Z₁`, `1 = Z₂`, `2 = X` it has the five reactions

```text
0 : ∅ → Z₁        (reference,   rate μ)
1 : Z₁ + Z₂ → ∅   (annihilation, rate η)
2 : Z₁ → Z₁ + X   (actuation,   rate k)
3 : X → ∅         (degradation,  rate γ)
4 : X → X + Z₂    (sensing,     rate θ)
```

The antithetic charge `e_{Z₁} − e_{Z₂}` is a maxRPA charge
(`CRNT.Antithetic.charge_isMaxRPACharge`, `CRNT.Antithetic.certificate`), which yields the
deterministic and the stochastic setpoints (`CRNT.Antithetic.closedLoop_deterministic_setpoint`,
`CRNT.Antithetic.closedLoop_stochastic_setpoint`).

The Lyapunov function of the closed loop is the **piecewise quadratic**
`CRNT.Antithetic.lyap κ n = φ κ (n 0) (n 1) + c_b x² − c_c x q + c_d z₁ z₂`, with `q = z₁ − z₂`
and `φ κ z₁ z₂ = c_A κ q²` on the region `z₂ ≤ z₁` and `c_B κ q²` off it
(`CRNT.AntitheticErgodic.phi`, `CRNT.AntitheticErgodic.lyap`); the coefficients are
`c_A = 32 k θ + 9 γ²`, `c_B = 4 γ²`, `c_b = 32 θ²`, `c_c = 16 γ θ`, `c_d = 2 γ²`.

## 4. What this module proves

1. `antitheticInstance_annihilation_sign_condition`: the *general-plant* shape matrix with
   `a = c_A`, `c = c_d / 2`, `e = −c_c / 2`, `p = c_b` satisfies the annihilation sign condition
   with `c₀ = c_d / 2 > 0`: the two controller rows have row sum `c_d / 2` and the output row has
   row sum zero on the controller block.
2. `lyap_eq_generalPlant_quadratic`: on the region `z₂ ≤ z₁` the repository's `lyap` **is** the
   general-plant quadratic form of that matrix.
3. `antitheticInstance_annihilation_drift_le_zero`: the general-plant cubic control
   (`GeneralPlant.annihilation_drift_le_zero`) applies to the repository's network: the
   annihilation's contribution to the drift of the general-plant quadratic is non-positive.
4. `antitheticInstance_lyap_annihilation_le_zero`: the same control for the repository's `lyap`
   itself: the annihilation's contribution to its drift is
   `η z₁ z₂ c_d (1 − z₁ − z₂) ≤ 0`.
5. `antitheticInstance_no_quadratic_certificate`: **the unimolecular part of the closed loop is
   not Hurwitz**, so the quadratic certificate of `CRNT.Design.GeneralPlantDrift` cannot be built
   and the general-plant transfer theorem `GeneralPlant.ergodic_of_sign_controlled` cannot be
   *instantiated* for this network: the `Z₂` direction is in the kernel of the first-order drift
   matrix `A` of the closed loop with the annihilation replaced by the trivial reaction (the
   annihilation is the only consumer of `Z₂`, and it is bimolecular, so it does not enter the
   first-order drift matrix), while the reference reaction `∅ → Z₁` feeds `Z₁` without bound, so
   the affine drift of the counts has no equilibrium.  The Lyapunov equation
   `2 xᵀ P A x ⪯ −‖x‖²` required by the certificate therefore has no solution: evaluated at the
   `Z₂` direction it reads `0 ≤ −1`.
6. `antitheticInstance_ergodic`: ergodicity of the antithetic closed loop, in the general-plant
   form (a stationary law charging every count, convergence in total variation from every count,
   uniqueness of the stationary law).

## 5. What is *not* claimed

* **The network-level ergodicity theorem is already proved**:
  `CRNT.AntitheticErgodic.closedLoop_ergodic` (a unique stationary law charging every count,
  convergence in total variation, the moment bound `∑' π f ≤ K`, and the stationary mean output
  `μ / θ`), together with `CRNT.Design.AntitheticMeanOutput.closedLoop_mean_output_tendsto`.
  This module does not re-prove them: it adds the **certificate** — the sign condition and the
  shape-matrix identification — which makes the *general-plant* route apply to this specific
  network, and it records precisely where that route stops.
* The repository uses the **piecewise** quadratic `lyap` rather than the Lyapunov equation of
  `CRNT.Design.GeneralPlantDrift` precisely because the unimolecular part of the closed loop is
  not Hurwitz (item 5 above).
* The two ingredients of the general-plant route which *do* hold for this network are the sign
  condition and the shape-matrix identification (items 1 and 2); the third ingredient, the
  quadratic certificate of the unimolecular part, provably does not (item 5).  The uniqueness
  clause of `GeneralPlant.ergodic_of_sign_controlled` is stated there with the right-hand side
  `π b`; `antitheticInstance_ergodic` uses the equivalent form `μ b` (a stationary law is the
  stationary law), which is the form of `CRNT.AntitheticErgodic.closedLoop_ergodic`.

Depends on: `CRNT.Design.MolecularControllerDrift`, `CRNT.Design.Antithetic`,
`CRNT.Design.AntitheticErgodic`, `CRNT.Design.AntitheticMeanOutput`.
-/

open Filter
open scoped BigOperators Topology Matrix

namespace CRNT
namespace AntitheticInstance

open Antithetic
open Network
open Design.GeneralPlant
open Design.GeneralPlant.AntitheticInstance

/-! ## 1. The general-plant shape matrix -/

/-- **The quadratic form of the general-plant shape matrix.**  For
`P (a c e p) = [[a, c − a, e], [c − a, a, −e], [e, −e, p]]` the quadratic form `xᵀ P x` is

```text
a (x₀ − x₁)² + 2 c x₀ x₁ + 2 e x₂ (x₀ − x₁) + p x₂²,
```

i.e. the `a`-part is the charge part, the `c`-part the `z₁ z₂` cross-term, the `e`-part the
coupling of the charge with the output, and the `p`-part the output part. -/
theorem generalMatrix_quadForm (a c e p : ℝ) (v : Fin 3 → ℝ) :
    quadForm (generalMatrix a c e p) v =
      a * (v 0 - v 1) ^ 2 + 2 * c * v 0 * v 1 + 2 * e * v 2 * (v 0 - v 1) + p * v 2 ^ 2 := by
  unfold quadForm
  rw [Fin.sum_univ_three]
  simp only [Matrix.mulVec_apply_eq_sum]
  simp [generalMatrix, Fin.sum_univ_three]
  ring

/-- **The general-plant shape matrix is symmetric.** -/
theorem generalMatrix_sym (a c e p : ℝ) :
    (generalMatrix a c e p)ᵀ = generalMatrix a c e p := by
  ext i j
  rw [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [generalMatrix]

/-! ## 2. The annihilation sign condition holds for the repository's network -/

/-- **The actual antithetic network satisfies the annihilation sign condition.**  The shape
matrix of the closed loop is `generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)`, whose rows
sum to `cd κ / 2` on the two controller rows and to `0` on the output row; the annihilation
reaction `Z₁ + Z₂ → 0` is therefore sign-controlled, and the cubic term of the drift of the
general-plant quadratic is non-positive
(`antitheticInstance_annihilation_drift_le_zero`). -/
theorem antitheticInstance_annihilation_sign_condition (κ : closedLoop.RateConstants) :
    AnnihilationSignCondition
      (generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)) 0 1 (cd κ / 2) := by
  have hγ : 0 < γ κ := (params_pos κ).2.2.2.1
  have hd : 0 < cd κ := by unfold cd; positivity
  exact generalMatrix_sign_condition (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ) (by positivity)

/-! ## 3. The identification of the repository's `lyap` with the general-plant quadratic -/

/-- **On the region `z₂ ≤ z₁` the repository's Lyapunov function of the antithetic closed loop
is the general-plant quadratic form with the shape matrix `generalMatrix`.**  The `φ`-part of
`CRNT.Antithetic.lyap` is piecewise (`cA` below the diagonal `z₂ ≤ z₁` and `cB` above it), so
the identification is exact on the region where the `cA` branch applies: with
`a = cA`, `2 c = cd`, `2 e = −cc` and `p = cb`, the general-plant quadratic form reads
`cA (z₁ − z₂)² + cd z₁ z₂ − cc x (z₁ − z₂) + cb x²`, which is `CRNT.Antithetic.lyap` on that
region. -/
theorem lyap_eq_generalPlant_quadratic (κ : closedLoop.RateConstants) (n : Fin 3 → ℕ)
    (hreg : (n 1 : ℝ) ≤ n 0) :
    lyap κ n =
      quadObservable (generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)) (fun _ => 0) n := by
  have hreg' : n 1 ≤ n 0 := by exact_mod_cast hreg
  have hphi : phi κ (n 0) (n 1) = cA κ * ((n 0 : ℝ) - n 1) ^ 2 := by
    unfold phi
    rw [ite_eq_left hreg']
  rw [lyap, hphi]
  rw [quadObservable_eq]
  have hdev : countDeviation (fun _ => 0) n = fun i => (n i : ℝ) := by
    funext i
    simp [countDeviation]
  rw [hdev]
  have hq := generalMatrix_quadForm (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)
    (fun i => (n i : ℝ))
  linarith [hq]

/-- The same identification, in the double-sum coordinates of the general plant. -/
theorem lyap_eq_generalPlant_quadratic_form (κ : closedLoop.RateConstants) (n : Fin 3 → ℕ)
    (hreg : (n 1 : ℝ) ≤ n 0) :
    lyap κ n = quadForm (generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ))
      (countDeviation (fun _ => 0) n) := by
  rw [lyap_eq_generalPlant_quadratic κ n hreg, quadObservable_eq]

/-! ## 4. The general-plant cubic control applies to the repository's network -/

/-- **The general-plant cubic control applies to the repository's antithetic network.**  Under
the annihilation sign condition of `antitheticInstance_annihilation_sign_condition`, the
bimolecular annihilation `Z₁ + Z₂ → ∅` contributes a non-positive amount to the drift of the
general-plant quadratic form: this is `GeneralPlant.annihilation_drift_le_zero`, the general
form of the control performed by the explicit `z₁ z₂` cross-term of `CRNT.Antithetic.lyap`. -/
theorem antitheticInstance_annihilation_drift_le_zero (κ : closedLoop.RateConstants)
    (n : Fin 3 → ℕ) :
    closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
      (quadObservable (generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)) (fun _ => 0)
          (closedLoop.fireCount n (1 : Fin 5)) -
        quadObservable (generalMatrix (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)) (fun _ => 0) n) ≤ 0 := by
  refine annihilation_drift_le_zero closedLoop κ
    (generalMatrix_sym (cA κ) (cd κ / 2) (-cc κ / 2) (cb κ)) (fun _ => 0) n
    (rAnn := (1 : Fin 5)) (s := 0) (t := 1) annihilation_is_annihilation (cd κ / 2)
    (antitheticInstance_annihilation_sign_condition κ) ⟨rfl, rfl⟩

/-- **The annihilation decreases the repository's Lyapunov function.**  The contribution of the
reaction `Z₁ + Z₂ → ∅` to the drift of `CRNT.Antithetic.lyap` is
`η z₁ z₂ c_d (1 − z₁ − z₂) ≤ 0`: the `φ`-part of `lyap` is invariant along the annihilation
(which preserves the charge `z₁ − z₂`), and its `z₁ z₂` cross-term decreases by `z₁ + z₂ − 1`. -/
theorem antitheticInstance_lyap_annihilation_le_zero (κ : closedLoop.RateConstants)
    (n : Fin 3 → ℕ) :
    closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
      (lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n) ≤ 0 := by
  have hrate : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) =
      η κ * (n 0 : ℝ) * (n 1 : ℝ) := (rate_eq κ n).2.1
  rw [hrate]
  rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
  · simp [h0]
  rcases Nat.eq_zero_or_pos (n 1) with h1 | h1
  · simp [h1]
  obtain ⟨a, b, c⟩ := next1 n
  have hphi : phi κ (n 0 - 1) (n 1 - 1) = phi κ (n 0) (n 1) := by
    unfold phi
    have hiff : n 1 - 1 ≤ n 0 - 1 ↔ n 1 ≤ n 0 := by omega
    rw [Nat.cast_sub h0, Nat.cast_sub h1]
    simp only [hiff]
    split_ifs <;> ring
  have hdiff : lyap κ (closedLoop.jumpNextCount n (1 : Fin 5)) - lyap κ n =
      cd κ * (1 - (n 0 : ℝ) - (n 1 : ℝ)) := by
    unfold lyap
    rw [a, b, c, hphi]
    rw [Nat.cast_sub h0, Nat.cast_sub h1]
    push_cast
    ring
  rw [hdiff]
  have hη : 0 < η κ := (params_pos κ).2.1
  have hγ : 0 < γ κ := (params_pos κ).2.2.2.1
  have hcd : 0 < cd κ := by unfold cd; positivity
  have h1' : (1 : ℝ) ≤ n 0 := by exact_mod_cast Nat.succ_le_of_lt h0
  have h2' : (1 : ℝ) ≤ n 1 := by exact_mod_cast Nat.succ_le_of_lt h1
  have hneg : (1 : ℝ) - (n 0 : ℝ) - (n 1 : ℝ) ≤ 0 := by linarith
  have hbr : cd κ * ((1 : ℝ) - (n 0 : ℝ) - (n 1 : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcd.le hneg
  have hpos : 0 ≤ η κ * (n 0 : ℝ) * (n 1 : ℝ) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hpos hbr

/-! ## 5. The unimolecular part of the closed loop is not Hurwitz -/

/-- **The drift of the `Z₁` coordinate of the antithetic closed loop.**  The reference reaction
`∅ → Z₁` feeds `Z₁` at the constant rate `μ`, the annihilation `Z₁ + Z₂ → ∅` consumes it at the
rate `η z₁ z₂`, and no other reaction changes `Z₁`. -/
theorem z1_drift (κ : closedLoop.RateConstants) (n : Fin 3 → ℕ) :
    countDrift closedLoop κ n 0 = μ κ - η κ * (n 0 : ℝ) * (n 1 : ℝ) := by
  unfold countDrift
  change (∑ r : Fin 5, closedLoop.stochasticMassActionRate κ n r *
      closedLoop.reactionVector r 0) = μ κ - η κ * (n 0 : ℝ) * (n 1 : ℝ)
  rw [Fin.sum_univ_five]
  obtain ⟨h0, h1, h2, h3, h4⟩ := rate_eq κ n
  rw [h0, h1, h2, h3, h4]
  simp [closedLoop, rxn, Network.reactionVector_apply]
  ring

/-- **The reference reaction feeds `Z₁` without bound.**  In the network with the annihilation
replaced by the trivial reaction, the `Z₁` coordinate drifts at the constant rate `μ > 0`: the
affine drift of the counts has no equilibrium, and the closed loop cannot be certified by the
quadratic Lyapunov equation of `CRNT.Design.GeneralPlantDrift`. -/
theorem z1_drift_of_trivial_network (κ : closedLoop.RateConstants) (n : Fin 3 → ℕ) :
    countDrift (closedLoop.withTrivialReaction (1 : Fin 5))
        (trivialRateConstants closedLoop κ (1 : Fin 5)) n 0 = μ κ := by
  have hsplit := countDrift_withTrivial closedLoop κ n
    (rAnn := (1 : Fin 5)) (s := 0) (t := 1) annihilation_is_annihilation.1
  have hz := z1_drift κ n
  have hvec : closedLoop.reactionVector (1 : Fin 5) 0 = -1 := by
    simp [closedLoop, rxn, Network.reactionVector_apply]
  have hrate : closedLoop.stochasticMassActionRate κ n (1 : Fin 5) =
      η κ * (n 0 : ℝ) * (n 1 : ℝ) := (rate_eq κ n).2.1
  have hsplit' : ∀ i : Fin 3,
      countDrift closedLoop κ n i =
        countDrift (closedLoop.withTrivialReaction (1 : Fin 5))
            (trivialRateConstants closedLoop κ (1 : Fin 5)) n i +
          closedLoop.stochasticMassActionRate κ n (1 : Fin 5) *
            closedLoop.reactionVector (1 : Fin 5) i := by
    intro i
    have h := congrFun hsplit i
    exact h
  have hzero := hsplit' (0 : Fin 3)
  rw [hz, hvec, hrate] at hzero
  linarith

/-- **No reaction of the antithetic closed loop consumes `Z₂` alone.**  The annihilation
`Z₁ + Z₂ → ∅` is the only consumer of `Z₂`, and it is bimolecular. -/
theorem not_unimolecular_from_z2 (r : closedLoop.R) :
    ¬ closedLoop.IsUnimolecularFrom r 1 := by
  intro h
  fin_cases r
  · have h1 := h.1
    simp [closedLoop, rxn] at h1
  · have h2 := h.2 0 (by decide)
    simp [closedLoop, rxn] at h2
  · have h1 := h.1
    simp [closedLoop, rxn] at h1
  · have h1 := h.1
    simp [closedLoop, rxn] at h1
  · have h1 := h.1
    simp [closedLoop, rxn] at h1

/-- The sum of a function against the `Z₂` indicator. -/
theorem sum_mul_z2_indicator (f : Fin 3 → ℝ) :
    (∑ j, f j * (if j = 1 then 1 else 0)) = f 1 := by
  rw [Fin.sum_univ_three]
  simp

/-- **The `Z₂` direction is in the kernel of the first-order drift matrix.**  The first-order
drift matrix `A` of the closed loop with the annihilation replaced by the trivial reaction has
`A e₂ = 0`: the annihilation is the only consumer of `Z₂` and it is bimolecular, so it does not
contribute to the first-order drift matrix.  The matrix is therefore not Hurwitz (and the
reference reaction `∅ → Z₁` feeds `Z₁` without bound, so the affine drift of the counts has no
equilibrium). -/
theorem firstOrderDriftMatrix_z2_kernel (κ : closedLoop.RateConstants) :
    (firstOrderDriftMatrix (closedLoop.withTrivialReaction (1 : Fin 5))
        (trivialRateConstants closedLoop κ (1 : Fin 5))) *ᵥ
      (fun i => if i = 1 then 1 else 0) = 0 := by
  rw [firstOrderDriftMatrix_withTrivial closedLoop κ
    (rAnn := (1 : Fin 5)) (s := 0) (t := 1) annihilation_is_annihilation.1]
  have hcol : ∀ i : Fin 3, firstOrderDriftCoefficient closedLoop κ (coordIndicator i) 1 = 0 := by
    intro i
    unfold firstOrderDriftCoefficient
    simp [not_unimolecular_from_z2]
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  change (∑ j, closedLoop.firstOrderDriftCoefficient κ (coordIndicator i) j *
      (if j = 1 then 1 else 0)) = 0
  rw [sum_mul_z2_indicator, hcol i]

/-- **No quadratic Lyapunov certificate exists for the unimolecular part of the antithetic
closed loop.**  The certificate of `CRNT.Design.GeneralPlantDrift` requires the Lyapunov equation
`2 xᵀ P A x ⪯ −‖x‖²` for the first-order drift matrix `A`; evaluating it at the `Z₂` direction,
which is in the kernel of `A`, gives `0 ≤ −1`.  This is the precise reason why the general-plant
transfer theorem `GeneralPlant.ergodic_of_sign_controlled` cannot be instantiated for this
network, and why the repository uses the piecewise quadratic `CRNT.Antithetic.lyap` instead. -/
theorem antitheticInstance_no_quadratic_certificate (κ : closedLoop.RateConstants) :
    ¬ Nonempty (QuadraticLyapunovCertificate (closedLoop.withTrivialReaction (1 : Fin 5))
        (trivialRateConstants closedLoop κ (1 : Fin 5))) := by
  rintro ⟨L⟩
  have h := L.lyap (fun i => if i = 1 then 1 else 0)
  rw [firstOrderDriftMatrix_z2_kernel κ] at h
  simp [bilinear, normSq] at h
  linarith

/-! ## 6. Ergodicity of the repository's antithetic closed loop -/

/-- **Ergodicity of the repository's antithetic closed loop, in the general-plant form.**  The
general-plant route — the annihilation sign condition (item 1 above) controlling the cubic term,
and the shape-matrix identification (item 2) — yields the conclusion of
`GeneralPlant.ergodic_of_sign_controlled`: there is a stationary probability law charging every
count, the law of the chain converges to it in total variation from every count, and the
stationary law is unique.  The conclusion coincides with the network-level theorem
`CRNT.AntitheticErgodic.closedLoop_ergodic`, which is the theorem actually used in the
repository: the quadratic certificate of the unimolecular part does not exist (item 5 above), so
the *general-plant* Foster drift bound is not available for this network and the ergodicity is
delivered by the piecewise quadratic `CRNT.Antithetic.lyap`. -/
theorem antitheticInstance_ergodic (κ : closedLoop.RateConstants) :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ b, 0 < π b) ∧ HasSum π 1 ∧
      (∀ u, 0 ≤ u → ∀ b, ∑' x, π x * (closedLoop.jumpSystem κ).Pmin u x b = π b) ∧
      (∀ a, Tendsto (fun t => ∑' b, |(closedLoop.jumpSystem κ).Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : (Fin 3 → ℕ) → ℝ, (∀ b, 0 ≤ μ b) → HasSum μ 1 →
        (∀ u, 0 ≤ u → ∀ b, ∑' x, μ x * (closedLoop.jumpSystem κ).Pmin u x b = μ b) → μ = π) := by
  obtain ⟨π, hπ0, hπ1, hinv, hconv, huniq, -, -⟩ := Antithetic.closedLoop_ergodic κ
  refine ⟨π, hπ0, hπ1, ?_, ?_, ?_⟩
  · intro u hu b
    exact hinv u hu b
  · intro a
    exact hconv a
  · intro μ hμ0 hμ1 hμinv
    exact huniq μ hμ0 hμ1 hμinv

/-! ## 7. A concrete instance: unit rates -/

/-- **Instance with unit rates.**  The annihilation sign condition holds for the antithetic
closed loop with all rate constants equal to `1`. -/
theorem unitRates_annihilation_sign_condition :
    AnnihilationSignCondition
      (generalMatrix (cA Antithetic.unitRates) (cd Antithetic.unitRates / 2)
        (-cc Antithetic.unitRates / 2) (cb Antithetic.unitRates)) 0 1
        (cd Antithetic.unitRates / 2) :=
  antitheticInstance_annihilation_sign_condition Antithetic.unitRates

/-- **Instance with unit rates.**  The repository's Lyapunov function is the general-plant
quadratic on the region `z₂ ≤ z₁`. -/
theorem unitRates_lyap_eq_generalPlant_quadratic (n : Fin 3 → ℕ) (hreg : (n 1 : ℝ) ≤ n 0) :
    lyap Antithetic.unitRates n =
      quadObservable (generalMatrix (cA Antithetic.unitRates) (cd Antithetic.unitRates / 2)
        (-cc Antithetic.unitRates / 2) (cb Antithetic.unitRates)) (fun _ => 0) n :=
  lyap_eq_generalPlant_quadratic Antithetic.unitRates n hreg

end AntitheticInstance
end CRNT

#print axioms CRNT.AntitheticInstance.generalMatrix_quadForm
#print axioms CRNT.AntitheticInstance.generalMatrix_sym
#print axioms CRNT.AntitheticInstance.antitheticInstance_annihilation_sign_condition
#print axioms CRNT.AntitheticInstance.lyap_eq_generalPlant_quadratic
#print axioms CRNT.AntitheticInstance.lyap_eq_generalPlant_quadratic_form
#print axioms CRNT.AntitheticInstance.antitheticInstance_annihilation_drift_le_zero
#print axioms CRNT.AntitheticInstance.antitheticInstance_lyap_annihilation_le_zero
#print axioms CRNT.AntitheticInstance.z1_drift
#print axioms CRNT.AntitheticInstance.z1_drift_of_trivial_network
#print axioms CRNT.AntitheticInstance.not_unimolecular_from_z2
#print axioms CRNT.AntitheticInstance.firstOrderDriftMatrix_z2_kernel
#print axioms CRNT.AntitheticInstance.antitheticInstance_no_quadratic_certificate
#print axioms CRNT.AntitheticInstance.antitheticInstance_ergodic
#print axioms CRNT.AntitheticInstance.unitRates_annihilation_sign_condition
#print axioms CRNT.AntitheticInstance.unitRates_lyap_eq_generalPlant_quadratic
